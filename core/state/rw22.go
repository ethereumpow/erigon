package state

import (
	"bytes"
	"container/heap"
	"encoding/binary"
	"fmt"
	"hash"
	"math/bits"
	"sync"
	"unsafe"

	"github.com/google/btree"
	"github.com/holiman/uint256"
	"github.com/ledgerwatch/erigon-lib/commitment"
	libcommon "github.com/ledgerwatch/erigon-lib/common"
	"github.com/ledgerwatch/erigon-lib/common/length"
	"github.com/ledgerwatch/erigon-lib/kv"
	libstate "github.com/ledgerwatch/erigon-lib/state"
	"golang.org/x/crypto/sha3"

	"github.com/ledgerwatch/erigon/common"
	"github.com/ledgerwatch/erigon/common/dbutils"
	"github.com/ledgerwatch/erigon/core/types"
	"github.com/ledgerwatch/erigon/core/types/accounts"
	"github.com/ledgerwatch/erigon/params"
)

// ReadWriteSet contains ReadSet, WriteSet and BalanceIncrease of a transaction,
// which is processed by a single thread that writes into the ReconState1 and
// flushes to the database
type TxTask struct {
	TxNum              uint64
	BlockNum           uint64
	Rules              *params.Rules
	Header             *types.Header
	Block              *types.Block
	BlockHash          common.Hash
	Sender             *common.Address
	TxIndex            int  // -1 for block initialisation
	Final              bool // true for latest tx in block
	Tx                 types.Transaction
	BalanceIncreaseSet map[common.Address]uint256.Int
	ReadLists          map[string]*KvList
	WriteLists         map[string]*KvList
	AccountPrevs       map[string][]byte
	AccountDels        map[string]*accounts.Account
	StoragePrevs       map[string][]byte
	CodePrevs          map[string]uint64
	ResultsSize        int64
	Error              error
	Logs               []*types.Log
	TraceFroms         map[common.Address]struct{}
	TraceTos           map[common.Address]struct{}
}

type TxTaskQueue []*TxTask

func (h TxTaskQueue) Len() int {
	return len(h)
}

func (h TxTaskQueue) Less(i, j int) bool {
	return h[i].TxNum < h[j].TxNum
}

func (h TxTaskQueue) Swap(i, j int) {
	h[i], h[j] = h[j], h[i]
}

func (h *TxTaskQueue) Push(a interface{}) {
	*h = append(*h, a.(*TxTask))
}

func (h *TxTaskQueue) Pop() interface{} {
	c := *h
	*h = c[:len(c)-1]
	return c[len(c)-1]
}

const CodeSizeTable = "CodeSize"

type State22 struct {
	lock         sync.RWMutex
	receiveWork  *sync.Cond
	triggers     map[uint64]*TxTask
	senderTxNums map[common.Address]uint64
	triggerLock  sync.RWMutex
	queue        TxTaskQueue
	queueLock    sync.Mutex
	changes      map[string]*btree.BTreeG[StateItem]
	sizeEstimate uint64
	txsDone      uint64
	finished     bool
}

type StateItem struct {
	key []byte
	val []byte
}

func stateItemLess(i, j StateItem) bool {
	return bytes.Compare(i.key, j.key) < 0
}

func NewState22() *State22 {
	rs := &State22{
		triggers:     map[uint64]*TxTask{},
		senderTxNums: map[common.Address]uint64{},
		changes:      map[string]*btree.BTreeG[StateItem]{},
	}
	rs.receiveWork = sync.NewCond(&rs.queueLock)
	return rs
}

func (rs *State22) put(table string, key, val []byte) {
	t, ok := rs.changes[table]
	if !ok {
		t = btree.NewG[StateItem](32, stateItemLess)
		rs.changes[table] = t
	}
	item := StateItem{key: key, val: val}
	t.ReplaceOrInsert(item)
	rs.sizeEstimate += uint64(unsafe.Sizeof(item)) + uint64(len(key)) + uint64(len(val))
}

func (rs *State22) Get(table string, key []byte) []byte {
	rs.lock.RLock()
	defer rs.lock.RUnlock()
	return rs.get(table, key)
}

func (rs *State22) get(table string, key []byte) []byte {
	t, ok := rs.changes[table]
	if !ok {
		return nil
	}
	if i, ok := t.Get(StateItem{key: key}); ok {
		return i.val
	}
	return nil
}

func (rs *State22) Flush(rwTx kv.RwTx) error {
	rs.lock.Lock()
	defer rs.lock.Unlock()
	for table, t := range rs.changes {
		var err error
		t.Ascend(func(item StateItem) bool {
			if len(item.val) == 0 {
				if err = rwTx.Delete(table, item.key); err != nil {
					return false
				}
				//fmt.Printf("Flush [%x]=>\n", ks)
			} else {
				if err = rwTx.Put(table, item.key, item.val); err != nil {
					return false
				}
				//fmt.Printf("Flush [%x]=>[%x]\n", ks, val)
			}
			return true
		})
		if err != nil {
			return err
		}
		t.Clear(true)
	}
	rs.sizeEstimate = 0
	return nil
}

func (rs *State22) Schedule() (*TxTask, bool) {
	rs.queueLock.Lock()
	defer rs.queueLock.Unlock()
	for !rs.finished && rs.queue.Len() == 0 {
		rs.receiveWork.Wait()
	}
	if rs.queue.Len() > 0 {
		return heap.Pop(&rs.queue).(*TxTask), true
	}
	return nil, false
}

func (rs *State22) RegisterSender(txTask *TxTask) bool {
	rs.triggerLock.Lock()
	defer rs.triggerLock.Unlock()
	lastTxNum, deferral := rs.senderTxNums[*txTask.Sender]
	if deferral {
		// Transactions with the same sender have obvious data dependency, no point running it before lastTxNum
		// So we add this data dependency as a trigger
		//fmt.Printf("trigger[%d] sender [%x]<=%x\n", lastTxNum, *txTask.Sender, txTask.Tx.Hash())
		rs.triggers[lastTxNum] = txTask
	}
	//fmt.Printf("senderTxNums[%x]=%d\n", *txTask.Sender, txTask.TxNum)
	rs.senderTxNums[*txTask.Sender] = txTask.TxNum
	return !deferral
}

func (rs *State22) CommitTxNum(sender *common.Address, txNum uint64) uint64 {
	rs.queueLock.Lock()
	defer rs.queueLock.Unlock()
	rs.triggerLock.Lock()
	defer rs.triggerLock.Unlock()
	count := uint64(0)
	if triggered, ok := rs.triggers[txNum]; ok {
		heap.Push(&rs.queue, triggered)
		rs.receiveWork.Signal()
		count++
		delete(rs.triggers, txNum)
	}
	if sender != nil {
		if lastTxNum, ok := rs.senderTxNums[*sender]; ok && lastTxNum == txNum {
			// This is the last transaction so far with this sender, remove
			delete(rs.senderTxNums, *sender)
		}
	}
	rs.txsDone++
	return count
}

func (rs *State22) AddWork(txTask *TxTask) {
	txTask.BalanceIncreaseSet = nil
	txTask.ReadLists = nil
	txTask.WriteLists = nil
	txTask.ResultsSize = 0
	txTask.Logs = nil
	txTask.TraceFroms = nil
	txTask.TraceTos = nil
	rs.queueLock.Lock()
	defer rs.queueLock.Unlock()
	heap.Push(&rs.queue, txTask)
	rs.receiveWork.Signal()
}

func (rs *State22) Finish() {
	rs.queueLock.Lock()
	defer rs.queueLock.Unlock()
	rs.finished = true
	rs.receiveWork.Broadcast()
}

func serialise2(a *accounts.Account) []byte {
	var l int
	l++
	if a.Nonce > 0 {
		l += (bits.Len64(a.Nonce) + 7) / 8
	}
	l++
	if !a.Balance.IsZero() {
		l += a.Balance.ByteLen()
	}
	l++
	if !a.IsEmptyCodeHash() {
		l += 32
	}
	l++
	if a.Incarnation > 0 {
		l += (bits.Len64(a.Incarnation) + 7) / 8
	}
	value := make([]byte, l)
	pos := 0
	if a.Nonce == 0 {
		value[pos] = 0
		pos++
	} else {
		nonceBytes := (bits.Len64(a.Nonce) + 7) / 8
		value[pos] = byte(nonceBytes)
		var nonce = a.Nonce
		for i := nonceBytes; i > 0; i-- {
			value[pos+i] = byte(nonce)
			nonce >>= 8
		}
		pos += nonceBytes + 1
	}
	if a.Balance.IsZero() {
		value[pos] = 0
		pos++
	} else {
		balanceBytes := a.Balance.ByteLen()
		value[pos] = byte(balanceBytes)
		pos++
		a.Balance.WriteToSlice(value[pos : pos+balanceBytes])
		pos += balanceBytes
	}
	if a.IsEmptyCodeHash() {
		value[pos] = 0
		pos++
	} else {
		value[pos] = 32
		pos++
		copy(value[pos:pos+32], a.CodeHash[:])
		pos += 32
	}
	if a.Incarnation == 0 {
		value[pos] = 0
	} else {
		incBytes := (bits.Len64(a.Incarnation) + 7) / 8
		value[pos] = byte(incBytes)
		var inc = a.Incarnation
		for i := incBytes; i > 0; i-- {
			value[pos+i] = byte(inc)
			inc >>= 8
		}
	}
	return value
}

func (rs *State22) Apply(emptyRemoval bool, roTx kv.Tx, txTask *TxTask, agg *libstate.Aggregator22) error {
	rs.lock.Lock()
	defer rs.lock.Unlock()
	agg.SetTxNum(txTask.TxNum)
	for addr, increase := range txTask.BalanceIncreaseSet {
		enc0 := rs.get(kv.PlainState, addr.Bytes())
		if enc0 == nil {
			var err error
			enc0, err = roTx.GetOne(kv.PlainState, addr.Bytes())
			if err != nil {
				return err
			}
		}
		a := new(accounts.Account)
		if err := a.DecodeForStorage(enc0); err != nil {
			return err
		}
		if len(enc0) > 0 {
			// Need to convert before balance increase
			enc0 = serialise2(a)
		}
		a.Balance.Add(&a.Balance, &increase)
		var enc1 []byte
		if emptyRemoval && a.Nonce == 0 && a.Balance.IsZero() && a.IsEmptyCodeHash() {
			enc1 = []byte{}
		} else {
			l := a.EncodingLengthForStorage()
			enc1 = make([]byte, l)
			a.EncodeForStorage(enc1)
		}
		rs.put(kv.PlainState, addr.Bytes(), enc1)
		if err := agg.AddAccountPrev(addr.Bytes(), enc0); err != nil {
			return err
		}
	}
	for addrS, original := range txTask.AccountDels {
		addr := []byte(addrS)
		addr1 := make([]byte, len(addr)+8)
		copy(addr1, addr)
		binary.BigEndian.PutUint64(addr1[len(addr):], original.Incarnation)
		prev := serialise2(original)
		if err := agg.AddAccountPrev(addr, prev); err != nil {
			return err
		}
		codePrev := rs.get(kv.Code, original.CodeHash.Bytes())
		if codePrev == nil {
			var err error
			codePrev, err = roTx.GetOne(kv.Code, original.CodeHash.Bytes())
			if err != nil {
				return err
			}
		}
		if err := agg.AddCodePrev(addr, codePrev); err != nil {
			return err
		}
		// Iterate over storage
		cursor, err := roTx.Cursor(kv.PlainState)
		if err != nil {
			return err
		}
		defer cursor.Close()
		var k, v []byte
		var e error
		if k, v, e = cursor.Seek(addr1); err != nil {
			return e
		}
		if !bytes.HasPrefix(k, addr1) {
			k = nil
		}
		rs.changes[kv.PlainState].AscendGreaterOrEqual(StateItem{key: addr1}, func(item StateItem) bool {
			if !bytes.HasPrefix(item.key, addr1) {
				return false
			}
			for ; e == nil && k != nil && bytes.HasPrefix(k, addr1) && bytes.Compare(k, item.key) <= 0; k, v, e = cursor.Next() {
				if !bytes.Equal(k, item.key) {
					// Skip the cursor item when the key is equal, i.e. prefer the item from the changes tree
					if e = agg.AddStoragePrev(addr, libcommon.Copy(k[28:]), libcommon.Copy(v)); e != nil {
						return false
					}
				}
			}
			if e != nil {
				return false
			}
			if e = agg.AddStoragePrev(addr, item.key[28:], item.val); e != nil {
				return false
			}
			return true
		})
		for ; e == nil && k != nil && bytes.HasPrefix(k, addr1); k, v, e = cursor.Next() {
			if e = agg.AddStoragePrev(addr, libcommon.Copy(k[28:]), libcommon.Copy(v)); e != nil {
				return e
			}
		}
		if e != nil {
			return e
		}
	}
	for addrS, enc0 := range txTask.AccountPrevs {
		if err := agg.AddAccountPrev([]byte(addrS), enc0); err != nil {
			return err
		}
	}
	for compositeS, val := range txTask.StoragePrevs {
		composite := []byte(compositeS)
		if err := agg.AddStoragePrev(composite[:20], composite[28:], val); err != nil {
			return err
		}
	}
	for addrS, incarnation := range txTask.CodePrevs {
		addr := []byte(addrS)
		k := dbutils.PlainGenerateStoragePrefix(addr, incarnation)
		codeHash := rs.get(kv.PlainContractCode, k)
		if codeHash == nil {
			var err error
			codeHash, err = roTx.GetOne(kv.PlainContractCode, k)
			if err != nil {
				return err
			}
		}
		var codePrev []byte
		if codeHash != nil {
			codePrev = rs.get(kv.Code, codeHash)
			if codePrev == nil {
				var err error
				codePrev, err = roTx.GetOne(kv.Code, codeHash)
				if err != nil {
					return err
				}
			}
		}
		if err := agg.AddCodePrev(addr, codePrev); err != nil {
			return err
		}
	}
	if txTask.TraceFroms != nil {
		for addr := range txTask.TraceFroms {
			if err := agg.AddTraceFrom(addr.Bytes()); err != nil {
				return err
			}
		}
	}
	if txTask.TraceTos != nil {
		for addr := range txTask.TraceTos {
			if err := agg.AddTraceTo(addr.Bytes()); err != nil {
				return err
			}
		}
	}
	for _, log := range txTask.Logs {
		if err := agg.AddLogAddr(log.Address[:]); err != nil {
			return fmt.Errorf("adding event log for addr %x: %w", log.Address, err)
		}
		for _, topic := range log.Topics {
			if err := agg.AddLogTopic(topic[:]); err != nil {
				return fmt.Errorf("adding event log for topic %x: %w", topic, err)
			}
		}
	}
	if txTask.Final {
		tr := NewTrieReader(rs, agg.MakeContext())
		rootHash, err := agg.ComputeCommitment(tr.branchFn, tr.accountFn, tr.storageFn, tr.trieMerge)
		if err != nil {
			return err
		}
		if !bytes.Equal(txTask.Header.Root.Bytes(), rootHash) {
			// return fmt.Errorf("invalid block hash evaluated for block %d expected %v but got %x", txTask.BlockNum, txTask.Header.Root.String(), rootHash)
			fmt.Printf("invalid block hash evaluated for block %d expected %v but got %x\n", txTask.BlockNum, txTask.Header.Root.String(), rootHash)
		}
	}
	if err := agg.FinishTx(); err != nil {
		return err
	}

	if txTask.WriteLists != nil {
		for table, list := range txTask.WriteLists {
			for i, key := range list.Keys {
				val := list.Vals[i]
				rs.put(table, key, val)
			}
		}
	}
	return nil
}

func (rs *State22) DoneCount() uint64 {
	rs.lock.RLock()
	defer rs.lock.RUnlock()
	return rs.txsDone
}

func (rs *State22) SizeEstimate() uint64 {
	rs.lock.RLock()
	defer rs.lock.RUnlock()
	return rs.sizeEstimate
}

func (rs *State22) ReadsValid(readLists map[string]*KvList) bool {
	rs.lock.RLock()
	defer rs.lock.RUnlock()
	//fmt.Printf("ValidReads\n")
	for table, list := range readLists {
		//fmt.Printf("Table %s\n", table)
		var t *btree.BTreeG[StateItem]
		var ok bool
		if table == CodeSizeTable {
			t, ok = rs.changes[kv.Code]
		} else {
			t, ok = rs.changes[table]
		}
		if !ok {
			continue
		}
		for i, key := range list.Keys {
			val := list.Vals[i]
			if item, ok := t.Get(StateItem{key: key}); ok {
				//fmt.Printf("key [%x] => [%x] vs [%x]\n", key, val, rereadVal)
				if table == CodeSizeTable {
					if binary.BigEndian.Uint64(val) != uint64(len(item.val)) {
						return false
					}
				} else if !bytes.Equal(val, item.val) {
					return false
				}
			}
		}
	}
	return true
}

type trieReader struct {
	rs     *State22
	ctx    *libstate.Aggregator22Context
	keccak hash.Hash
}

func NewTrieReader(rs *State22, ctx *libstate.Aggregator22Context) *trieReader {
	return &trieReader{rs: rs, ctx: ctx, keccak: sha3.NewLegacyKeccak256()}
}

func (r *trieReader) trieMerge(prefix []byte, update commitment.BranchData) (commitment.BranchData, error) {
	stateValue := r.rs.get(kv.StateCommitment, prefix)
	if len(stateValue) == 0 {
		found, prevTxNum := r.ctx.MaxCommitmentTxNum(prefix)
		if found {
			history, found, _, err := r.ctx.ReadCommitmentNoState(prefix, prevTxNum)
			if err != nil {
				return nil, err
			}
			if !found {
				history = make([]byte, 0)
			}
			stateValue = history
		}
	}

	var refNum uint32
	var encodedNum []byte
	if len(stateValue) >= 4 {
		refNum = binary.BigEndian.Uint32(stateValue[:4])
		encodedNum = stateValue[:4]
		stateValue = stateValue[4:]
	}

	stated := commitment.BranchData(stateValue)
	if bytes.Equal(stated, update) {
		return append(encodedNum, stated...), nil
	}

	merged, err := update.MergeHexBranches(stated, nil)
	if err != nil {
		return nil, err
	}

	// fmt.Printf("computeCommitment merge [%x] [%x]+[%x]=>[%x]\n", prefix, stated, update, merged)
	update = merged

	refNumAndValue := make([]byte, 4+len(merged))
	binary.BigEndian.PutUint32(refNumAndValue[:4], refNum+1)
	copy(refNumAndValue[4:], merged)

	r.rs.put(kv.StateCommitment, prefix, refNumAndValue)
	return refNumAndValue, nil
}

func (r *trieReader) branchFn(prefix []byte) ([]byte, error) {
	// Look in the summary table first
	stateValue := r.rs.get(kv.StateCommitment, prefix)
	if stateValue != nil {
		stateValue = stateValue[4:]
	}
	// var stateValue []byte
	// Look in the files and merge, while it becomes complete
	for stateValue == nil || !commitment.BranchData(stateValue).IsComplete() {
		found, txNum := r.ctx.MaxCommitmentTxNum(prefix)
		if !found {
			return nil, nil
		}
		historyValue, found, _, err := r.ctx.ReadCommitmentNoState(prefix, txNum)
		if err != nil {
			return nil, fmt.Errorf("history commitment prefix %x: %w", prefix, err)
		}
		if historyValue == nil {
			if stateValue == nil {
				return nil, nil
			}
			panic(fmt.Sprintf("Incomplete branch data prefix [%x], mergeVal=[%x], maxTxNum=%d\n", commitment.CompactedKeyToHex(prefix), stateValue, txNum))
		}
		//fmt.Printf("Pre-merge prefix [%x] [%x]+[%x], startBlock %d\n", commitment.CompactToHex(prefix), val, mergedVal, startBlock)
		if stateValue == nil {
			stateValue = historyValue
		} else if stateValue, err = commitment.BranchData(historyValue).MergeHexBranches(stateValue, nil); err != nil {
			return nil, err
		}
		//fmt.Printf("Post-merge prefix [%x] [%x], startBlock %d\n", commitment.CompactToHex(prefix), mergedVal, startBlock)
	}
	if stateValue == nil {
		return nil, nil
	}
	//fmt.Printf("Returning branch data prefix [%x], mergeVal=[%x], startBlock=%d\n", commitment.CompactToHex(prefix), mergedVal, startBlock)
	return stateValue[2:], nil // Skip touchMap but keep afterMap
}

func (r *trieReader) accountFn(plainKey []byte, cell *commitment.Cell) (err error) {
	// Look in the summary table first
	enc := r.rs.get(kv.PlainState, plainKey)
	if enc != nil {
		// enc = enc[4:]
	} else {
		// Look in the files
		found, txNum := r.ctx.MaxAccountsTxNum(plainKey)
		if !found {
			return nil
		}
		enc, found, _, err = r.ctx.ReadAccountDataNoState(plainKey, txNum)
		if err != nil {
			return fmt.Errorf("history read account key %x: %v", plainKey, err)
		}
	}

	cell.Nonce = 0
	cell.Balance.Clear()
	copy(cell.CodeHash[:], commitment.EmptyCodeHash)

	account := new(accounts.Account)
	err = account.DecodeForStorage(enc)
	if err != nil {
		return err
	}
	cell.Nonce = account.Nonce
	cell.Balance.SetBytes(account.Balance.Bytes())
	// copy(cell.CodeHash[:], account.CodeHash[:])

	enc = r.rs.get(kv.Code, plainKey)
	if enc != nil {
		// enc = enc[4:]
	} else {
		// Look in the files
		found, txNum := r.ctx.MaxCodeTxNum(plainKey)
		if !found {
			return nil
		}
		enc, found, _, err = r.ctx.ReadAccountCodeNoState(plainKey, txNum)
		if err != nil {
			return fmt.Errorf("history read account code by key %x: %v", plainKey, err)
		}
		if len(enc) > 0 {
			// r.keccak.Reset()
			// r.keccak.Write(enc)
			// r.keccak.Sum(cell.CodeHash[:])
			//r.keccak.(io.Reader).Read()
			copy(cell.CodeHash[:], enc)
		}
	}
	return nil
}

func (r *trieReader) storageFn(plainKey []byte, cell *commitment.Cell) error {
	// Look in the summary table first
	enc := r.rs.get(kv.PlainState, plainKey)
	if enc != nil {
		// enc = enc[4:]
	} else {
		// Look in the files
		found, txNum := r.ctx.MaxStorageTxNum(plainKey[:length.Addr], plainKey[length.Addr:])
		if !found {
			return nil
		}
		var err error
		enc, found, _, err = r.ctx.ReadAccountStorageNoState(plainKey[:length.Addr], plainKey[length.Addr:], txNum)
		if err != nil {
			return fmt.Errorf("history read storage key %x: %v", plainKey, err)
		}
	}
	cell.StorageLen = len(enc)
	copy(cell.Storage[:], enc)
	return nil
}

// KvList sort.Interface to sort write list by keys
type KvList struct {
	Keys, Vals [][]byte
}

func (l KvList) Len() int {
	return len(l.Keys)
}

func (l KvList) Less(i, j int) bool {
	return bytes.Compare(l.Keys[i], l.Keys[j]) < 0
}

func (l *KvList) Swap(i, j int) {
	l.Keys[i], l.Keys[j] = l.Keys[j], l.Keys[i]
	l.Vals[i], l.Vals[j] = l.Vals[j], l.Vals[i]
}

type StateWriter22 struct {
	rs           *State22
	txNum        uint64
	writeLists   map[string]*KvList
	accountPrevs map[string][]byte
	accountDels  map[string]*accounts.Account
	storagePrevs map[string][]byte
	codePrevs    map[string]uint64
}

func NewStateWriter22(rs *State22) *StateWriter22 {
	return &StateWriter22{
		rs: rs,
		writeLists: map[string]*KvList{
			kv.PlainState:        {},
			kv.Code:              {},
			kv.PlainContractCode: {},
			kv.IncarnationMap:    {},
		},
		accountPrevs: map[string][]byte{},
		accountDels:  map[string]*accounts.Account{},
		storagePrevs: map[string][]byte{},
		codePrevs:    map[string]uint64{},
	}
}

func (w *StateWriter22) SetTxNum(txNum uint64) {
	w.txNum = txNum
}

func (w *StateWriter22) ResetWriteSet() {
	w.writeLists = map[string]*KvList{
		kv.PlainState:        {},
		kv.Code:              {},
		kv.PlainContractCode: {},
		kv.IncarnationMap:    {},
	}
	w.accountPrevs = map[string][]byte{}
	w.accountDels = map[string]*accounts.Account{}
	w.storagePrevs = map[string][]byte{}
	w.codePrevs = map[string]uint64{}
}

func (w *StateWriter22) WriteSet() map[string]*KvList {
	return w.writeLists
}

func (w *StateWriter22) PrevAndDels() (map[string][]byte, map[string]*accounts.Account, map[string][]byte, map[string]uint64) {
	return w.accountPrevs, w.accountDels, w.storagePrevs, w.codePrevs
}

func (w *StateWriter22) UpdateAccountData(address common.Address, original, account *accounts.Account) error {
	value := make([]byte, account.EncodingLengthForStorage())
	account.EncodeForStorage(value)
	//fmt.Printf("account [%x]=>{Balance: %d, Nonce: %d, Root: %x, CodeHash: %x} txNum: %d\n", address, &account.Balance, account.Nonce, account.Root, account.CodeHash, w.txNum)
	w.writeLists[kv.PlainState].Keys = append(w.writeLists[kv.PlainState].Keys, address.Bytes())
	w.writeLists[kv.PlainState].Vals = append(w.writeLists[kv.PlainState].Vals, value)
	var prev []byte
	if original.Initialised {
		prev = serialise2(original)
	}
	w.accountPrevs[string(address.Bytes())] = prev
	return nil
}

func (w *StateWriter22) UpdateAccountCode(address common.Address, incarnation uint64, codeHash common.Hash, code []byte) error {
	w.writeLists[kv.Code].Keys = append(w.writeLists[kv.Code].Keys, codeHash.Bytes())
	w.writeLists[kv.Code].Vals = append(w.writeLists[kv.Code].Vals, code)
	if len(code) > 0 {
		//fmt.Printf("code [%x] => [%x] CodeHash: %x, txNum: %d\n", address, code, codeHash, w.txNum)
		w.writeLists[kv.PlainContractCode].Keys = append(w.writeLists[kv.PlainContractCode].Keys, dbutils.PlainGenerateStoragePrefix(address[:], incarnation))
		w.writeLists[kv.PlainContractCode].Vals = append(w.writeLists[kv.PlainContractCode].Vals, codeHash.Bytes())
	}
	w.codePrevs[string(address.Bytes())] = incarnation
	return nil
}

func (w *StateWriter22) DeleteAccount(address common.Address, original *accounts.Account) error {
	w.writeLists[kv.PlainState].Keys = append(w.writeLists[kv.PlainState].Keys, address.Bytes())
	w.writeLists[kv.PlainState].Vals = append(w.writeLists[kv.PlainState].Vals, []byte{})
	if original.Incarnation > 0 {
		var b [8]byte
		binary.BigEndian.PutUint64(b[:], original.Incarnation)
		w.writeLists[kv.IncarnationMap].Keys = append(w.writeLists[kv.IncarnationMap].Keys, address.Bytes())
		w.writeLists[kv.IncarnationMap].Vals = append(w.writeLists[kv.IncarnationMap].Vals, b[:])
	}
	if original.Initialised {
		w.accountDels[string(address.Bytes())] = original
	}
	return nil
}

func (w *StateWriter22) WriteAccountStorage(address common.Address, incarnation uint64, key *common.Hash, original, value *uint256.Int) error {
	if *original == *value {
		return nil
	}
	composite := dbutils.PlainGenerateCompositeStorageKey(address.Bytes(), incarnation, key.Bytes())
	w.writeLists[kv.PlainState].Keys = append(w.writeLists[kv.PlainState].Keys, composite)
	w.writeLists[kv.PlainState].Vals = append(w.writeLists[kv.PlainState].Vals, value.Bytes())
	//fmt.Printf("storage [%x] [%x] => [%x], txNum: %d\n", address, *key, v, w.txNum)
	w.storagePrevs[string(composite)] = original.Bytes()
	return nil
}

func (w *StateWriter22) CreateContract(address common.Address) error {
	return nil
}

type StateReader22 struct {
	tx        kv.Tx
	txNum     uint64
	trace     bool
	rs        *State22
	composite []byte
	readLists map[string]*KvList
}

func NewStateReader22(rs *State22) *StateReader22 {
	return &StateReader22{
		rs: rs,
		readLists: map[string]*KvList{
			kv.PlainState:     {},
			kv.Code:           {},
			CodeSizeTable:     {},
			kv.IncarnationMap: {},
		},
	}
}

func (r *StateReader22) SetTxNum(txNum uint64) {
	r.txNum = txNum
}

func (r *StateReader22) SetTx(tx kv.Tx) {
	r.tx = tx
}

func (r *StateReader22) ResetReadSet() {
	r.readLists = map[string]*KvList{
		kv.PlainState:     {},
		kv.Code:           {},
		CodeSizeTable:     {},
		kv.IncarnationMap: {},
	}
}

func (r *StateReader22) ReadSet() map[string]*KvList {
	return r.readLists
}

func (r *StateReader22) SetTrace(trace bool) {
	r.trace = trace
}

func (r *StateReader22) ReadAccountData(address common.Address) (*accounts.Account, error) {
	enc := r.rs.Get(kv.PlainState, address.Bytes())
	if enc == nil {
		var err error
		enc, err = r.tx.GetOne(kv.PlainState, address.Bytes())
		if err != nil {
			return nil, err
		}
	}
	r.readLists[kv.PlainState].Keys = append(r.readLists[kv.PlainState].Keys, address.Bytes())
	r.readLists[kv.PlainState].Vals = append(r.readLists[kv.PlainState].Vals, common.CopyBytes(enc))
	if len(enc) == 0 {
		return nil, nil
	}
	var a accounts.Account
	if err := a.DecodeForStorage(enc); err != nil {
		return nil, err
	}
	if r.trace {
		fmt.Printf("ReadAccountData [%x] => [nonce: %d, balance: %d, codeHash: %x], txNum: %d\n", address, a.Nonce, &a.Balance, a.CodeHash, r.txNum)
	}
	return &a, nil
}

func (r *StateReader22) ReadAccountStorage(address common.Address, incarnation uint64, key *common.Hash) ([]byte, error) {
	if cap(r.composite) < 20+8+32 {
		r.composite = make([]byte, 20+8+32)
	} else if len(r.composite) != 20+8+32 {
		r.composite = r.composite[:20+8+32]
	}
	copy(r.composite, address.Bytes())
	binary.BigEndian.PutUint64(r.composite[20:], incarnation)
	copy(r.composite[20+8:], key.Bytes())

	enc := r.rs.Get(kv.PlainState, r.composite)
	if enc == nil {
		var err error
		enc, err = r.tx.GetOne(kv.PlainState, r.composite)
		if err != nil {
			return nil, err
		}
	}
	r.readLists[kv.PlainState].Keys = append(r.readLists[kv.PlainState].Keys, common.CopyBytes(r.composite))
	r.readLists[kv.PlainState].Vals = append(r.readLists[kv.PlainState].Vals, common.CopyBytes(enc))
	if r.trace {
		if enc == nil {
			fmt.Printf("ReadAccountStorage [%x] [%x] => [], txNum: %d\n", address, key.Bytes(), r.txNum)
		} else {
			fmt.Printf("ReadAccountStorage [%x] [%x] => [%x], txNum: %d\n", address, key.Bytes(), enc, r.txNum)
		}
	}
	if enc == nil {
		return nil, nil
	}
	return enc, nil
}

func (r *StateReader22) ReadAccountCode(address common.Address, incarnation uint64, codeHash common.Hash) ([]byte, error) {
	enc := r.rs.Get(kv.Code, codeHash.Bytes())
	if enc == nil {
		var err error
		enc, err = r.tx.GetOne(kv.Code, codeHash.Bytes())
		if err != nil {
			return nil, err
		}
	}
	r.readLists[kv.Code].Keys = append(r.readLists[kv.Code].Keys, address.Bytes())
	r.readLists[kv.Code].Vals = append(r.readLists[kv.Code].Vals, common.CopyBytes(enc))
	if r.trace {
		fmt.Printf("ReadAccountCode [%x] => [%x], txNum: %d\n", address, enc, r.txNum)
	}
	return enc, nil
}

func (r *StateReader22) ReadAccountCodeSize(address common.Address, incarnation uint64, codeHash common.Hash) (int, error) {
	enc := r.rs.Get(kv.Code, codeHash.Bytes())
	if enc == nil {
		var err error
		enc, err = r.tx.GetOne(kv.Code, codeHash.Bytes())
		if err != nil {
			return 0, err
		}
	}
	var sizebuf [8]byte
	binary.BigEndian.PutUint64(sizebuf[:], uint64(len(enc)))
	r.readLists[CodeSizeTable].Keys = append(r.readLists[CodeSizeTable].Keys, address.Bytes())
	r.readLists[CodeSizeTable].Vals = append(r.readLists[CodeSizeTable].Vals, sizebuf[:])
	size := len(enc)
	if r.trace {
		fmt.Printf("ReadAccountCodeSize [%x] => [%d], txNum: %d\n", address, size, r.txNum)
	}
	return size, nil
}

func (r *StateReader22) ReadAccountIncarnation(address common.Address) (uint64, error) {
	enc := r.rs.Get(kv.IncarnationMap, address.Bytes())
	if enc == nil {
		var err error
		enc, err = r.tx.GetOne(kv.IncarnationMap, address.Bytes())
		if err != nil {
			return 0, err
		}
	}
	r.readLists[kv.IncarnationMap].Keys = append(r.readLists[kv.IncarnationMap].Keys, address.Bytes())
	r.readLists[kv.IncarnationMap].Vals = append(r.readLists[kv.IncarnationMap].Vals, common.CopyBytes(enc))
	if len(enc) == 0 {
		return 0, nil
	}
	return binary.BigEndian.Uint64(enc), nil
}
