package cltypes

import (
	"fmt"

	libcommon "github.com/ledgerwatch/erigon-lib/common"

	"github.com/ledgerwatch/erigon/cl/cltypes/ssz_utils"
	"github.com/ledgerwatch/erigon/cl/merkle_tree"
	"github.com/ledgerwatch/erigon/cl/utils"
	"github.com/ledgerwatch/erigon/common"
)

const (
	DepositProofLength = 33
	SyncCommitteeSize  = 512
)

type DepositData struct {
	PubKey                [48]byte
	WithdrawalCredentials [32]byte // 32 byte
	Amount                uint64
	Signature             [96]byte
	Root                  libcommon.Hash // Ignored if not for hashing
}

func (d *DepositData) EncodeSSZ(dst []byte) []byte {
	buf := dst
	buf = append(buf, d.PubKey[:]...)
	buf = append(buf, d.WithdrawalCredentials[:]...)
	buf = append(buf, ssz_utils.Uint64SSZ(d.Amount)...)
	buf = append(buf, d.Signature[:]...)
	return buf
}

func (d *DepositData) UnmarshalSSZ(buf []byte) error {
	copy(d.PubKey[:], buf)
	copy(d.WithdrawalCredentials[:], buf[48:])
	d.Amount = ssz_utils.UnmarshalUint64SSZ(buf[80:])
	copy(d.Signature[:], buf[88:])
	return nil
}

func (d *DepositData) SizeSSZ() int {
	return 184
}

func (d *DepositData) HashTreeRoot() ([32]byte, error) {
	var (
		leaves = make([][32]byte, 4)
		err    error
	)
	leaves[0], err = merkle_tree.PublicKeyRoot(d.PubKey)
	if err != nil {
		return [32]byte{}, err
	}
	leaves[1] = d.WithdrawalCredentials
	leaves[2] = merkle_tree.Uint64Root(d.Amount)
	leaves[3], err = merkle_tree.SignatureRoot(d.Signature)
	if err != nil {
		return [32]byte{}, err
	}
	return merkle_tree.ArraysRoot(leaves, 4)
}

type Deposit struct {
	// Merkle proof is used for deposits
	Proof [][]byte // 33 X 32 size.
	Data  *DepositData
}

func (d *Deposit) EncodeSSZ(dst []byte) []byte {

	buf := dst
	for _, proofSeg := range d.Proof {
		buf = append(buf, proofSeg...)
	}
	buf = d.Data.EncodeSSZ(buf)
	return buf
}

func (d *Deposit) UnmarshalSSZ(buf []byte) error {
	d.Proof = make([][]byte, DepositProofLength)
	for i := range d.Proof {
		d.Proof[i] = common.CopyBytes(buf[i*32 : i*32+32])
	}

	if d.Data == nil {
		d.Data = new(DepositData)
	}
	return d.Data.UnmarshalSSZ(buf[33*32:])
}

func (d *Deposit) UnmarshalSSZWithVersion(buf []byte, _ int) error {
	return d.UnmarshalSSZ(buf)
}

func (d *Deposit) EncodingSizeSSZ() int {
	return 1240
}

func (d *Deposit) HashTreeRoot() ([32]byte, error) {
	proofLeaves := make([][32]byte, DepositProofLength)
	for i, segProof := range d.Proof {
		proofLeaves[i] = libcommon.BytesToHash(segProof)
	}

	proofRoot, err := merkle_tree.ArraysRoot(proofLeaves, 64)
	if err != nil {
		return [32]byte{}, err
	}

	depositRoot, err := d.Data.HashTreeRoot()
	if err != nil {
		return [32]byte{}, err
	}

	return merkle_tree.ArraysRoot([][32]byte{proofRoot, depositRoot}, 2)
}

type VoluntaryExit struct {
	Epoch          uint64
	ValidatorIndex uint64
}

func (e *VoluntaryExit) EncodeSSZ(buf []byte) []byte {
	return append(buf, append(ssz_utils.Uint64SSZ(e.Epoch), ssz_utils.Uint64SSZ(e.ValidatorIndex)...)...)
}

func (e *VoluntaryExit) DecodeSSZ(buf []byte) error {
	e.Epoch = ssz_utils.UnmarshalUint64SSZ(buf)
	e.ValidatorIndex = ssz_utils.UnmarshalUint64SSZ(buf[8:])
	return nil
}

func (e *VoluntaryExit) HashTreeRoot() ([32]byte, error) {
	epochRoot := merkle_tree.Uint64Root(e.Epoch)
	indexRoot := merkle_tree.Uint64Root(e.ValidatorIndex)
	return utils.Keccak256(epochRoot[:], indexRoot[:]), nil
}

func (e *VoluntaryExit) SizeSSZ() int {
	return 16
}

type SignedVoluntaryExit struct {
	VolunaryExit *VoluntaryExit
	Signature    [96]byte
}

func (e *SignedVoluntaryExit) EncodeSSZ(dst []byte) []byte {
	buf := e.VolunaryExit.EncodeSSZ(dst)
	return append(buf, e.Signature[:]...)
}

func (e *SignedVoluntaryExit) UnmarshalSSZ(buf []byte) error {
	if e.VolunaryExit == nil {
		e.VolunaryExit = new(VoluntaryExit)
	}

	if err := e.VolunaryExit.DecodeSSZ(buf); err != nil {
		return err
	}
	copy(e.Signature[:], buf[16:])
	return nil
}

func (e *SignedVoluntaryExit) UnmarshalSSZWithVersion(buf []byte, _ int) error {
	return e.UnmarshalSSZ(buf)
}

func (e *SignedVoluntaryExit) HashTreeRoot() ([32]byte, error) {
	sigRoot, err := merkle_tree.SignatureRoot(e.Signature)
	if err != nil {
		return [32]byte{}, err
	}
	exitRoot, err := e.VolunaryExit.HashTreeRoot()
	if err != nil {
		return [32]byte{}, err
	}
	return utils.Keccak256(exitRoot[:], sigRoot[:]), nil
}

func (e *SignedVoluntaryExit) EncodingSizeSSZ() int {
	return 96 + e.VolunaryExit.SizeSSZ()
}

/*
 * Sync committe public keys and their aggregate public keys, we use array of pubKeys.
 */
type SyncCommittee struct {
	PubKeys            [][48]byte `ssz-size:"512,48"`
	AggregatePublicKey [48]byte   `ssz-size:"48"`
}

// MarshalSSZTo ssz marshals the SyncCommittee object to a target array
func (s *SyncCommittee) EncodeSSZ(buf []byte) ([]byte, error) {
	dst := buf

	if len(s.PubKeys) != SyncCommitteeSize {
		return nil, fmt.Errorf("wrong sync committee size")
	}
	for _, key := range s.PubKeys {
		dst = append(dst, key[:]...)
	}
	dst = append(dst, s.AggregatePublicKey[:]...)

	return dst, nil
}

// UnmarshalSSZ ssz unmarshals the SyncCommittee object
func (s *SyncCommittee) DecodeSSZ(buf []byte) error {
	if len(buf) < 24624 {
		return ssz_utils.ErrLowBufferSize
	}

	s.PubKeys = make([][48]byte, SyncCommitteeSize)
	for i := range s.PubKeys {
		copy(s.PubKeys[i][:], buf[i*48:(i*48)+48])
	}
	copy(s.AggregatePublicKey[:], buf[24576:])

	return nil
}

// SizeSSZ returns the ssz encoded size in bytes for the SyncCommittee object
func (s *SyncCommittee) SizeSSZ() (size int) {
	size = 24624
	return
}

// HashTreeRootWith ssz hashes the SyncCommittee object with a hasher
func (s *SyncCommittee) HashSSZ() ([32]byte, error) {
	// Compute the sync committee leaf
	pubKeysLeaves := make([][32]byte, SyncCommitteeSize)
	if len(s.PubKeys) != SyncCommitteeSize {
		return [32]byte{}, fmt.Errorf("wrong sync committee size")
	}
	var err error
	for i, key := range s.PubKeys {
		pubKeysLeaves[i], err = merkle_tree.PublicKeyRoot(key)
		if err != nil {
			return [32]byte{}, err
		}
	}
	pubKeyLeaf, err := merkle_tree.ArraysRoot(pubKeysLeaves, SyncCommitteeSize)
	if err != nil {
		return [32]byte{}, err
	}
	aggregatePublicKeyRoot, err := merkle_tree.PublicKeyRoot(s.AggregatePublicKey)
	if err != nil {
		return [32]byte{}, err
	}

	return merkle_tree.ArraysRoot([][32]byte{pubKeyLeaf, aggregatePublicKeyRoot}, 2)
}