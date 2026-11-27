/-
  Evm.Avalanche.Trie — Coreth storage-trie key normalization and 5-field multi-coin account RLP.

  Source: avalanchego d38de7e0
    graft/coreth/core/state/state_object.go   NormalizeStateKey (clears bit 0 of byte 0 before
                                              keccak256 so odd first-byte keys stay reserved for
                                              legacy multi-coin balances)
    graft/coreth/core/types/state_account.go  StateAccount RLP (4 fields normally; 5th field
                                              when MultiCoin = true)
-/

import Evm.BaseTypes
import Evm.Rlp

namespace Evm.Avalanche.Trie

/-- Clear the lowest bit of byte 0 of a storage slot key (`NormalizeStateKey`).
    Empty byte arrays are returned unchanged. -/
def normalizeStorageSlot (slot : Evm.Bytes) : Evm.Bytes :=
  if h : 0 < slot.data.size then
    ⟨slot.data.set 0 (slot.data[0]'h &&& 0xfe) h⟩
  else
    slot

/-- Coreth account RLP encoding: ALWAYS encodes 5 fields
    `[nonce, balance, storageRoot, codeHash, multiCoin]` where the 5th RLP item is
    empty bytes (`0x80`) when `multiCoin = false` and single byte `0x01` when `multiCoin = true`.
    (avalanchego `graft/coreth/core/types/state_account.go` `SlimAccount` / `StateAccount`.) -/
def corethAccountRlp (nonce balance : Nat) (storageRoot codeHash : Evm.Bytes) (multiCoin : Bool) :
    Evm.Rlp.Item :=
  .list
    [ .bytes (Evm.Rlp.natToBytes nonce)
    , .bytes (Evm.Rlp.natToBytes balance)
    , .bytes storageRoot
    , .bytes codeHash
    , .bytes (if multiCoin then ByteArray.mk #[1] else ByteArray.empty) ]

theorem normalizeStorageSlot_size (slot : Evm.Bytes) :
    (normalizeStorageSlot slot).size = slot.size := by
  unfold normalizeStorageSlot
  split
  · next h => exact Array.size_set h
  · rfl

private theorem u8_clear_bit0_even (b : UInt8) : (b &&& 0xfe) &&& 0x01 = 0 := by
  apply UInt8.eq_of_toBitVec_eq
  change (b.toBitVec &&& 0xfe#8) &&& 0x01#8 = 0#8
  rw [BitVec.and_assoc]
  have h : (0xfe#8 &&& 0x01#8) = 0#8 := rfl
  rw [h, BitVec.and_zero]

private theorem u8_clear_bit0_idem (b : UInt8) : (b &&& 0xfe) &&& 0xfe = b &&& 0xfe := by
  apply UInt8.eq_of_toBitVec_eq
  change (b.toBitVec &&& 0xfe#8) &&& 0xfe#8 = b.toBitVec &&& 0xfe#8
  rw [BitVec.and_assoc]
  have h : (0xfe#8 &&& 0xfe#8) = 0xfe#8 := rfl
  rw [h]

theorem normalizeStorageSlot_byte0_even (slot : Evm.Bytes) (h : 0 < slot.size) :
    (normalizeStorageSlot slot)[0]'(by rw [normalizeStorageSlot_size]; exact h) &&& 0x01 = 0 := by
  have hd : 0 < slot.data.size := h
  simp only [normalizeStorageSlot, hd, dite_true]
  change (slot.data.set 0 (slot.data[0]'hd &&& 0xfe) hd)[0]'(by simpa using hd) &&& 0x01 = 0
  rw [Array.getElem_set_self]
  exact u8_clear_bit0_even _

theorem normalizeStorageSlot_idempotent (slot : Evm.Bytes) :
    normalizeStorageSlot (normalizeStorageSlot slot) = normalizeStorageSlot slot := by
  cases slot with | mk data =>
  by_cases h : 0 < data.size
  · have h2 : 0 < (data.set 0 (data[0]'h &&& 0xfe) h).size := by simpa using h
    simp only [normalizeStorageSlot, h, h2, dite_true]
    apply congrArg ByteArray.mk
    apply Array.ext
    · simp
    · intro i hi1 hi2
      by_cases hi0 : i = 0
      · subst hi0
        simp only [Array.getElem_set_self]
        exact u8_clear_bit0_idem _
      · simp [Array.getElem_set, Ne.symm hi0]
  · simp [normalizeStorageSlot, h]

theorem corethAccountRlp_false_is_5fields (n b : Nat) (sr ch : Evm.Bytes) :
    corethAccountRlp n b sr ch false =
      .list [ .bytes (Evm.Rlp.natToBytes n)
            , .bytes (Evm.Rlp.natToBytes b)
            , .bytes sr
            , .bytes ch
            , .bytes ByteArray.empty ] := by
  rfl

theorem corethAccountRlp_true_is_5fields (n b : Nat) (sr ch : Evm.Bytes) :
    corethAccountRlp n b sr ch true =
      .list [ .bytes (Evm.Rlp.natToBytes n)
            , .bytes (Evm.Rlp.natToBytes b)
            , .bytes sr
            , .bytes ch
            , .bytes (ByteArray.mk #[1]) ] := by
  rfl

end Evm.Avalanche.Trie
