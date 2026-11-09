/-
  Evm.Constantinople.Spec.Refinement — proofs that the Constantinople
  Effect interpreter refines the Constantinople Spec relations.

  Pattern: per the Frontier/Spec/Refinement.lean template, each
  refinement is a soundness theorem:

    ∀ inputs, executable inputs = .ok output → IsXxxStep inputs output

  Most of Constantinople's new opcodes (SHL/SHR/SAR) are pure binary
  ops and reduce to a one-line invocation of `runBinary_sound` from
  the Frontier refinement layer. EXTCODEHASH is a state-reading
  unary op. SSTORE (EIP-1283) and CREATE2 are heavier; we state the
  obligations and discharge what we can — refinements that require
  recursive induction over the trampoline are left as `sorry` per
  the SPEC-METHODOLOGY ("tolerate sorries on heavier obligations").

  EELS reference: refinement obligations come from the Effect.lean
  step1 dispatch we ship; the relations come from this fork's Spec/
  files (BitwiseStep, ExtcodehashStep, SstoreStep, Create2Step).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Constantinople.Spec.BitwiseStep
import Evm.Constantinople.Spec.ExtcodehashStep
import Evm.Constantinople.Spec.SstoreStep
import Evm.Constantinople.Spec.Create2Step
import Evm.Constantinople.Vm.Instructions.Bitwise
import Evm.Constantinople.Vm.Instructions.Environment
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Constantinople.Vm.Effect

namespace Evm.Constantinople.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Constantinople.Spec
open Evm.Frontier.Spec.Refinement (runBinary_sound runBinary_complete)

/-! ## EIP-145 shift opcodes -/

/-- 0x1b SHL is a binary op with the bitwise-shift-left semantics. -/
theorem shl_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.shl evm = .ok evm' →
    IsShlStep evm evm' := by
  intro h
  -- `Instructions.shl = runBinary Gas.veryLow shl_op` where
  -- `shl_op shift value` is exactly the operation embedded in
  -- `IsShlStep` (defined as `IsBinaryStep shl_op Gas.veryLow`).
  -- So the proof is structurally `runBinary_sound`.
  exact runBinary_sound _ _ evm evm' h

theorem shr_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.shr evm = .ok evm' →
    IsShrStep evm evm' := by
  intro h; exact runBinary_sound _ _ evm evm' h

/-- The impl's negative-SAR fill mask `MAX ^^^ (2^(256-s) - 1)` is the spec's top-`s`-bits
    mask `(2^s - 1) <<< (256 - s)`, bit by bit. -/
theorem sar_mask_eq (s : Nat) (hs : s < 256) :
    ((1 <<< 256) - 1) ^^^ ((1 <<< (256 - s)) - 1) = ((1 <<< s) - 1) <<< (256 - s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft]
  by_cases h1 : i < 256 <;> by_cases h2 : i < 256 - s <;> simp [h1, h2] <;> omega

/-- 0x1d SAR refines `IsSarStep`: EELS `forks/constantinople/vm/instructions/bitwise.py::
    bitwise_sar` (216-): Python's arithmetic `>>` on the signed value; shift ≥ 256 gives 0
    or all-ones by sign. The impl's fill mask equals the spec's (`sar_mask_eq`). -/
theorem sar_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.sar evm = .ok evm' →
    IsSarStep evm evm' := by
  intro h
  have := runBinary_sound _ _ evm evm' h
  unfold IsSarStep
  have hf : (fun shift value => match Evm.Constantinople.Vm.Instructions.toSigned value with
      | (neg, _mag) =>
        let s := shift.toNat
        if s ≥ 256 then if neg = true then Evm.U256.ofNat (1 <<< 256 - 1) else 0
        else if ¬neg = true then Evm.U256.ofNat (value.toNat >>> s)
        else Evm.U256.ofNat ((value.toNat >>> s) ||| ((1 <<< 256) - 1 ^^^ (1 <<< (256 - s)) - 1)))
      = (fun (shift value : Evm.U256) =>
        let neg := value.toNat ≥ (1 <<< 255)
        let s   := shift.toNat
        if s ≥ 256 then
          if neg then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
        else if ¬ neg then
          Evm.U256.ofNat (value.toNat >>> s)
        else
          Evm.U256.ofNat ((value.toNat >>> s) ||| (((1 <<< s) - 1) <<< (256 - s)))) := by
    funext shift value
    unfold Evm.Constantinople.Vm.Instructions.toSigned
    by_cases hn : value.toNat ≥ 1 <<< 255
    · rw [ite_eq_left hn]
      by_cases hs : shift.toNat ≥ 256
      · show (if shift.toNat ≥ 256 then _ else _) = (if shift.toNat ≥ 256 then _ else _)
        rw [ite_eq_left hs, ite_eq_left hs, ite_eq_left rfl, ite_eq_left hn]
      · show (if shift.toNat ≥ 256 then _ else _) = (if shift.toNat ≥ 256 then _ else _)
        rw [ite_eq_right hs, ite_eq_right hs, ite_eq_right (by decide), ite_eq_right (not_not_intro hn), sar_mask_eq _ (by omega)]
    · rw [ite_eq_right hn]
      by_cases hs : shift.toNat ≥ 256
      · show (if shift.toNat ≥ 256 then _ else _) = (if shift.toNat ≥ 256 then _ else _)
        rw [ite_eq_left hs, ite_eq_left hs, ite_eq_right (by decide), ite_eq_right hn]
      · show (if shift.toNat ≥ 256 then _ else _) = (if shift.toNat ≥ 256 then _ else _)
        rw [ite_eq_right hs, ite_eq_right hs, ite_eq_left (by decide), ite_eq_left hn]
  exact hf ▸ this

/-! ## EIP-1052 EXTCODEHASH -/

/-- 0x3f EXTCODEHASH refines `IsExtcodehashStep`: pop the address, charge
    `GAS_CODE_HASH` (400), push 0 for an absent-or-empty account, else `keccak(code)`.
    EELS `forks/constantinople/vm/instructions/environment.py::extcodehash` (450-477):
    `account == EMPTY_ACCOUNT` (absent accounts read as `EMPTY_ACCOUNT`) → 0, else
    `account.code_hash`. -/
theorem extcodehash_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.extcodehash evm = .ok evm' →
    IsExtcodehashStep evm evm' := by
  intro h
  unfold Evm.Constantinople.Vm.Instructions.extcodehash at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, ⟨a, rest⟩, hp, s', hpush, h⟩
  have hg' := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  have hs' := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  injection h with h
  refine ⟨a, rest, hStack, hs'.1, hg'.1, ?_⟩
  rw [← h, hs'.2, hg'.2]
  have hb : ∀ (e i : Bool) (x y : Evm.U256),
      (if (!e || i) = true then x else y) = (if ¬ e = true ∨ i = true then x else y) := by
    intro e i x y; cases e <;> cases i <;> rfl
  simp only [hb]
  rfl  -- the impl's and the spec's (private) `u256ToAddr` are both `Address.ofNat ∘ toNat`

/-! ## EIP-1283 SSTORE -/

/-- 0x55 SSTORE under EIP-1283 net-metering refines `IsSstoreStep`.
    Nine-case decision tree with refund counter (clamped at 0)
    deltas — the heaviest opcode refinement in this fork. Left as
    `sorry` per methodology; the spec captures the obligations. -/
theorem sstore_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.sstore evm = .ok evm' →
    IsSstoreStep evm evm' := by
  intro _; sorry

/-! ## EIP-1014 CREATE2

    CREATE2 yields a `.createLike` effect that's handled by the
    trampoline. The relation here covers the entry-point obligations
    (`IsCreate2FailFastDepth`, `IsCreate2FailFastBalance`,
    `IsCreate2EntryCollision`, `IsCreate2EntrySuccess`); the merge
    phase belongs to a separate trampoline-refinement theorem. The
    full refinement requires induction on the recursive sub-frame
    execution and is out of scope for the relation-only pass. -/

end Evm.Constantinople.Spec.Refinement
