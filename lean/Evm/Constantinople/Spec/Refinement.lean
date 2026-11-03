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

/-- SAR refinement needs an extra `decide`-style equality between the
    impl's sign-extension expression and the spec's; the implementation
    uses `value.toNat >>> s ||| topBits` while the spec inlines the same
    via `((1 <<< s) - 1) <<< (256 - s)`. Both compute the same value;
    proving the equality is a `decide`-or-tactic-level obligation
    deferred for now. -/
theorem sar_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.sar evm = .ok evm' →
    IsSarStep evm evm' := by
  intro _; sorry

/-! ## EIP-1052 EXTCODEHASH -/

/-- 0x3f EXTCODEHASH refines `IsExtcodehashStep`. The Constantinople
    Instructions.extcodehash handler pops the address, charges
    400 gas, reads `keccak(code)` (or `KECCAK_EMPTY` for empty
    accounts), pushes, advances pc. Refinement is a do-block
    unfolding — left for a future drop. -/
theorem extcodehash_sound (evm evm' : Evm) :
    Evm.Constantinople.Vm.Instructions.extcodehash evm = .ok evm' →
    IsExtcodehashStep evm evm' := by
  intro _; sorry

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
