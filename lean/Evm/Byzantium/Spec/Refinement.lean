/-
  Evm.Byzantium.Spec.Refinement — proofs that the Byzantium Effect
  interpreter refines the Byzantium Spec relations.

  Byzantium adds:

    * `RevertStep.lean` — EIP-140 0xfd REVERT (terminal halting step).
    * `ReturndataStep.lean` — EIP-211 0x3d RETURNDATASIZE +
                              0x3e RETURNDATACOPY.

  RETURNDATASIZE is a NullaryPush; the rest involve memory expansion
  and/or trampoline obligations. We state every soundness theorem
  and discharge with `sorry` where the impl shape doesn't reduce to
  a Frontier shape lemma.
-/

import Evm.Frontier.Spec.Refinement
import Evm.Byzantium.Spec.RevertStep
import Evm.Byzantium.Spec.ReturndataStep
import Evm.Byzantium.Vm.Instructions.Memory
import Evm.Byzantium.Vm.Instructions.System
import Evm.Byzantium.Vm.Effect

namespace Evm.Byzantium.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Byzantium.Spec

/-! ## EIP-140 REVERT (0xfd)

    REVERT halts the frame with `halted = true ∧ reverted = true`
    and an output drawn from memory. Memory-expansion + halt-flag
    obligations. -/

/-- REVERT impl `Instructions.revert` returns `.ok evm'` with
    `evm'.halted = true ∧ evm'.reverted = true`. -/
theorem revert_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.revert evm = .ok evm' →
    IsRevertStep evm evm' := by
  -- Needs to unfold the monadic do-block in `Instructions.revert`,
  -- match memory-expansion / charge gas / record-update against
  -- the spec relation. State-touching multi-step obligation.
  intro _; sorry

/-! ## EIP-211 RETURNDATA*

    RETURNDATASIZE is a pure nullary push; RETURNDATACOPY pops 3
    operands and copies into memory (with explicit bounds check). -/

/-- 0x3d RETURNDATASIZE — `IsNullaryPushStep`-shaped. Closing this
    needs a `runNullaryPush_sound` shape lemma (not yet in
    `Frontier/Spec/StepShapes.lean`); for now `sorry`. -/
theorem returndatasize_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.returndatasize evm = .ok evm' →
    IsReturndatasizeStep evm evm' := by
  intro _; sorry

/-- 0x3e RETURNDATACOPY — memory-expansion + bounded copy. Multi-step
    monadic obligation. -/
theorem returndatacopy_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.returndatacopy evm = .ok evm' →
    IsReturndatacopyStep evm evm' := by
  intro _; sorry

/-! ## EIP-214 STATICCALL (0xfa)

    STATICCALL yields a sub-frame setup with `isStatic := true`. The
    relations describe the two pre-sub-frame branches (depth
    fail-fast and entry success). Trampoline obligation, `sorry`-
    deferred. -/

/-! ## Notes

    - Frontier's refinement file is re-exported by import; every
      opcode Byzantium doesn't change keeps its Frontier proof.

    - The `StaticPropagates` predicate is a structural fact about
      sub-frame setups, not a step relation; no soundness theorem
      needed here — it's a lemma callers can use directly.

    - The Byzantium BN256 precompile spec (`Bn256Step.lean`,
      reserved per SPEC-METHODOLOGY) is not yet in this directory
      so no soundness theorem is stated for it. -/

end Evm.Byzantium.Spec.Refinement
