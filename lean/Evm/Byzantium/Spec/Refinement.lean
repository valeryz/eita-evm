/-
  Evm.Byzantium.Spec.Refinement — proofs that the Byzantium Effect
  interpreter refines the Byzantium Spec relations.

  Byzantium adds:

    * `RevertStep.lean` — EIP-140 0xfd REVERT (terminal halting step).
    * `ReturndataStep.lean` — EIP-211 0x3d RETURNDATASIZE +
                              0x3e RETURNDATACOPY.

  RETURNDATASIZE is a NullaryPush; REVERT and RETURNDATACOPY walk the
  memory-expansion charge (`Frontier.Spec.chargeMemory_spec`).
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

/-- Shape lemma for the `StepResult`-returning nullary-push handlers (`do*` in the Byzantium+
    fork `Vm/Effect.lean` files, which share Byzantium's `StepResult`: PUSH0, SLOTNUM, …) — charge `gas`, push `f evm`, advance pc by
    1, written with explicit `match`es instead of `Except`'s `do`. A `.continue` result is
    the matching `IsNullaryPushStep`. -/
theorem stepNullaryPush_sound (gas : Gas.Gas) (f : Evm → Evm.U256) (evm evm' : Evm) :
    (match Gas.charge evm.gasLeft gas with
      | .error e => Evm.Byzantium.Vm.Effect.StepResult.error evm e
      | .ok gasLeft =>
        match Stack.push evm.stack (f evm) with
        | .error e => .error evm e
        | .ok s    => .continue { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 })
      = .continue evm' →
    Evm.Frontier.Spec.IsNullaryPushStep f gas evm evm' := by
  intro h
  split at h
  · exact absurd h (by simp)
  · rename_i g hg
    split at h
    · exact absurd h (by simp)
    · rename_i s hs
      obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
      obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hs
      injection h with h
      subst h
      exact ⟨hlt, hle, rfl⟩

/-! ## EIP-140 REVERT (0xfd)

    REVERT halts the frame with `halted = true ∧ reverted = true`
    and an output drawn from memory. Memory-expansion + halt-flag
    obligations. -/

/-- REVERT: every successful run of `Instructions.revert` is an `IsRevertStep` — the
    memory-expansion charge, the output read from the expanded memory, `halted` and
    `reverted` set. EELS `forks/byzantium/vm/instructions/system.py::revert` (589-615):
    pop `memory_start_index`, `size`; `charge_gas(extend_memory.cost)`; extend; output :=
    `memory_read_bytes`; `raise Revert`. (EELS leaves `pc` alone — the frame halts, so the
    `pc + 1` both sides write is unobservable.) -/
theorem revert_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.revert evm = .ok evm' →
    IsRevertStep evm evm' := by
  intro h
  unfold Evm.Byzantium.Vm.Instructions.revert at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨a, b, rest⟩, hp, ⟨g, m⟩, hc, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
  obtain ⟨hle, rfl, rfl⟩ := Evm.Frontier.Spec.chargeMemory_spec hc
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨a, b, rest, hStack, hle, rfl⟩

/-! ## EIP-211 RETURNDATA*

    RETURNDATASIZE is a pure nullary push; RETURNDATACOPY pops 3
    operands and copies into memory (with explicit bounds check). -/

/-- 0x3d RETURNDATASIZE — a nullary push of `len(evm.return_data)` at `GAS_BASE`.
    EELS `forks/byzantium/vm/instructions/environment.py::returndatasize`. -/
theorem returndatasize_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.returndatasize evm = .ok evm' →
    IsReturndatasizeStep evm evm' := by
  unfold Evm.Byzantium.Vm.Instructions.returndatasize
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound Gas.base
    (fun e => Evm.U256.ofNat e.returnData.size) evm evm'

/-- 0x3e RETURNDATACOPY — every successful run is an `IsReturndatacopyStep`: the
    source range lies inside the return data, the gas is `GAS_VERY_LOW + GAS_COPY · words
    + extend_memory.cost`, memory is extended then written. EELS
    `forks/byzantium/vm/instructions/environment.py::returndatacopy` (409-446). EELS
    charges before the bounds check, the impl checks first; both end in an exception, so
    the successful runs coincide. -/
theorem returndatacopy_sound (evm evm' : Evm) :
    Evm.Byzantium.Vm.Instructions.returndatacopy evm = .ok evm' →
    IsReturndatacopyStep evm evm' := by
  intro h
  unfold Evm.Byzantium.Vm.Instructions.returndatacopy at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨d, o, l, rest⟩, hp, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp
  split at h
  · exact absurd h (by simp)
  · rename_i hb
    simp only [Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    rcases h with ⟨⟨g, m⟩, hc, g2, hg2, h⟩
    obtain ⟨hle, rfl, rfl⟩ := Evm.Frontier.Spec.chargeMemory_spec hc
    obtain ⟨hle2, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg2
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only at hb hle2
    obtain ⟨hA, hB⟩ := Evm.Frontier.Spec.charge2_nat hle hle2
    refine ⟨d, o, l, rest, hStack, by omega, hA, ?_⟩
    simp only [hB]

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
