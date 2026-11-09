/-
  Evm.Petersburg.Spec.Refinement — proofs that the Petersburg Effect
  interpreter refines the Petersburg Spec relations.

  Petersburg only delta: revert EIP-1283 SSTORE back to the Frontier
  schedule. The spec re-defines `IsSstoreStep` as an `abbrev` for the
  Frontier relation, so refinement is identical to Frontier's.

  Per SPEC-METHODOLOGY: a re-import alone counts as a refinement.
-/

import Evm.Frontier.Spec.Refinement
import Evm.Petersburg.Spec.SstoreStep
import Evm.Petersburg.Vm.Effect

namespace Evm.Petersburg.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Petersburg.Spec

/-! ## 0x55 SSTORE refinement at Petersburg

    `Petersburg.Spec.IsSstoreStep` is defined as
    `abbrev IsSstoreStep := Evm.Frontier.Spec.IsSstoreStep`. The
    Petersburg `Effect.step1` for 0x55 routes through Byzantium's
    `doSstore`, which itself implements the Frontier schedule
    (the intervening forks didn't re-price SSTORE).

    SSTORE is state-touching and refunds-bearing; per methodology
    the soundness obligation is stated and discharged with `sorry`. -/

/-- 0x55 SSTORE under Petersburg refines `IsSstoreStep` (= Frontier's
    two-bucket schedule), stated on the path that actually runs: Petersburg's
    `step1` at an SSTORE yields `.sstore key value` (Byzantium's `doSstore`: static
    check, two pops), and `handleYield` discharges it (cost `sSet` for 0 → non-zero
    else `sReset`, `sClearRefund` for non-zero → 0, storage written, pc + 1).
    EELS `forks/constantinople/vm/instructions/storage.py::sstore` (main 636b5f1,
    the post-Petersburg schedule EELS keeps under the Constantinople name). -/
theorem sstore_sound (evm evm1 evm' : Evm) (eff : Evm.Byzantium.Vm.Effect.YieldEffect)
    (runSub : Evm → Except Exception Evm)
    (hHalt : evm.halted = false) (hpc : evm.pc < evm.message.code.size)
    (hop : (evm.message.code.get! evm.pc).toNat = 0x55) :
    Evm.Petersburg.Vm.Effect.step1 evm = .yield evm1 eff →
    Evm.Petersburg.Vm.Effect.handleYield evm1 eff runSub = .ok evm' →
    IsSstoreStep evm evm' := by
  intro h1 h2
  simp only [Evm.Petersburg.Vm.Effect.step1, hHalt, Bool.false_eq_true, ite_false,
    show ¬ evm.pc ≥ evm.message.code.size from Nat.not_le.mpr hpc, hop] at h1
  unfold Evm.Byzantium.Vm.Effect.doSstore at h1
  split at h1
  · exact absurd h1 (by simp)
  · split at h1
    · exact absurd h1 (by simp)
    · rename_i key value rest hp
      obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
      simp only [Evm.Byzantium.Vm.Effect.StepResult.yield.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp only [Evm.Petersburg.Vm.Effect.handleYield] at h2
      split at h2
      · exact absurd h2 (by simp)
      · rename_i g hg
        obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
        injection h2 with h2
        subst h2
        exact ⟨key, value, rest, hStack, hle, rfl⟩

/-! ## Notes

    - The pure `Evm.Frontier.Vm.Instructions.sstore` (same schedule) is
      not Petersburg's `step1` path; it is the IR's per-op handler
      (`IR.Dispatch` `Op.handler .petersburg .sstore`), tied to the yield
      path by `IR.Soundness.runFrameR_sstore_shifted`. It stays.

    - There is exactly one new spec file at Petersburg and exactly
      one new soundness theorem. Every other opcode is unchanged
      from Constantinople / Byzantium / earlier, and is covered by
      those Refinement.lean files via `import`.

    - The Constantinople refinement file is NOT imported here (since
      Petersburg "reverts" Constantinople's SSTORE) — but every
      OTHER Constantinople opcode's refinement (SHL, SHR, SAR,
      EXTCODEHASH, CREATE2) IS active at Petersburg by virtue of
      the impl re-dispatch. A more careful methodology would import
      Constantinople and re-prove SSTORE only. -/

end Evm.Petersburg.Spec.Refinement
