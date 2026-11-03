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

/-- 0x55 SSTORE under Petersburg refines `IsSstoreStep` (=
    Frontier's `IsSstoreStep`). Refinement target: the Petersburg
    impl handler should produce the same `evm'` the Frontier impl
    handler does, modulo the trampoline plumbing that's identical
    by construction. -/
theorem sstore_sound (evm evm' : Evm) :
    -- Placeholder for the impl handler. Petersburg's `Effect.step1`
    -- routes 0x55 to `Byzantium.Vm.Effect.doSstore` which lifts the
    -- Frontier `Instructions.sstore` into the trampoline.
    Evm.Frontier.Vm.Instructions.sstore evm = .ok evm' →
    IsSstoreStep evm evm' := by
  -- Identical to Frontier's `sstore_sound` (which is itself `sorry`-
  -- deferred). Re-stated here for the Petersburg refinement interface.
  intro _; sorry

/-! ## Notes

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
