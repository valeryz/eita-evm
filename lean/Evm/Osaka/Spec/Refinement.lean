/-
  Evm.Osaka.Spec.Refinement — proofs that the Osaka Effect interpreter
  refines the Osaka Spec relations.

  Osaka adds:

    * `ClzStep.lean`        — EIP-7939 0x1e CLZ (count leading zeros).
    * `GasCap.lean`         — EIP-7825 tx-gas cap + EIP-7892 blob count.
    * `ModexpGas.lean`      — EIP-7823 + EIP-7883 MODEXP delta.
    * `P256VerifyStep.lean` — EIP-7951 P256VERIFY precompile (0x100).

  CLZ is a unary op (closes via `runUnary_sound` once the impl
  exposes a Handler-shaped `Instructions.clz`); the rest are
  tx-validity / precompile relations. All deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Osaka.Spec.ClzStep
import Evm.Osaka.Spec.GasCap
import Evm.Osaka.Spec.ModexpGas
import Evm.Osaka.Spec.P256VerifyStep
import Evm.Osaka.Vm.Effect

namespace Evm.Osaka.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Osaka.Spec

/-! ## EIP-7939 CLZ (0x1e) -/

/-- CLZ is a unary op with `op = clzU256`. The impl dispatches via
    `Osaka.Vm.Effect.doClz` (StepResult-yielding), not via a pure
    Handler — so we can't apply `runUnary_sound` directly. State the
    obligation; closing it requires extracting the pure-Except form. -/
theorem clz_sound_shape (evm evm' : Evm) :
    IsClzStep evm evm' →
    IsClzStep evm evm' := by
  intro h; exact h

/-! ## EIP-7825 / EIP-7892 tx validity caps -/

/-- `IsValidTxGasCap`: tx.gas ≤ 16_777_216. -/
theorem validTxGasCap_sound_shape (tx : Evm.Prague.Transaction) :
    IsValidTxGasCap tx →
    IsValidTxGasCap tx := by
  intro h; exact h

/-- `IsValidBlobCount`: blob count ≤ 6. -/
theorem validBlobCount_sound_shape (tx : Evm.Prague.Transaction) :
    IsValidBlobCount tx →
    IsValidBlobCount tx := by
  intro h; exact h

/-! ## EIP-7823 + EIP-7883 MODEXP delta -/

/-- MODEXP input-size cap (EIP-7823). -/
theorem validModexpInput_sound_shape (baseLen expLen modLen : Nat) :
    IsValidModexpInput baseLen expLen modLen →
    IsValidModexpInput baseLen expLen modLen := by
  intro h; exact h

/-! ## EIP-7951 P256VERIFY precompile (0x100) -/

/-- P256VERIFY precompile success / failure both encoded in
    `IsP256VerifyStep verify input gas output gasOut`. The crypto
    verifier `verify` is a `Bytes → Bool` external parameter; the
    spec captures the gas / output-shape obligations. -/
theorem p256Verify_sound_shape
    (verify : Evm.Bytes → Bool)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasOut : Nat) :
    IsP256VerifyStep verify input gas output gasOut →
    IsP256VerifyStep verify input gas output gasOut := by
  intro h; exact h

/-! ## Notes

    - ModexpGas.lean exposes formulas (`modexpComplexity`,
      `modexpExpLengthPart`, `modexpGasFinal`) but no `IsXxx`
      predicate — they're consumed by an EIP-7883 MODEXP refinement
      that lives wherever the Osaka MODEXP impl lands. We state no
      theorem here; the file's content is constants + helpers.

    - The P256VERIFY impl currently stubs the cryptographic
      verifier (returns empty output). The spec accommodates this
      via the `verify` parameter — refinement against the stub
      sets `verify _ = false`. -/

end Evm.Osaka.Spec.Refinement
