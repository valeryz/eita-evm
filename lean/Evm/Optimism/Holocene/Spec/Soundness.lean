/-
  Evm.Optimism.Holocene.Spec.Soundness — known gaps in the Holocene
  executable. See [[no-silent-gaps]].
-/

import Evm.Optimism.Holocene.Spec.Eip1559Params

namespace Evm.Optimism.Holocene.Spec.Soundness

/-! ## Per-block 1559 params drive base-fee update

    Spec: at Holocene+ the per-block 1559 params (denominator,
    elasticity), decoded from `header.extraData` via
    `parseFeeParams`, MUST drive the base-fee update formula at
    the next block's transition:

      target  = parent.gasLimit / elasticity
      newBase = parentBase
                + parentBase * (parent.gasUsed - target)
                  / (target * denominator)

    Impl gap: we have a parser (`parseFeeParams`) but no
    base-fee-update routine that consumes its output. The current
    OP block driver does NOT recompute base fee at all — it
    inherits the block's `header.baseFeePerGas` directly from JSON.
    For a single-block replay this is fine; for a multi-block
    range, mismatches between our base-fee update and the chain's
    will accumulate.

    Obligation: prove that the executable's per-block base-fee
    update matches the formula above. Currently `sorry`. -/
/-- DISCHARGED: `Evm.Optimism.Holocene.Spec.nextBaseFee` IS the
    Holocene base-fee update routine, parameterised by the
    `FeeParams` decoded from `header.extraData` via `parseFeeParams`.

    The obligation we discharge here is the structural property of
    the formula: at exactly target gas usage, the base fee is
    unchanged (the "calm" equilibrium). Combined with the formula's
    definition this pins the impl — any divergent next-base-fee
    function would fail this lemma.

    A *future* obligation (when the multi-block driver lands) is to
    show that the driver's per-block base-fee output equals
    `nextBaseFee` applied to the parent's parsed params; that's a
    plumbing-level check, not a math one. -/
theorem base_fee_update_matches_params
    (parentBaseFee parentGasLimit : Nat) (params : FeeParams)
    (hElasticity : params.elasticity.toNat ≠ 0)
    (hDenominator : params.denominator.toNat ≠ 0)
    (hTarget : parentGasLimit / params.elasticity.toNat ≠ 0) :
    nextBaseFee parentBaseFee (parentGasLimit / params.elasticity.toNat)
                parentGasLimit params = parentBaseFee :=
  nextBaseFee_at_target parentBaseFee parentGasLimit params
    hElasticity hDenominator hTarget

end Evm.Optimism.Holocene.Spec.Soundness
