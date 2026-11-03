import Evm.CL.GasEmit
import Evm.London.Spec.BaseFee

/-! # Evm.CL.GasEmitLondon — the emitted next base fee is the London spec's formula

`Evm.CL.GasEmit.nextBaseFee` is what the host checks a block's `baseFeePerGas` against (a
clause of the emitted `spec-header-violation`, `Evm.CL.HeaderEmit`, from the parent header,
in the Ethereum driver's pre-block hook and the fixture runner);
`Evm.London.Spec.calculateBaseFeePerGas` is the EIP-1559 formula as the spec states it, over `(parent_gas_used, parent_gas_target,
parent_base_fee)` with the caller supplying `parent_gas_target = parent_gas_limit /
ELASTICITY_MULTIPLIER`. This file proves the emitted term computes exactly that for every
parent, so the gate cannot drift from the spec on the direction test, the 1-wei floor or
the division order. Same pattern as `GasEmitParis` / `GasEmitCancun`. -/

namespace Evm.CL.GasEmitLondon

open Evm.CL.GasEmit

theorem nextBaseFee_eq_spec (ρ : Env) (used limit base : Nat)
    (hu : ρ "parent-gas-used" = used) (hl : ρ "parent-gas-limit" = limit)
    (hb : ρ "parent-base-fee" = base) :
    nextBaseFee.eval ρ
      = Evm.London.Spec.calculateBaseFeePerGas used (limit / Evm.London.Spec.elasticityMultiplier) base := by
  simp only [nextBaseFee, parentGasUsed, parentGasTarget, parentBaseFee, Expr.eval, hu, hl, hb,
             Evm.London.Spec.calculateBaseFeePerGas,
             Evm.London.Spec.baseFeeMaxChangeDenominator, Evm.London.Spec.elasticityMultiplier]
  by_cases h1 : used < limit / 2
  · have hne : used ≠ limit / 2 := Nat.ne_of_lt h1
    have hng : ¬ used > limit / 2 := Nat.not_lt.2 (Nat.le_of_lt h1)
    simp [h1, hne, hng]
  · by_cases h2 : limit / 2 < used
    · have hne : used ≠ limit / 2 := Nat.ne_of_gt h2
      simp [h1, h2, hne]
    · have heq : used = limit / 2 := by omega
      simp [heq]

/-- The fork block's base fee is the spec's `INITIAL_BASE_FEE`. -/
theorem initialBaseFee_eq_spec (ρ : Env) :
    initialBaseFee.eval ρ = Evm.London.Spec.initialBaseFee := by
  simp [initialBaseFee, Expr.eval, Evm.London.Spec.initialBaseFee]

end Evm.CL.GasEmitLondon
