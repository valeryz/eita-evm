import Evm.CL.GasEmit
import Evm.Prague.Spec.CalldataCost

/-! # Evm.CL.GasEmitPrague — the emitted transaction-gas formulas ARE the Prague spec

`GasEmit` holds the formulas the replay runs (emitted to `src/generated/host.lisp`);
`Evm.Prague.Spec.CalldataCost` holds the EIP-7623 spec, cited clause by clause against
EELS. They used to be two independent definitions with nothing between them, and the
spec one was wrong for months without anything noticing (40/10 per byte, a floor with
the create/access-list extras in it). These theorems make them one definition: from
Prague on, every emitted cost equals the spec's for ALL inputs, not just test vectors. -/

namespace Evm.CL.GasEmitPrague

open Evm.CL.GasEmit
open Evm.Prague.Spec (standardCost floorCost gasUsedAfterRefund)

/-- The emitted calldata floor is EELS `calldata_floor` (transactions.py:626-628). -/
theorem calldataFloor_eq_spec (ρ : Env) (h : 17 ≤ ρ "fork-ord") :
    calldataFloorGas.eval ρ = floorCost (ρ "zero-bytes") (ρ "nonzero-bytes") := by
  have : ¬ ρ "fork-ord" < 17 := by omega
  simp [calldataFloorGas, fork, Expr.eval, this, floorCost, Evm.Prague.Spec.tokens,
    Evm.Prague.Spec.txBaseCost, Evm.Prague.Spec.txDataTokenFloor, Evm.Prague.Spec.tokensPerNonZero]
  all_goals omega

/-- The emitted intrinsic gas of a call (no CREATE) is EELS `regular`
    (transactions.py:651-658) with the access-list cost as the extras. -/
theorem intrinsicCall_eq_spec (ρ : Env) (h : 17 ≤ ρ "fork-ord") (hc : ρ "is-create" = 0) :
    intrinsicGas.eval ρ =
      standardCost (ρ "zero-bytes") (ρ "nonzero-bytes")
        (2400 * ρ "al-addrs" + 1900 * ρ "al-keys") := by
  have h8 : ¬ ρ "fork-ord" < 8 := by omega
  simp [intrinsicGas, fork, Expr.eval, hc, h8, standardCost, Evm.Prague.Spec.tokens,
    Evm.Prague.Spec.txBaseCost, Evm.Prague.Spec.txDataTokenStandard, Evm.Prague.Spec.tokensPerNonZero]
  all_goals omega

/-- The same for a CREATE: the extras add TX_CREATE and the EIP-3860 initcode words. -/
theorem intrinsicCreate_eq_spec (ρ : Env) (h : 17 ≤ ρ "fork-ord") (hc : ρ "is-create" = 1) :
    intrinsicGas.eval ρ =
      standardCost (ρ "zero-bytes") (ρ "nonzero-bytes")
        (32000 + 2 * ((ρ "data-len" + 31) / 32) + (2400 * ρ "al-addrs" + 1900 * ρ "al-keys")) := by
  have h1 : ¬ ρ "fork-ord" < 1 := by omega
  have h8 : ¬ ρ "fork-ord" < 8 := by omega
  have h15 : ¬ ρ "fork-ord" < 15 := by omega
  simp [intrinsicGas, fork, Expr.eval, hc, h1, h8, h15, standardCost, Evm.Prague.Spec.tokens,
    Evm.Prague.Spec.txBaseCost, Evm.Prague.Spec.txDataTokenStandard, Evm.Prague.Spec.tokensPerNonZero]
  all_goals omega

/-- The emitted settlement is EELS fork.py:913-923: refund capped at used/5, then the floor. -/
theorem txGasUsed_eq_spec (ρ : Env) (h : 17 ≤ ρ "fork-ord") :
    txGasUsed.eval ρ =
      gasUsedAfterRefund (ρ "gas-used") (ρ "refund-counter")
        (floorCost (ρ "zero-bytes") (ρ "nonzero-bytes")) := by
  have h11 : ¬ ρ "fork-ord" < 11 := by omega
  rw [← calldataFloor_eq_spec ρ h]
  simp [txGasUsed, refundCap, fork, Expr.eval, h11, gasUsedAfterRefund, Nat.min_comm]

end Evm.CL.GasEmitPrague
