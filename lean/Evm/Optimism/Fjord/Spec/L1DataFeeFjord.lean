/-
  Evm.Optimism.Fjord.Spec.L1DataFeeFjord — Fjord L1 cost function
  (FastLZ-compressed estimate with floor).

  Source: optimism-specs `specs/protocol/fjord/exec-engine.md`.

  Fjord swaps Ecotone's "weighted bytes" cost-estimator for a
  FastLZ-compressed-size estimator with a 100-byte floor:

    estimated_size_scaled = max(
        minTxSizeScaled,
        intercept + fastlzCoef * fastlz_compressed_size(tx_rlp)
    )

  with EELS-defined constants:

    minTxSizeScaled            = 100 * 10^6         -- 100 bytes, scaled
    intercept                  = -42_585_600        -- ≈ -42.6, scaled
    fastlzCoef                 =   836_500          -- ≈ 0.836, scaled
    tx_compressed_size_scaled  = estimated_size_scaled / 10^6

  Then the Ecotone weighted price is applied to the SCALED estimate, with
  one division at the end (op-geth@a5f1641 `core/types/rollup_cost.go`
  `NewL1CostFuncFjord`, lines 608-627):

    l1_fee_wei = estimated_size_scaled
                 * (16*l1BaseFee*baseFeeScalar + l1BlobBaseFee*blobBaseFeeScalar)
                 / 10^12

  (Until 2026-11-02 the replay dispatch divided the estimate by 10^6 first
  and fed it to the — then wrong — Ecotone function as a byte count.)

  (intercept can be negative in raw int64 arithmetic; spec clamps the
  estimated_size_scaled at ≥ minTxSizeScaled which dominates for
  small txs and keeps the result ≥ 0 wei.)
-/

import Evm.BaseTypes
import Evm.Optimism.Forks
import Evm.Optimism.Ecotone.Spec.L1DataFeeEcotone

namespace Evm.Optimism.Fjord.Spec

/-- Per-spec constants (scaled by 10^6 throughout). -/
def minTxSizeScaled : Nat := 100 * 1_000_000

/-- Linear fit: -42.585600. Stored as the (signed) integer constant
    `-42_585_600`; we apply the clamp before subtracting so the
    arithmetic stays in `Nat`. -/
def interceptScaled  : Int := -42_585_600
/-- Linear fit: 0.836500. -/
def fastlzCoefScaled : Int :=    836_500

/-- The estimator: clamp the linear fit at the 100-byte floor. -/
def estimatedSizeScaled (fastlzSize : Nat) : Nat :=
  let raw  : Int := interceptScaled + fastlzCoefScaled * (fastlzSize : Int)
  let rawN : Nat := if raw < 0 then 0 else raw.toNat
  max minTxSizeScaled rawN

/-- op-geth `fjordDivisor`: the estimate's 1e6 times the scalars' 1e6. -/
def fjordDivisor : Nat := 1_000_000_000_000

/-- Fjord L1 fee in wei from the FastLZ-compressed length of the signed tx. -/
def l1FeeWei (fastlzSize l1BaseFee l1BlobBaseFee baseFeeScalar blobBaseFeeScalar : Nat) : Nat :=
  estimatedSizeScaled fastlzSize
    * Evm.Optimism.Ecotone.Spec.l1FeeScaled l1BaseFee l1BlobBaseFee baseFeeScalar blobBaseFeeScalar
    / fjordDivisor

/-- The op-revm vector: OP Mainnet Fjord block 124665056, tx
    `0x1059e800…87c4a4a` (op-revm `l1block.rs` `calculate_tx_l1_cost_fjord`):
    data gas 4471, fee `0x5bf1ab43d`. Its FastLZ length is 385 — the only
    length whose estimate gives that data gas (384 → 4458, 386 → 4484); the
    tree has no FastLZ, so the length is the vector's input. -/
theorem op_124665056 :
    estimatedSizeScaled 385 * 16 / 1_000_000 = 4471 ∧
    l1FeeWei 385 1055991687 1 5227 1014213 = 0x5bf1ab43d := by
  decide

/-- The Fjord formula is in effect at Fjord-or-later. -/
def usesFjordL1Formula (f : Evm.Optimism.OpFork) : Bool := f.atLeast .fjord

theorem fjord_formula_iff_fjord (f : Evm.Optimism.OpFork) :
    usesFjordL1Formula f = true ↔ f.atLeast .fjord := by
  unfold usesFjordL1Formula; rfl

end Evm.Optimism.Fjord.Spec
