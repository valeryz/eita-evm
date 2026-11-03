/-
  Evm.Optimism.Ecotone.Spec.L1DataFeeEcotone — Ecotone L1 cost
  function (EIP-4844 blob-aware).

  Source: optimism-specs `specs/protocol/exec-engine.md` §"Ecotone
  L1-Cost fee changes (EIP-4844 DA)" (specs@808223d, lines 163-191):

    (zeroes*4 + ones*16) * (16*l1BaseFee*l1BaseFeeScalar
                            + l1BlobBaseFee*l1BlobBaseFeeScalar) / 16e6

  "an unlimited precision integer computation" over the full encoded
  signed tx. The conceptual form divides `calldataGas` by 16 first
  (`compressedTxSize`); the spec states the division is postponed to the
  very end to keep precision, and op-geth does exactly that
  (`core/types/rollup_cost.go` `newL1CostFuncEcotone`, op-geth@a5f1641
  lines 321-348: `fee = (l1BaseFee*16*l1BaseFeeScalar +
  l1BlobBaseFee*l1BlobBaseFeeScalar) * calldataGasUsed / (16 * 1e6)`).

  The weighted price `l1FeeScaled` is shared with Fjord, which applies it
  to its FastLZ size estimate instead (`L1DataFeeFjord`).

  First Ecotone block: op-geth (`NewL1CostFunc`, lines 169-179) uses the
  Bedrock cost function while the L1Block's blob base fee and both Ecotone
  scalars are still zero (`firstEcotoneBlock`).

  Until 2026-11-02 `l1FeeWei` ignored `l1BlobBaseFee`, weighted the blob
  scalar with `l1BaseFee`, and took a pre-divided size — 60x too high on
  the vector below; nothing called it with real data (the replay takes
  `l1Fee` from the receipt).
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Ecotone.Spec

/-- op-geth `ecotoneDivisor = 1_000_000 * 16`: the scalars' 1e6 and the
    postponed `/16` of `compressedTxSize`. -/
def ecotoneDivisor : Nat := 16 * 1_000_000

/-- The weighted L1 price per (compressed) byte, scaled by 1e6:
    `16*l1BaseFee*l1BaseFeeScalar + l1BlobBaseFee*l1BlobBaseFeeScalar`
    (op-geth `calldataCostPerByte + blobCostPerByte`). -/
def l1FeeScaled (l1BaseFee l1BlobBaseFee baseFeeScalar blobBaseFeeScalar : Nat) : Nat :=
  16 * l1BaseFee * baseFeeScalar + l1BlobBaseFee * blobBaseFeeScalar

/-- Ecotone L1 fee in wei, from the tx's `calldataGas`
    (`Bedrock.Spec.calldataGas`, zeroes*4 + ones*16): one division, last. -/
def l1FeeWei
    (calldataGas l1BaseFee l1BlobBaseFee baseFeeScalar blobBaseFeeScalar : Nat) : Nat :=
  calldataGas * l1FeeScaled l1BaseFee l1BlobBaseFee baseFeeScalar blobBaseFeeScalar
    / ecotoneDivisor

/-- The very first Ecotone block still runs the Bedrock cost function:
    the L1Block's Ecotone fields are unset (op-geth `firstEcotoneBlock`). -/
def firstEcotoneBlock (l1BlobBaseFee baseFeeScalar blobBaseFeeScalar : Nat) : Bool :=
  l1BlobBaseFee == 0 && baseFeeScalar == 0 && blobBaseFeeScalar == 0

/-- **Base mainnet block 12,000,000, tx 3**
    (`0x5cb72f1f…ac630eb6`, Ecotone, pre-Fjord). From its receipt:
    `l1GasUsed = 1916` (op-geth's `calldataGasUsed`), `l1GasPrice =
    39963009028`, `l1BlobBaseFee = 1`, `l1BaseFeeScalar = 1101`,
    `l1BlobBaseFeeScalar = 659851`, `l1Fee = 84302607031`. The 1916 is
    re-derived from the signed tx's bytes in `Replay.L1Fee`. -/
theorem base_12000000_tx3 : l1FeeWei 1916 39963009028 1 1101 659851 = 84302607031 := by
  decide

/-- The op-revm/op-geth vector: OP Mainnet block 118024092, tx
    `0xa75ef696…63749c2` (op-revm `l1block.rs`
    `calculate_tx_l1_cost_ecotone`): calldata gas 2456, fee 7306020222001. -/
theorem op_118024092 :
    l1FeeWei 2456 47036678951 57422457042 1368 810949 = 7306020222001 := by
  decide

/-- The Ecotone formula is in effect at Ecotone..pre-Fjord. -/
def usesEcotoneL1Formula (f : Evm.Optimism.OpFork) : Bool :=
  f.atLeast .ecotone ∧ ¬ f.atLeast .fjord

theorem ecotone_formula_iff_ecotone_only (f : Evm.Optimism.OpFork) :
    usesEcotoneL1Formula f = true ↔
      (f.atLeast .ecotone ∧ ¬ f.atLeast .fjord) := by
  unfold usesEcotoneL1Formula
  cases f <;> decide

end Evm.Optimism.Ecotone.Spec
