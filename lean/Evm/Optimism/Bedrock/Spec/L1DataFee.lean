/-
  Evm.Optimism.Bedrock.Spec.L1DataFee — Bedrock-era L1 data fee.

  Source: optimism-specs `specs/protocol/exec-engine.md` §"L1 cost
  function". On user txs (NOT deposited txs), the L2 charges the user
  the cost of POSTING the tx's calldata to L1, and routes it to
  `L1FeeVault`.

  Pre-Ecotone formula (exec-engine.md §"Pre-Ecotone", specs@808223d
  lines 130-142; op-geth@a5f1641 `core/types/rollup_cost.go`
  `newL1CostFuncBedrockHelper`, lines 301-316, and `l1CostHelper`):

    rollupDataGas = zeroes * 4 + ones * 16        -- over the full signed tx
    l1_fee_wei    = (rollupDataGas + l1FeeOverhead) * l1BaseFee * l1FeeScalar / 1e6

  Before Regolith the spec adds 68 non-zero bytes to `rollupDataGas`.
  `OpFork` has no pre-Regolith fork: every chain this tree replays (Base,
  OP Mainnet) has Regolith active from its Bedrock genesis (superchain-
  registry configs carry no `regolith_time`), so the Regolith
  rule is the only one stated. (Until 2026-11-02 this file always added
  the 68 bytes and had no overhead term — the pre-Regolith formula without
  its overhead, wrong for every chain here; nothing called it.)

  Later forks change the formula entirely:
    Ecotone:    blob-aware (blob_base_fee + base_fee composite)
    Fjord:      FastLZ compressed size with 100-byte floor

  See `Optimism/Ecotone/Spec/L1DataFeeEcotone.lean` and
  `Optimism/Fjord/Spec/L1DataFeeFjord.lean`.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Bedrock.Spec

/-- Per-zero-byte L1 gas cost (`params.TxDataZeroGas`). -/
def l1GasPerZeroByte    : Nat := 4
/-- Per-non-zero-byte L1 gas cost (`params.TxDataNonZeroGasEIP2028`). -/
def l1GasPerNonZeroByte : Nat := 16
/-- Scalar denominator (1e6). -/
def feeScalarDenominator : Nat := 1_000_000

/-- `rollupDataGas` (Regolith+): `zeroes * 4 + ones * 16` over the full
    EIP-2718-encoded signed tx. op-geth `bedrockCalldataGasUsed` (lines
    662-665). The Ecotone formula is weighted by the same quantity. -/
def calldataGas (txBytes : Evm.Bytes) : Nat :=
  txBytes.toList.foldl
    (init := 0)
    (fun acc b => acc + (if b = 0 then l1GasPerZeroByte else l1GasPerNonZeroByte))

/-- Pre-Ecotone L1 fee in wei:
    `(rollupDataGas + l1FeeOverhead) * l1BaseFee * l1FeeScalar / 1e6`, one
    division at the end (`l1CostHelper`). -/
def l1FeeWei (txBytes : Evm.Bytes) (l1BaseFee l1FeeOverhead l1FeeScalar : Nat) : Nat :=
  (calldataGas txBytes + l1FeeOverhead) * l1BaseFee * l1FeeScalar / feeScalarDenominator

/-! ## Fork-conditional applicability

    The *formula* used to compute the L1 fee changes by fork (this
    file = Bedrock; Ecotone & Fjord override). The L1FeeVault routing
    itself is unconditional from Bedrock onwards.

    Stated as: the BEDROCK linear formula is in use iff the fork is
    Bedrock-or-Canyon (i.e. < Ecotone). -/

def usesBedrockL1Formula (f : Evm.Optimism.OpFork) : Bool :=
  ¬ f.atLeast .ecotone

theorem bedrock_formula_iff_pre_ecotone (f : Evm.Optimism.OpFork) :
    usesBedrockL1Formula f = true ↔ ¬ f.atLeast .ecotone := by
  unfold usesBedrockL1Formula
  cases f <;> decide

end Evm.Optimism.Bedrock.Spec
