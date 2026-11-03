/-
  Evm.Optimism.Replay.L1Fee — fork-dispatched L1 data fee.

  Picks the right formula by `OpFork`, as op-geth `NewL1CostFunc` does
  (`core/types/rollup_cost.go`, op-geth@a5f1641 lines 151-211):
    pre-Ecotone (Bedrock, Canyon), and the first Ecotone block:
                         (calldataGas + overhead) * l1BaseFee * scalar / 1e6
    Ecotone:             calldataGas * weighted price / 16e6
    Fjord and later:     FastLZ size estimate * weighted price / 1e12

  The formulas live in the spec modules; this is only the dispatch.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks
import Evm.Optimism.Bedrock.Spec.L1DataFee
import Evm.Optimism.Ecotone.Spec.L1DataFeeEcotone
import Evm.Optimism.Fjord.Spec.L1DataFeeFjord

namespace Evm.Optimism.Replay

/-- Bundle of the L1-attribute params needed to compute the L1 data
    fee. Populated from the L1Block predeploy storage after the
    per-block prologue tx has executed (or read directly from the
    `setL1BlockValuesEcotone` / `setL1BlockValuesIsthmus` calldata
    if the predeploy isn't actually executed). -/
structure L1FeeParams where
  /-- L1 base fee in wei (per L1 gas unit). -/
  l1BaseFee         : Nat
  /-- L1 blob base fee in wei (per L1 blob gas unit). Used Ecotone+. -/
  l1BlobBaseFee     : Nat
  /-- Pre-Ecotone scalar (legacy single scalar). -/
  l1FeeScalar       : Nat := 0
  /-- Pre-Ecotone overhead (L1Block slot 5), in L1 gas. -/
  l1FeeOverhead     : Nat := 0
  /-- Ecotone+ split scalars. -/
  baseFeeScalar     : Nat := 0
  blobBaseFeeScalar : Nat := 0
  deriving Repr, Inhabited

/-- A precise FastLZ-compressed length, supplied by the caller.
    Eita does not currently implement FastLZ; for Fjord+ blocks the
    user passes the value op-geth would have computed (from the
    receipt's `l1GasUsed` you can back out the size, or call out to
    `cast estimate-tx-cost` as a side channel). When we add a
    Lean-side FastLZ impl this argument becomes a derived value. -/
def l1FeeWei
    (f : Evm.Optimism.OpFork)
    (params : L1FeeParams)
    (txBytes : Evm.Bytes)
    (fastlzSize : Nat := 0) : Nat :=
  let ecotoneSet := !Evm.Optimism.Ecotone.Spec.firstEcotoneBlock
    params.l1BlobBaseFee params.baseFeeScalar params.blobBaseFeeScalar
  if f.atLeast .fjord && ecotoneSet then
    Evm.Optimism.Fjord.Spec.l1FeeWei fastlzSize
      params.l1BaseFee params.l1BlobBaseFee params.baseFeeScalar params.blobBaseFeeScalar
  else if f.atLeast .ecotone && ecotoneSet then
    Evm.Optimism.Ecotone.Spec.l1FeeWei (Evm.Optimism.Bedrock.Spec.calldataGas txBytes)
      params.l1BaseFee params.l1BlobBaseFee params.baseFeeScalar params.blobBaseFeeScalar
  else
    Evm.Optimism.Bedrock.Spec.l1FeeWei txBytes params.l1BaseFee params.l1FeeOverhead
      params.l1FeeScalar

/-- Base mainnet block 12,000,000 tx 3 (`0x5cb72f1f…ac630eb6`), the signed
    EIP-1559 tx as re-encoded from `eth_getTransactionByHash` (its keccak is
    the tx hash). -/
def base12000000tx3 : Evm.Bytes := ⟨#[
  0x02, 0xf8, 0x77, 0x82, 0x21, 0x05, 0x83, 0x03, 0xcf, 0x6d, 0x84, 0x05, 0xf5, 0xe1, 0x00, 0x85,
  0x5d, 0x21, 0xdb, 0xa0, 0x00, 0x82, 0x9c, 0x40, 0x94, 0x6f, 0xf2, 0x83, 0xbd, 0x2b, 0x37, 0x30,
  0x2f, 0x3a, 0x2a, 0x13, 0xc7, 0x27, 0xfd, 0xf7, 0xfc, 0xd6, 0x9d, 0xd5, 0xae, 0x87, 0x19, 0x66,
  0xe3, 0x1a, 0x24, 0xe0, 0x00, 0x80, 0xc0, 0x01, 0xa0, 0xec, 0xb8, 0xa5, 0x04, 0xd4, 0xb5, 0x9b,
  0x49, 0x6b, 0xff, 0x57, 0x53, 0x50, 0xe2, 0xe1, 0x1d, 0x7b, 0xc7, 0x62, 0x16, 0xa7, 0x4a, 0x2c,
  0x49, 0x39, 0xc8, 0x02, 0x7b, 0x72, 0x6d, 0x1f, 0x98, 0xa0, 0x2a, 0x20, 0x5a, 0xfb, 0x8a, 0x6e,
  0x4d, 0x17, 0xe5, 0x26, 0x38, 0x51, 0x32, 0x17, 0x75, 0x7e, 0x45, 0x3a, 0xc3, 0xad, 0x91, 0x9f,
  0xe4, 0xf8, 0x32, 0xb1, 0x71, 0x41, 0x4c, 0x6a, 0x0b, 0xac]⟩

/-- **The receipt's `l1Fee`, from the tx bytes and the receipt's L1 params**:
    `l1GasUsed = 1916`, `l1Fee = 84302607031` wei. -/
theorem base_12000000_tx3_l1Fee :
    Evm.Optimism.Bedrock.Spec.calldataGas base12000000tx3 = 1916 ∧
    l1FeeWei .ecotone { l1BaseFee := 39963009028, l1BlobBaseFee := 1,
                        baseFeeScalar := 1101, blobBaseFeeScalar := 659851 }
      base12000000tx3 = 84302607031 := by
  decide +kernel

end Evm.Optimism.Replay
