/-
  Evm.Optimism.Bedrock.Spec.FeeVaults — three predeploy fee vaults.

  Source: optimism-specs `specs/protocol/exec-engine.md` (fees).

  OP Stack does NOT burn the L1 base-fee component of a user tx
  (vs. Ethereum mainnet's EIP-1559 burn). Instead three predeploys
  collect the fee streams:

    0x4200000000000000000000000000000000000011  SequencerFeeVault
        — receives priority fee  (effective_gas_price - base_fee) × gas_used
    0x4200000000000000000000000000000000000019  BaseFeeVault
        — receives base fee × gas_used  (NOT burned)
    0x420000000000000000000000000000000000001A  L1FeeVault
        — receives L1 data fee (formula varies by fork, see L1DataFee.lean)

  Invariants:
    * Sum routed to vaults = total wei deducted from sender (excluding
      priority going to coinbase, which OP Stack treats as
      SequencerFeeVault — not the `coinbase` field of the header).
    * Per Bedrock+: the `coinbase` field of the block header always
      points to SequencerFeeVault. The header carries it for
      backwards compat with mainnet tooling, but the EL doesn't
      special-case it beyond routing fees there.

  Deposited txs (type 0x7E) bypass all three vaults: gas was paid at
  deposit time on L1; no L2 fee accounting.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Bedrock.Spec

def sequencerFeeVault : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000011
def baseFeeVault      : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000019
def l1FeeVault        : Evm.Address := Evm.Address.ofNat 0x420000000000000000000000000000000000001a

/-- BaseFeeVault receives the base-fee component of every user tx
    from Bedrock onwards (i.e. always, in OP land). On Ethereum
    mainnet the same wei would be BURNT (EIP-1559). Stated as iff:
    the route-to-vault behaviour is active iff OP fork is Bedrock+
    (trivially: always, in OP land). -/
def routesBaseFeeToVault (f : Evm.Optimism.OpFork) : Bool := f.atLeast .bedrock

theorem base_fee_vault_iff_bedrock (f : Evm.Optimism.OpFork) :
    routesBaseFeeToVault f = true ↔ f.atLeast .bedrock := by
  unfold routesBaseFeeToVault; rfl

/-- The three vault addresses are pairwise distinct (typo catcher). -/
example : sequencerFeeVault ≠ baseFeeVault := by decide
example : baseFeeVault      ≠ l1FeeVault   := by decide
example : sequencerFeeVault ≠ l1FeeVault   := by decide

end Evm.Optimism.Bedrock.Spec
