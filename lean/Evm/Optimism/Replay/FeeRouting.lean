/-
  Evm.Optimism.Replay.FeeRouting — credit the three OP fee vaults
  for a user transaction.

  Per `Evm/Optimism/Bedrock/Spec/FeeVaults.lean`, every non-deposited
  user tx contributes to three vault streams:

    SequencerFeeVault  ← (effective_gas_price - base_fee_per_gas) * gas_used
    BaseFeeVault       ← base_fee_per_gas                          * gas_used
    L1FeeVault         ← l1_fee_wei  (the L1 data fee, fork-dispatched)

  vs. Ethereum mainnet (EIP-1559) where the base-fee component is
  BURNT, on OP it accumulates in BaseFeeVault. The header's
  `coinbase` field always points to SequencerFeeVault.

  Isthmus adds a fourth stream: OperatorFeeVault. Handled in a
  separate helper since the params come from L1Block storage.
-/

import Evm.Frontier.State
import Evm.Optimism.Bedrock.Spec.FeeVaults
import Evm.Optimism.Isthmus.Spec.PragueInheritance

namespace Evm.Optimism.Replay

open Evm.Frontier (State)

/-- Credit the three OP fee vaults for one user tx. Pass the
    pre-computed L1 data fee (use `Evm.Optimism.Replay.l1FeeWei`). -/
def creditVaults
    (state : State)
    (gasUsed : Nat)
    (effectiveGasPrice baseFeePerGas : Nat)
    (l1FeeWei : Nat) : State :=
  let priority := effectiveGasPrice - baseFeePerGas
  let st := state.addBalance
              Evm.Optimism.Bedrock.Spec.sequencerFeeVault
              (Evm.U256.ofNat (priority * gasUsed))
  let st := st.addBalance
              Evm.Optimism.Bedrock.Spec.baseFeeVault
              (Evm.U256.ofNat (baseFeePerGas * gasUsed))
  let st := st.addBalance
              Evm.Optimism.Bedrock.Spec.l1FeeVault
              (Evm.U256.ofNat l1FeeWei)
  st

/-- Isthmus-only addendum: credit the OperatorFeeVault. Caller has
    already computed `operatorFeeWei` from L1Block storage params. -/
def creditOperatorFee
    (state : State)
    (operatorFeeWei : Nat) : State :=
  state.addBalance
    Evm.Optimism.Isthmus.Spec.operatorFeeVault
    (Evm.U256.ofNat operatorFeeWei)

end Evm.Optimism.Replay
