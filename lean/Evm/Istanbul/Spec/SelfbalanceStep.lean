/-
  Evm.Istanbul.Spec.SelfbalanceStep — EIP-1884 SELFBALANCE (0x47).

  EELS reference: `forks/istanbul/vm/instructions/environment.py`
  `self_balance` (lines 494-506):
      charge_gas(evm, GasCosts.FAST_STEP)            # 5
      balance = get_account(state, currentTarget).balance
      push(stack, balance)

  Same shape as Frontier's CALLVALUE / GASPRICE etc. — a no-arg push
  whose value is computed from the current frame. The only twist is
  that the value depends on `evm.env.state` (specifically the running
  contract's account balance), not solely on the message / env scalars.
  `IsNullaryPushStep` handles this fine: its `value` callback is
  passed the full `Evm` record.

  Gas: 5 (`FAST_STEP`); explicitly cheaper than `BALANCE address`
  (which is 700 at Istanbul) because no account lookup beyond the
  trivially-cached `currentTarget` is required.
-/

import Evm.Frontier.Vm
import Evm.Frontier.State
import Evm.Frontier.Spec.StepShapes

namespace Evm.Istanbul.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- Istanbul SELFBALANCE gas (`FAST_STEP` = 5). -/
def selfBalanceGas : Nat := 5

/-- 0x47 SELFBALANCE — push the balance of `currentTarget`. 5 gas. -/
abbrev IsSelfbalanceStep : Evm → Evm → Prop :=
  IsNullaryPushStep
    (fun evm => evm.env.state.getBalance evm.message.currentTarget)
    selfBalanceGas

end Evm.Istanbul.Spec
