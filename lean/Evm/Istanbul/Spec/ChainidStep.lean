/-
  Evm.Istanbul.Spec.ChainidStep — EIP-1344 CHAINID (0x46).

  EELS reference: `forks/istanbul/vm/instructions/block.py` `chain_id`
  function. EELS source: `push(stack, U256(env.chain_id))`. Gas:
  `BASE` (= 2), `GasCosts.OPCODE_CHAINID`.

  Pushes the chain identifier from `evm.env.chainId`. Same shape as
  Frontier's ADDRESS / ORIGIN / COINBASE / etc. NullaryPush
  relations.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.StepShapes

namespace Evm.Istanbul.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x46 CHAINID — push `evm.env.chainId`. 2 gas. -/
abbrev IsChainidStep : Evm → Evm → Prop :=
  IsNullaryPushStep (fun evm => evm.env.chainId) Gas.base

end Evm.Istanbul.Spec
