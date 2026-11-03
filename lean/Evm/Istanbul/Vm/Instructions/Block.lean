/-
  Evm.Istanbul.Vm.Instructions.Block — EIP-1344 CHAINID (0x46).

  EELS reference: `forks/istanbul/vm/instructions/block.py`
  function `chain_id` (also re-exposed via the dispatch table in
  `forks/istanbul/vm/instructions/__init__.py` as `Ops.CHAINID`).

  Pushes the chain identifier from the per-tx environment onto the
  stack, charging `BASE` (2 gas). The chain ID lives on `env.chainId`
  (defaulted to `1` for mainnet); the per-tx `processTransaction`
  pipeline is what plumbs it in.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Istanbul.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x46 CHAINID — push the chain identifier. EELS line 35 of
    `block.py`: `push(stack, U256(env.chain_id))`. EELS gas constant
    `GasCosts.OPCODE_CHAINID` (`= BASE = 2`). -/
def chainid : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.base
  let s ← Stack.push evm.stack evm.env.chainId
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Istanbul.Vm.Instructions
