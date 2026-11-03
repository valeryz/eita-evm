/-
  Evm.London.Vm.Instructions.Block — EIP-3198 BASEFEE (0x48).

  EELS reference: `forks/london/vm/instructions/environment.py`
  lines 532-553. (EELS files BASEFEE under `environment.py` for
  historical reasons; the user-facing taxonomy keeps it next to the
  block instructions since it pushes a block-scoped value.)

  Pushes `block.baseFeePerGas` on the stack, charges 2 gas (BASE tier).
  EIP-3198: gas cost = GAS_BASE = 2; opcode = 0x48.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.London.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x48 BASEFEE — push the current block's base fee. EELS:
    `forks/london/vm/instructions/environment.py` line 532
    (`base_fee`). Charges `GAS_BASE = 2`. -/
def baseFee : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.base
  let s ← Stack.push evm.stack (Evm.U256.ofNat evm.env.baseFeePerGas)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.London.Vm.Instructions
