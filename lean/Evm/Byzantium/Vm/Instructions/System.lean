/-
  Evm.Byzantium.Vm.Instructions.System — EIP-140 REVERT (0xfd).

  EELS reference: ethereum/byzantium/vm/instructions/system.py.

  REVERT halts the frame with `output := memory[offset, offset+len)`
  and `reverted := true`. The trampoline's call-resume layer sees
  the reverted flag and:
    - does NOT merge the sub-frame's env into the parent;
    - DOES preserve the output as parent's returndata;
    - pushes 0 to indicate failure;
    - refunds the sub-frame's remaining gas (unlike a hard error
      which consumes all forwarded gas).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Byzantium.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0xfd REVERT — halt with output AND failure-signal. -/
def revert : Handler := fun evm => do
  let (offset, len, s) ← Stack.pop2 evm.stack
  let off  := offset.toNat
  let lenN := len.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory off lenN
  let output := Memory.read mem off lenN
  return { evm with
    gasLeft := gasLeft, memory := mem, stack := s,
    output := output, halted := true, reverted := true,
    pc := evm.pc + 1 }

end Evm.Byzantium.Vm.Instructions
