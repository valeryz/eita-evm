/-
  Evm.Frontier.Vm.Instructions.System — opcode 0xf3 RETURN.

  EELS reference: ethereum/frontier/vm/instructions/system.py.

  The other system opcodes (CREATE 0xf0, CALL 0xf1, CALLCODE 0xf2,
  SELFDESTRUCT 0xff) recurse into the interpreter and so live in
  `Frontier/Vm/Interpreter.lean` inside a `mutual` block alongside the
  run loop. This module covers only RETURN, which is non-recursive.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- 0xf3 RETURN: halt the current frame with `memory[offset, offset+len)`
    as the output. Charges only memory-expansion gas. -/
def return_ : Handler := fun evm => do
  let (offset, len, s) ← Stack.pop2 evm.stack
  let off  := offset.toNat
  let lenN := len.toNat
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory off lenN
  let output := Memory.read mem off lenN
  return { evm with
    gasLeft := gasLeft, memory := mem, stack := s,
    output := output, halted := true, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
