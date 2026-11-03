/-
  Evm.Byzantium.Vm.Instructions.Memory — EIP-211 RETURNDATASIZE
  (0x3d) and RETURNDATACOPY (0x3e).

  EELS reference: ethereum/byzantium/vm/instructions/memory.py
  (plus environment.py for returndatasize, which EELS puts there
  for historical reasons).

  RETURNDATASIZE pushes the size of the last sub-call's returndata.
  RETURNDATACOPY copies a slice of returndata into memory; out-of-
  bounds access (offset + len > returndata size) raises an exception.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Byzantium.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x3d RETURNDATASIZE — push the size of the last sub-call's
    return data on the stack. -/
def returndatasize : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.base
  let s ← Stack.push evm.stack (Evm.U256.ofNat evm.returnData.size)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x3e RETURNDATACOPY — copy `len` bytes from `returndata[offset]`
    to `memory[destOff]`. Errors if the source range exceeds the
    returndata size. -/
def returndatacopy : Handler := fun evm => do
  let (destOff, offset, len, s) ← Stack.pop3 evm.stack
  let destOffN := destOff.toNat
  let offsetN  := offset.toNat
  let lenN     := len.toNat
  if offsetN + lenN > evm.returnData.size then
    .error .outOfGas  -- EELS uses OutOfBounds; we use OOG as nearest peer
  else
    let copyCost := Gas.veryLow + Gas.copy * ((lenN + 31) / 32)
    let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory destOffN lenN
    let gasLeft ← Gas.charge gasLeft copyCost
    let bytes := Evm.Bytes.sliceZeroPad evm.returnData offsetN lenN
    let mem := Memory.write mem destOffN bytes
    return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

end Evm.Byzantium.Vm.Instructions
