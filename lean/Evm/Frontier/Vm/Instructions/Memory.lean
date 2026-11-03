/-
  Evm.Frontier.Vm.Instructions.Memory — opcodes 0x51 MLOAD, 0x52 MSTORE,
  0x53 MSTORE8, 0x59 MSIZE.

  EELS reference: ethereum/frontier/vm/instructions/memory.py.

  Each memory access charges `GAS_VERY_LOW` plus the expansion cost
  computed from the new high-water mark.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- Charge the gas for growing memory to cover `[offset, offset+size)`
    and return the expanded memory. No-op when `size = 0`. -/
def chargeMemory (gasLeft : Gas.Gas) (memory : Memory) (offset size : Nat) :
    Except Exception (Gas.Gas × Memory) := do
  if size = 0 then return (gasLeft, memory)
  let oldWords := Memory.words memory
  let newWords := (offset + size + 31) / 32
  let cost     := Gas.memoryExpansionCost oldWords newWords
  let gasLeft  ← Gas.charge gasLeft cost
  return (gasLeft, Memory.extend memory (offset + size))

/-- 0x51 MLOAD: push the 32-byte word at `offset`. -/
def mload : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let (offset, s) ← Stack.pop evm.stack
  let off := offset.toNat
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory off 32
  let value := Evm.U256.ofBytesBE (Memory.read mem off 32)
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

/-- 0x52 MSTORE: write `value` as 32 big-endian bytes at `offset`. -/
def mstore : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let (offset, value, s) ← Stack.pop2 evm.stack
  let off := offset.toNat
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory off 32
  let mem := Memory.write mem off (Evm.U256.toBytesBE value)
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

/-- 0x53 MSTORE8: write the low byte of `value` at `offset`. -/
def mstore8 : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let (offset, value, s) ← Stack.pop2 evm.stack
  let off := offset.toNat
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory off 1
  let mem := Memory.writeByte mem off (UInt8.ofNat (value.toNat &&& 0xff))
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

/-- 0x59 MSIZE: push the current memory size in bytes (always a multiple of 32). -/
def msize : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.memory.size)

end Evm.Frontier.Vm.Instructions
