/-
  Evm.Frontier.Vm.Instructions.Stack — opcodes 0x50 POP, 0x60..0x7f PUSHn,
  0x80..0x8f DUPn, 0x90..0x9f SWAPn.

  EELS reference: ethereum/frontier/vm/instructions/stack.py.

  PUSHn consumes `n` bytes of code immediately following the opcode byte
  and treats them as a big-endian integer (left-zero-padded if the code
  ends before `n` bytes are available — matches `Bytes.sliceZeroPad`).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- 0x50 POP -/
def pop : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.base
  let (_, s) ← Stack.pop evm.stack
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- PUSHn (n ∈ 1..32). The opcode dispatcher calls this with the explicit
    `n` derived from the opcode byte (0x60 + n - 1). -/
def push (n : Nat) : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let bytes := Evm.Bytes.sliceZeroPad evm.message.code (evm.pc + 1) n
  let value := Evm.U256.ofBytesBE bytes
  let s ← Stack.push evm.stack value
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 + n }

/-- DUPn (n ∈ 1..16). Duplicates the item at depth `n-1` onto the top. -/
def dup (n : Nat) : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let s ← Stack.dup evm.stack n
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- SWAPn (n ∈ 1..16). Swaps the top with the item at depth `n`. -/
def swap (n : Nat) : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let s ← Stack.swap evm.stack n
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
