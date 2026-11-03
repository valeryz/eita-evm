/-
  Evm.Frontier.Vm.Instructions — opcode-handler infrastructure.

  EELS reference: ethereum/frontier/vm/instructions/__init__.py and the
  per-category files in the same directory. Per-category handlers live
  in `Instructions/Arithmetic.lean`, `Instructions/Comparison.lean`, etc.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- An opcode handler maps a pre-state to a post-state or an exception.
    Handlers are responsible for charging gas, manipulating the stack and
    memory, and advancing `pc`. -/
abbrev Handler := Evm → Except Exception Evm

/-- Charge `cost`, pop one operand, push `op v`, advance pc. -/
def runUnary (cost : Gas.Gas) (op : Evm.U256 → Evm.U256) : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft cost
  let (a, s) ← Stack.pop evm.stack
  let s ← Stack.push s (op a)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Charge `cost`, pop two operands `(top, second)`, push `op top second`,
    advance pc. -/
def runBinary (cost : Gas.Gas) (op : Evm.U256 → Evm.U256 → Evm.U256) : Handler :=
  fun evm => do
    let gasLeft ← Gas.charge evm.gasLeft cost
    let (a, b, s) ← Stack.pop2 evm.stack
    let s ← Stack.push s (op a b)
    return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Charge `cost`, pop three operands, push `op a b c`, advance pc. -/
def runTernary (cost : Gas.Gas) (op : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256) :
    Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft cost
  let (a, b, c, s) ← Stack.pop3 evm.stack
  let s ← Stack.push s (op a b c)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Charge `cost`, push `value evm` (read from the pre-charge frame),
    advance pc. Covers the nullary environment/block readers
    (ADDRESS, CALLER, TIMESTAMP, …) plus PC, MSIZE and GAS. -/
def runNullaryPush (cost : Gas.Gas) (value : Evm → Evm.U256) : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft cost
  let s ← Stack.push evm.stack (value evm)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
