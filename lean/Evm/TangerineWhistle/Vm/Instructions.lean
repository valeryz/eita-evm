/-
  Evm.TangerineWhistle.Vm.Instructions — non-recursive EIP-150 deltas.

  EELS reference: ethereum/tangerine_whistle/vm/instructions/.

  Four handlers change in straightforward gas-only ways and live here.
  The recursive ones (CALL family, CREATE, SELFDESTRUCT) live in
  `Vm/Interpreter.lean` because they're tied into the dispatch / run
  loop mutual block.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory
import Evm.TangerineWhistle.Vm.Gas

namespace Evm.TangerineWhistle.Vm.Instructions

open Evm.Frontier.Vm

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x31 BALANCE — gas 400 (was 20). -/
def balance : Evm.Frontier.Vm.Instructions.Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.balance
  let (addrW, s) ← Stack.pop evm.stack
  let bal := evm.env.state.getBalance (u256ToAddr addrW)
  let s ← Stack.push s bal
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x54 SLOAD — gas 200 (was 50). -/
def sload : Evm.Frontier.Vm.Instructions.Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.sLoad
  let (key, s) ← Stack.pop evm.stack
  let value := evm.env.state.getStorage evm.message.currentTarget key
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x3b EXTCODESIZE — gas 700 (was 20). -/
def extcodesize : Evm.Frontier.Vm.Instructions.Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.TangerineWhistle.Vm.Gas.extCode
  let (addrW, s) ← Stack.pop evm.stack
  let acc := evm.env.state.getAccount (u256ToAddr addrW)
  let s ← Stack.push s (Evm.U256.ofNat acc.code.size)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x3c EXTCODECOPY — base 700 (was 20), per-word `GAS_COPY` unchanged. -/
def extcodecopy : Evm.Frontier.Vm.Instructions.Handler := fun evm => do
  let (addrW, dest, off, len, s) ← do
    let (a, s1) ← Stack.pop evm.stack
    let (b, s2) ← Stack.pop s1
    let (c, s3) ← Stack.pop s2
    let (d, s4) ← Stack.pop s3
    pure (a, b, c, d, s4)
  let destN := dest.toNat
  let offN  := off.toNat
  let lenN  := len.toNat
  let words := (lenN + 31) / 32
  let baseCost := Evm.TangerineWhistle.Vm.Gas.extCode + Gas.copy * words
  let gasLeft ← Gas.charge evm.gasLeft baseCost
  let (gasLeft, mem) ← Evm.Frontier.Vm.Instructions.chargeMemory gasLeft evm.memory destN lenN
  let code := (evm.env.state.getAccount (u256ToAddr addrW)).code
  let mem := Memory.write mem destN (Evm.Bytes.sliceZeroPad code offN lenN)
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

end Evm.TangerineWhistle.Vm.Instructions
