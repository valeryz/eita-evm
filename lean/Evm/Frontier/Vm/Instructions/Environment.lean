/-
  Evm.Frontier.Vm.Instructions.Environment — opcodes 0x30..0x3c.

  EELS reference: ethereum/frontier/vm/instructions/environment.py.

  Frontier set: ADDRESS, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD,
  CALLDATASIZE, CALLDATACOPY, CODESIZE, CODECOPY, GASPRICE, EXTCODESIZE,
  EXTCODECOPY. EXTCODEHASH arrives at Constantinople (EIP-1052).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

private def addrToU256 (a : Evm.Address) : Evm.U256 :=
  Evm.U256.ofNat a.toNat

private def u256ToAddr (x : Evm.U256) : Evm.Address :=
  Evm.Address.ofNat x.toNat

/-- 0x30 ADDRESS -/
def address : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.message.currentTarget.toNat)

/-- 0x31 BALANCE -/
def balance : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.balance
  let (addrW, s) ← Stack.pop evm.stack
  let bal := evm.env.state.getBalance (u256ToAddr addrW)
  let s ← Stack.push s bal
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x32 ORIGIN -/
def origin : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.env.origin.toNat)

/-- 0x33 CALLER -/
def caller : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.message.caller.toNat)

/-- 0x34 CALLVALUE -/
def callvalue : Handler :=
  runNullaryPush Gas.base (fun evm => evm.message.value)

/-- 0x35 CALLDATALOAD -/
def calldataload : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.veryLow
  let (offset, s) ← Stack.pop evm.stack
  let value := Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad evm.message.data offset.toNat 32)
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x36 CALLDATASIZE -/
def calldatasize : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.message.data.size)

/-- Generic copy from a source `Bytes` (calldata / code / extcode) into
    memory, with the standard `VERY_LOW + 3·words` gas + expansion. -/
def copyToMemory (src : Evm.Bytes) (evm : Evm) : Except Exception Evm := do
  let (dest, off, len, s) ← Stack.pop3 evm.stack
  let destN := dest.toNat
  let offN  := off.toNat
  let lenN  := len.toNat
  let words := (lenN + 31) / 32
  let baseCost := Gas.veryLow + Gas.copy * words
  let gasLeft  ← Gas.charge evm.gasLeft baseCost
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory destN lenN
  let payload := Evm.Bytes.sliceZeroPad src offN lenN
  let mem := Memory.write mem destN payload
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

/-- 0x37 CALLDATACOPY -/
def calldatacopy : Handler := fun evm => copyToMemory evm.message.data evm

/-- 0x38 CODESIZE -/
def codesize : Handler :=
  runNullaryPush Gas.base (fun evm => Evm.U256.ofNat evm.message.code.size)

/-- 0x39 CODECOPY -/
def codecopy : Handler := fun evm => copyToMemory evm.message.code evm

/-- 0x3a GASPRICE -/
def gasprice : Handler :=
  runNullaryPush Gas.base (fun evm => evm.env.gasPrice)

/-- 0x3b EXTCODESIZE -/
def extcodesize : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.extCode
  let (addrW, s) ← Stack.pop evm.stack
  let acc := evm.env.state.getAccount (u256ToAddr addrW)
  let s ← Stack.push s (Evm.U256.ofNat acc.code.size)
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x3c EXTCODECOPY: like CODECOPY but reading from another account. -/
def extcodecopy : Handler := fun evm => do
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
  let gasLeft ← Gas.charge evm.gasLeft (Gas.extCode + Gas.copy * words)
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory destN lenN
  let code := (evm.env.state.getAccount (u256ToAddr addrW)).code
  let mem := Memory.write mem destN (Evm.Bytes.sliceZeroPad code offN lenN)
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
