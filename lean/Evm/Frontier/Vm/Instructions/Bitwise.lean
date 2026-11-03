/-
  Evm.Frontier.Vm.Instructions.Bitwise — opcodes 0x16..0x1a.

  EELS reference: ethereum/frontier/vm/instructions/bitwise.py.

  Frontier has AND, OR, XOR, NOT, BYTE. The shift opcodes SHL/SHR/SAR
  arrive at Constantinople (EIP-145).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- The `i`-th byte of `x`, big-endian (0 when `i ≥ 32`). Public and
    shared by the spec's `IsByteStep` (like `signExtend`), so BYTE's
    refinement lemma holds definitionally. EELS
    frontier/vm/instructions/bitwise.py `bitwise_byte`. -/
def byteOf (i x : Evm.U256) : Evm.U256 :=
  let ix := i.toNat
  if ix ≥ 32 then 0
  else
    let shift := (31 - ix) * 8
    Evm.U256.ofNat ((x.toNat >>> shift) &&& 0xff)

/-- 0x16 AND -/
def and_ : Handler := runBinary Gas.veryLow (· &&& ·)

/-- 0x17 OR -/
def or_  : Handler := runBinary Gas.veryLow (· ||| ·)

/-- 0x18 XOR -/
def xor_ : Handler := runBinary Gas.veryLow (· ^^^ ·)

/-- 0x19 NOT -/
def not_ : Handler := runUnary Gas.veryLow (fun a => ~~~ a)

/-- 0x1a BYTE: i-th byte of `x` (big-endian). Returns 0 if `i ≥ 32`. -/
def byte : Handler := runBinary Gas.veryLow byteOf

end Evm.Frontier.Vm.Instructions
