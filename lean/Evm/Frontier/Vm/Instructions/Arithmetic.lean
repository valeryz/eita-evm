/-
  Evm.Frontier.Vm.Instructions.Arithmetic — opcodes 0x01..0x0b.

  EELS reference: ethereum/frontier/vm/instructions/arithmetic.py.

  Covers ADD, MUL, SUB, DIV, SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP, and
  SIGNEXTEND. All arithmetic is mod 2^256 by construction (`BitVec 256`).
  Signed operations use the two's-complement view via `BitVec.sdiv` /
  `BitVec.srem` — note that EVM's SMOD truncates toward zero (sign follows
  the dividend), which is `srem`, not `smod`.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

def powMod (base e modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else
    let rec go (b e acc : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => acc
      | fuel+1 =>
        if e = 0 then acc
        else
          let acc' := if e % 2 = 1 then (acc * b) % modulus else acc
          go ((b * b) % modulus) (e / 2) acc' fuel
    -- 257 iterations cover any exponent < 2^256.
    go (base % modulus) e (1 % modulus) 257

def signExtend (b x : Evm.U256) : Evm.U256 :=
  let bn := b.toNat
  if bn ≥ 31 then x
  else
    let k       := 8 * bn + 7
    let xn      := x.toNat
    let mask    : Nat := (1 <<< (k + 1)) - 1
    let allOnes : Nat := (1 <<< 256) - 1
    let upper   : Nat := allOnes - mask
    if (xn >>> k) &&& 1 = 1 then
      Evm.U256.ofNat ((xn &&& mask) ||| upper)
    else
      Evm.U256.ofNat (xn &&& mask)

def expByteSize (e : Nat) : Nat :=
  if e = 0 then 0 else Nat.log2 e / 8 + 1

/-- 0x01 ADD -/
def add : Handler := runBinary Gas.veryLow (· + ·)

/-- 0x02 MUL -/
def mul : Handler := runBinary Gas.low (· * ·)

/-- 0x03 SUB -/
def sub : Handler := runBinary Gas.veryLow (· - ·)

/-- 0x04 DIV (unsigned). EVM convention: `x / 0 = 0`. (Coincides with
    `BitVec.udiv` since `Nat.div n 0 = 0`, but we make the intent
    explicit since the same isn't true for `BitVec.umod`/`srem`.) -/
def div : Handler := runBinary Gas.low fun a b =>
  if b = 0 then 0 else BitVec.udiv a b

/-- 0x05 SDIV (signed, truncates toward zero). EVM: `x / 0 = 0`;
    `INT256_MIN / -1 = INT256_MIN`. -/
def sdiv : Handler := runBinary Gas.low fun a b =>
  if b = 0 then 0 else BitVec.sdiv a b

/-- 0x06 MOD (unsigned). EVM: `x mod 0 = 0`. Lean's `BitVec.umod x 0`
    returns `x` (since `Nat.mod n 0 = n`), so the explicit guard is
    required. -/
def mod_ : Handler := runBinary Gas.low fun a b =>
  if b = 0 then 0 else BitVec.umod a b

/-- 0x07 SMOD (signed, sign of dividend). EVM: `x smod 0 = 0`.
    Note: EVM's SMOD is C-style remainder (`srem`), not the
    mathematician's modulo (`smod`) — the sign follows the dividend. -/
def smod_ : Handler := runBinary Gas.low fun a b =>
  if b = 0 then 0 else BitVec.srem a b

/-- 0x08 ADDMOD: `(a + b) mod n`; `n = 0` yields 0. The addition happens
    in `Nat` (unbounded), so no wrap before the mod. -/
def addmod : Handler := runTernary Gas.mid fun a b n =>
  if n = 0 then 0
  else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)

/-- 0x09 MULMOD: `(a * b) mod n`; `n = 0` yields 0. -/
def mulmod : Handler := runTernary Gas.mid fun a b n =>
  if n = 0 then 0
  else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)

/-- 0x0a EXP: `base^exp mod 2^256`. Gas: `10 + 10 * byteLen(exp)` at
    Frontier (per-byte cost rises to 50 at Spurious Dragon, EIP-160). -/
def exp : Handler := fun evm => do
  let (base, e, s) ← Stack.pop2 evm.stack
  let cost := Gas.exp + Gas.expByte * expByteSize e.toNat
  let gasLeft ← Gas.charge evm.gasLeft cost
  let result := Evm.U256.ofNat (powMod base.toNat e.toNat (1 <<< 256))
  let s ← Stack.push s result
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x0b SIGNEXTEND: sign-extend `x` from byte `b` (counted from LSB). -/
def signextend : Handler := runBinary Gas.low signExtend

end Evm.Frontier.Vm.Instructions
