/-
  Evm.Constantinople.Vm.Instructions.Bitwise — EIP-145 SHL / SHR / SAR.

  EELS reference: ethereum/forks/constantinople/vm/instructions/bitwise.py.
  All three opcodes cost `OPCODE_SHL = OPCODE_SHR = OPCODE_SAR = VERY_LOW`
  (3 gas, ethereum/forks/constantinople/vm/gas.py lines 107-109).

  Stack layout: top is `shift`, next is `value`. Result is pushed.

  Shift-out-of-range:
    * SHL: shift ≥ 256 ⇒ 0
    * SHR: shift ≥ 256 ⇒ 0
    * SAR: shift ≥ 256 ⇒ 0 if `value ≥ 0` signed, else `MAX_VALUE`
      (i.e. all-ones; sign-extending right shift saturates)
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Constantinople.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x1b SHL (logical shift left).

    EELS `bitwise_shl` (forks/constantinople/vm/instructions/bitwise.py
    lines 159-186): `if shift < 256: U256((value << shift) & MAX) else
    0`. We perform the shift on `Nat` (unbounded) and then re-cast to
    `U256`, which discards the high bits exactly as the EELS mask does. -/
def shl : Handler := runBinary Gas.veryLow fun shift value =>
  let s := shift.toNat
  if s ≥ 256 then 0
  else Evm.U256.ofNat (value.toNat <<< s)

/-- 0x1c SHR (logical shift right).

    EELS `bitwise_shr` (forks/constantinople/vm/instructions/bitwise.py
    lines 189-216): `if shift < 256: value >> shift else 0`. Unsigned
    `>>>` on a non-negative `Nat` is exactly the EELS semantics. -/
def shr : Handler := runBinary Gas.veryLow fun shift value =>
  let s := shift.toNat
  if s ≥ 256 then 0
  else Evm.U256.ofNat (value.toNat >>> s)

/-- Treat `x : U256` as signed two's-complement; return `(isNegative,
    absoluteValue)`. -/
private def toSigned (x : Evm.U256) : Bool × Nat :=
  let n := x.toNat
  let signBit := 1 <<< 255
  if n ≥ signBit then
    (true, (1 <<< 256) - n)
  else
    (false, n)

/-- 0x1d SAR (arithmetic shift right).

    EELS `bitwise_sar` (forks/constantinople/vm/instructions/bitwise.py
    lines 219-248): the value is interpreted as a signed integer and
    shifted right (Python's `>>` on a signed `int` is arithmetic). The
    out-of-range case splits on the sign:
      * `shift >= 256` and `signed_value >= 0` ⇒ 0
      * `shift >= 256` and `signed_value <  0` ⇒ U256.MAX_VALUE
        (all-ones, i.e. -1 in two's complement)

    We emulate two's-complement arithmetic-right-shift by `Nat.shr` on
    the magnitude and OR-ing in the sign-extension bits at the top. -/
def sar : Handler := runBinary Gas.veryLow fun shift value =>
  let (neg, _mag) := toSigned value
  let s := shift.toNat
  if s ≥ 256 then
    if neg then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
  else if ¬ neg then
    -- Positive: plain unsigned shift suffices.
    Evm.U256.ofNat (value.toNat >>> s)
  else
    -- Negative: shift the *value* (not the magnitude) and sign-extend
    -- the top `s` bits with 1s. Computing `-((-x) >> s)`-style via
    -- magnitudes is awkward because the absolute value of INT256_MIN
    -- doesn't fit in 256 unsigned bits. We instead arithmetic-shift
    -- by ORing the magnitude shift with the high-bit mask.
    let raw      := value.toNat >>> s
    -- Bits we need to set to 1 (the top `s` bits, since the value was
    -- negative).
    let topMask  : Nat :=
      ((1 <<< 256) - 1) ^^^ ((1 <<< (256 - s)) - 1)
    Evm.U256.ofNat (raw ||| topMask)

end Evm.Constantinople.Vm.Instructions
