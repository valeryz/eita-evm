/-
  Evm.Petersburg.Vm.Instructions.Bitwise — EIP-145 shift opcodes
  (SHL 0x1b, SHR 0x1c, SAR 0x1d).

  EELS reference: ethereum/forks/constantinople/vm/instructions/bitwise.py
  (EELS has no separate Petersburg directory; its `constantinople`
  module is the EIP-1283-removed flavour our project labels
  "Petersburg").

  All three opcodes cost `Gas.veryLow` (3) and pop `(shift, value)` —
  shift on top of stack. EVM semantics for the shift count:

    * If `shift >= 256`, SHL/SHR push 0; SAR pushes 0 (positive value)
      or -1 = U256.MAX (negative value).
    * Otherwise SHL is a bit-vector left shift, SHR is a logical right
      shift, SAR is an arithmetic (sign-extending) right shift.

  EELS line numbers below refer to its `bitwise.py` (functions
  `bitwise_shl`, `bitwise_shr`, `bitwise_sar`).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Petersburg.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x1b SHL — logical left shift, modulo 2^256.

    EELS `bitwise_shl` (constantinople/vm/instructions/bitwise.py):

      if shift < 256:
        result = U256((value << shift) & U256.MAX_VALUE)
      else:
        result = U256(0) -/
def shl : Handler := runBinary Gas.veryLow fun shift value =>
  let sN := shift.toNat
  if sN ≥ 256 then 0
  else Evm.U256.ofNat ((value.toNat <<< sN) &&& ((1 <<< 256) - 1))

/-- 0x1c SHR — logical (zero-filling) right shift.

    EELS `bitwise_shr` (constantinople/vm/instructions/bitwise.py):

      if shift < 256:
        result = value >> shift
      else:
        result = U256(0) -/
def shr : Handler := runBinary Gas.veryLow fun shift value =>
  let sN := shift.toNat
  if sN ≥ 256 then 0
  else Evm.U256.ofNat (value.toNat >>> sN)

/-- 0x1d SAR — arithmetic (sign-extending) right shift.

    EELS `bitwise_sar` (constantinople/vm/instructions/bitwise.py):

      shift = int(pop(evm.stack))
      signed_value = pop(evm.stack).to_signed()
      if shift < 256:
        result = U256.from_signed(signed_value >> shift)
      elif signed_value >= 0:
        result = U256(0)
      else:
        result = U256.MAX_VALUE

    For shifts ≥ 256 we collapse to 0 or all-ones based on the top
    bit; otherwise we sign-extend the high bits of the result. We
    work in `Nat` and reconstruct the wrapped 256-bit word at the
    end (mirrors the `signExtend` helper's pattern). -/
def sar : Handler := runBinary Gas.veryLow fun shift value =>
  let sN := shift.toNat
  let vN := value.toNat
  let allOnes : Nat := (1 <<< 256) - 1
  let topBit  : Bool := (vN >>> 255) &&& 1 = 1
  if sN ≥ 256 then
    if topBit then Evm.U256.ofNat allOnes else 0
  else
    let shifted := vN >>> sN
    if topBit then
      -- Sign-extend: OR in 1-bits at positions [256 - sN, 256).
      let signMask : Nat := allOnes - ((1 <<< (256 - sN)) - 1)
      Evm.U256.ofNat (shifted ||| signMask)
    else
      Evm.U256.ofNat shifted

end Evm.Petersburg.Vm.Instructions
