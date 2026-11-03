/-
  Evm.Constantinople.Spec.BitwiseStep — step relations for the EIP-145
  shift opcodes SHL / SHR / SAR.

  EELS reference: forks/constantinople/vm/instructions/bitwise.py
  `bitwise_shl` / `bitwise_shr` / `bitwise_sar`.

  All three opcodes share the binary stack shape from
  `Evm.Frontier.Spec.StepShapes.IsBinaryStep`. Only the operation
  itself differs, so each spec is a one-liner.

  Per the SPEC-METHODOLOGY: these are *new* relations introduced at
  Constantinople. They live here (and only here) and are imported by
  every later fork that needs them (Petersburg / Istanbul / Berlin /
  ... all inherit unchanged — none of them re-prices or re-defines
  shifts). The corresponding `Evm.Constantinople.Vm.Instructions.shl/
  shr/sar` are refined against these by the Refinement file.
-/

import Evm.Frontier.Spec.StepShapes
import Evm.Constantinople.Vm.Instructions.Bitwise

namespace Evm.Constantinople.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsBinaryStep)

/-- 0x1b SHL (logical shift left). Top of stack is the shift amount;
    second-from-top is the value. Shift ≥ 256 yields 0. -/
abbrev IsShlStep : Evm → Evm → Prop :=
  IsBinaryStep
    (fun shift value =>
      let s := shift.toNat
      if s ≥ 256 then 0 else Evm.U256.ofNat (value.toNat <<< s))
    Gas.veryLow

/-- 0x1c SHR (logical shift right). Unsigned. Shift ≥ 256 yields 0. -/
abbrev IsShrStep : Evm → Evm → Prop :=
  IsBinaryStep
    (fun shift value =>
      let s := shift.toNat
      if s ≥ 256 then 0 else Evm.U256.ofNat (value.toNat >>> s))
    Gas.veryLow

/-- 0x1d SAR (arithmetic shift right). Two's-complement sign-extending.
    Shift ≥ 256 yields all-ones if `value` is negative, else 0. -/
abbrev IsSarStep : Evm → Evm → Prop :=
  IsBinaryStep
    (fun shift value =>
      -- Mirror `Evm.Constantinople.Vm.Instructions.sar` exactly:
      let neg := value.toNat ≥ (1 <<< 255)
      let s   := shift.toNat
      if s ≥ 256 then
        if neg then Evm.U256.ofNat ((1 <<< 256) - 1) else 0
      else if ¬ neg then
        Evm.U256.ofNat (value.toNat >>> s)
      else
        -- Negative case: shift the magnitude, then sign-extend by
        -- filling the top `s` bits with 1s. Same trick the
        -- implementation uses; see `Vm/Instructions/Bitwise.lean`.
        let mag := value.toNat
        let shifted := mag >>> s
        let topBits := ((1 <<< s) - 1) <<< (256 - s)
        Evm.U256.ofNat (shifted ||| topBits))
    Gas.veryLow

end Evm.Constantinople.Spec
