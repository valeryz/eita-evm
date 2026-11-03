/-
  Evm.Frontier.Spec.Step — per-opcode step relations for the
  simple opcodes (arithmetic / bitwise / comparison / stack /
  push / nullary lookups).

  Each spec is a one-line `abbrev` over the parametric shapes in
  `StepShapes.lean`. Adding a new arithmetic opcode is two lines:
  declare its operation, then `abbrev IsXxxStep := IsBinaryStep ...`.

  Out of scope (more substantial spec work, separate files):
    - Memory ops (MLOAD, MSTORE, MSTORE8) — memory expansion.
    - Storage ops (SLOAD, SSTORE) — read/write env.state.
    - Account-state lookups (BALANCE, EXTCODESIZE, EXTCODECOPY) —
      read env.state of arbitrary addresses.
    - LOG0..LOG4 — write to env.logs.
    - Control flow (JUMP, JUMPI) — needs jumpdest validation.
    - System ops (CALL, CREATE, RETURN, REVERT, SELFDESTRUCT) —
      multi-frame.
-/

import Evm.Frontier.Spec.StepShapes
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Instructions.Bitwise
import Evm.Frontier.Vm

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions (signExtend powMod expByteSize byteOf)

/-! ## Arithmetic (0x01..0x0b)

    All of these are pure stack ops with a fixed gas cost. -/

abbrev IsAddStep := IsBinaryStep (fun a b => a + b) Gas.veryLow

abbrev IsMulStep := IsBinaryStep (fun a b => a * b) Gas.low

abbrev IsSubStep := IsBinaryStep (fun a b => a - b) Gas.veryLow

abbrev IsDivStep :=
  IsBinaryStep (fun a b => if b = 0 then 0 else BitVec.udiv a b) Gas.low

abbrev IsSdivStep :=
  IsBinaryStep (fun a b => if b = 0 then 0 else BitVec.sdiv a b) Gas.low

abbrev IsModStep :=
  IsBinaryStep (fun a b => if b = 0 then 0 else BitVec.umod a b) Gas.low

abbrev IsSmodStep :=
  IsBinaryStep (fun a b => if b = 0 then 0 else BitVec.srem a b) Gas.low

abbrev IsAddmodStep :=
  IsTernaryStep (fun a b n =>
    if n = 0 then 0
    else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)) Gas.mid

abbrev IsMulmodStep :=
  IsTernaryStep (fun a b n =>
    if n = 0 then 0
    else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)) Gas.mid

/-- EXP has a dynamic gas cost dependent on the byte-size of the
    exponent, so it doesn't fit the fixed-gas `IsBinaryStep` shape. -/
def IsExpStep (evm evm' : Evm) : Prop :=
  ∃ base e rest,
    evm.stack = base :: e :: rest ∧
    rest.length < stackLimit ∧
    let cost := Gas.exp + Gas.expByte * expByteSize e.toNat
    evm.gasLeft ≥ cost ∧
    evm' = { evm with
      stack   := Evm.U256.ofNat (powMod base.toNat e.toNat (1 <<< 256)) :: rest,
      gasLeft := evm.gasLeft - cost,
      pc      := evm.pc + 1 }

abbrev IsSignextendStep := IsBinaryStep signExtend Gas.low

/-! ## Comparison (0x10..0x15)

    Boolean results encoded as 0 / 1. -/

abbrev IsLtStep :=
  IsBinaryStep (fun a b => if a < b then 1 else 0) Gas.veryLow

abbrev IsGtStep :=
  IsBinaryStep (fun a b => if a > b then 1 else 0) Gas.veryLow

abbrev IsSltStep :=
  IsBinaryStep (fun a b => if BitVec.slt a b then 1 else 0) Gas.veryLow

abbrev IsSgtStep :=
  IsBinaryStep (fun a b => if BitVec.slt b a then 1 else 0) Gas.veryLow

abbrev IsEqStep :=
  IsBinaryStep (fun a b => if a = b then 1 else 0) Gas.veryLow

abbrev IsIszeroStep :=
  IsUnaryStep (fun a => if a = 0 then 1 else 0) Gas.veryLow

/-! ## Bitwise (0x16..0x1a) -/

abbrev IsAndStep := IsBinaryStep (fun a b => a &&& b) Gas.veryLow
abbrev IsOrStep  := IsBinaryStep (fun a b => a ||| b) Gas.veryLow
abbrev IsXorStep := IsBinaryStep (fun a b => a ^^^ b) Gas.veryLow
abbrev IsNotStep := IsUnaryStep  (fun a => ~~~ a) Gas.veryLow

/-- BYTE: extract the `n`-th byte of `x`, indexed from the most
    significant. `n ≥ 32` yields 0. Shares `byteOf` with the
    executable handler. -/
abbrev IsByteStep := IsBinaryStep byteOf Gas.veryLow

/-! ## Stack manipulation (0x50, 0x60..0x9f) -/

abbrev IsPopStep' := IsPopStep Gas.base

/-- PUSH-N for N ∈ [1..32]. -/
abbrev IsPush1Step  := IsPushStep 1  Gas.veryLow
abbrev IsPush2Step  := IsPushStep 2  Gas.veryLow
abbrev IsPush3Step  := IsPushStep 3  Gas.veryLow
abbrev IsPush4Step  := IsPushStep 4  Gas.veryLow
abbrev IsPush5Step  := IsPushStep 5  Gas.veryLow
abbrev IsPush6Step  := IsPushStep 6  Gas.veryLow
abbrev IsPush7Step  := IsPushStep 7  Gas.veryLow
abbrev IsPush8Step  := IsPushStep 8  Gas.veryLow
abbrev IsPush16Step := IsPushStep 16 Gas.veryLow
abbrev IsPush32Step := IsPushStep 32 Gas.veryLow
-- (the others, 9..15 and 17..31, follow the same pattern;
-- omitted to keep the file short — declare on demand)

/-- DUP-n for n ∈ [1..16]. -/
abbrev IsDup1Step  := IsDupStep 1  Gas.veryLow
abbrev IsDup2Step  := IsDupStep 2  Gas.veryLow
abbrev IsDup3Step  := IsDupStep 3  Gas.veryLow
abbrev IsDup4Step  := IsDupStep 4  Gas.veryLow
abbrev IsDup16Step := IsDupStep 16 Gas.veryLow

/-- SWAP-n for n ∈ [1..16]. -/
abbrev IsSwap1Step  := IsSwapStep 1  Gas.veryLow
abbrev IsSwap2Step  := IsSwapStep 2  Gas.veryLow
abbrev IsSwap3Step  := IsSwapStep 3  Gas.veryLow
abbrev IsSwap16Step := IsSwapStep 16 Gas.veryLow

/-! ## Environment / context reads (0x30..0x45)

    Each pushes one value derived from the running frame and its
    environment. -/

abbrev IsAddressStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.message.currentTarget.toNat) Gas.base

abbrev IsOriginStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.origin.toNat) Gas.base

abbrev IsCallerStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.message.caller.toNat) Gas.base

abbrev IsCallvalueStep :=
  IsNullaryPushStep (fun evm => evm.message.value) Gas.base

abbrev IsCalldatasizeStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.message.data.size) Gas.base

/-- CALLDATALOAD pops an offset and pushes 32 bytes of calldata
    (zero-padded past the end). The result depends on the frame's
    calldata, not just the popped word, so it doesn't fit the pure
    `IsUnaryStep` shape. -/
def IsCalldataloadStep (evm evm' : Evm) : Prop :=
  ∃ a rest,
    evm.stack = a :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := Evm.U256.ofBytesBE
                   (Evm.Bytes.sliceZeroPad evm.message.data a.toNat 32) :: rest,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 1 }

abbrev IsCodesizeStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.message.code.size) Gas.base

abbrev IsGaspriceStep :=
  IsNullaryPushStep (fun evm => evm.env.gasPrice) Gas.base

abbrev IsCoinbaseStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.coinbase.toNat) Gas.base

abbrev IsTimestampStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.timestamp) Gas.base

abbrev IsNumberStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.number) Gas.base

abbrev IsDifficultyStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.difficulty) Gas.base

abbrev IsGaslimitStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.gasLimit) Gas.base

abbrev IsPcStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.pc) Gas.base

abbrev IsMsizeStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.memory.size) Gas.base

/-- GAS pushes the gas remaining AFTER charging GAS's own cost. -/
abbrev IsGasStep :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat (evm.gasLeft - Gas.base)) Gas.base

/-! ## JUMPDEST (0x5b)

    No-op except for pc-advance and gas charge. Identity on stack. -/

def IsJumpdestStep (evm evm' : Evm) : Prop :=
  evm.gasLeft ≥ Gas.jumpDest ∧
  evm' = { evm with
    gasLeft := evm.gasLeft - Gas.jumpDest,
    pc      := evm.pc + 1 }

/-! ## ADD's IsAddStep is now just an abbrev over IsBinaryStep.
    The corresponding refinement proof in Refinement.lean still
    targets `IsAddStep` -- but now `IsAddStep evm evm'` unfolds to
    a proposition with the same shape, so the proof obligation is
    identical. -/

end Evm.Frontier.Spec
