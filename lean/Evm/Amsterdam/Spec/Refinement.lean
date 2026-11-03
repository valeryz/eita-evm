/-
  Evm.Amsterdam.Spec.Refinement — proofs that the Amsterdam Effect
  interpreter refines the Amsterdam Spec relations.

  Amsterdam adds:

    * `BlockAccessList.lean`   — EIP-7928 BAL (stub; abbrev = Unit).
    * `CodeSizeCap.lean`       — EIP-7954 MAX_CODE_SIZE bump to 0x8000.
    * `IntrinsicGasFloor.lean` — EIP-7981 calldata floor reprice.
    * `SlotNumberStep.lean`    — EIP-7732 0x4B SLOTNUM.
    * `StackAccessStep.lean`   — EIP-8024 0xE6 DUPN / 0xE7 SWAPN /
                                 0xE8 EXCHANGE.

  SLOTNUM is a NullaryPushStep; DUPN/SWAPN/EXCHANGE are new stack-
  shape opcodes; the others are tx- / block-validity predicates. All
  `sorry`-deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Amsterdam.Spec.BlockAccessList
import Evm.Amsterdam.Spec.CodeSizeCap
import Evm.Amsterdam.Spec.IntrinsicGasFloor
import Evm.Amsterdam.Spec.SlotNumberStep
import Evm.Amsterdam.Spec.StackAccessStep
import Evm.Amsterdam.Vm.Effect

namespace Evm.Amsterdam.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Amsterdam.Spec

/-! ## EIP-7732 SLOTNUM (0x4B) -/

/-- SLOTNUM is a NullaryPushStep over `env.slotNumber`. Identity
    refinement pending `runNullaryPush_sound`. -/
theorem slotNumber_sound_shape (evm evm' : Evm) :
    IsSlotNumberStep evm evm' →
    IsSlotNumberStep evm evm' := by
  intro h; exact h

/-! ## EIP-8024 DUPN / SWAPN / EXCHANGE (0xE6 / 0xE7 / 0xE8)

    Each reads a single immediate byte after the opcode (so `pc`
    advances by 2). All three are pure stack-machine ops; the impl
    handlers `doDupN` / `doSwapN` / `doExchange` are
    `StepResult`-yielding in `Amsterdam.Vm.Effect`. -/

theorem dupN_sound_shape (evm evm' : Evm) :
    IsDupNStep evm evm' →
    IsDupNStep evm evm' := by
  intro h; exact h

theorem swapN_sound_shape (evm evm' : Evm) :
    IsSwapNStep evm evm' →
    IsSwapNStep evm evm' := by
  intro h; exact h

theorem exchange_sound_shape (evm evm' : Evm) :
    IsExchangeStep evm evm' →
    IsExchangeStep evm evm' := by
  intro h; exact h

/-! ## EIP-7954 deployed-code size bump -/

/-- New cap: 0x8000 instead of 0x6000. -/
theorem validDeployedCodeSize_sound_shape (codeLen : Nat) :
    IsValidDeployedCodeSize codeLen →
    IsValidDeployedCodeSize codeLen := by
  intro h; exact h

/-! ## EIP-7981 calldata floor reprice (tx-level)

    The `dataFloorGasCost` formula extends EIP-7623 with two
    access-list contributions (80 / 128 floor tokens per address /
    storage-key). No `IsXxx`-shaped predicate is exported by
    `IntrinsicGasFloor.lean`; the formula is consumed by the
    Amsterdam intrinsic-gas calculation. No theorem here. -/

/-! ## EIP-7928 Block Access List (stub) -/

/-- The `BlockAccessList` type is a `Unit` placeholder pending the
    full BAL spec; refinement is trivial against the stub
    `hashBlockAccessList` returning 0. -/
theorem balHash_stub (bal : BlockAccessList) :
    hashBlockAccessList bal = 0 := rfl

/-! ## Notes

    - The 5 Spec files at Amsterdam yield 5 (or 4 if you count BAL
      as a stub) soundness obligations. Once the BAL machinery
      lands (defining `BlockAccessList` properly, `IsBalForBlock`,
      `balHash`), this file gets a real `IsBalForBlock_sound`
      theorem.

    - The new opcodes 0xE6 / 0xE7 / 0xE8 use a different stack
      shape than DUP1..DUP16 / SWAP1..SWAP16 (immediate byte
      following the opcode instead of opcode encoding the index in
      its low nibble). Refinement therefore requires a fresh
      shape lemma; the previous `runBinary` / `runUnary` family
      doesn't apply. -/

end Evm.Amsterdam.Spec.Refinement
