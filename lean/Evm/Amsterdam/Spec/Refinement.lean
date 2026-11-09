/-
  Evm.Amsterdam.Spec.Refinement — proofs that the Amsterdam Effect
  interpreter refines the Amsterdam Spec relations.

  Amsterdam adds:

    * `BlockAccessList.lean`   — EIP-7928 BAL (stub; abbrev = Unit).
    * `CodeSizeCap.lean`       — EIP-7954 MAX_CODE_SIZE bump to 0x10000.
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
import Evm.Byzantium.Spec.Refinement
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

/-- SLOTNUM (`doSlotNumber`, the 0x4b arm) is a nullary push of `slot_number` at
    `GAS_BASE`. EELS `forks/amsterdam/vm/instructions/block.py::slot_number`. -/
theorem slotNumber_sound (evm evm' : Evm) :
    Evm.Amsterdam.Vm.Effect.doSlotNumber evm = .continue evm' →
    IsSlotNumberStep evm evm' :=
  Evm.Byzantium.Spec.Refinement.stepNullaryPush_sound Gas.base
    (fun e => Evm.U256.ofNat e.env.slotNumber) evm evm'

/-! ## EIP-8024 DUPN / SWAPN / EXCHANGE (0xE6 / 0xE7 / 0xE8)

    Each reads a single immediate byte after the opcode (so `pc`
    advances by 2). All three are pure stack-machine ops; the impl
    handlers `doDupN` / `doSwapN` / `doExchange` are
    `StepResult`-yielding in `Amsterdam.Vm.Effect`. -/

/-- The implementation's `decodeSingle` is EELS `decode_single` as the spec states it. -/
theorem decodeSingle_eq (x : Nat) :
    Evm.Amsterdam.Vm.Effect.decodeSingle x = decodeSingle x := by
  unfold Evm.Amsterdam.Vm.Effect.decodeSingle decodeSingle
  by_cases h : x ≤ 90 ∨ 128 ≤ x
  · rw [ite_eq_left h, ite_eq_right (show ¬(90 < x ∧ x < 128) by omega)]
  · rw [ite_eq_right h, ite_eq_left (show 90 < x ∧ x < 128 by omega)]

/-- The implementation's `decodePair` is EELS `decode_pair` as the spec states it. -/
theorem decodePair_eq (x : Nat) :
    Evm.Amsterdam.Vm.Effect.decodePair x = decodePair x := by
  unfold Evm.Amsterdam.Vm.Effect.decodePair decodePair
  by_cases h : x ≤ 81 ∨ 128 ≤ x
  · rw [ite_eq_left h, ite_eq_right (show ¬(81 < x ∧ x < 128) by omega)]
  · rw [ite_eq_right h, ite_eq_left (show 81 < x ∧ x < 128 by omega)]

/-- 0xE6 DUPN (`doDupN`) refines `IsDupNStep`. EELS
    `forks/amsterdam/vm/instructions/stack.py::dupn` (213-242). -/
theorem dupN_sound (evm evm' : Evm) :
    Evm.Amsterdam.Vm.Effect.doDupN evm = .continue evm' →
    IsDupNStep evm evm' := by
  intro h
  unfold Evm.Amsterdam.Vm.Effect.doDupN at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn
    split at h
    · exact absurd h (by simp)
    · rename_i v hv
      split at h
      · exact absurd h (by simp)
      · rename_i g hg
        split at h
        · exact absurd h (by simp)
        · rename_i st hs
          obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
          obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hs
          injection h with h; subst h
          rw [decodeSingle_eq] at hn
          exact ⟨n, v, hn, hv, hlt, hle, rfl⟩

/-- 0xE7 SWAPN (`doSwapN`) refines `IsSwapNStep`. EELS `stack.py::swapn` (245-278). -/
theorem swapN_sound (evm evm' : Evm) :
    Evm.Amsterdam.Vm.Effect.doSwapN evm = .continue evm' →
    IsSwapNStep evm evm' := by
  intro h
  unfold Evm.Amsterdam.Vm.Effect.doSwapN at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn
    split at h
    · exact absurd h (by simp)
    · rename_i top rest hst
      split at h
      · exact absurd h (by simp)
      · rename_i other ho
        split at h
        · exact absurd h (by simp)
        · rename_i g hg
          obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
          injection h with h; subst h
          rw [decodeSingle_eq] at hn
          exact ⟨n, top, other, rest, hn, hst, ho, hle, rfl⟩

/-- 0xE8 EXCHANGE (`doExchange`) refines `IsExchangeStep`. EELS `stack.py::exchange`
    (281-314). -/
theorem exchange_sound (evm evm' : Evm) :
    Evm.Amsterdam.Vm.Effect.doExchange evm = .continue evm' →
    IsExchangeStep evm evm' := by
  intro h
  unfold Evm.Amsterdam.Vm.Effect.doExchange at h
  split at h
  · exact absurd h (by simp)
  · rename_i n m hnm
    split at h
    · rename_i vn vm hn hm
      split at h
      · exact absurd h (by simp)
      · rename_i g hg
        obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
        injection h with h; subst h
        rw [decodePair_eq] at hnm
        exact ⟨n, m, vn, vm, hnm, hn, hm, hle, rfl⟩
    · exact absurd h (by simp)

/-! ## EIP-7954 deployed-code size bump -/

/-- EIP-7954: new cap 0x10000 instead of 0x6000. OPEN, and not provable as things stand:
    the implementation (`Create.resume`, `Tx.createEnd`, the derived `EffectCreate` /
    `EffectTx`) still applies EIP-170's 0x6000 at Amsterdam, so Amsterdam deployments of
    0x6001..0x10000 bytes fail where EELS accepts them. Closing it changes emitted code. -/
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
