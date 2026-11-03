/-
  Evm.Byzantium.Spec.ReturndataStep — EIP-211 RETURNDATASIZE (0x3d)
  and RETURNDATACOPY (0x3e).

  EELS reference: `forks/byzantium/vm/instructions/memory.py`
  (`returndatacopy`) and `vm/instructions/environment.py`
  (`returndatasize`).

  These two opcodes expose the last sub-call's return data to the
  parent frame between sub-calls. The `returnData` field on `Evm`
  is updated by every CALL/CALLCODE/DELEGATECALL/STATICCALL
  sub-frame merge (whether successful or REVERTed); RETURNDATASIZE
  reads its length, RETURNDATACOPY copies a slice into memory.

  RETURNDATACOPY differs from CALLDATACOPY/CODECOPY in one key
  way: out-of-bounds reads ARE an error (not silently zero-padded).
  EELS raises `OutOfBoundsRead`; Lean rounds it to `OutOfGas` as
  the nearest neighbour exception.

  Implementation reference:
    * `Evm.Byzantium.Vm.Instructions.Memory.returndatasize`
      (lines 26-29) — pushes `Evm.U256.ofNat evm.returnData.size`.
    * `Evm.Byzantium.Vm.Instructions.Memory.returndatacopy`
      (lines 34-47) — bounds-check, charge, copy.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.StepShapes  -- IsNullaryPushStep
import Evm.Frontier.Spec.MemStep     -- memExpansionGas, memAfterExpand

namespace Evm.Byzantium.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep memExpansionGas memAfterExpand)

/-! ## 0x3d RETURNDATASIZE

    Push the size of `evm.returnData`. Uses the
    `IsNullaryPushStep` shape — same family as MSIZE, CODESIZE,
    etc. Cost is `Gas.base` (= 2). -/
abbrev IsReturndatasizeStep : Evm → Evm → Prop :=
  IsNullaryPushStep
    (fun evm => Evm.U256.ofNat evm.returnData.size)
    Gas.base

/-! ## 0x3e RETURNDATACOPY

    Pop `destOff`, `offset`, `len`. Bounds-check:
      `offset + len ≤ |returnData|`.
    Otherwise error (no silent zero-pad). Charge memExpansion +
    `Gas.veryLow + Gas.copy * ceilWords(len)`. Copy
    `returnData[offset .. offset+len]` to `memory[destOff ..
    destOff+len]`. Advance pc.

    Bounds-check failure is captured by NOT including the success
    relation as the active step — there's no separate "failed"
    post-state in our spec language (the impl returns `.error`,
    refinement maps it to "no `IsReturndatacopyStep evm evm'`
    holds"). -/
def IsReturndatacopyStep (evm evm' : Evm) : Prop :=
  ∃ destOff offset len rest,
    evm.stack = destOff :: offset :: len :: rest ∧
    let destOffN := destOff.toNat
    let offsetN  := offset.toNat
    let lenN     := len.toNat
    -- EIP-211 bounds check: source range must lie within returnData.
    offsetN + lenN ≤ evm.returnData.size ∧
    let copyCost := Gas.veryLow + Gas.copy * ((lenN + 31) / 32)
    let memCost  := memExpansionGas evm.memory destOffN lenN
    let totalGas := copyCost + memCost
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory destOffN lenN
    let bytes := Evm.Bytes.sliceZeroPad evm.returnData offsetN lenN
    evm' = { evm with
      stack   := rest,
      memory  := Memory.write mem' destOffN bytes,
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## Structural facts -/

/-- RETURNDATASIZE never touches memory, state, or returnData. -/
theorem returndatasize_pure (evm evm' : Evm)
    (h : IsReturndatasizeStep evm evm') :
    evm'.memory     = evm.memory ∧
    evm'.env        = evm.env    ∧
    evm'.returnData = evm.returnData := by
  -- IsNullaryPushStep evm evm' unfolds to a record update touching
  -- only stack/gasLeft/pc. Extract the witnesses and read off the
  -- equation for each preserved field.
  unfold IsReturndatasizeStep IsNullaryPushStep at h
  obtain ⟨_, _, hEq⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [hEq]

/-- RETURNDATACOPY does not modify `returnData` itself (it's the
    SOURCE of the copy, not the target). -/
theorem returndatacopy_preserves_returndata (evm evm' : Evm)
    (h : IsReturndatacopyStep evm evm') :
    evm'.returnData = evm.returnData := by
  obtain ⟨_, _, _, _, _, _, _, hEvm⟩ := h
  rw [hEvm]

/-! ## Notes

    - The `returnData` field is set by every CALL/CALLCODE/
      DELEGATECALL/STATICCALL post-merge (the trampoline's
      `resumeCallOk` / `resumeCallRevert` write it to `subEvm.output`
      / `subEvm.output` respectively). Hard-errors (`resumeCallErr`)
      reset it to `Bytes.empty`. RETURNDATASIZE reads whatever was
      most recently set; pre-any-call it's `Bytes.empty`.

    - RETURNDATACOPY is uncopyable with `Frontier.Spec.IsNullaryPush
      Step` because it pops 3 args. But it's also not a clean
      `IsTernaryStep` (which assumes a pure stack op with no
      memory effect). Hence a one-off relation here.

    - The "out-of-bounds" failure is, in spec terms, the negation
      of the relation: no `evm'` exists. EELS' explicit `raise
      OutOfBoundsRead` and Lean impl's `.error .outOfGas` both
      encode this. The refinement obligation must show the impl
      raises iff the relation has no witness.

    - The Lean impl uses `Evm.Bytes.sliceZeroPad` for the copy.
      With the explicit bounds-check ensuring `offsetN + lenN ≤
      |returnData|`, the zero-padding is never triggered — the
      `sliceZeroPad` reduces to a plain slice. Kept in the spec
      for parity with the impl. -/

end Evm.Byzantium.Spec
