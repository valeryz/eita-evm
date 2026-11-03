/-
  Evm.Byzantium.Spec.RevertStep — EIP-140 0xfd REVERT.

  EELS reference: `forks/byzantium/vm/instructions/system.py::revert`.

  REVERT halts the frame WITH a returndata payload AND a
  failure-signal. Distinguishing features vs STOP/RETURN:

    1. State mutations from the frame are NOT merged into the
       parent (the trampoline's `resumeCallRevert` path skips
       `mergeChild`).
    2. The output IS preserved as the parent's `returnData`.
    3. The parent's CALL/STATICCALL/DELEGATECALL pushes 0 (failure)
       rather than 1.
    4. Forwarded gas remaining at the time of REVERT is REFUNDED to
       the parent (unlike hard errors which consume all forwarded
       gas).

  Gas cost: memory expansion for `[offset, offset+len)`. No fixed
  base cost (other than the implicit per-step accounting).

  Implementation reference: `Evm.Byzantium.Vm.Instructions.System.revert`
  (lines 27-36):

      let (offset, len, s) ← Stack.pop2 evm.stack
      let (gasLeft, mem)   ← chargeMemory ...
      let output := Memory.read mem off lenN
      return { evm with halted := true, reverted := true,
                        output := output, ... }
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.MemStep  -- reuse memExpansionGas, memAfterExpand
import Evm.Byzantium.Vm.Instructions.System

namespace Evm.Byzantium.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (memExpansionGas memAfterExpand)

/-! ## IsRevertStep — terminal REVERT step relation

    Pop `offset`, `len`. Charge memory expansion for `[offset,
    offset+len)`. Set `halted := true`, `reverted := true`,
    `output := Memory.read mem offset len`. Advance pc.

    This is a *terminating* step: from the parent trampoline's
    perspective, the sub-frame halts with the revert flag set, and
    the post-merge step routes through `resumeCallRevert`. The
    relation here is purely about the in-frame transition, not the
    parent merge. -/
def IsRevertStep (evm evm' : Evm) : Prop :=
  ∃ offset len rest,
    evm.stack = offset :: len :: rest ∧
    let off  := offset.toNat
    let lenN := len.toNat
    let totalGas := memExpansionGas evm.memory off lenN
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory off lenN
    evm' = { evm with
      stack    := rest,
      memory   := mem',
      gasLeft  := evm.gasLeft - totalGas,
      output   := Memory.read mem' off lenN,
      halted   := true,
      reverted := true,
      pc       := evm.pc + 1 }

/-! ## Structural lemmas -/

/-- REVERT always sets both `halted` and `reverted`. -/
theorem revert_halts_and_reverts (evm evm' : Evm)
    (h : IsRevertStep evm evm') :
    evm'.halted = true ∧ evm'.reverted = true := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  refine ⟨?_, ?_⟩ <;> rw [hEvm]

/-- REVERT preserves env (logs, refundCounter, state, …): no
    "incorporate-on-success"-style merge. The trampoline's
    `resumeCallRevert` is the layer that actually discards
    `subEvm.env`; here we just observe that the frame's own env is
    unchanged by the opcode itself. -/
theorem revert_env_unchanged (evm evm' : Evm)
    (h : IsRevertStep evm evm') :
    evm'.env = evm.env := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  rw [hEvm]

/-! ## Notes

    - REVERT was added at Byzantium. Pre-Byzantium frames cannot
      produce a `reverted = true` post-state (no opcode sets the
      flag). The `resumeCallRevert` path in earlier forks'
      trampolines is defensively present but unreachable.

    - The opcode's cost is *just* memory expansion. There is no
      fixed base cost beyond what every opcode pays implicitly
      (zero, in the IR-level accounting). Some EVM impls list
      "REVERT base cost = 0"; that's what this relation reflects.

    - The output is `Memory.read mem' off lenN` — note `mem'`
      (post-expansion), not `mem` (pre). For `len > 0` past the
      pre-expansion size, the bytes are zero (memory is zero-filled
      on expansion). For `len = 0`, output is `Bytes.empty`.

    - `evm'.gasLeft` is `evm.gasLeft - totalGas`. The trampoline's
      `resumeCallRevert` then refunds `evm'.gasLeft` to the
      parent's `gasLeft`. This means the parent sees a refund of
      exactly the gas the sub-frame had remaining at REVERT time —
      consistent with EELS' `incorporate_child_on_error` analogue
      for the revert path. -/

end Evm.Byzantium.Spec
