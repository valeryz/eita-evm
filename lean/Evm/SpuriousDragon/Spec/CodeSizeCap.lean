/-
  Evm.SpuriousDragon.Spec.CodeSizeCap — EIP-170 24576-byte cap on
  deployed code.

  EELS reference: `forks/spurious_dragon/vm/interpreter.py::
  process_create_message`, the check inserted *after* init code
  runs but *before* the deposit-gas charge:

      if len(output) > MAX_CODE_SIZE:
          raise OutOfGasError

  Constant value: `MAX_CODE_SIZE = 24576` (= 2 KiB × 12 = 0x6000).

  This is one of the smallest deltas in the SD bucket and applies
  to:
    * the CREATE opcode's post-init-code merge,
    * the tx-level CREATE (txn.to = none),
    * (later) the CREATE2 opcode at Constantinople.

  At SpuriousDragon, EIP-170's failure mode mirrors EIP-2 (Homestead)
  deposit-fail: the CREATE reverts the init code's state changes,
  the sender's nonce bump survives, the parent's CREATE pushes 0.
  EELS routes both EIP-2 deposit-fail and EIP-170 size-cap through
  the same `OutOfGasError` path inside `process_create_message`.

  Implementation reference:
    * `Evm.SpuriousDragon.Fork.lean` line 141:
        `if codeBytes.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize`
      for the tx-CREATE branch.
    * The CREATE-opcode branch lives in `SpuriousDragon/Vm/Effect.lean`'s
      `Evm.Frontier.Vm.Create.resume` (same shape).
-/

import Evm.Frontier.Vm
import Evm.SpuriousDragon.Vm.Gas
import Evm.Forks

namespace Evm.SpuriousDragon.Spec

open Evm.Frontier.Vm

/-! ## The cap

    24576 bytes is the maximum size of the bytecode a CREATE may
    deploy. Output longer than this aborts the deploy. -/

/-- EIP-170 maximum deployed-code size, in bytes. -/
def maxCodeSize : Nat := Evm.SpuriousDragon.Vm.Gas.maxCodeSize

/-- The predicate: the init-code output is short enough to be
    deployable under EIP-170. -/
def IsCodeSizeAllowed (output : Evm.Bytes) : Prop :=
  output.size ≤ maxCodeSize

/-! ## IsCreateCodeSizeRevertStep — the new revert path

    Triggered when init code halts cleanly but produces > 24576
    bytes. Same shape as `Homestead.Spec.CreateStep.IsCreateDeposit
    Revert` (push 0, no state merge, gas consumed); distinguished by
    the size-violation pre-condition.

    Inputs match `IsCreateDepositRevert` for one-to-one comparison. -/
def IsCreateCodeSizeRevertStep (parent subEvm : Evm)
                                (gasLeft : Nat) (mem : Memory)
                                (s : Stack) (pc : Nat) (parent' : Evm) :
    Prop :=
  ¬ subEvm.reverted ∧
  subEvm.halted ∧
  subEvm.output.size > maxCodeSize ∧
  s.length < stackLimit ∧
  parent' = { parent with
    gasLeft     := gasLeft,
    memory      := mem,
    stack       := (0 : Evm.U256) :: s,
    returnData  := Evm.Bytes.empty,
    pc          := pc + 1 }

/-! ## Structural facts -/

/-- An init code that produces no output trivially passes the cap. -/
theorem empty_output_allowed : IsCodeSizeAllowed Evm.Bytes.empty := by
  -- `Bytes.empty.size = 0 ≤ 24576`
  show 0 ≤ maxCodeSize
  simp [maxCodeSize, Evm.SpuriousDragon.Vm.Gas.maxCodeSize]

/-! ## Fork-conditional value (iff form)

    EIP-170 enforces a hard cap on deployed code size starting at
    Spurious Dragon. Pre-SD there is no cap. Stated as one iff:

      `codeAcceptedAt f (maxCodeSize + 1) = false  ↔  f ≥ SD`. -/

def codeAcceptedAt (f : Evm.Fork) (codeLen : Nat) : Bool :=
  if f.atLeast .spuriousDragon then decide (codeLen ≤ maxCodeSize) else true

theorem cap_active_iff_spurious_dragon (f : Evm.Fork) :
    codeAcceptedAt f (maxCodeSize + 1) = false ↔ f.atLeast .spuriousDragon := by
  unfold codeAcceptedAt
  cases f <;> decide

/-- Adding bytes can only *break* the cap, never fix it. -/
theorem cap_monotone (a b : Evm.Bytes) (h : IsCodeSizeAllowed (a ++ b)) :
    IsCodeSizeAllowed a := by
  unfold IsCodeSizeAllowed at h ⊢
  -- `|a| ≤ |a ++ b|` follows from `ByteArray.size_append`.
  have hsize : a.size ≤ (a ++ b).size := by
    simp [ByteArray.size_append, Nat.le_add_right]
  exact Nat.le_trans hsize h

/-! ## Notes

    - At Constantinople, EIP-1014 (CREATE2) introduces a parallel
      check at the same spot. The relation reused there is exactly
      this one — the cap is the same constant, the failure shape is
      the same. Constantinople's spec module re-imports
      `IsCreateCodeSizeRevertStep` rather than redeclaring it.

    - At Shanghai (EIP-3860) an analogous cap on *init code length*
      (vs deployed code length) lands. That's a different spec
      relation (`Evm.Shanghai.Spec.InitcodeCap`), different
      constant, different failure point — not a redefinition of
      this one.

    - The combined SD post-merge possibilities for a successfully-
      halted init-code frame are now three:
        1. `IsCreateDepositRevert`  (Homestead: deposit-gas)
        2. `IsCreateCodeSizeRevertStep` (this file: size-cap)
        3. `IsCreateDepositOk`      (Homestead: happy path)
      Refinement obligation must show the impl's `if` cascade
      picks the right one for each input. -/

end Evm.SpuriousDragon.Spec
