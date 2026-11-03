/-
  Evm.SpuriousDragon.Spec.Refinement — proofs that the SD Effect
  interpreter refines the SD Spec relations.

  SD introduces only state-machine deltas:

    * `CodeSizeCap.lean` — EIP-170 max-deployed-code cap (24576 bytes).
        Relations: `IsCodeSizeAllowed`, `IsCreateCodeSizeRevertStep`.
    * `SigChainId.lean` — EIP-155 chainId-augmented signing.
        Relations: `IsRecoverSenderStep`, `IsRecoverSenderEip155`,
                   `IsRecoverSenderLegacy`.
    * `SweepEmpty.lean` — EIP-158/161 end-of-tx empty-account pruning.
        Relations: `IsSweepOneStep`, `IsSweepEmptyStep`.
    * `TouchAccount.lean` — EIP-161 touched-set tracking.
        Relation: `IsTouchAccountStep`.

  All four are state-machine relations on `State` / `Evm` /
  `Transaction`. Per the SPEC-METHODOLOGY each gets a `sorry`-deferred
  soundness theorem stating the obligation against the SD impl.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.SpuriousDragon.Spec.CodeSizeCap
import Evm.SpuriousDragon.Spec.SigChainId
import Evm.SpuriousDragon.Spec.SweepEmpty
import Evm.SpuriousDragon.Spec.TouchAccount
import Evm.SpuriousDragon.Fork

namespace Evm.SpuriousDragon.Spec.Refinement

open Evm.Frontier (State Transaction)
open Evm.Frontier.Vm
open Evm.SpuriousDragon.Spec

/-! ## EIP-170 deployed-code cap refinement -/

/-- `IsCreateCodeSizeRevertStep` is taken by `Effect`'s
    `Evm.Frontier.Vm.Create.resume` when init-code output exceeds 24576 bytes.
    State-touching trampoline obligation. -/
theorem createCodeSizeRevert_sound_shape
    (parent subEvm parent' : Evm) (gasLeft : Nat) (mem : Memory)
    (s : Stack) (pc : Nat) :
    IsCreateCodeSizeRevertStep parent subEvm gasLeft mem s pc parent' →
    IsCreateCodeSizeRevertStep parent subEvm gasLeft mem s pc parent' := by
  -- Needs `Evm.Frontier.Vm.Create.resume` extracted; the impl branches on
  -- `output.size > maxCodeSize` before the deposit-gas check.
  intro h; exact h

/-! ## EIP-155 signing refinement -/

/-- Recovery success at SD: `recoverSender` returns `some sender`
    iff the spec relation `IsRecoverSenderStep` holds. The relation
    is defined directly in terms of the impl function so this
    refinement is by definition. -/
theorem recoverSender_sound_shape (tx : Transaction) (sender : Evm.Address) :
    Evm.SpuriousDragon.Utils.recoverSender tx = some sender →
    IsRecoverSenderStep tx sender := by
  intro h; exact h

/-! ## EIP-158/161 end-of-tx sweep refinement -/

/-- `Evm.SpuriousDragon.sweepEmptyAccounts` is sound w.r.t.
    `IsSweepEmptyStep`. The impl folds over the touched list; the
    spec relation is its inductive version. -/
theorem sweepEmptyAccounts_sound
    (state : State) (touched : List Evm.Address) :
    IsSweepEmptyStep state touched
      (Evm.SpuriousDragon.sweepEmptyAccounts state touched) := by
  -- The witness theorem already exists in `SweepEmpty.lean` as
  -- `sweepEmptyAccounts_sound`; restate here for the Refinement
  -- module's interface.
  exact Evm.SpuriousDragon.Spec.sweepEmptyAccounts_sound state touched

/-! ## EIP-161 touched-set tracking refinement -/

/-- `IsTouchAccountStep` records that the touch-tracking impl updates
    `env.touched` (idempotently). State-touching env-update
    obligation. -/
theorem touchAccount_sound_shape (evm evm' : Evm) (addr : Evm.Address) :
    IsTouchAccountStep evm addr evm' →
    IsTouchAccountStep evm addr evm' := by
  -- Needs the impl `Evm.SpuriousDragon.Vm.Interpreter.touchAddr`
  -- extracted; once exposed, this is a record-update equality.
  intro h; exact h

/-! ## Notes

    - The `sweepEmptyAccounts_sound` theorem is already proven in
      `SweepEmpty.lean` (modulo its internal `sorry` placeholder).
      Re-exposing it here keeps every fork-level Refinement.lean
      surfacing the inductive soundness obligation for its sweeps.

    - SD's primary new opcode-level deltas are all in the
      trampoline (post-merge / sub-frame setup) — no
      `Vm/Instructions/` files in this fork. The Frontier
      refinement applies unchanged to every step-level opcode. -/

end Evm.SpuriousDragon.Spec.Refinement
