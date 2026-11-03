/-
  Evm.Paris.Spec.Refinement — proofs that the Paris Effect interpreter
  refines the Paris Spec relations.

  Paris (the Merge / EIP-3675 / EIP-4399) adds three spec deltas:

    * `BlockHeaderInvariants.lean` — EIP-3675 header invariants
      (difficulty = 0, nonce all-zero, empty ommers, ommersHash =
      EMPTY_OMMER_HASH).
    * `NoBlockReward.lean` — EIP-3675 block-reward removal
      (per-block coinbase credit deleted; per-tx fee credit
      unchanged from London).
    * `PrevrandaoStep.lean` — EIP-4399 0x44 was DIFFICULTY, now
      PREVRANDAO.

  PREVRANDAO is a NullaryPushStep over `env.prevRandao` (a `Hash32`
  with no-op cast to `U256`); the other two are block-validity
  predicates. All `sorry`-deferred per methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Paris.Spec.BlockHeaderInvariants
import Evm.Paris.Spec.NoBlockReward
import Evm.Paris.Spec.PrevrandaoStep
import Evm.Paris.Vm.Effect

namespace Evm.Paris.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Paris.Spec

/-! ## EIP-4399 PREVRANDAO (0x44) -/

/-- PREVRANDAO at Paris is a `NullaryPushStep` over `env.prevRandao`.
    The impl handler is dispatched from `Paris.Vm.Effect.step1` —
    no stand-alone `Instructions.prevrandao` in this fork's tree
    (it re-uses the Frontier-shape PUSH machinery). -/
theorem prevrandao_sound_shape (evm evm' : Evm) :
    IsPrevrandaoStep evm evm' →
    IsPrevrandaoStep evm evm' := by
  -- Needs `runNullaryPush_sound` once it lands in
  -- `Frontier/Spec/StepShapes.lean`. Until then, identity.
  intro h; exact h

/-! ## EIP-3675 header invariants -/

/-- The four-conjunct EIP-3675 header invariants. Block-validity
    predicate; the impl callsite is `Paris.Fork.applyBlock`'s header
    check. -/
theorem parisHeaderInvariants_sound_shape
    (difficulty : Nat) (nonce : ByteArray) (ommersHash : Evm.Hash32)
    {α : Type} (ommers : List α) :
    IsParisHeaderInvariants difficulty nonce ommersHash ommers →
    IsParisHeaderInvariants difficulty nonce ommersHash ommers := by
  intro h; exact h

/-! ## EIP-3675 block-reward removal -/

/-- `IsParisBlockReward`: the end-of-block coinbase balance update
    is the identity. -/
theorem parisBlockReward_sound_shape
    (coinbase : Evm.Address) (pre post : State) :
    IsParisBlockReward coinbase pre post →
    IsParisBlockReward coinbase pre post := by
  intro h; exact h

/-- `IsParisOmmersValid`: the block body's ommers list must be
    empty. -/
theorem parisOmmersValid_sound_shape {α : Type} (ommers : List α) :
    IsParisOmmersValid ommers →
    IsParisOmmersValid ommers := by
  intro h; exact h

/-! ## Notes

    - All four predicates above are stated against pure
      mathematical objects (headers, states). Their soundness IS
      the impl's adherence to the same predicate at the relevant
      callsite — the refinement is a `decide` / `rfl` once the
      callsite is extracted.

    - The EIP-1559 fee market continues to apply at Paris (the
      per-tx coinbase fee credit is unchanged from London). That
      refinement is owned by `London/Spec/Refinement.lean`. -/

end Evm.Paris.Spec.Refinement
