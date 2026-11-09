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
import Evm.Paris.Fork
import Evm.Frontier.Vm.Block

namespace Evm.Paris.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Paris.Spec

/-! ## EIP-4399 PREVRANDAO (0x44) -/

/-- PREVRANDAO (`Paris.Vm.Effect.prevRandao`, the 0x44 arm) is a nullary push of
    `prev_randao` at `GAS_BASE`. EELS `forks/paris/vm/instructions/block.py::prev_randao`
    (168-). -/
theorem prevrandao_sound (evm evm' : Evm) :
    Evm.Paris.Vm.Effect.prevRandao evm = .ok evm' →
    IsPrevrandaoStep evm evm' :=
  Evm.Frontier.Spec.Refinement.nullaryPush_sound Gas.base (fun e => e.env.prevRandao) evm evm'

/-! ## EIP-3675 header invariants -/

/-- The post-Merge block checks (`Paris.checkMergeHeader`, run first by both
    `Paris.applyBlock` and `Paris.applyBlockTyped`, the replay's path) establish the
    four EIP-3675 invariants. EELS `forks/paris/fork.py::state_transition` 159 and
    `validate_header` 330-335. -/
theorem parisHeaderInvariants_sound {α : Type} (header : Evm.Frontier.Header)
    (ommers : List α) :
    _root_.Evm.Paris.checkMergeHeader header ommers = .ok () →
    IsParisHeaderInvariants header.difficulty header.nonce header.ommersHash ommers := by
  intro h
  unfold _root_.Evm.Paris.checkMergeHeader at h
  by_cases h1 : ommers.isEmpty = true
  · by_cases h2 : header.difficulty = 0
    · by_cases h3 : header.ommersHash = _root_.Evm.Paris.EMPTY_OMMER_HASH
      · simp [h1, h2, h3] at h
        split at h
        · simp at h
        · rename_i hn
          simp only [not_or, Decidable.not_not, not_exists, not_and] at hn
          refine ⟨h2, ⟨hn.1, fun i hi => hn.2 i hi⟩, h3, ?_⟩
          simpa [IsParisOmmersBodyValid] using h1
      · simp [h1, h2, h3, bind, Except.bind] at h
    · simp [h1, h2, bind, Except.bind] at h
  · simp [h1, bind, Except.bind] at h

/-! ## EIP-3675 block-reward removal -/

/-- EIP-3675: from Paris (`k ≥ 14`) the block's reward step (`Block.payRewards`) leaves the
    coinbase's balance as it was. EELS `forks/paris/fork.py::apply_body` has no
    `pay_rewards` call (London's `fork.py` 683 is the last). -/
theorem parisBlockReward_sound (k : Nat) (coinbase : Evm.Address) (number : Nat)
    (ommers : List (Evm.Address × Nat)) (pre post : State) :
    Evm.Frontier.Vm.Block.payRewards k pre coinbase number ommers = post → k ≥ 14 →
    IsParisBlockReward coinbase pre post := by
  intro h hk
  unfold Evm.Frontier.Vm.Block.payRewards at h
  rw [if_pos hk] at h
  subst h; rfl

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
