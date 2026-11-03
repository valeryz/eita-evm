/-
  Evm.SpuriousDragon.Spec.SweepEmpty — EIP-158/161 end-of-tx empty
  account pruning.

  EELS reference: `forks/spurious_dragon/fork.py::process_transaction`
  (the call to `destroy_empty_account_set` at the end of the tx) and
  `state_tracker.py::destroy_empty_account` (the per-address worker).

  EIP-158 specified empty-account pruning; EIP-161 (also in SD)
  generalised it to the touched-set. The combined SD rule:

      after processTransaction completes its main body:
        for each addr ∈ touched:
          if addr exists in state AND state[addr].isEmpty:
            delete addr  (account row AND any leftover storage rows)

  The implementation lives at `Evm.SpuriousDragon.sweepEmptyAccounts`
  (`SpuriousDragon/Fork.lean`). It folds over the touched list in
  order, applying the predicate-based delete at each step.

  Emptiness is exactly EELS `account_is_empty`:
  `nonce = 0 ∧ balance = 0 ∧ code = []`. STORAGE IS IRRELEVANT — an
  empty-with-storage touched account is deleted (and its storage
  discarded), matching mainnet (0xd29dfe5a at block 4457731). A
  reverted-frame touch is kept off the sweep by revert-scoping the
  touched set (`SpuriousDragon/Vm/Effect.lean`), not by a storage guard.
  See the comment in `SpuriousDragon/Fork.lean::sweepEmptyAccounts`.
-/

import Evm.Frontier.Vm
import Evm.SpuriousDragon.Fork

namespace Evm.SpuriousDragon.Spec

open Evm.Frontier (State Account)

/-! ## Predicate: an account is sweep-deletable

    Two conjuncts, both of which must hold against the post-tx
    state for the address to be deleted (EELS `account_is_empty`;
    storage is irrelevant to emptiness). -/

/-- The address exists in `state` and the account is empty. -/
def IsSweepable (state : State) (addr : Evm.Address) : Prop :=
  state.accountExists addr ∧
  (state.getAccount addr).isEmpty

/-! ## IsSweepEmptyStep — the end-of-tx folding relation

    Inputs:
      * `pre` — the state immediately after the main tx body
        (including coinbase credit, selfDestruct pruning).
      * `touched` — the per-tx touched-set, in the order populated
        by CALL/CREATE/SELFDESTRUCT.
      * `post` — the state after the sweep.

    The relation says: `post` is obtained from `pre` by *successively*
    deleting every sweepable touched account, in `touched`-list
    order. The order doesn't matter for the final state (deletion of
    one address never makes another sweepable — sweepability looks
    only at one address's own row + storage), but we state the
    relation as the fold to match the implementation. -/

/-- One step of the sweep. -/
def IsSweepOneStep (state : State) (addr : Evm.Address) (state' : State) :
    Prop :=
  state' =
    (if state.accountExists addr ∧
        (state.getAccount addr).isEmpty
     then state.deleteAccount addr
     else state)

/-- The whole sweep: walk the touched list, applying `IsSweepOneStep`
    at each step. Stated as an inductive proposition over the list
    structure. -/
inductive IsSweepEmptyStep : State → List Evm.Address → State → Prop where
  | nil  (state : State) : IsSweepEmptyStep state [] state
  | cons (state mid post : State) (a : Evm.Address) (rest : List Evm.Address)
         (hStep : IsSweepOneStep state a mid)
         (hRest : IsSweepEmptyStep mid rest post) :
         IsSweepEmptyStep state (a :: rest) post

/-! ## Equivalence with the implementation

    The implementation `sweepEmptyAccounts` is a left fold over the
    touched list. The spec relation `IsSweepEmptyStep` is the
    relational version of the same fold. -/

/-- The implementation respects the relation. -/
theorem sweepEmptyAccounts_sound (state : State) (touched : List Evm.Address) :
    IsSweepEmptyStep state touched
      (Evm.SpuriousDragon.sweepEmptyAccounts state touched) := by
  -- Induct on `touched`. The implementation's `foldl` step matches
  -- the `cons` constructor's `hStep`; the IH closes the tail.
  induction touched generalizing state with
  | nil =>
    unfold Evm.SpuriousDragon.sweepEmptyAccounts
    simp
    exact .nil _
  | cons a rest ih =>
    unfold Evm.SpuriousDragon.sweepEmptyAccounts
    simp only [List.foldl_cons]
    -- The fold's step on `a` produces `mid`:
    let mid :=
      if state.accountExists a ∧ (state.getAccount a).isEmpty
      then state.deleteAccount a else state
    have hStep : IsSweepOneStep state a mid := by
      unfold IsSweepOneStep
      rfl
    -- The remaining fold over `rest` from `mid` is exactly
    -- `sweepEmptyAccounts mid rest`, which IH gives us.
    have hRest :
        IsSweepEmptyStep mid rest
          (Evm.SpuriousDragon.sweepEmptyAccounts mid rest) := ih mid
    -- Now the goal: IsSweepEmptyStep state (a :: rest) <fold result>.
    -- The fold result equals `sweepEmptyAccounts mid rest`.
    have hFoldEq :
        rest.foldl (fun st addr =>
          let acc := st.getAccount addr
          if st.accountExists addr ∧ acc.isEmpty then
            st.deleteAccount addr
          else st) mid
        = Evm.SpuriousDragon.sweepEmptyAccounts mid rest := by
      unfold Evm.SpuriousDragon.sweepEmptyAccounts
      rfl
    rw [hFoldEq]
    exact .cons state mid _ a rest hStep hRest

/-! ## Notes

    - The fold order doesn't affect the final state (each step's
      sweepability test is on `addr` only; deletion of `addr` can't
      change the sweepability test for any *other* address). A
      stronger statement: `IsSweepEmptyStep` is well-defined on
      sets, not just lists. We keep the list ordering here to make
      `sweepEmptyAccounts_sound` syntactically straightforward.

    - Emptiness is EELS `account_is_empty` exactly: storage plays no
      part. An earlier `state.storage.all ...` survivor guard kept
      empty-with-storage touched accounts alive; that was wrong (it
      diverged from mainnet at block 4457731, 0xd29dfe5a, the post-#37
      4.5M state-root mismatch). The reverted-frame touch it was
      meant to handle is excluded earlier by revert-scoping the
      touched set, not at the sweep.

    - Pre-EIP-161 forks (Frontier, Homestead, TW): the touched set
      is always empty in `processTransaction`, so this relation is
      always `state' = state` — i.e., the sweep is a no-op without
      having to special-case the call site.

    - Cancun's EIP-6780 modifies a related sweep (only for
      `createdAccounts ∩ selfDestructSet`); that's an orthogonal
      relation in `Evm.Cancun.Spec.Selfdestruct`. -/

end Evm.SpuriousDragon.Spec
