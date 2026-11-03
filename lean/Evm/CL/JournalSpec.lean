/-! # CL/JournalSpec — provably-correct storage journal & revert (#236 / GH #15)

The replay's per-frame revert engine (`cb-sstore` journals `(addr, slot, old)`,
`revert-journal-to` replays it backward) is hand-written, unverified CL — Tier A
in `docs/vericoding-host-layer.md`. Its bug class has now bitten THREE times:
#256 (apply-tx revert order, block 1,936,837), #264 (CREATE deposit rollback),
and the state-root drift at block 4,085,884 (a failed/OOG `addHashes` tx whose
`hashes`-array SSTORE we kept and mainnet reverted — contract 0xfb4ebcf2, slot
0x1cf6a0c3, [[project_stateroot_4m_pin]]).

This module models the storage journal the same way `Evm.CL.Arena` models the
call-frame arena: ONE term, with the structural property a correct revert MUST
satisfy proved, and the buggy variant proved WRONG — so the bug is ruled out by
construction, not by audit.

The discipline: every SSTORE that changes a slot journals the slot's CURRENT
value (the "old" value, possibly 0 for a fresh slot) BEFORE writing. Then
reverting a frame's journal restores the pre-frame storage EXACTLY — including
fresh slots (old = 0 ⇒ restored to 0). The bug — a write that survives a failed
frame — is exactly "an entry not journaled / not reverted", which `dropped_entry_is_wrong`
shows produces a storage that disagrees with the spec.
-/

namespace Evm.CL.JournalSpec

/-- Storage as a total map (the world's `(addr,slot) → value`). `Nat` keys/values
    abstract `Address×U256 → U256`; the journal/revert argument is structural and
    does not depend on the bit-width. Total ⇒ a "fresh" slot reads 0. -/
abbrev Key : Type := Nat
abbrev Val : Type := Nat
abbrev Storage : Type := Key → Val

/-- Point write — the SSTORE effect. -/
def store (s : Storage) (k : Key) (v : Val) : Storage :=
  fun x => if x = k then v else s x

@[simp] theorem store_get_eq (s : Storage) (k : Key) (v : Val) : store s k v k = v := by
  simp [store]

/-- Restoring a slot to its own current value is a no-op. (Fresh slot: v = 0.) -/
theorem store_self (s : Storage) (k : Key) : store s k (s k) = s := by
  funext x; simp [store]; intro h; subst h; rfl

/-- An outer write to the same key shadows an inner one. -/
theorem store_store (s : Storage) (k : Key) (v w : Val) :
    store (store s k v) k w = store s k w := by
  funext x; by_cases h : x = k <;> simp [store, h]

/-- A journal entry records a slot's value AS IT WAS before the write, so a revert
    can restore it. This is exactly what `cb-sstore` pushes (host type 0). -/
structure Entry where
  key : Key
  old : Val

/-- Run a frame's SSTORE sequence, threading the journal. Each step records the
    CURRENT value (`s k`) then writes the new one — the cb-sstore discipline.
    Returns the final storage and the entries this frame appended (chronological;
    head = oldest). -/
def runWrites (s : Storage) : List (Key × Val) → Storage × List Entry
  | []           => (s, [])
  | (k, v) :: ws =>
      let (s', es) := runWrites (store s k v) ws
      (s', ⟨k, s k⟩ :: es)

/-- Revert: replay the frame's entries, restoring each slot's recorded `old`
    value. `foldr` restores the HEAD (oldest write's old value) LAST, so if a slot
    was written twice in the frame its earliest pre-frame value wins — exactly
    `revert-journal-to`'s reverse replay down to the frame snapshot. -/
def undo (s : Storage) (es : List Entry) : Storage :=
  es.foldr (fun e st => store st e.key e.old) s

/-- **Revert correctness.** For ANY sequence of writes a frame makes, reverting
    its journal restores the pre-frame storage EXACTLY — fresh slots included.
    A failed/OOG frame therefore cannot leave a stray SSTORE: the bug at block
    4,085,884 is unrepresentable in code that satisfies this refinement. -/
theorem undo_runWrites (s : Storage) (ws : List (Key × Val)) :
    undo (runWrites s ws).1 (runWrites s ws).2 = s := by
  induction ws generalizing s with
  | nil => rfl
  | cons kv ws ih =>
      obtain ⟨k, v⟩ := kv
      have h := ih (store s k v)
      simp only [runWrites, undo, List.foldr] at h ⊢
      rw [h, store_store, store_self]

/-- **The bug is real.** A revert that DROPS an entry (here, fails to record/undo
    a write — precisely what happened to slot 0x1cf6a0c3) leaves a storage that
    DISAGREES with the spec: the fresh slot keeps its value instead of returning
    to 0. So "every changed slot is journaled" is forced, not optional. -/
def undoBuggy (s : Storage) (es : List Entry) : Storage :=
  es.tail.foldr (fun e st => store st e.key e.old) s   -- drops the first entry

theorem dropped_entry_is_wrong :
    ∃ (s : Storage) (ws : List (Key × Val)),
      undoBuggy (runWrites s ws).1 (runWrites s ws).2 ≠ s := by
  -- Witness: empty storage (slot 0 fresh = 0), one write of value 5 to slot 0.
  refine ⟨(fun _ => 0), [(0, 5)], ?_⟩
  -- runWrites writes 5; undoBuggy drops the lone entry ⇒ slot 0 stays 5 ≠ 0.
  intro h
  have := congrFun h 0
  simp [runWrites, undoBuggy, store] at this

end Evm.CL.JournalSpec
