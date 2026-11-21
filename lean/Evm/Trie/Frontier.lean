import Evm.Trie.Stack
import Evm.Frontier.StateRoot

/-! # Trie.Frontier — subtrie references at a fixed depth, and how a block's writes update them

The per-block state root (`docs/state-snapshot-format.md`, v2: "The frontier") does not rebuild
the trie. It keeps, for every trie (the account trie and each large storage trie), the
**frontier**: the reference to every subtrie at nibble depth `d`. A block's writes dirty a
few of those subtries; the root worker rebuilds only them, from the contiguous leaves the
hashed-order snapshot holds under each dirty prefix, and recomputes the dense branches above
them up to the root.

This file is that algorithm's specification, written against `Evm.Trie.patricialise`:

* **F0, definitions.** `prefixed p items` (the leaves under prefix `p`, `p` stripped),
  `subRef p items` (the reference a parent branch holds for that subtrie), `DenseAbove d
  items` (every prefix shorter than `d` that has keys under it is a branch with two or more
  children), `refAt`/`assemble` (the dense branches over a frontier function), `FrontierOK`.
* **F1, locality** (`prefixed_update`, `subRef_update`): writes to keys outside prefix `p`
  leave the subtrie under `p` unchanged. A congruence: it never unfolds `patricialise`.
* **F2, update** (`frontierOK_update`, `frontierOK_step`, `refAt_congr`,
  `refAt_step_clean`): a frontier that was right before the block, recomputed on the dirty
  prefixes and kept on the clean ones, is right after it; a dense branch with no dirty prefix
  under it keeps its reference.
* **L2, decomposition** (`patricialise_assemble`): under `DenseAbove d`, the trie is the
  dense branches over its depth-`d` subtrie references. **Stated, `sorry`.**
* **L1′, emission** (`buildFrontier`, `build_emits_frontier`): the depth-`d` stack builds of
  the sorted leaves' prefix runs are the frontier. Completeness is proved
  (`buildFrontier_complete`); soundness is **stated, `sorry`**.
* `Trie1.root_step`: one trie's incremental root after a block equals the root of its
  post-state leaves, **from L2 and F2** (no `sorry` of its own; it inherits L2's).
* **L4, two levels** (`stateRoot_two_levels`): the world-state root is the account trie
  over leaves carrying their storage tries' roots, in any order of distinct hashed keys.
  **Stated, `sorry`.**
* **R, the refinement gap** (`layered_frontier_root_eq`): the worker's two-level step,
  over the leaves the layered store composes (`Persist.Layered.viewRange_slot`/`_acct`, F3),
  yields the fork's `stateRootBytes` of the composed state. **Stated, `sorry`.**

Why L2, L1′ and L4 are not proved: `patricialise` and `nodeRef` are `partial def`s, opaque
to the kernel (the blocker `Trie/Stack.lean` records for its three lemmas); L4 also needs
the order independence of `rootBytes` over distinct keys. R assembles F2, F3, L2 and L4, and
closes with them. At run time each unproved step has a check: the header root every block
(or every catch-up interval, bisected on a mismatch), `DenseAbove` on every recomputed dense
branch, 32-byte references, the compaction's in-pass root with its entry-by-entry frontier
comparison, and the resume self-check.

The Lisp root worker (specified, not yet written) is to mirror these definitions one to one
(`frontier-subref` = `subRef`, the dense-level loop = `refAt`, the per-bucket rebuild =
`buildFrontier`'s runs), as `src/state/root.lisp` mirrors `Trie.Stack`, checked by a
`tests/frontier.lisp` against `eita.mpt:trie-root`. -/

namespace Evm.Trie.Frontier
open Evm Evm.Trie Evm.Trie.Stack

/-- The leaves of one trie: nibble keys and their values, `patricialise`'s input. -/
abbrev Items := List (List UInt8 × Bytes)

/-! ## F0 — definitions -/

/-- The leaves under prefix `p`, in their order, with `p` stripped from their keys. -/
def prefixed (p : List UInt8) (items : Items) : Items :=
  items.filterMap fun kv => if p.isPrefixOf kv.1 then some (kv.1.drop p.length, kv.2) else none

/-- The reference a parent branch holds for the subtrie under `p`: `emptyItem` when no key has
    the prefix (thirty-two zero bytes in the frontier files), else `nodeRef` of the subtrie. -/
def subRef (p : List UInt8) (items : Items) : Rlp.Item :=
  match prefixed p items with
  | [] => emptyItem
  | ys => nodeRef (patricialise ys)

/-- Every prefix shorter than `d` that has keys under it is a branch with two or more children:
    for every key and every level `j < d`, another key shares its first `j` nibbles and differs
    in nibble `j`. Checked at run time on every dense branch the worker recomputes. -/
def DenseAbove (d : Nat) (items : Items) : Prop :=
  ∀ kv ∈ items, ∀ j < d, ∃ kw ∈ items, kw.1.take j = kv.1.take j ∧ nib kw.1 j ≠ nib kv.1 j

instance (d : Nat) (items : Items) : Decidable (DenseAbove d items) := by
  unfold DenseAbove; infer_instance

/-- An absent child (`emptyItem`). -/
def isEmptyRef : Rlp.Item → Bool
  | .bytes b => b.size == 0
  | .list _ => false

/-- The reference at prefix `q`, `n` levels above the frontier `F`: `F q` at the frontier;
    above it, the branch over its 16 children, referenced, or `emptyItem` when every child is
    absent. -/
def refAt (F : List UInt8 → Rlp.Item) : Nat → List UInt8 → Rlp.Item
  | 0, q => F q
  | n + 1, q =>
    let cs := (List.range 16).map fun i => refAt F n (q ++ [UInt8.ofNat i])
    if cs.all isEmptyRef then emptyItem else nodeRef (.list (cs ++ [emptyItem]))

/-- The root node of a trie with frontier depth `d ≥ 1`: the branch over the references one
    level down (the root is hashed whole, never referenced). -/
def assemble (d : Nat) (F : List UInt8 → Rlp.Item) : Rlp.Item :=
  .list (((List.range 16).map fun i => refAt F (d - 1) [UInt8.ofNat i]) ++ [emptyItem])

/-- `F` is the depth-`d` frontier of `items`. -/
def FrontierOK (d : Nat) (F : List UInt8 → Rlp.Item) (items : Items) : Prop :=
  ∀ p : List UInt8, p.length = d → F p = subRef p items

/-- A block's writes to one trie: per key its post value, `none` when the key leaves the trie
    (a slot set to 0, an account removed). -/
abbrev Writes := List (List UInt8 × Option Bytes)

/-- Key `k` is written. -/
def written (D : Writes) (k : List UInt8) : Bool := D.any (·.1 == k)

/-- The leaves after the writes: the unwritten leaves in their order, then the written keys
    that stay in the trie. -/
def update (items : Items) (D : Writes) : Items :=
  items.filter (fun kv => !written D kv.1) ++ D.filterMap fun w => w.2.map (w.1, ·)

/-- Prefix `p` is dirty: a written key lies under it. -/
def dirty (D : Writes) (p : List UInt8) : Bool := D.any fun w => p.isPrefixOf w.1

/-! ## F1 — locality -/

theorem prefixed_append (p : List UInt8) (a b : Items) :
    prefixed p (a ++ b) = prefixed p a ++ prefixed p b := by
  simp [prefixed, List.filterMap_append]

/-- No leaf of `xs` is under `p`: nothing is prefixed. -/
theorem prefixed_eq_nil {p : List UInt8} {xs : Items} (h : ∀ kv ∈ xs, p.isPrefixOf kv.1 = false) :
    prefixed p xs = [] := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    simp only [prefixed, List.filterMap_cons] at ih ⊢
    rw [h kv List.mem_cons_self]
    exact ih fun kv' hm => h kv' (List.mem_cons_of_mem _ hm)

/-- Removing leaves that are not under `p` does not change what is under `p`. -/
theorem prefixed_filter {p : List UInt8} {xs : Items} {f : List UInt8 × Bytes → Bool}
    (h : ∀ kv ∈ xs, f kv = false → p.isPrefixOf kv.1 = false) :
    prefixed p (xs.filter f) = prefixed p xs := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    have ih' := ih fun kv' hm => h kv' (List.mem_cons_of_mem _ hm)
    by_cases hf : f kv = true
    · simp only [List.filter_cons, hf, ite_true, prefixed, List.filterMap_cons] at ih' ⊢
      rw [ih']
    · have hf' : f kv = false := by simpa using hf
      have hp := h kv List.mem_cons_self hf'
      simp only [List.filter_cons, hf', prefixed, List.filterMap_cons, hp] at ih' ⊢
      simpa using ih'

/-- **F1.** A block's writes outside prefix `p` leave the leaves under `p` as they were. -/
theorem prefixed_update (p : List UInt8) (items : Items) (D : Writes) (hclean : dirty D p = false) :
    prefixed p (update items D) = prefixed p items := by
  have hD : ∀ w ∈ D, p.isPrefixOf w.1 = false := by
    intro w hw
    have := hclean
    simp only [dirty, List.any_eq_false] at this
    cases h : p.isPrefixOf w.1
    · rfl
    · exact absurd h (this w hw)
  rw [update, prefixed_append]
  have h2 : prefixed p (D.filterMap fun w => w.2.map (w.1, ·)) = [] := by
    apply prefixed_eq_nil
    intro kv hkv
    obtain ⟨w, hw, hwkv⟩ := List.mem_filterMap.1 hkv
    cases hw2 : w.2 with
    | none => simp [hw2] at hwkv
    | some v =>
      simp only [hw2, Option.map_some, Option.some.injEq] at hwkv
      subst hwkv
      exact hD w hw
  rw [h2, List.append_nil]
  apply prefixed_filter
  intro kv _ hf
  have hw : written D kv.1 = true := by simpa using hf
  simp only [written, List.any_eq_true, beq_iff_eq] at hw
  obtain ⟨w, hwD, hwk⟩ := hw
  rw [← hwk]; exact hD w hwD

/-- **F1.** The reference to a clean subtrie is unchanged. -/
theorem subRef_update (p : List UInt8) (items : Items) (D : Writes) (hclean : dirty D p = false) :
    subRef p (update items D) = subRef p items := by
  unfold subRef; rw [prefixed_update p items D hclean]

/-! ## F2 — the frontier update -/

/-- **F2.** A right frontier, recomputed over the post-state on the dirty prefixes and kept on
    the clean ones, is the post-state's frontier. -/
theorem frontierOK_update {d : Nat} {F F' : List UInt8 → Rlp.Item} {items : Items} {D : Writes}
    (hF : FrontierOK d F items)
    (hclean : ∀ p, p.length = d → dirty D p = false → F' p = F p)
    (hdirty : ∀ p, p.length = d → dirty D p = true → F' p = subRef p (update items D)) :
    FrontierOK d F' (update items D) := by
  intro p hp
  cases hd : dirty D p
  · rw [hclean p hp hd, hF p hp, subRef_update p items D hd]
  · exact hdirty p hp hd

/-- The worker's step on one frontier: the dirty prefixes rebuilt from the post-state's leaves,
    the clean ones kept. -/
def stepFrontier (F : List UInt8 → Rlp.Item) (post : Items) (D : Writes) : List UInt8 → Rlp.Item :=
  fun p => if dirty D p then subRef p post else F p

theorem frontierOK_step {d : Nat} {F : List UInt8 → Rlp.Item} {items : Items} {D : Writes}
    (hF : FrontierOK d F items) : FrontierOK d (stepFrontier F (update items D) D) (update items D) :=
  frontierOK_update hF (fun p _ h => by simp [stepFrontier, h]) (fun p _ h => by simp [stepFrontier, h])

/-- A dense reference depends only on the frontier entries under it: the worker recomputes only
    the dense branches above changed entries. -/
theorem refAt_congr {F F' : List UInt8 → Rlp.Item} :
    ∀ (n : Nat) (q : List UInt8), (∀ p, q <+: p → p.length = q.length + n → F' p = F p) →
      refAt F' n q = refAt F n q
  | 0, q, h => h q (List.prefix_refl q) rfl
  | n + 1, q, h => by
    have hc : ∀ i, refAt F' n (q ++ [UInt8.ofNat i]) = refAt F n (q ++ [UInt8.ofNat i]) :=
      fun i => refAt_congr n _ fun p hp hl =>
        h p ((List.prefix_append q _).trans hp) (by simp at hl; omega)
    simp only [refAt, hc]

/-- `assemble` reads the frontier only at depth `d`. -/
theorem assemble_congr {d : Nat} {F F' : List UInt8 → Rlp.Item} (hd : 0 < d)
    (h : ∀ p, p.length = d → F' p = F p) : assemble d F' = assemble d F := by
  unfold assemble
  have hc : ∀ i, refAt F' (d - 1) [UInt8.ofNat i] = refAt F (d - 1) [UInt8.ofNat i] := by
    intro i
    apply refAt_congr
    intro p _ hl
    exact h p (by simp at hl; omega)
  simp only [hc]

/-- A prefix under a clean prefix is clean. -/
theorem dirty_mono {D : Writes} {q p : List UInt8} (hq : dirty D q = false) (hqp : q <+: p) :
    dirty D p = false := by
  simp only [dirty, List.any_eq_false] at hq ⊢
  intro w hw hpw
  have : p <+: w.1 := by simpa using hpw
  exact hq w hw (by simpa using hqp.trans this)

/-- The step keeps every dense reference with no write under it. -/
theorem refAt_step_clean {F : List UInt8 → Rlp.Item} {post : Items} {D : Writes} (n : Nat)
    {q : List UInt8} (hq : dirty D q = false) :
    refAt (stepFrontier F post D) n q = refAt F n q :=
  refAt_congr n q fun p hp _ => by simp [stepFrontier, dirty_mono hq hp]

/-! ## L2 — decomposition (stated) -/

/-- Keys of one length `n`, distinct, every element a nibble. -/
def WellFormed (n : Nat) (items : Items) : Prop :=
  (∀ kv ∈ items, kv.1.length = n ∧ ∀ x ∈ kv.1, x < 16) ∧ (items.map (·.1)).Nodup

/-- **L2.** Under `DenseAbove d`, the trie is the dense branches over its depth-`d` subtrie
    references. `sorry`: `patricialise` is a `partial def` (the total trie spec, L0, comes
    first); it also needs `patricialise`'s independence of the order of distinct keys (its
    buckets are built in reverse). -/
theorem patricialise_assemble (d n : Nat) (items : Items) (hwf : WellFormed n items)
    (hd : 0 < d) (hdn : d ≤ n) (hne : items ≠ []) (hdense : DenseAbove d items) :
    patricialise items = assemble d (fun p => subRef p items) := by
  sorry

/-! ## One trie: the incremental root -/

/-- The root of a trie over nibble keys (`Evm.Trie.rootBytes` after `bytesToNibbles`). -/
def rootN (items : Items) : Bytes :=
  if items.isEmpty then emptyRootBytes
  else Evm.Crypto.keccak256Bytes (Rlp.encode (patricialise items))

/-- One trie as the worker holds it: its frontier depth (`0`: no frontier, rebuilt whole) and
    its frontier. -/
structure Trie1 where
  d : Nat
  F : List UInt8 → Rlp.Item

/-- The worker's root of one trie: the dense levels over the frontier when `DenseAbove` holds
    (checked on the post-state), else the whole rebuild (`d = 0`, or the fallback that re-lays
    the trie at a lower depth). -/
def Trie1.root (t : Trie1) (post : Items) : Bytes :=
  if t.d ≠ 0 ∧ post ≠ [] ∧ DenseAbove t.d post then
    Evm.Crypto.keccak256Bytes (Rlp.encode (assemble t.d t.F))
  else rootN post

/-- One block on one trie: the frontier stepped over the post-state's leaves. -/
def Trie1.step (t : Trie1) (post : Items) (D : Writes) : Trie1 := { t with F := stepFrontier t.F post D }

/-- **The incremental root of one trie** equals the root of its post-state leaves, from a right
    frontier (F2 and L2; it carries L2's `sorry` through `patricialise_assemble`). -/
theorem Trie1.root_step (t : Trie1) (n : Nat) (items : Items) (D : Writes)
    (hF : FrontierOK t.d t.F items) (hwf : WellFormed n (update items D)) (hdn : t.d ≤ n) :
    (t.step (update items D) D).root (update items D) = rootN (update items D) := by
  unfold Trie1.root Trie1.step
  simp only
  split
  · rename_i h
    obtain ⟨hd0, hne, hdense⟩ := h
    have hok := frontierOK_step (D := D) hF
    rw [assemble_congr (F := fun p => subRef p (update items D)) (Nat.pos_of_ne_zero hd0) hok,
      ← patricialise_assemble t.d n _ hwf (Nat.pos_of_ne_zero hd0) hdn hne hdense]
    have : (update items D).isEmpty = false := by
      cases h : update items D with
      | nil => exact absurd h hne
      | cons _ _ => rfl
    simp [rootN, this]
  · rfl

/-! ## L1′ — what the streaming build emits at depth `d` -/

/-- The leaves, in their order, cut into runs of equal first `d` nibbles (in a sorted list
    each prefix's leaves are one contiguous run: one `storage.dat` / `accounts.dat` range). -/
def runs (d : Nat) : Items → List (List UInt8 × Items)
  | [] => []
  | kv :: rest =>
    match runs d rest with
    | (p, r) :: gs =>
      if kv.1.take d = p then (p, kv :: r) :: gs else (kv.1.take d, [kv]) :: (p, r) :: gs
    | [] => [(kv.1.take d, [kv])]

/-- The frontier the converter, a promotion and the compaction's in-pass root emit at depth
    `d`: per run, the depth-`d` stack build of its leaves, referenced. -/
def buildFrontier (d : Nat) (items : Items) : List (List UInt8 × Rlp.Item) :=
  (runs d items).map fun g =>
    (g.1, match build d g.2 with
          | none => emptyItem
          | some node => nodeRef node)

theorem runs_cover (d : Nat) : ∀ (items : Items), ∀ kv ∈ items,
    ∃ g ∈ runs d items, g.1 = kv.1.take d ∧ kv ∈ g.2
  | [], kv, h => by simp at h
  | kw :: rest, kv, h => by
    have ih := runs_cover d rest
    simp only [runs]
    split
    · rename_i p r gs heq
      rw [heq] at ih
      by_cases hk : kw.1.take d = p
      · simp only [hk, ite_true]
        rcases List.mem_cons.1 h with e | hm
        · subst e; exact ⟨(p, kv :: r), List.mem_cons_self, hk.symm, List.mem_cons_self⟩
        · obtain ⟨g, hg, hg1, hg2⟩ := ih kv hm
          rcases List.mem_cons.1 hg with e | hg'
          · subst e; exact ⟨_, List.mem_cons_self, hg1, List.mem_cons_of_mem _ hg2⟩
          · exact ⟨g, List.mem_cons_of_mem _ hg', hg1, hg2⟩
      · simp only [hk, ite_false]
        rcases List.mem_cons.1 h with e | hm
        · subst e; exact ⟨_, List.mem_cons_self, rfl, List.mem_cons_self⟩
        · obtain ⟨g, hg, hg1, hg2⟩ := ih kv hm
          exact ⟨g, List.mem_cons_of_mem _ hg, hg1, hg2⟩
    · rename_i heq
      rw [heq] at ih
      rcases List.mem_cons.1 h with e | hm
      · subst e; exact ⟨_, List.mem_cons_self, rfl, List.mem_cons_self⟩
      · obtain ⟨g, hg, _, _⟩ := ih kv hm; simp at hg

/-- **L1′, completeness** (proved): every depth-`d` prefix with keys under it gets an entry. -/
theorem buildFrontier_complete (d : Nat) (items : Items) (p : List UInt8) (hp : p.length = d)
    (hne : prefixed p items ≠ []) : ∃ e ∈ buildFrontier d items, e.1 = p := by
  obtain ⟨kw, hkw⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨kv, hkv, hkvw⟩ := List.mem_filterMap.1 hkw
  have hpre : p <+: kv.1 := by
    cases h : p.isPrefixOf kv.1
    · simp [h] at hkvw
    · simpa using h
  obtain ⟨g, hg, hg1, _⟩ := runs_cover d items kv hkv
  refine ⟨_, List.mem_map_of_mem hg, ?_⟩
  simp only [hg1]
  rw [← hp]; exact (List.prefix_iff_eq_take.1 hpre).symm

/-- **L1′, soundness.** Over sorted leaves, every emitted entry is the frontier's reference:
    the stack build of a prefix's run at base `d` is the subtrie under that prefix.
    `sorry`: the generalization of `Stack.build_eq_patricialise` (`sorry`, L1) to base `d`. -/
theorem build_emits_frontier (d n : Nat) (items : Items) (h : SortedKeys 0 n items)
    (hnib : ∀ kv ∈ items, ∀ x ∈ kv.1, x < 16) (hdn : d ≤ n) :
    ∀ e ∈ buildFrontier d items, e.2 = subRef e.1 items := by
  sorry

/-! ## L4 — two levels (stated) -/

section TwoLevels
open Evm.Frontier (State Account accountRlp emptyCodeHashBytes)

/-- An account's storage leaves: hashed slot, RLP of the value (`Frontier.storageRootBytes`'s
    items). -/
def storageItems (σ : State) (a : Address) : List (Bytes × Bytes) :=
  σ.storage.filterMap fun ((b, slot), v) =>
    if b = a then
      some (Evm.Crypto.keccak256Bytes (U256.toBytesBE slot), Rlp.encode (.bytes (Rlp.natToBytes v.toNat)))
    else none

/-- An account's code hash, as `Frontier.stateRootBytes` computes it. -/
def codeHashOf (acc : Account) : Bytes :=
  if acc.code.size = 0 then emptyCodeHashBytes else Evm.Crypto.keccak256Bytes acc.code

/-- **L4.** The world-state root is the account trie over leaves that carry their storage
    tries' roots, the leaves of both levels in any order (the worker's hashed order) as long as
    their hashed keys are distinct. `sorry`: needs `rootBytes`'s independence of the order of
    distinct keys, after the total trie spec (L0). -/
theorem stateRoot_two_levels (σ : State) (slots : Address → List (Bytes × Bytes))
    (accts : List (Bytes × Bytes))
    (hslots : ∀ a, (slots a).Perm (storageItems σ a))
    (hslotKeys : ∀ a, ((storageItems σ a).map (·.1)).Nodup)
    (haccts : accts.Perm (σ.accounts.map fun aa =>
      (Evm.Crypto.keccak256Bytes (Address.toBytesBE aa.1),
       accountRlp (Evm.Trie.rootBytes (slots aa.1)) (codeHashOf aa.2) aa.2)))
    (hacctKeys : (accts.map (·.1)).Nodup) :
    Evm.Frontier.stateRootBytes σ = Evm.Trie.rootBytes accts := by
  sorry

end TwoLevels

/-! ## R — the worker's two levels over the layered store (stated: the refinement gap) -/

/-- The root worker's state (`docs/state-snapshot-format.md`, "The frontier"): the account
    trie and every contract's storage trie, by hashed address, and the storage roots
    (`roots.dat`; `emptyRootBytes` for an account without storage). -/
structure Worker where
  acct  : Trie1
  sto   : List UInt8 → Trie1
  roots : List UInt8 → Bytes

/-- The leaves of both levels at a block, as the layered store composes them (each range a
    `Persist.Layered.viewRange`, F3): per hashed address its storage leaves, and the account
    leaves given every account's storage root. -/
structure Leaves where
  slots : List UInt8 → Items
  accts : (List UInt8 → Bytes) → Items

/-- The worker is right at a block: every frontier is its trie's, every root its storage
    trie's. -/
def Worker.OK (W : Worker) (L : Leaves) : Prop :=
  FrontierOK W.acct.d W.acct.F (L.accts W.roots) ∧
  ∀ c, FrontierOK (W.sto c).d (W.sto c).F (L.slots c) ∧ W.roots c = rootN (L.slots c)

/-- One block (or one catch-up interval): the storage tries of the written contracts, then
    their roots, then the account trie over the written accounts and the contracts whose root
    changed (`acctWrites`, the account leaves re-encoded with the new roots); the worker's
    state after it and its root. -/
def Worker.step (W : Worker) (L' : Leaves) (stoWrites : List UInt8 → Writes)
    (acctWrites : Writes) : Worker × Bytes :=
  let sto := fun c => (W.sto c).step (L'.slots c) (stoWrites c)
  let roots := fun c => (sto c).root (L'.slots c)
  let acct := W.acct.step (L'.accts roots) acctWrites
  (⟨acct, sto, roots⟩, acct.root (L'.accts roots))

/-- A nibble-keyed leaf as a byte-keyed one. -/
def unpack (kv : List UInt8 × Bytes) : Bytes × Bytes := (packNibbles kv.1, kv.2)

/-- An address's key in the account trie, as nibbles. -/
def hkey (a : Address) : List UInt8 := bytesToNibbles (Evm.Crypto.keccak256Bytes (Address.toBytesBE a))

/-- **R, the refinement gap.** From a right worker state, a block whose leaves `L'` are the
    layered store's composition after it (every storage trie's and the account trie's leaves
    updated by the block's writes; `acctWrites` names every account whose leaf changed,
    including those whose storage root did) leaves the worker right, and its root is the
    fork's `stateRootBytes` of the composed state `σ'` (whose leaves `L'` holds in hashed
    order). `sorry`: it assembles F2 (`frontierOK_step`), F3 (`Persist.Layered.viewRange_slot`,
    `viewRange_acct`), L2 (through `Trie1.root_step`) and L4 (`stateRoot_two_levels`), and
    closes with them. The Lisp root worker mirrors `Worker.step`; until it is extracted or
    proved, the header root of every block and the compaction's in-pass root are the checks. -/
theorem layered_frontier_root_eq (W : Worker) (L L' : Leaves)
    (stoWrites : List UInt8 → Writes) (acctWrites : Writes) (σ' : Evm.Frontier.State)
    (hW : W.OK L)
    (hsto : ∀ c, L'.slots c = update (L.slots c) (stoWrites c) ∧ WellFormed 64 (L'.slots c) ∧
      (W.sto c).d ≤ 64)
    (hacct : L'.accts (fun c => rootN (L'.slots c)) = update (L.accts W.roots) acctWrites)
    (hacctWf : WellFormed 64 (L'.accts fun c => rootN (L'.slots c))) (hdn : W.acct.d ≤ 64)
    (hσsto : ∀ a, ((L'.slots (hkey a)).map unpack).Perm (storageItems σ' a))
    (hσacct : ((L'.accts fun c => rootN (L'.slots c)).map unpack).Perm
      (σ'.accounts.map fun aa => (Evm.Crypto.keccak256Bytes (Address.toBytesBE aa.1),
        Evm.Frontier.accountRlp (rootN (L'.slots (hkey aa.1))) (codeHashOf aa.2) aa.2))) :
    (W.step L' stoWrites acctWrites).1.OK L' ∧
    (W.step L' stoWrites acctWrites).2 = Evm.Frontier.stateRootBytes σ' := by
  sorry

end Evm.Trie.Frontier
