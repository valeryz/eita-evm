import Mathlib.Logic.Function.Basic

/-! # CL/Journal — proved refinement spec for per-frame revert journaling (#236)

The SBCL replay (`src/evm/`) implements REVERT by appending an
entry to a per-frame *journal* on every world mutation and replaying it
*backwards* if the frame reverts (`revert-journal-to`). The Lean reference
semantics (`Cancun.Vm.Effect.applyMessage`) instead snapshots the pre-frame
world and *discards* the frame's mutations on `reverted=true`. This file proves
the two strategies coincide.

## Why a function-world model (and why it pins the bug we hit)

The world's journaled projection — storage `(addr,slot)→value`, balance
`addr→u256`, nonce `addr→u64`, presence `addr→bool` — is modelled as ONE total
function `World = Key → Value`, with writes as `Function.update`. The crucial
consequence: there is **no "present-with-default" vs "absent" distinction** in
the spec — a slot/account holding the default value (0 storage, 0 balance, 0
nonce) is *identical* to one that is absent, because both are just `Key → Value`
returning the default.

That is precisely the bug #241 found: the executable hashtable distinguished a
present-0 entry from an absent key, so reverting a 0-write left a stray entry.
The fix (`world-storage-set` / the type-9/type-2 revert remhash on 0, emitted
from `HostEmit.lean`) makes the hashtable a CANONICAL representation of this
function — no default-valued entries. So this model is both what we prove the
revert against AND the spec the executable representation must refine.

The per-op inverse theorem (`revert_restores_snapshot`) is proved here. The
FRAME-SCOPING obligation (some substate effects — the EIP-2929 callee warm-up —
belong to the caller's journal segment and SURVIVE a child revert) is a separate
property about *where* entries are appended, stated in `segmentRevert` below; it
is not a consequence of the per-op law and must not be conflated with it. -/

namespace Evm.CL.Journal

/-! ## Legacy storage-only journal types

These 3-parameter types are the in-frame journal-log shape used by
`Evm.CL.MacroSpec` / `Evm.CL.Extract` (the `journal : Journal Addr Val Val`
field of their frame state). The GENERAL, PROVED model is `World` below; these
remain for API compatibility until those consumers migrate. -/
inductive Entry (Addr Slot Value : Type) where
  | sstore (addr : Addr) (slot : Slot) (oldValue : Value)
  deriving DecidableEq, Inhabited

-- `Journal.Journal`: the type is named after its module; callers write `Journal _ _ _`.
set_option linter.dupNamespace false in
abbrev Journal (Addr Slot Value : Type) := List (Entry Addr Slot Value)

/-! ## The general function-world model (#236) -/

namespace World

variable {Key Value : Type}

/-- A journal entry records a key and the value it held *before* the write, so
    the revert direction restores it. Generic over the world's key/value: the
    concrete world instantiates `Key` with a sum of storage/balance/nonce/
    presence keys and `Value` with the corresponding (defaulted) value type. -/
structure Entry (Key Value : Type) where
  key : Key
  old : Value
  deriving Inhabited

/-- A journal is a stack — most-recent at the head, matching the CL
    `journal-push!` / reverse-replay discipline. -/
abbrev Journal (Key Value : Type) := List (Entry Key Value)

-- `World.World`: the type is named after its namespace; callers write `World _ _`.
set_option linter.dupNamespace false in
/-- The world's journaled projection: a total function. `read = w k`,
    `write = Function.update`. "Absent" is just the default value `w k`. -/
abbrev World (Key Value : Type) := Key → Value

variable [DecidableEq Key]

/-- Revert a single entry: restore the recorded old value. -/
@[simp] def applyRevertEntry (w : World Key Value) (e : Entry Key Value) :
    World Key Value :=
  Function.update w e.key e.old

/-- Replay the journal backwards (head = newest, undone first). -/
def revert : Journal Key Value → World Key Value → World Key Value
  | [],        w => w
  | e :: rest, w => revert rest (applyRevertEntry w e)

@[simp] theorem revert_nil (w : World Key Value) : revert [] w = w := rfl
@[simp] theorem revert_cons (e : Entry Key Value) (rest : Journal Key Value)
    (w : World Key Value) :
    revert (e :: rest) w = revert rest (applyRevertEntry w e) := rfl

/-! ## Two update lemmas (proved, not assumed)

These are exactly the facts the old `StorageOps`-based proof lacked because it
had no state extensionality. With a function world, `funext` gives them. -/

/-- Overwriting the same key keeps only the later value. -/
theorem write_write_same (w : World Key Value) (k : Key) (v₁ v₂ : Value) :
    Function.update (Function.update w k v₁) k v₂ = Function.update w k v₂ := by
  funext k'; by_cases h : k' = k <;> simp [Function.update, h]

/-- Writing a key its current value is a no-op (the "old = read" case). -/
theorem write_self (w : World Key Value) (k : Key) :
    Function.update w k (w k) = w := by
  funext k'; by_cases h : k' = k <;> simp [Function.update, h]

/-! ## The snapshot-equivalence theorem (PROVED)

`RecordsWrites w0 j w1` says journal `j` (newest at head) records exactly the
writes carrying `w0` to `w1`, each entry recording the pre-write value. The CL
eval-loop establishes this by appending one entry per mutation (`journal-push!`)
just before each write. -/

inductive RecordsWrites : World Key Value → Journal Key Value → World Key Value → Prop where
  | nil  (w : World Key Value) : RecordsWrites w [] w
  | cons (w0 w1 : World Key Value) (k : Key) (vNew : Value) (js : Journal Key Value) :
      RecordsWrites w0 js w1 →
      RecordsWrites w0 (⟨k, w1 k⟩ :: js) (Function.update w1 k vNew)

/-- **Soundness of journal-based revert.** If `j` records the writes taking `w0`
    to `w1`, replaying `j` backwards against `w1` returns `w0`. This is the
    contract `revert-journal-to` discharges — formerly `sorry`, now proved. -/
theorem revert_restores_snapshot
    (w0 w1 : World Key Value) (j : Journal Key Value)
    (h : RecordsWrites w0 j w1) :
    revert j w1 = w0 := by
  induction h with
  | nil => rfl
  | cons w0 w1 k vNew js ih =>
      -- newest entry is ⟨k, w1 k⟩; world is (w1.update k vNew)
      simp only [revert_cons, applyRevertEntry]
      -- update (update w1 k vNew) k (w1 k) = update w1 k (w1 k) = w1
      rw [write_write_same, write_self]
      exact ih

/-! ## Account-existence corollary

Presence is a `Key → Bool` projection of the same world (key = `.present addr`,
default `false`). `account-dead-p` / `world-account-present-p` read this
projection; `mark-account-present!` writes `true` (journaled, type 11) and a
revert restores `false` (= remhash, the canonical default). So existence obeys
the same inverse law — no special-casing. The historical +25000 overcharge bugs
(a revert deleting an empty-but-present account) are exactly a violation of
`revert_restores_snapshot` on the presence projection: caught here structurally,
not by a hand-comment. -/

/-! ## Frame scoping (the part the per-op law does NOT give you)

EIP-2929: a `CALL`'s warm-up of the callee address happens in the CALLER's frame
(before the sub-context), so it belongs to the caller's journal segment and
SURVIVES the child's revert. Thus the frame-level "revert to a cursor restores
the world at that cursor" is only correct if caller-scoped effects are appended
BELOW the child's cursor. `segmentRevert` reverts only the suffix above cursor
`c`; the eval loop's obligation is that child-frame reverts use a cursor
at-or-above any caller-scoped entry, so those entries are never in the reverted
suffix. This is a property of snapshot placement, distinct from (and not implied
by) `revert_restores_snapshot`. -/

/-- Revert only entries appended after cursor `c` (= journal length at snapshot).
    `j` is newest-first; the segment is the first `j.length - c` entries. -/
def segmentRevert (c : Nat) (j : Journal Key Value) (w : World Key Value) :
    World Key Value :=
  revert (j.take (j.length - c)) w

/-- Reverting an empty segment (cursor at the current top) is a no-op:
    a frame that mutated nothing leaves the world untouched on revert. -/
@[simp] theorem segmentRevert_top (j : Journal Key Value) (w : World Key Value) :
    segmentRevert j.length j w = w := by
  simp [segmentRevert]

end World

end Evm.CL.Journal
