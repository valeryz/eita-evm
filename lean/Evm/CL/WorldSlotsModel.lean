/-
  WorldSlotsModel.lean — the semantics of the native slot tables (c/world_slots.h;
  docs/native-storage.md): a finite map (account id, slot key) -> value, and the set of
  ids that have a table (a write creates an id's table, a drop removes it and every key
  of the id). The C table is an implementation of this map: open addressing, tombstones,
  growth and the walk order are below the model. It is checked against the model by
  `lake exe worldSlotsVectors` (traces with the model's answers, replayed on the C table
  by c/test_world_slots.c) and by the CBMC harness (c/cbmc/world_slots_harness.c), which
  encodes the same map. The lemmas are the contract each C primitive is tested for.
-/
namespace Evm.CL.WorldSlotsModel

abbrev Word := BitVec 256

/-- The model state: values by (id, key), and table existence by id. -/
structure M where
  val : Nat → Word → Option Word
  has : Nat → Bool

def empty : M := ⟨fun _ _ => none, fun _ => false⟩

/-- `eita_ws_get`: the value of (id, key), or none. -/
def get (m : M) (id : Nat) (k : Word) : Option Word := m.val id k
/-- `eita_ws_table(...) != NULL`. -/
def hasTable (m : M) (id : Nat) : Bool := m.has id
/-- `eita_ws_put`: (id, key) := v; id's table exists. -/
def put (m : M) (id : Nat) (k v : Word) : M :=
  ⟨fun i j => if i = id ∧ j = k then some v else m.val i j, fun i => i = id || m.has i⟩
/-- `eita_ws_remove`: (id, key) absent; id's table exists. -/
def remove (m : M) (id : Nat) (k : Word) : M :=
  ⟨fun i j => if i = id ∧ j = k then none else m.val i j, fun i => i = id || m.has i⟩
/-- `eita_ws_drop`: id has no table and no keys. -/
def drop (m : M) (id : Nat) : M :=
  ⟨fun i j => if i = id then none else m.val i j, fun i => i ≠ id && m.has i⟩
/-- `eita_ws_copy` (dst, id, src's table of id): dst's id becomes src's id. -/
def copy (dst src : M) (id : Nat) : M :=
  ⟨fun i j => if i = id then src.val id j else dst.val i j, fun i => if i = id then src.has id else dst.has i⟩

theorem get_put_same (m : M) (id : Nat) (k v : Word) : get (put m id k v) id k = some v := by
  simp [get, put]
theorem get_put_other (m : M) (id i : Nat) (k j v : Word) (h : ¬(i = id ∧ j = k)) :
    get (put m id k v) i j = get m i j := by
  simp only [get, put]; rw [if_neg h]
theorem get_remove_same (m : M) (id : Nat) (k : Word) : get (remove m id k) id k = none := by
  simp [get, remove]
theorem get_remove_other (m : M) (id i : Nat) (k j : Word) (h : ¬(i = id ∧ j = k)) :
    get (remove m id k) i j = get m i j := by
  simp only [get, remove]; rw [if_neg h]
theorem get_drop_same (m : M) (id : Nat) (j : Word) : get (drop m id) id j = none := by
  simp [get, drop]
theorem get_drop_other (m : M) (id i : Nat) (j : Word) (h : i ≠ id) : get (drop m id) i j = get m i j := by
  simp [get, drop, h]
theorem hasTable_put (m : M) (id : Nat) (k v : Word) : hasTable (put m id k v) id = true := by
  simp [hasTable, put]
theorem hasTable_drop (m : M) (id : Nat) : hasTable (drop m id) id = false := by
  simp [hasTable, drop]
/-- A journal's type-0 restore: re-putting the old value of every write, newest first,
    gives back the pre-state's value at every key that was present before. -/
theorem get_put_put (m : M) (id : Nat) (k v w : Word) : get (put (put m id k v) id k w) id k = some w := by
  simp [get, put]
theorem get_restore (m : M) (id : Nat) (k v old : Word) (h : get m id k = some old) (i : Nat) (j : Word) :
    get (put (put m id k v) id k old) i j = get m i j := by
  simp only [get, put] at *
  by_cases e : i = id ∧ j = k
  · rw [if_pos e, ← h, e.1, e.2]
  · rw [if_neg e, if_neg e]

end Evm.CL.WorldSlotsModel
