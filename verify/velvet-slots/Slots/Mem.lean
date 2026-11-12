import Velvet
import Slots.Frame

/-!
Proof-carrying array access for the Velvet methods.

Every read and write in a method body goes through `rd` / `wr` (or the 8-limb `wrKV` / `wrV`),
which index with `a[i]'h` / `a.set i v h` under `if h : i < a.size`. The `else` branch is `oob`,
an `Option` failure. A method whose contract forbids failure (`signals False`, the default)
therefore carries the obligation `i < a.size` at every access: the vcgen meets it through the
`@[spec]` triples below, whose precondition is the bound. The C printer emits only the `then`
branch, and only in methods whose proved contract forbids failure (so the `else` is dead).

`wsAbort msg` is the one deliberate failure: the printer emits `fputs(msg); abort()`. A method
using it states, in a `signals` clause, exactly when it aborts.
-/

open Std.WP Lean.Order

/-- An out-of-bounds access: unreachable in a method whose contract forbids failure. -/
def oob {α : Type} : Option α := throw ()

/-- Abort the process with a message (the C table's `fputs(...); abort()`). -/
def wsAbort {α : Type} (_msg : String) : Option α := throw ()

def rd {α : Type} [Inhabited α] (a : Array α) (i : Nat) : Option α :=
  if h : i < a.size then pure (a[i]'h) else oob

def wr {α : Type} (a : Array α) (i : Nat) (v : α) : Option (Array α) :=
  if h : i < a.size then pure (a.set i v h) else oob

@[spec] theorem rd_spec {α : Type} [Inhabited α] (a : Array α) (i : Nat) (post : α → Prop)
    (epost : Unit → Prop) : Triple (rd a i) (⌜i < a.size⌝ ⊓ post a[i]!) post epost := by
  constructor
  refine ofProp_meet_le_left fun h => ?_
  intro hp
  simp only [rd, h, dite_true]
  rw [getElem!_pos a i h] at hp
  exact hp

theorem set_eq_set! {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    a.set i v h = a.set! i v := by
  simp [Array.set!, Array.setIfInBounds, h]

@[spec] theorem wr_spec {α : Type} (a : Array α) (i : Nat) (v : α) (post : Array α → Prop)
    (epost : Unit → Prop) : Triple (wr a i v) (⌜i < a.size⌝ ⊓ post (a.set! i v)) post epost := by
  constructor
  refine ofProp_meet_le_left fun h => ?_
  intro hp
  simp only [wr, h, dite_true]
  rw [← set_eq_set! a i v h] at hp
  exact hp

/-- Write key and value limbs of entry `i` (the order of `ws_place`). -/
def wrKV (w : Array UInt64) (i : Nat) (k : Key) (v : Val) : Option (Array UInt64) := do
  let w ← wr w (8*i) k.1
  let w ← wr w (8*i+1) k.2.1
  let w ← wr w (8*i+2) k.2.2.1
  let w ← wr w (8*i+3) k.2.2.2
  let w ← wr w (8*i+4) v.1
  let w ← wr w (8*i+5) v.2.1
  let w ← wr w (8*i+6) v.2.2.1
  wr w (8*i+7) v.2.2.2

/-- Overwrite the value limbs of entry `i`. -/
def wrV (w : Array UInt64) (i : Nat) (v : Val) : Option (Array UInt64) := do
  let w ← wr w (8*i+4) v.1
  let w ← wr w (8*i+5) v.2.1
  let w ← wr w (8*i+6) v.2.2.1
  wr w (8*i+7) v.2.2.2

theorem wr_some {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    wr a i v = some (a.set! i v) := by
  simp only [wr, h, dite_true, set_eq_set! a i v h]; rfl

theorem wr_bind {α β : Type} (a : Array α) (i : Nat) (v : α) (f : Array α → Option β) (h : i < a.size) :
    (wr a i v >>= f) = f (a.set! i v) := by
  rw [wr_some a i v h]; rfl

theorem wrKV_eq (w : Array UInt64) (i : Nat) (k : Key) (v : Val) (h : 8*i+7 < w.size) :
    wrKV w i k v = some (setKV w i k v) := by
  simp (disch := ((try simp only [Array.size_set!]); omega)) only [wrKV, setKV, wr_bind]
  exact wr_some _ _ _ (by (try simp only [Array.size_set!]); omega)

theorem wrV_eq (w : Array UInt64) (i : Nat) (v : Val) (h : 8*i+7 < w.size) :
    wrV w i v = some (setV w i v) := by
  simp (disch := ((try simp only [Array.size_set!]); omega)) only [wrV, setV, wr_bind]
  exact wr_some _ _ _ (by (try simp only [Array.size_set!]); omega)

@[spec] theorem wrKV_spec (w : Array UInt64) (i : Nat) (k : Key) (v : Val)
    (post : Array UInt64 → Prop) (epost : Unit → Prop) :
    Triple (wrKV w i k v) (⌜8*i+7 < w.size⌝ ⊓ post (setKV w i k v)) post epost := by
  constructor
  refine ofProp_meet_le_left fun h => ?_
  intro hp
  rw [wrKV_eq w i k v h]; exact hp

@[spec] theorem wrV_spec (w : Array UInt64) (i : Nat) (v : Val)
    (post : Array UInt64 → Prop) (epost : Unit → Prop) :
    Triple (wrV w i v) (⌜8*i+7 < w.size⌝ ⊓ post (setV w i v)) post epost := by
  constructor
  refine ofProp_meet_le_left fun h => ?_
  intro hp
  rw [wrV_eq w i v h]; exact hp
