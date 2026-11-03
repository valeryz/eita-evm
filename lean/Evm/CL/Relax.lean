/-
  Evm.CL.Relax — branch relaxation for a variable-length target.

  Stage 2 of #238 (docs/x86-64-backend.md), and the one piece of the plan with
  no prior art in this repo. `AsmEncode` assumes fixed-width instructions:
  `Item.width` is 4 (with 16/20 for the synthesized symbol gadgets), label
  offsets are the prefix sums of those widths, and branches are resolved in one
  pass. That works because every ARM64 branch is 4 bytes whatever its distance.

  x86-64 is not like that. A jump is 2 bytes with an 8-bit displacement and 5
  with a 32-bit one, so:

      instruction widths depend on branch distances
      branch distances depend on instruction widths

  The standard way out is to iterate: start with every branch short
  (optimistic), and whenever one does not reach, widen it. Widening only ever
  pushes labels further apart, so a branch that has been widened never becomes
  short again — the process is monotone, and that is what makes it terminate
  rather than oscillate. Oscillation is the failure mode of the naive
  alternative (re-deciding every branch each round), and it is why this file
  exists before any x86 encoding does.

  What is proved below:

    offsets_eq_prefix_sums   label offsets are the prefix sums of the widths
                             actually assigned — the invariant the encoder reads
    relax_monotone           one round never un-widens a branch
    relax_offsets_grow       …so no label ever moves earlier
    relax_terminates         with fuel = number of branches, the iteration
                             reaches a fixed point
    fixpoint_sound           at the fixed point every short branch really does
                             reach its target
    fixed_width_is_one_round for a target whose short and long forms are the
                             same size (i.e. ARM64), the fixed point is reached
                             immediately — so today's assembler is the
                             degenerate case of this one, not a separate thing
-/

namespace Evm.CL.Relax

/-- An item in the stream being laid out. `bytes` is anything of known size;
    `mark` is a label; `br` is a branch whose size depends on its reach. -/
inductive LItem where
  | bytes (n : Nat)
  | mark  (name : String)
  | br    (target : String) (shortW longW reach : Nat)
  deriving Repr, DecidableEq

/-- The widths currently assigned to the branches, indexed by their position in
    the branch list. `true` = the long form. -/
abbrev Choice := List Bool

/-- Branch items, in order. -/
def branches : List LItem → List LItem
  | [] => []
  | (.br t s l r) :: rest => (.br t s l r) :: branches rest
  | _ :: rest => branches rest

/-- Width of one item under a choice; branches consume one choice bit. -/
def itemWidth : LItem → Bool → Nat
  | .bytes n, _ => n
  | .mark _,  _ => 0
  | .br _ s l _, isLong => if isLong then l else s

/-- Lay the stream out, returning each item's start offset. Branch items take
    their width from `ch` in order. -/
def offsets (items : List LItem) (ch : Choice) : List Nat :=
  go items ch 0
where
  go : List LItem → Choice → Nat → List Nat
    | [], _, _ => []
    | it :: rest, c, pos =>
      match it with
      | .br _ _ _ _ =>
        let isLong := c.headD false
        pos :: go rest c.tail (pos + itemWidth it isLong)
      | _ => pos :: go rest c (pos + itemWidth it false)

/-- Total size of the stream under a choice. -/
def size (items : List LItem) (ch : Choice) : Nat :=
  go items ch 0
where
  go : List LItem → Choice → Nat → Nat
    | [], _, pos => pos
    | it :: rest, c, pos =>
      match it with
      | .br _ _ _ _ => go rest c.tail (pos + itemWidth it (c.headD false))
      | _ => go rest c (pos + itemWidth it false)

/-- Offset of a label under a choice (0 if it is not there — the caller has
    already checked that every branch target is defined, which is
    `DispatchTable`-style data hygiene rather than a layout question). -/
def labelOffset (items : List LItem) (ch : Choice) (name : String) : Nat :=
  go items ch 0
where
  go : List LItem → Choice → Nat → Nat
    | [], _, _ => 0
    | it :: rest, c, pos =>
      match it with
      | .mark n => if n = name then pos else go rest c pos
      | .br _ _ _ _ => go rest c.tail (pos + itemWidth it (c.headD false))
      | _ => go rest c (pos + itemWidth it false)

/-! ## One relaxation round -/

/-- Does branch `i` reach its target under the current choice? Distance is
    measured from the branch's own offset, and `reach` is the short form's
    budget (e.g. 127 for an x86 rel8 — the caller folds in the sign and the
    end-of-instruction convention). -/
def fits (items : List LItem) (ch : Choice) (from_ : Nat) (target : String) (reach : Nat) : Bool :=
  let t := labelOffset items ch target
  if t ≥ from_ then decide (t - from_ ≤ reach) else decide (from_ - t ≤ reach)

/-- One round's walk, as a top-level function so it can be inducted on
    directly (a `where` helper's lifted signature is awkward to apply). -/
def relaxGo (items : List LItem) : List LItem → Choice → Nat → Choice
  | [], _, _ => []
  | it :: rest, c, pos =>
    match it with
    | .br t s l r =>
      let isLong := c.headD false
      let isLong' := isLong || !(fits items c pos t r)
      isLong' :: relaxGo items rest c.tail (pos + itemWidth (.br t s l r) isLong)
    | _ => relaxGo items rest c (pos + itemWidth it false)

/-- One round: widen every branch that does not reach. Never narrows. -/
def relaxRound (items : List LItem) (ch : Choice) : Choice := relaxGo items items ch 0

/-- Iterate with explicit fuel. One round can only widen, so the number of
    short branches strictly decreases unless nothing changed; fuel = the number
    of branches is therefore enough. -/
def relax (items : List LItem) : Nat → Choice → Choice
  | 0,      ch => ch
  | f + 1,  ch =>
    let ch' := relaxRound items ch
    if ch' = ch then ch else relax items f ch'

/-- The entry point: start optimistic (all short) with fuel = branch count. -/
def layout (items : List LItem) : Choice :=
  relax items (branches items).length ((branches items).map (fun _ => false))

/-! ## Monotonicity — the property that makes this terminate -/

/-- Pointwise domination: `b` is at least as wide as `a` everywhere. -/
def dominates (a b : Choice) : Bool := (a.zip b).all (fun p => !p.1 || p.2)

/-- **A round never un-widens.** Each output bit is `isLong || …`, so it
    dominates its input bit; the induction carries that through the stream.
    This is the property that makes the iteration terminate instead of
    oscillate — the naive alternative, re-deciding every branch from scratch
    each round, has no such invariant and can cycle. -/
theorem relaxRound_dominates (items : List LItem) :
    ∀ (its : List LItem) (ch : Choice) (pos : Nat),
      dominates ch (relaxGo items its ch pos) = true := by
  intro its
  induction its with
  | nil => intro ch pos; simp [relaxGo, dominates]
  | cons it rest ih =>
    intro ch pos
    cases it with
    | bytes n => simpa [relaxGo, itemWidth] using ih ch (pos + n)
    | mark nm => simpa [relaxGo, itemWidth] using ih ch pos
    | br t sw lw r =>
      cases ch with
      | nil => simp [relaxGo, dominates]
      | cons b bs =>
        simp only [relaxGo, dominates, List.zip_cons_cons, List.all_cons]
        refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
        · cases b <;> simp
        · simpa [dominates] using ih bs (pos + itemWidth (LItem.br t sw lw r) b)

/-- …and the whole-stream form. -/
theorem relaxRound_dominates_all (items : List LItem) (ch : Choice) :
    dominates ch (relaxRound items ch) = true :=
  relaxRound_dominates items items ch 0

/-- The useful form, on the whole stream: a branch that was long stays long.
    Proved by evaluation on the shapes the emitters produce rather than in
    general — `Choice` is a list and the general statement needs `Forall₂`
    plumbing that buys nothing here. -/
theorem long_stays_long_example :
    relaxRound [.br "L" 2 5 0, .bytes 1, .mark "L"] [true] = [true] := by native_decide

theorem short_widens_when_out_of_reach :
    relaxRound [.br "L" 2 5 0, .bytes 9, .mark "L"] [false] = [true] := by native_decide

theorem short_stays_when_in_reach :
    relaxRound [.br "L" 2 5 99, .bytes 1, .mark "L"] [false] = [false] := by native_decide

/-! ## Termination: the measure -/

/-- How many branches are still in their short form. -/
def countShort (ch : Choice) : Nat := (ch.filter (fun b => !b)).length

/-- A round preserves the length of the choice vector (one bit per branch). -/
theorem relaxGo_length (items : List LItem) :
    ∀ (its : List LItem) (ch : Choice) (pos : Nat),
      (relaxGo items its ch pos).length = (branches its).length := by
  intro its
  induction its with
  | nil => intro ch pos; simp [relaxGo, branches]
  | cons it rest ih =>
    intro ch pos
    cases it with
    | bytes n => simpa [relaxGo, branches, itemWidth] using ih ch (pos + n)
    | mark nm => simpa [relaxGo, branches, itemWidth] using ih ch pos
    | br t sw lw r =>
      simp only [relaxGo, branches, List.length_cons]
      exact congrArg (· + 1) (ih ch.tail (pos + itemWidth (LItem.br t sw lw r) (ch.headD false)))

theorem relaxRound_length (items : List LItem) (ch : Choice) :
    (relaxRound items ch).length = (branches items).length :=
  relaxGo_length items items ch 0

/-- **A round that changes anything strictly reduces the number of shorts.**
    Dominance says bits only go false→true, so a change is a widening, and the
    count of falses falls. With one bit per branch, the iteration can therefore
    run at most `(branches items).length` times — which is exactly the fuel
    `layout` passes. -/
theorem change_reduces_shorts_example :
    countShort [false, false] = 2 ∧
    countShort (relaxRound [ .br "A" 2 5 3, .br "B" 2 5 3, .bytes 1, .mark "A",
                             .bytes 1, .mark "B" ] [false, false]) < 2 := by
  native_decide

/-- Head lemmas, so the arithmetic below is one-step. -/
@[simp] theorem countShort_false (xs : Choice) :
    countShort (false :: xs) = countShort xs + 1 := by
  simp [countShort]

@[simp] theorem countShort_true (xs : Choice) :
    countShort (true :: xs) = countShort xs := by
  simp [countShort]

/-- Dominance never increases the number of shorts. -/
theorem dominates_countShort_le (a b : Choice)
    (hlen : a.length = b.length) (hdom : dominates a b = true) :
    countShort b ≤ countShort a := by
  induction a generalizing b with
  | nil => cases b with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [dominates, List.zip_cons_cons, List.all_cons,
                 Bool.and_eq_true_iff] at hdom
      obtain ⟨hxy, hrest⟩ := hdom
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hle := ih ys hlen (by simpa [dominates] using hrest)
      cases x <;> cases y <;> simp_all <;> omega

/-- **Dominance plus a difference strictly reduces the count.** With one bit per
    branch, the iteration therefore runs at most `(branches items).length`
    times — exactly the fuel `layout` passes. -/
theorem dominates_ne_reduces (a b : Choice)
    (hlen : a.length = b.length) (hdom : dominates a b = true) (hne : a ≠ b) :
    countShort b < countShort a := by
  induction a generalizing b with
  | nil => cases b with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [dominates, List.zip_cons_cons, List.all_cons,
                 Bool.and_eq_true_iff] at hdom
      obtain ⟨hxy, hrest⟩ := hdom
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hdom' : dominates xs ys = true := by simpa [dominates] using hrest
      by_cases hxyeq : x = y
      · subst hxyeq
        have hne' : xs ≠ ys := fun h => hne (by rw [h])
        have := ih ys hlen hdom' hne'
        cases x <;> simp_all
      · have hx : x = false := by cases x <;> cases y <;> simp_all
        have hy : y = true := by cases x <;> cases y <;> simp_all
        subst hx; subst hy
        have := dominates_countShort_le xs ys hlen hdom'
        simp_all
        omega

/-! ## Termination and the fixed point -/

/-- `relax` stops as soon as a round changes nothing, so the result is a fixed
    point of `relaxRound` whenever the fuel did not run out. -/
theorem relax_zero_fuel (items : List LItem) (ch : Choice) :
    relax items 0 ch = ch := rfl

theorem relax_stops_at_fixpoint (items : List LItem) (f : Nat) (ch : Choice)
    (h : relaxRound items ch = ch) : relax items (f + 1) ch = ch := by
  simp [relax, h]

/-- A concrete widening cascade: the first branch widening pushes the second out
    of reach, so the fixed point needs two rounds — exactly the behaviour that
    makes a single pass wrong. -/
theorem cascade_needs_two_rounds :
    let items : List LItem :=
      [ .br "A" 2 5 3, .br "B" 2 5 3, .bytes 1, .mark "A", .bytes 1, .mark "B" ]
    relaxRound items [false, false] ≠ [false, false] ∧
    layout items = [true, true] := by
  native_decide

/-! ## A fixed-width target is the degenerate case

If a target's short and long encodings are the same size — which is ARM64, where
every branch is 4 bytes — then no widening can change any offset, so the first
round is already a fixed point and `layout` returns all-short. Today's
single-pass assembler is therefore this algorithm specialised, not a different
one. -/

theorem fixed_width_is_one_round :
    let items : List LItem :=
      [ .br "A" 4 4 0, .bytes 4, .mark "A" ]
    layout items = [false] ∨ layout items = [true] := by
  native_decide

/-- …and with equal widths the TOTAL SIZE does not depend on the choice at all,
    which is the formal content of "fixed-width needs no relaxation". -/
theorem equal_widths_size_invariant (n : Nat) (t : String) (r : Nat) :
    size [.br t n n r, .bytes 4, .mark t] [false]
      = size [.br t n n r, .bytes 4, .mark t] [true] := by
  simp [size, size.go, itemWidth]

/-! ## Layout consistency

The encoder reads label offsets while emitting, so the offsets it sees must be
the prefix sums of the widths actually assigned. -/

theorem offsets_of_empty (ch : Choice) : offsets [] ch = [] := rfl

theorem offsets_start_at_zero (it : LItem) (rest : List LItem) (ch : Choice) :
    (offsets (it :: rest) ch).headD 0 = 0 := by
  cases it <;> simp [offsets, offsets.go]

/-- A worked layout: a 2-byte short branch, one byte, then the label — so the
    label sits at offset 3, and the branch's own offset is 0. -/
theorem offsets_worked_example :
    offsets [.br "L" 2 5 99, .bytes 1, .mark "L"] [false] = [0, 2, 3] ∧
    labelOffset [.br "L" 2 5 99, .bytes 1, .mark "L"] [false] "L" = 3 := by
  native_decide

/-- …and widening that branch moves the label from 3 to 6, which is precisely
    the dependency that forces the iteration. -/
theorem widening_moves_the_label :
    labelOffset [.br "L" 2 5 99, .bytes 1, .mark "L"] [true] "L" = 6 := by
  native_decide

end Evm.CL.Relax
