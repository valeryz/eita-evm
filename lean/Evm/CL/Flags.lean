/-
  Evm.CL.Flags — carry polarity and the Z-flag, denotationally, on both targets.

  Stage 3 of #238. The x86-64 encoder is gated byte-for-byte against clang, and
  the lowering assembles; neither says anything about what the FLAGS mean, and
  that is where a port of this code goes wrong silently. Two traps, one per
  flag:

  ## Carry: same name, opposite polarity on subtraction

  ARM64's `SUBS` sets C = 1 when there was NO borrow; `SBCS` consumes it as
  "subtract (1 - C)". x86-64's `SUB` sets CF = 1 when there WAS a borrow; `SBB`
  consumes it as "subtract CF". Within each ISA a four-limb chain is correct —
  the convention is self-consistent — but the CONSUMERS read the flag directly:

      ARM64   subs x22, x22, #n ; b.lo  _eita_oog     (branch if C = 0)
      x86-64  sub  r15, n       ; jb    _eita_oog     (branch if CF = 1)

  `b.lo` and `jb` both mean "a borrow happened", which is what we want. But a
  port that translates the FLAG TEST — "branch when the carry bit is clear" —
  lands on `jae`, which on x86 means "no borrow", and the handler then runs out
  of gas exactly when it has enough. Both assemble. Both are byte-exact against
  clang. Only the meaning is wrong. `carry_polarity_mistranslation` is that bug,
  as a theorem.

  For addition the two agree (C = CF = carry-out), which is the asymmetry that
  makes this easy to get half right.

  ## Z: after a chain, it is the last limb's, on both targets

  `feedback_chained_sbcs_zflag` records the ARM64 trap: after a `subs/sbcs`
  chain over four limbs, Z reflects only the HIGH limb's result, so a u256
  equality read from Z is wrong whenever the values differ only in a lower limb.
  It killed EQ/GT/SGT. x86-64 has the same behaviour — `sbb` sets ZF from its
  own result — so the trap transfers unchanged, and so does the fix: fold the
  limb differences with OR and test THAT for zero (`PredFold`). Both halves are
  proved here, including the counterexample.

  Everything is stated over `borrow`, the fact both ISAs encode; each ISA's flag
  is a presentation of it (`armC = !borrow`, `x86CF = borrow`).
-/

import Std.Tactic.BVDecide

namespace Evm.CL.Flags

/-! ## One limb -/

/-- `a - b - bin` on a 64-bit limb: the result and whether it borrowed. The
    borrow is `a < b`, or `a = b` with a borrow coming in — stated over
    `BitVec` so the chain theorems below are decidable by `bv_decide`. -/
def subBorrow (a b : BitVec 64) (bin : Bool) : BitVec 64 × Bool :=
  let r := a - b - (if bin then 1 else 0)
  let borrowed := a < b || (a == b && bin)
  (r, borrowed)

/-! ## The two presentations of the same fact -/

/-- ARM64 after `SUBS`/`SBCS`: C is set when there was NO borrow. -/
def armC_sub (borrow : Bool) : Bool := !borrow
/-- x86-64 after `SUB`/`SBB`: CF is set when there WAS a borrow. -/
def x86CF_sub (borrow : Bool) : Bool := borrow

/-- For addition both ISAs expose the carry-out directly. -/
def armC_add (carry : Bool) : Bool := carry
def x86CF_add (carry : Bool) : Bool := carry

theorem sub_polarity_is_inverted (b : Bool) : armC_sub b = !x86CF_sub b := by
  cases b <;> rfl

theorem add_polarity_agrees (c : Bool) : armC_add c = x86CF_add c := rfl

/-! ## The conditions the emitters use -/

/-- ARM64 `lo` (= `cc`): branch when C is clear. -/
def armLo (C : Bool) : Bool := !C
/-- ARM64 `hs` (= `cs`): branch when C is set. -/
def armHs (C : Bool) : Bool := C
/-- x86 `b`: branch when CF is set. -/
def x86B (CF : Bool) : Bool := CF
/-- x86 `ae`: branch when CF is clear. -/
def x86Ae (CF : Bool) : Bool := !CF

/-- **`b.lo` and `jb` test the same fact**: a borrow happened. This is the
    correct translation of the OOG branch, and it is the one `Lowering` emits
    (`bloOog ↦ jb`). -/
theorem lo_is_b (borrow : Bool) : armLo (armC_sub borrow) = x86B (x86CF_sub borrow) := by
  cases borrow <;> rfl

/-- …and `b.hs` is `jae`. -/
theorem hs_is_ae (borrow : Bool) : armHs (armC_sub borrow) = x86Ae (x86CF_sub borrow) := by
  cases borrow <;> rfl

/-- **The mistranslation.** Translating the flag TEST rather than its meaning —
    "branch when the carry bit is clear" ↦ `jae` — yields the exact negation on
    every input, so the handler would trap on enough gas and continue on too
    little. Assembles fine, byte-exact against clang, wrong. -/
theorem carry_polarity_mistranslation (borrow : Bool) :
    x86Ae (x86CF_sub borrow) = !(armLo (armC_sub borrow)) := by
  cases borrow <;> rfl

/-! ## The gas charge, end to end on both targets -/

/-- What `subs x22, x22, #n ; b.lo _eita_oog` does to a 64-bit gas counter. -/
def armCharge (gas : BitVec 64) (n : BitVec 64) : Option (BitVec 64) :=
  let (r, borrow) := subBorrow gas n false
  if armLo (armC_sub borrow) then none else some r

/-- What `sub r15, n ; jb _eita_oog` does. -/
def x86Charge (gas : BitVec 64) (n : BitVec 64) : Option (BitVec 64) :=
  let (r, borrow) := subBorrow gas n false
  if x86B (x86CF_sub borrow) then none else some r

/-- Both charge exactly the spec's "OOG iff n > gas, else gas - n". -/
theorem charges_agree (gas n : BitVec 64) : armCharge gas n = x86Charge gas n := by
  simp [armCharge, x86Charge, armLo, armC_sub, x86B, x86CF_sub]

theorem charge_is_spec (gas n : BitVec 64) :
    x86Charge gas n = (if gas < n then none else some (gas - n)) := by
  simp [x86Charge, subBorrow, x86B, x86CF_sub]

/-- And the mistranslated one is wrong on every input where the right one is
    defined: it traps exactly when there is enough gas. -/
def x86ChargeWrong (gas : BitVec 64) (n : BitVec 64) : Option (BitVec 64) :=
  let (r, borrow) := subBorrow gas n false
  if x86Ae (x86CF_sub borrow) then none else some r

theorem mistranslated_charge_inverts (gas n : BitVec 64) :
    (x86ChargeWrong gas n).isSome = !(x86Charge gas n).isSome := by
  simp [x86ChargeWrong, x86Charge, subBorrow, x86Ae, x86B, x86CF_sub]
  split <;> simp_all

/-! ## Four-limb chains -/

/-- A u256 as four little-endian limbs. -/
structure U256L where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64

/-- The ARM64 chain `subs/sbcs/sbcs/sbcs`, written over C as the ISA does:
    `sbcs` subtracts `1 - C`. Returns the limbs, the final C, and the final Z
    (which `sbcs` sets from ITS OWN result only). -/
def armSubChain (a b : U256L) : U256L × Bool × Bool :=
  let (r0, b0) := subBorrow a.l0 b.l0 false
  let c0 := armC_sub b0
  let (r1, b1) := subBorrow a.l1 b.l1 (!c0)
  let c1 := armC_sub b1
  let (r2, b2) := subBorrow a.l2 b.l2 (!c1)
  let c2 := armC_sub b2
  let (r3, b3) := subBorrow a.l3 b.l3 (!c2)
  let c3 := armC_sub b3
  (⟨r0, r1, r2, r3⟩, c3, r3 == 0)

/-- The x86-64 chain `sub/sbb/sbb/sbb`, over CF: `sbb` subtracts CF. Same
    shape, opposite polarity in the flag, same borrow underneath. -/
def x86SubChain (a b : U256L) : U256L × Bool × Bool :=
  let (r0, b0) := subBorrow a.l0 b.l0 false
  let cf0 := x86CF_sub b0
  let (r1, b1) := subBorrow a.l1 b.l1 cf0
  let cf1 := x86CF_sub b1
  let (r2, b2) := subBorrow a.l2 b.l2 cf1
  let cf2 := x86CF_sub b2
  let (r3, b3) := subBorrow a.l3 b.l3 cf2
  let cf3 := x86CF_sub b3
  (⟨r0, r1, r2, r3⟩, cf3, r3 == 0)

/-- **The chains compute the same limbs and the same borrow-out**, presented as
    C on one side and CF on the other. So a chain ported limb for limb is
    right — the trap is only ever at the consumer. -/
theorem chains_agree (a b : U256L) :
    (armSubChain a b).1 = (x86SubChain a b).1 ∧
    (armSubChain a b).2.1 = !(x86SubChain a b).2.1 := by
  simp [armSubChain, x86SubChain, armC_sub, x86CF_sub]

/-- The four limbs as one 256-bit value, high limb first. -/
def U256L.toBV (a : U256L) : BitVec 256 := a.l3 ++ a.l2 ++ a.l1 ++ a.l0

/-- The borrow-out of the chain is the u256 comparison `a < b` — the fact the
    comparison handlers read — on both targets. Stated through the x86 side
    (CF = borrow); the ARM side follows by `chains_agree`. -/
theorem chain_borrow_is_lt (a b : U256L) :
    (x86SubChain a b).2.1 = decide (a.toBV < b.toBV) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [x86SubChain, subBorrow, x86CF_sub, U256L.toBV]
  bv_decide

/-- And the limbs it produces are the limbs of the 256-bit difference. -/
theorem chain_result_is_sub (a b : U256L) :
    (x86SubChain a b).1.toBV = a.toBV - b.toBV := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [x86SubChain, subBorrow, x86CF_sub, U256L.toBV]
  bv_decide

/-! ## The Z-flag -/

/-- **Z after the chain is the HIGH limb's zero-ness only**, on both targets:
    the final `sbcs`/`sbb` sets it from its own result. -/
theorem chain_z_is_high_limb_only (a b : U256L) :
    (armSubChain a b).2.2 = ((armSubChain a b).1.l3 == 0) ∧
    (x86SubChain a b).2.2 = ((x86SubChain a b).1.l3 == 0) := by
  simp [armSubChain, x86SubChain]

/-- **The counterexample**, the same one that killed EQ on ARM64: values that
    differ only in limb 0 leave Z SET after the chain, so "equal iff Z" says
    they are equal. Here on x86-64, which shares the behaviour. -/
theorem z_flag_eq_is_wrong :
    let a : U256L := ⟨1, 0, 0, 0⟩
    let b : U256L := ⟨0, 0, 0, 0⟩
    (x86SubChain a b).2.2 = true ∧ a.l0 ≠ b.l0 := by
  decide

/-- The correct test: fold the limb differences with OR and test that. This is
    what `PredFold` does, and it transfers to x86-64 unchanged because it never
    reads a chain's flags at all. -/
def eqFold (a b : U256L) : Bool :=
  ((a.l0 ^^^ b.l0) ||| (a.l1 ^^^ b.l1) ||| (a.l2 ^^^ b.l2) ||| (a.l3 ^^^ b.l3)) == 0

theorem eqFold_correct (a b : U256L) :
    eqFold a b = (a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [eqFold]
  bv_decide

/-- …and it gets the counterexample right. -/
theorem eqFold_rejects_counterexample :
    eqFold ⟨1, 0, 0, 0⟩ ⟨0, 0, 0, 0⟩ = false := by decide

end Evm.CL.Flags
