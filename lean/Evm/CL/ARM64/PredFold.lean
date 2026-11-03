/-
  Evm.CL.ARM64.PredFold — the predicate prologue: limb folds to booleans.

  Stage 1 of #238, and the piece that completes `SstoreGasDenote`. The five
  SSTORE routines open with six predicates computed by folding 64-bit limbs:

      isZero p dst           isEq p q dst
        ldp x6, x7, [p]        ldp x6, x7, [p] ; ldp x8, x9, [q]
        ldp x8, x9, [p,#16]    eor x6,x6,x8 ; eor x7,x7,x9 ; orr x6,x6,x7
        orr x6, x6, x7         ldp x8,x9,[p,#16] ; ldp x16,x17,[q,#16]
        orr x8, x8, x9         eor x8,x8,x16 ; eor x9,x9,x17 ; orr x8,x8,x9
        orr x6, x6, x8         orr x6, x6, x8
        cmp x6, #0             cmp x6, #0
        cset dst, eq           cset dst, eq

  The folds are the reason this is worth a theorem rather than a glance. The
  u256 is four limbs; `cmp`/`cset eq` reads ONE 64-bit register, so correctness
  rests on the OR (resp. XOR-then-OR) collapsing all four limbs into that
  register without losing a bit. This is the same family as the chained-`sbcs`
  Z-flag trap (`AsmCore.chained_z_unreliable`), where a comparison that looked
  fine was only testing the high limb — EQ/GT/SGT were all wrong, and random
  fixtures missed it because single-limb differences are rare by chance.

  With `prologue_predicates` below, the SSTORE routines are denoted end to end:
  the prologue produces exactly the six booleans the tree theorems in
  `SstoreGasDenote` assume.
-/

import Evm.BaseTypes
import Std.Tactic.BVDecide

namespace Evm.CL.ARM64.PredFold

/-- The four limbs of a u256, as `ldp` loads them: little-endian 64-bit words,
    l0 at offset 0. Written as four extracts rather than a shift by `64*i`
    because `bv_decide` bitblasts an extract and abstracts a Nat shift. -/
def limb0 (x : Evm.U256) : BitVec 64 := x.extractLsb' 0 64
def limb1 (x : Evm.U256) : BitVec 64 := x.extractLsb' 64 64
def limb2 (x : Evm.U256) : BitVec 64 := x.extractLsb' 128 64
def limb3 (x : Evm.U256) : BitVec 64 := x.extractLsb' 192 64

/-- `orr x6,x6,x7 ; orr x8,x8,x9 ; orr x6,x6,x8` — the whole u256 folded into
    one register. The tree shape (pairs, then the pair) is the asm's, not a
    left fold: with `|||` associative and commutative it is the same value, and
    writing it the asm's way keeps the correspondence visible. -/
def orFold (x : Evm.U256) : BitVec 64 :=
  (limb0 x ||| limb1 x) ||| (limb2 x ||| limb3 x)

/-- `eor` per limb, then the same OR tree. -/
def xorFold (x y : Evm.U256) : BitVec 64 :=
  ((limb0 x ^^^ limb0 y) ||| (limb1 x ^^^ limb1 y)) |||
  ((limb2 x ^^^ limb2 y) ||| (limb3 x ^^^ limb3 y))

/-- `cmp r, #0 ; cset dst, eq`. -/
def csetEqZero (r : BitVec 64) : Bool := r = 0

/-- What `isZero p dst` leaves in `dst`. -/
def isZeroFold (x : Evm.U256) : Bool := csetEqZero (orFold x)

/-- What `isEq p q dst` leaves in `dst`. -/
def isEqFold (x y : Evm.U256) : Bool := csetEqZero (xorFold x y)

/-- **No bit is lost by the OR tree**: the folded register is zero exactly when
    the 256-bit value is. -/
theorem isZeroFold_eq (x : Evm.U256) : isZeroFold x = decide (x = 0) := by
  simp only [isZeroFold, csetEqZero, orFold, limb0, limb1, limb2, limb3]
  bv_decide

/-- **…and by the XOR/OR tree**: zero exactly when the two values are equal. -/
theorem isEqFold_eq (x y : Evm.U256) : isEqFold x y = decide (x = y) := by
  simp only [isEqFold, csetEqZero, xorFold, limb0, limb1, limb2, limb3]
  bv_decide

/-- The six predicates the SSTORE prologue computes (x10..x15), against what the
    tree proofs in `SstoreGasDenote` assume. This is the join between the two
    halves of those routines. -/
theorem prologue_predicates (o c n : Evm.U256) :
    (isZeroFold o, isZeroFold c, isZeroFold n, isEqFold o c, isEqFold c n, isEqFold o n)
      = (decide (o = 0), decide (c = 0), decide (n = 0),
         decide (o = c), decide (c = n), decide (o = n)) := by
  simp only [isZeroFold_eq, isEqFold_eq]

/-! ## Why the fold has to be over all four limbs

Dropping a limb from either fold is not caught by a value that differs in the
limbs you kept — which is exactly how a single-limb difference survives a
fixture suite. Both counterexamples are a difference in ONE limb only. -/

/-- A three-limb OR fold calls `2^192` zero. -/
example :
    ((limb0 (BitVec.ofNat 256 (2^192)) ||| limb1 (BitVec.ofNat 256 (2^192)))
      ||| limb2 (BitVec.ofNat 256 (2^192))) = 0
    ∧ orFold (BitVec.ofNat 256 (2^192)) ≠ 0 := by
  constructor <;> simp only [limb0, limb1, limb2, limb3, orFold] <;> bv_decide

/-- A three-limb XOR fold calls two values equal when they differ only in the
    limb it skipped — the selector-sized case the trap notes warn about. -/
example :
    (((limb0 (BitVec.ofNat 256 (2^64)) ^^^ limb0 (0 : Evm.U256))
       ||| (limb2 (BitVec.ofNat 256 (2^64)) ^^^ limb2 (0 : Evm.U256)))
       ||| (limb3 (BitVec.ofNat 256 (2^64)) ^^^ limb3 (0 : Evm.U256))) = 0
    ∧ xorFold (BitVec.ofNat 256 (2^64)) (0 : Evm.U256) ≠ 0 := by
  constructor <;> simp only [limb0, limb1, limb2, limb3, xorFold] <;> bv_decide

end Evm.CL.ARM64.PredFold
