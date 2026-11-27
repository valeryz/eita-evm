/-
  Evm.CL.RV32.Carry — the arithmetic the rv32 lowering rests on, as theorems.

  RISC-V has no condition flags, so `Evm.CL.RV32.Lower` materialises the carry
  in a register, and the budget (`Regs`) leaves room for exactly one. A 32-bit
  add with both a carry-in and a carry-out looks like it needs two bits: either
  `p + c` or `(p + c) + q` can wrap. The lowering instead accumulates the second
  into the first with a conditional skip, which is only sound because the two
  wraps are mutually exclusive — and that was an argument in a comment until
  this file.

  Everything here is about `BitVec 32` and is decided by bit-blasting, so these
  are statements about the machine's arithmetic, not about a model of it.
-/

import Std.Tactic.BVDecide

namespace Evm.CL.RV32.Carry

/-- `sltu` on a sum against an operand: the hardware's unsigned carry test. -/
abbrev wrapped (sum operand : BitVec 32) : Bool := sum.ult operand

/-- A flag as a bit, which is what the carry register holds. -/
abbrev bit (b : Bool) : BitVec 1 := if b then 1#1 else 0#1

/-- The TRUE carry out of `p + q + c`, computed in 33 bits so it cannot be
    lost: the 33rd bit of the widened sum. -/
abbrev trueCarry (p q c : BitVec 32) : BitVec 1 :=
  ((p.zeroExtend 33) + (q.zeroExtend 33) + (c.zeroExtend 33)).extractLsb' 32 1

/-- The TRUE borrow out of `p - q - c`, likewise. -/
abbrev trueBorrow (p q c : BitVec 32) : BitVec 1 :=
  ((p.zeroExtend 33) - (q.zeroExtend 33) - (c.zeroExtend 33)).extractLsb' 32 1

/-! ## Addition -/

/-- **The two carries cannot both happen.** If `p + c` wraps then `p` is all
    ones and `c = 1`, so the sum is zero and adding `q` cannot wrap. This is
    what licenses `addi carry, carry, 1` after the skip: the register is known
    to be 0 there. -/
theorem add_carries_exclusive (p q c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    (bit (wrapped (p + c) c) &&& bit (wrapped ((p + c) + q) q)) = 0#1 := by
  rcases hc with h | h <;> subst h <;> bv_decide

/-- …and the sum of the two carries is the true 33rd bit of `p + q + c`: what
    the lowering leaves in the carry register is the carry-out. -/
theorem add_carry_out (p q c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    (bit (wrapped (p + c) c) ||| bit (wrapped ((p + c) + q) q)) = trueCarry p q c := by
  rcases hc with h | h <;> subst h <;> bv_decide

/-- The value is the ordinary wrapping sum, whichever order the lowering adds
    in (it adds the carry first, then the operand). -/
theorem add_value (p q c : BitVec 32) : (p + c) + q = p + q + c := by bv_decide

/-! ## The carry-out of an add WITHOUT a carry-in

The lowering measures it against whichever operand survived the write to the
destination — either is correct, which is why the aliasing cases can pick. -/

theorem add_carry_either_operand (p q : BitVec 32) :
    bit (wrapped (p + q) p) = bit (wrapped (p + q) q) := by bv_decide

theorem add_carry_is_the_33rd_bit (p q : BitVec 32) :
    bit (wrapped (p + q) q) = trueCarry p q 0#32 := by bv_decide

/-- Doubling, where the lowering reads the top bit instead (`srli d, p, 31`). -/
theorem double_carry_is_the_top_bit (p : BitVec 32) :
    (p >>> 31) = (if wrapped (p + p) p then 1 else 0) := by bv_decide

/-! ## Subtraction

`sltu` before the write is the borrow; the lowering subtracts the borrow-IN
first so that the single flag register is free to hold the second borrow. -/

/-- **The two borrows cannot both happen.** If `p - c` borrows then `p = 0` and
    `c = 1`, so the difference is all ones and subtracting `q` cannot borrow. -/
theorem sub_borrows_exclusive (p q c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    (bit (wrapped p c) &&& bit (wrapped (p - c) q)) = 0#1 := by
  rcases hc with h | h <;> subst h <;> bv_decide

/-- …so their `or` is the borrow out of `p - q - c`. -/
theorem sub_borrow_out (p q c : BitVec 32) (hc : c = 0#32 ∨ c = 1#32) :
    (bit (wrapped p c) ||| bit (wrapped (p - c) q)) = trueBorrow p q c := by
  rcases hc with h | h <;> subst h <;> bv_decide

theorem sub_value (p q c : BitVec 32) : (p - c) - q = p - q - c := by bv_decide

/-! ## The 64-bit view

What the pair of 32-bit halves means: the lowering's low-then-high sequence is
the 64-bit operation on `hi ++ lo`. -/

/-- A pair is the 64-bit value it denotes. -/
abbrev pair (hi lo : BitVec 32) : BitVec 64 := hi ++ lo

/-- **The two-half add is the 64-bit add.** The low half's carry-out, fed into
    the high half, reconstructs exactly `BitVec 64` addition — which is what
    makes `add64` a lowering of `AsmCore`'s 64-bit `add` rather than an
    approximation of it. -/
theorem pair_add (ah al bh bl : BitVec 32) :
    pair (ah + bh + (if wrapped (al + bl) bl then 1 else 0)) (al + bl)
      = pair ah al + pair bh bl := by
  bv_decide

/-- The same for subtract, with the borrow. -/
theorem pair_sub (ah al bh bl : BitVec 32) :
    pair (ah - bh - (if wrapped al bl then 1 else 0)) (al - bl)
      = pair ah al - pair bh bl := by
  bv_decide

end Evm.CL.RV32.Carry
