/-
  Evm.CL.X86Lower — lowering `AInstr` to x86-64, and the two-operand problem.

  Stage 2 of #238. `AInstr`'s vocabulary is already ISA-neutral — three-operand
  RISC forms — but x86-64's arithmetic is TWO-OPERAND and destructive (`add dst,
  src` means `dst += src`), and it has no shifted-operand add. So the lowering
  is not a plain register substitution for every form; some need expanding, and
  an expansion that needs a temporary is a problem, because `Evm.CL.Pressure`
  showed the gadgets already peak at exactly the five scratch registers
  `Evm.CL.Target` set aside.

  This module settles whether that is a problem in practice, by classifying each
  three-operand form by what its lowering costs:

    inPlace        the destination already IS the left operand: one insn
    inPlaceInv     a conditional select whose destination is the TRUE operand:
                   one insn, with the condition INVERTED (see below)
    commuted       destination is the right operand of a commutative op: swap
    leaScale       shifted add with shift ≤ 3: `lea d, [a + b*2^sh]`, which is
                   non-destructive and costs no temporary
    shiftThenAdd   destination IS the shifted operand: shift in place, then add
    movThenOp      destination distinct from both: materialise into the
                   destination itself — still no temporary
    needsTemp      the shift cannot be done in place without destroying the
                   other operand: WOULD need a sixth scratch register

  Result: `no_gadget_needs_a_temp` — every three-operand instruction in the
  gadget set lands in a no-temp class, so the lowering is substitution plus
  local expansion and the five-register pool survives.

  Two things this classification taught me, both corrections to my first guess:

   * `csel d, a, b, hi` with `d = a` is NOT a temporary case. x86's `cmov`
     overwrites its destination when the condition holds, so "keep a, else take
     b" is `cmov<inverted> d, b` — one instruction. My first rule called it
     `needsTemp`, and the gadget set contains exactly one instance
     (`cselHi x0 x0 x14`), which is how the error surfaced.
   * The expansion is a constant factor, not a multiple — see
     `Evm.CL.Lowering.expansion_under_a_quarter`, which counts the emitted text
     rather than estimating it.
-/

import Evm.CL.Pressure

namespace Evm.CL.X86Lower

open Evm.CL.AsmCore Evm.CL.Pressure

/-- What an x86-64 lowering costs for one three-operand form. -/
inductive Form where
  | inPlace | inPlaceInv | commuted | leaScale | shiftThenAdd | movThenOp | needsTemp
  deriving Repr, DecidableEq

/-- `lea [base + index*scale]` allows scale 1, 2, 4, 8 — shifts 0 to 3. -/
def leaScaleOk (sh : Nat) : Bool := sh ≤ 3

/-- Classify. `none` for forms x86 has one-to-one (loads, stores, compares,
    branches, moves, single-operand shifts). -/
def form : AInstr → Option Form
  -- commutative, unshifted: destination on either side is one instruction
  | .addReg d a b => some (if d == a then .inPlace else if d == b then .commuted else .movThenOp)
  | .adds d a b   => some (if d == a then .inPlace else if d == b then .commuted else .movThenOp)
  | .orr3 d a b   => some (if d == a then .inPlace else if d == b then .commuted else .movThenOp)
  | .mulReg d a b => some (if d == a then .inPlace else if d == b then .commuted else .movThenOp)
  -- NOT commutative: `sub d, a, b` with d = b computes b - a on x86 unless it
  -- is expanded, which is the classic mistranslation.
  | .subReg d a b  => some (if d == a then .inPlace else if d == b then .needsTemp else .movThenOp)
  | .subsReg d a b => some (if d == a then .inPlace else if d == b then .needsTemp else .movThenOp)
  -- shifted adds: d = a + (b << sh) or a + (b >> sh)
  | .addLsl d a b sh =>
      some (if leaScaleOk sh then .leaScale
            else if d == b then .shiftThenAdd
            else if d != a then .movThenOp
            else .needsTemp)
  | .addLsl5 d a b =>
      some (if d == b then .shiftThenAdd
            else if d != a then .movThenOp
            else .needsTemp)
  | .addLsr d a b _ =>
      some (if d == b then .shiftThenAdd
            else if d != a then .movThenOp
            else .needsTemp)
  -- cmov: one instruction whichever operand the destination is, because the
  -- condition can be inverted.
  | .cselHi d a b =>
      some (if d == b then .inPlace else if d == a then .inPlaceInv else .movThenOp)
  | _ => none

/-- Classes that cost no extra register. -/
def noTemp : Form → Bool
  | .needsTemp => false
  | _ => true

/-- **Every three-operand instruction in the gadget set lowers without a
    temporary**, so `Evm.CL.Pressure`'s five-register budget survives the
    lowering and no spill slot is needed. -/
theorem no_gadget_needs_a_temp :
    gadgetSet.all (fun p => p.all (fun it =>
      match form it with
      | some f => noTemp f
      | none => true)) = true := by
  native_decide

/-- The forms that actually occur — so the x86 encoder has five cases to
    implement, and a sixth showing up is a visible change here. -/
theorem forms_in_use :
    (gadgetSet.flatMap (fun p => p.filterMap form)).eraseDups
      = [.movThenOp, .shiftThenAdd, .leaScale, .inPlace, .inPlaceInv] := by
  native_decide

/-! ## The mistranslations this classification exists to prevent -/

/-- `sub d, a, b` with `d = b`: x86's `sub rd, ra` computes `b - a`, the
    operands backwards. Classified `needsTemp`, absent from the gadgets, and
    named here because it is representable. -/
theorem sub_reversed_needs_a_temp :
    form (.subReg .x14 .x15 .x14) = some .needsTemp := by native_decide

/-- A shifted add whose destination is the LEFT operand with a shift too big for
    `lea`: the shift cannot be done in place without destroying the right
    operand. The single form that would force a sixth scratch register. -/
theorem big_shift_into_left_operand_needs_a_temp :
    form (.addLsl .x14 .x14 .x15 5) = some .needsTemp := by native_decide

/-- The same instruction with the destination on the RIGHT shifts in place and
    costs nothing extra — which is how the gadgets' `addLsl5` and `addLsr`
    instances happen to be written. -/
theorem shift_into_right_operand_is_free :
    form (.addLsl5 .x14 .x24 .x14) = some .shiftThenAdd ∧
    form (.addLsr .x16 .x14 .x16 9) = some .shiftThenAdd := by native_decide

/-- A small shift is a single `lea`, non-destructive, whatever the aliasing —
    including `d = a = b`, which is `lea d, [d + d*2]`. -/
theorem small_shift_is_one_lea :
    form (.addLsl .x16 .x16 .x14 1) = some .leaScale ∧
    form (.addLsl .x16 .x16 .x16 1) = some .leaScale := by native_decide

/-- **And the one I got wrong.** `csel d, a, b, hi` with `d = a` is one `cmov`
    with the condition inverted — "keep a when hi" is "take b when NOT hi" —
    not a temporary case. The gadget set has exactly one such instruction, which
    is how my first (pessimistic) rule was caught. -/
theorem csel_into_true_operand_inverts :
    form (.cselHi .x0 .x0 .x14) = some .inPlaceInv := by native_decide

theorem csel_into_false_operand_is_direct :
    form (.cselHi .x16 .x15 .x16) = some .inPlace := by native_decide

/-! ## Instruction counts

The size question — how much bigger is the x86 code — used to be answered here
by a per-form estimate. `Evm.CL.Lowering` now emits the real text and
`scripts/verify-x86-emit.sh` assembles it, so the counts live there, measured
rather than modelled. (The estimate said 317 against a true 310: it charged one
instruction for each label, which emits none, and one for each `ldpOff`,
`cbzLbl` and register-moving shift, which emit two.) -/

end Evm.CL.X86Lower
