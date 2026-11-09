/-
  Evm.CL.ARM64.SstoreGasDenote — what the five `_eita_sstore_gas_*` routines
  compute, and the proof that each is its fork's `sstoreGas`.

  Stage 1 of #238 (docs/x86-64-backend.md), third piece. `ARM64.SstoreGas`
  probes its CONSTANTS out of the spec, so a schedule change re-emits without a
  hand edit — but the branch tree and, above all, the REFUND CLAMP DISCIPLINE
  around them are hand-written asm. There are four different disciplines across
  five forks:

    legacy    unconditional add (never negative)
    eip1283   ONE signed sum, clamped at 0 once    (two's-complement in x9)
    eip2200   sequential adjustments, each clamped (`subs`+`csel lo` per step)
    berlin    add first, then ONE clamped subtract (refundAdd/refundSub in x7/x9)
    london    same shape, EIP-3529 constants

  Getting a clamp wrong does not fail loudly: it silently changes the refund,
  hence the gas the tx actually paid, hence the state root — and only at a slot
  whose history hits that branch. These are exactly the lines a port to a second
  ISA mistranslates, so each discipline is now a theorem rather than a comment.

  ## What this module covers, and what it does not

  The routines are: a PROLOGUE that folds limbs into six predicates, then a
  BRANCH TREE over those predicates. This module proves the tree — given the six
  predicates, the cost/refund pair is the fork's `sstoreGas`, for every refund
  counter, every cold flag and every (original, current, new).

  The prologue's limb folds (`isZero` = OR-fold + `cset eq`, `isEq` = XOR/OR-fold
  + `cset eq`) are proven in `PredFold`, and `SstoreGasSem` executes the emitted
  `AInstr` programs under `AsmSem` and shows they store exactly these plans —
  so the chain is program → plan (there) → spec (here), with nothing between
  the instruction list and `sstoreGas` left to inspection.
-/

import Evm.CL.ARM64
import Evm.CL.ARM64.PredFold
import Mathlib.Tactic.SplitIfs
import Evm.Frontier.Vm.Instructions.Storage
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Berlin.Vm.Instructions.Storage
import Evm.London.Vm.Effect

namespace Evm.CL.ARM64.SstoreGasDenote

/-! ## Spec probes — the constants the emitter materialises.

Each is the spec function evaluated at a distinguished `(original, current,
new)` point; 0/1/2/3 are distinct zero/nonzero markers. These definitions are
the ones `ARM64.SstoreGas` emits from, so the numbers in the asm and the numbers
in the theorems below are the same numbers. -/

private def frontierP (cur new_ : Evm.U256) : Nat × Nat :=
  Evm.Frontier.Vm.Instructions.sstoreGas 0 cur new_

private def eip1283P (refund : Nat) (o c n : Evm.U256) : Nat × Nat :=
  Evm.Constantinople.Vm.Instructions.sstoreGas refund o c n

private def eip2200P (refund : Nat) (o c n : Evm.U256) : Nat × Nat :=
  Evm.Istanbul.Vm.Instructions.sstoreGas refund o c n

private def berlinP (refund : Nat) (cold : Bool) (o c n : Evm.U256) : Nat × Nat :=
  Evm.Berlin.Vm.Instructions.Storage.sstoreGas refund cold o c n

private def londonP (refund : Nat) (cold : Bool) (o c n : Evm.U256) : Nat × Nat :=
  Evm.London.Vm.Effect.sstoreGas refund cold o c n

/-- `simp` normalises `(0 : Evm.U256)` to `0#256` inside `ite` conditions, so a
    `by_cases h : c = 0` hypothesis stops matching the goal. Bridging the two
    spellings as a simp lemma keeps the case analysis usable. -/
private theorem u256_zero_numeral : (0 : Evm.U256) = 0#256 := rfl

/-- One-directional orientation fix: the Berlin/London specs test
    `original = 0` AFTER a substitution has already replaced `original`, so the
    goal carries `0#256 = c` while the case hypothesis says `c = 0#256`. Plain
    `eq_comm` in a simp set loops; this direction terminates. -/
private theorem zero_eq_comm (x : Evm.U256) : (0#256 = x) ↔ (x = 0#256) := eq_comm

/-- `Int.toNat` of a cast sum/difference, so the clamps reduce to ℕ arithmetic
    that `omega` can finish. -/
private theorem toNat_cast_add (r k : Nat) : ((r : Int) + (k : Int)).toNat = r + k := by omega
private theorem toNat_cast_sub (r k : Nat) : ((r : Int) - (k : Int)).toNat = r - k := by omega

/-- The spec's single clamp, `if refund + δ < 0 then 0 else (refund + δ).toNat`,
    reduced to ℕ for a non-negative and for a negative δ. These two are what let
    `omega` finish each branch; without them the clamp is an opaque atom. -/
private theorem clamp_nonneg (r : Nat) (c : Int) (h : 0 ≤ c) :
    (if ((r : Int) + c) < 0 then 0 else ((r : Int) + c).toNat) = r + c.toNat := by
  have hn : ¬ ((r : Int) + c < 0) := by omega
  simp only [hn, ite_false]; omega

/-- The δ = 0 shape, which `simp only` leaves as `↑r + 0`. -/
private theorem clamp_zero (r : Nat) :
    (if ((r : Int) + 0) < 0 then 0 else ((r : Int) + 0).toNat) = r := by
  have hn : ¬ ((r : Int) + 0 < 0) := by omega
  simp only [hn, ite_false]; omega

private theorem clamp_negative (r : Nat) (c : Int) (h : c < 0) :
    (if ((r : Int) + c) < 0 then 0 else ((r : Int) + c).toNat) = r - (-c).toNat := by
  by_cases hb : (r : Int) + c < 0
  · simp only [hb, ite_true]; omega
  · simp only [hb, ite_false]; omega

/-! ### Legacy (Frontier..Byzantium, Petersburg) -/

def setCost     : Nat := (frontierP 0 1).1
def resetCost   : Nat := (frontierP 1 2).1
def clearRefund : Nat := (frontierP 1 0).2

/-- `_eita_sstore_gas_legacy`: cost from `(curZero ∧ ¬newZero)`, refund an
    unconditional add gated on `(¬curZero ∧ newZero)`. No clamp exists on this
    path — the asm's `add x17, x1, x8` cannot go negative, and the theorem says
    that is right. -/
def planLegacy (refund : Nat) (curZero newZero : Bool) : Nat × Nat :=
  ( if curZero && !newZero then setCost else resetCost,
    refund + (if !curZero && newZero then clearRefund else 0) )

theorem legacy_eq_spec (refund : Nat) (c n : Evm.U256) :
    planLegacy refund (decide (c = 0)) (decide (n = 0))
      = Evm.Frontier.Vm.Instructions.sstoreGas refund c n := by
  unfold planLegacy Evm.Frontier.Vm.Instructions.sstoreGas
  by_cases hc : c = 0 <;> by_cases hn : n = 0 <;>
    simp_all [setCost, resetCost, clearRefund, frontierP,
              Evm.Frontier.Vm.Instructions.sstoreGas]

/-! ### EIP-1283 (Constantinople) — one signed sum, clamped once

Factored into three pieces so each proof is small: the COST tree, the positive
accumulation (`add`), the negative one (`sub`). The asm keeps a single signed
delta in x9 and clamps once; `add − sub` is that delta, and `clampBridge` below
is what says a single ℕ clamp of `refund + add − sub` is the same number as the
spec's single ℤ clamp of `refund + δ`. -/

def noopCost1283   : Nat := (eip1283P 0 1 1 1).1
def setCost1283    : Nat := (eip1283P 0 0 0 1).1
def resetCost1283  : Nat := (eip1283P 0 1 1 2).1
def dirtyCost1283  : Nat := (eip1283P 0 1 2 3).1
def clearRef1283   : Nat := (eip1283P 0 1 1 0).2
def resetZeroR1283 : Nat := (eip1283P 0 0 1 0).2
def resetNzR1283   : Nat := (eip1283P 0 1 2 1).2

/-- Pin the probed constants ONCE. Without this every case below re-evaluates
    `sstoreGas` on u256 literals in the kernel — slow, and at 64 cases deep
    enough to blow the recursion limit. -/
theorem noopCost1283_eq   : noopCost1283   = 200   := by native_decide
theorem setCost1283_eq    : setCost1283    = 20000 := by native_decide
theorem resetCost1283_eq  : resetCost1283  = 5000  := by native_decide
theorem dirtyCost1283_eq  : dirtyCost1283  = 200   := by native_decide
theorem clearRef1283_eq   : clearRef1283   = 15000 := by native_decide
theorem resetZeroR1283_eq : resetZeroR1283 = 19800 := by native_decide
theorem resetNzR1283_eq   : resetNzR1283   = 4800  := by native_decide

/-- The cost tree: `cbz x14` (curEqNew), then `cbz x13` (origEqCur), then
    `cbz x10` (origZero). -/
def cost1283 (origZero origEqCur curEqNew : Bool) : Nat :=
  if curEqNew then noopCost1283
  else if origEqCur then (if origZero then setCost1283 else resetCost1283)
  else dirtyCost1283

/-- Everything the asm ADDS to x9 (and, on the clean branch, to x17). -/
def add1283 (origZero newZero origEqCur curEqNew origEqNew : Bool) : Nat :=
  if curEqNew then 0
  else if origEqCur then (if origZero then 0 else (if newZero then clearRef1283 else 0))
  else (if !origZero && newZero then clearRef1283 else 0)
     + (if origEqNew then (if origZero then resetZeroR1283 else resetNzR1283) else 0)

/-- Everything the asm SUBTRACTS from x9 — only the cancel-a-previous-clear rule
    on the dirty branch. -/
def sub1283 (origZero curZero origEqCur curEqNew : Bool) : Nat :=
  if curEqNew then 0
  else if origEqCur then 0
  else (if !origZero && curZero then clearRef1283 else 0)

/-- `_eita_sstore_gas_eip1283`: one clamp, at the end. -/
def planEip1283 (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  let a := add1283 origZero newZero origEqCur curEqNew origEqNew
  let b := sub1283 origZero curZero origEqCur curEqNew
  (cost1283 origZero origEqCur curEqNew, if refund + a < b then 0 else refund + a - b)

/-- The spec's signed delta, as a function of the six predicates. -/
def delta1283 (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Int :=
  if curEqNew then 0
  else if origEqCur then
    (if origZero then 0 else (if newZero then (clearRef1283 : Int) else 0))
  else
    (if !origZero then
       (if curZero then -(clearRef1283 : Int) else 0)
       + (if newZero then (clearRef1283 : Int) else 0)
     else 0)
    + (if origEqNew then
         (if origZero then (resetZeroR1283 : Int) else (resetNzR1283 : Int))
       else 0)

/-- The spec as a function of the six predicates (a transcription of
    `Constantinople.sstoreGas`'s tree with its conditions abstracted). -/
def specB1283 (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  let d := delta1283 origZero curZero newZero origEqCur curEqNew origEqNew
  (cost1283 origZero origEqCur curEqNew,
   if (refund : Int) + d < 0 then 0 else ((refund : Int) + d).toNat)

/-- A single ℕ clamp of `r + a − b` is the single ℤ clamp of `r + (a − b)`.
    This is the ONLY arithmetic fact the refund proof needs; keeping it separate
    is what stops the 64-way case split from carrying clamp reasoning. -/
theorem clampBridge (r a b : Nat) :
    (if (r : Int) + ((a : Int) - (b : Int)) < 0 then 0
     else ((r : Int) + ((a : Int) - (b : Int))).toNat)
      = (if r + a < b then 0 else r + a - b) := by
  by_cases h : (r : Int) + ((a : Int) - (b : Int)) < 0
  · simp only [h, ite_true]
    have : r + a < b := by omega
    simp only [this, ite_true]
  · simp only [h, ite_false]
    have : ¬ (r + a < b) := by omega
    simp only [this, ite_false]
    omega

/-- The signed delta IS `add − sub`: 64 closed cases, no refund counter, no
    clamp — the asm's two accumulators against the spec's one delta. -/
theorem delta1283_eq (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) :
    delta1283 origZero curZero newZero origEqCur curEqNew origEqNew
      = (add1283 origZero newZero origEqCur curEqNew origEqNew : Int)
        - (sub1283 origZero curZero origEqCur curEqNew : Int) := by
  unfold delta1283 add1283 sub1283
  simp only [clearRef1283_eq, resetZeroR1283_eq, resetNzR1283_eq]
  cases origZero <;> cases curZero <;> cases newZero <;>
    cases origEqCur <;> cases curEqNew <;> cases origEqNew <;> decide

/-- The tree, for every predicate combination and every refund counter. -/
theorem plan1283_eq_specB (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) :
    planEip1283 refund origZero curZero newZero origEqCur curEqNew origEqNew
      = specB1283 refund origZero curZero newZero origEqCur curEqNew origEqNew := by
  simp only [planEip1283, specB1283, delta1283_eq, clampBridge]

/-- The spec depends on `(original, current, new)` ONLY through the six
    predicates: all the u256 reasoning, in one case split with the constants
    left opaque (so the kernel never evaluates a BitVec comparison). -/
theorem spec1283_factors (refund : Nat) (o c n : Evm.U256) :
    Evm.Constantinople.Vm.Instructions.sstoreGas refund o c n
      = specB1283 refund (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
                         (decide (o = c)) (decide (c = n)) (decide (o = n)) := by
  unfold Evm.Constantinople.Vm.Instructions.sstoreGas specB1283 cost1283 delta1283
  simp only [noopCost1283_eq, setCost1283_eq, resetCost1283_eq, dirtyCost1283_eq,
             clearRef1283_eq, resetZeroR1283_eq, resetNzR1283_eq,
             Evm.Constantinople.Vm.Gas.sLoadGas, Evm.Frontier.Vm.Gas.sSet,
             Evm.Frontier.Vm.Gas.sReset, Evm.Frontier.Vm.Gas.sClearRefund,
             Evm.Constantinople.Vm.Gas.sSetRefund, Evm.Constantinople.Vm.Gas.sResetRefund]
  by_cases hcn : c = n <;> by_cases hoc : o = c <;> by_cases ho : o = 0 <;>
    by_cases hc : c = 0 <;> by_cases hn : n = 0 <;> by_cases hon : o = n <;>
    simp_all

/-- **`_eita_sstore_gas_eip1283` is `Constantinople.sstoreGas`.** -/
theorem eip1283_eq_spec (refund : Nat) (o c n : Evm.U256) :
    planEip1283 refund (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
                       (decide (o = c)) (decide (c = n)) (decide (o = n))
      = Evm.Constantinople.Vm.Instructions.sstoreGas refund o c n := by
  rw [spec1283_factors, plan1283_eq_specB]


/-! ### EIP-2200 (Istanbul, MuirGlacier) — sequential, each step clamped

The difference from EIP-1283 is the whole point of this section: three refund
adjustments applied IN ORDER, each clamped at 0 on its own
(`subs x9,x17,x8 ; csel x17,xzr,x9,lo` for the middle one), which is NOT the
same number as summing the deltas and clamping once when the counter
transiently hits 0. -/

def sloadCost2200  : Nat := (eip2200P 0 1 1 1).1
def setCost2200    : Nat := (eip2200P 0 0 0 1).1
def resetCost2200  : Nat := (eip2200P 0 1 1 2).1
def clearRef2200   : Nat := (eip2200P 0 1 1 0).2
def resetZeroR2200 : Nat := (eip2200P 0 0 1 0).2
def resetNzR2200   : Nat := (eip2200P 0 1 2 1).2

theorem sloadCost2200_eq  : sloadCost2200  = 800   := by native_decide
theorem setCost2200_eq    : setCost2200    = 20000 := by native_decide
theorem resetCost2200_eq  : resetCost2200  = 5000  := by native_decide
theorem clearRef2200_eq   : clearRef2200   = 15000 := by native_decide
theorem resetZeroR2200_eq : resetZeroR2200 = 19200 := by native_decide
theorem resetNzR2200_eq   : resetNzR2200   = 4200  := by native_decide

def cost2200 (origZero origEqCur curEqNew : Bool) : Nat :=
  if curEqNew then sloadCost2200
  else if origEqCur then (if origZero then setCost2200 else resetCost2200)
  else sloadCost2200

/-- `adjustRefund` with a non-negative delta is an `add`; with a negative one it
    is the saturating `subs`+`csel lo`. Two lemmas, and the sequential
    discipline reduces to ℕ. -/
theorem adjust_nonneg (n k : Nat) :
    Evm.Istanbul.Vm.Instructions.adjustRefund n (k : Int) = n + k := by
  simp only [Evm.Istanbul.Vm.Instructions.adjustRefund]
  split_ifs <;> omega

theorem adjust_neg (n k : Nat) :
    Evm.Istanbul.Vm.Instructions.adjustRefund n (-(k : Int)) = n - k := by
  simp only [Evm.Istanbul.Vm.Instructions.adjustRefund]
  split_ifs <;> omega

/-- The refund chain with its constants as PARAMETERS. Keeping them variable is
    what makes the proof cheap: nothing can unfold a probed constant back into a
    `sstoreGas` application on u256 literals, which is what the kernel choked on
    when they were baked in. -/
def chainPlan (refund cl rz rn : Nat) (origZero curZero newZero origEqNew : Bool) : Nat :=
  let r1 := refund + (if !origZero && !curZero && newZero then cl else 0)
  let r2 := if !origZero && curZero then r1 - cl else r1
  r2 + (if origEqNew then (if origZero then rz else rn) else 0)

/-- The same chain as the spec writes it: three `adjustRefund`s, in order. -/
def chainSpec (refund cl rz rn : Nat) (origZero curZero newZero origEqNew : Bool) : Nat :=
  let r1 := if !origZero && !curZero && newZero then
              Evm.Istanbul.Vm.Instructions.adjustRefund refund (cl : Int) else refund
  let r2 := if !origZero && curZero then
              Evm.Istanbul.Vm.Instructions.adjustRefund r1 (-(cl : Int)) else r1
  if origEqNew then
    (if origZero then Evm.Istanbul.Vm.Instructions.adjustRefund r2 (rz : Int)
     else Evm.Istanbul.Vm.Instructions.adjustRefund r2 (rn : Int))
  else r2

/-- **The sequential clamping is implemented exactly**: `add`, then saturating
    `subs`+`csel lo`, then `add` — 16 cases over the predicates the chain
    branches on, for arbitrary constants and an arbitrary counter. -/
theorem chain_eq (refund cl rz rn : Nat) (origZero curZero newZero origEqNew : Bool) :
    chainPlan refund cl rz rn origZero curZero newZero origEqNew
      = chainSpec refund cl rz rn origZero curZero newZero origEqNew := by
  simp only [chainPlan, chainSpec, adjust_nonneg, adjust_neg]
  cases origZero <;> cases curZero <;> cases newZero <;> cases origEqNew <;> simp

/-- `_eita_sstore_gas_eip2200`. -/
def planEip2200 (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  (cost2200 origZero origEqCur curEqNew,
   if curEqNew then refund
   else chainPlan refund clearRef2200 resetZeroR2200 resetNzR2200
          origZero curZero newZero origEqNew)

/-- The spec as a function of the six predicates. -/
def specB2200 (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  (cost2200 origZero origEqCur curEqNew,
   if curEqNew then refund
   else chainSpec refund clearRef2200 resetZeroR2200 resetNzR2200
          origZero curZero newZero origEqNew)

/-- The tree, for every predicate combination and every refund counter. -/
theorem plan2200_eq_specB (refund : Nat)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) :
    planEip2200 refund origZero curZero newZero origEqCur curEqNew origEqNew
      = specB2200 refund origZero curZero newZero origEqCur curEqNew origEqNew := by
  simp only [planEip2200, specB2200, chain_eq]

set_option maxRecDepth 8000 in
/-- The spec depends on `(original, current, new)` only through the six
    predicates. -/
theorem spec2200_factors (refund : Nat) (o c n : Evm.U256) :
    Evm.Istanbul.Vm.Instructions.sstoreGas refund o c n
      = specB2200 refund (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
                         (decide (o = c)) (decide (c = n)) (decide (o = n)) := by
  unfold Evm.Istanbul.Vm.Instructions.sstoreGas specB2200 cost2200
  simp only [sloadCost2200_eq, setCost2200_eq, resetCost2200_eq, clearRef2200_eq,
             resetZeroR2200_eq, resetNzR2200_eq, Evm.Istanbul.Vm.Gas.sLoad,
             Evm.Istanbul.Vm.Gas.sstoreSet, Evm.Istanbul.Vm.Gas.sstoreReset,
             Evm.Istanbul.Vm.Gas.sstoreClearRefund]
  by_cases hcn : c = n <;> by_cases hoc : o = c <;> by_cases ho : o = 0 <;>
    by_cases hc : c = 0 <;> by_cases hn : n = 0 <;> by_cases hon : o = n <;>
    simp_all [chainSpec]

/-- **`_eita_sstore_gas_eip2200` is `Istanbul.sstoreGas`** — with the sequential
    clamping, not EIP-1283's single one. -/
theorem eip2200_eq_spec (refund : Nat) (o c n : Evm.U256) :
    planEip2200 refund (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
                       (decide (o = c)) (decide (c = n)) (decide (o = n))
      = Evm.Istanbul.Vm.Instructions.sstoreGas refund o c n := by
  rw [spec2200_factors, plan2200_eq_specB]

/-- The two disciplines really are different numbers: a counter of 10 000, a
    dirty slot cleared then restored. Clamping once keeps the excursion;
    clamping per step loses it. This is why the fork lane cannot share one
    routine. -/
example :
    (planEip1283 10000 false true true false false true).2
      ≠ (planEip2200 10000 false true true false false true).2 := by
  native_decide


/-! ### Berlin / London (EIP-2929, EIP-3529) — add, then ONE clamped subtract

`ARM64.SstoreGas.eip2929Code` is emitted TWICE from one body, parameterised over
the fork's plan function, so this section is parameterised the same way: one
`plan2929` over a record of constants, one theorem, two instantiations. The
constants stay variables in the tree proof for the reason the 2200 section
learned the hard way — a probed constant that the kernel can unfold turns 64
cases into a BitVec evaluation storm.

The emitter probes the SUBTRACTED clear refund indirectly, as
`big - (p big false 1 0 2).2` with `big = 1000000`, because the subtraction is
only observable through the clamp. `subClear_eq` below checks that this recovers
the schedule's clears-refund exactly — the kind of step where an off-by-one in
the probe would silently halve a refund. -/

structure Consts2929 where
  warm       : Nat
  set        : Nat
  reset      : Nat
  coldSurch  : Nat
  clearRef   : Nat
  resetZeroA : Nat
  resetNzA   : Nat
  deriving DecidableEq, Repr

/-- `_eita_sstore_gas_{berlin,london}`: the EIP-2200 tree with a cold surcharge
    on the cost and `refundAdd`/`refundSub` accumulated in x7/x9, folded by one
    clamped subtraction (`add x17,x1,x7 ; subs x8,x17,x9 ; csel x17,xzr,x8,lo`).

    Note the dirty branch's `curZero` arm does NOT also test `newZero`: the asm
    jumps straight to the origEqNew check. Sound because `curZero ∧ newZero`
    would mean `current = new`, which the first test already took. -/
def plan2929 (k : Consts2929) (refund : Nat) (cold : Bool)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  let base :=
    if curEqNew then k.warm
    else if origEqCur then (if origZero then k.set else k.reset)
    else k.warm
  let add :=
    if curEqNew then 0
    else if origEqCur then (if origZero then 0 else if newZero then k.clearRef else 0)
    else (if !origZero && !curZero && newZero then k.clearRef else 0)
       + (if origEqNew then (if origZero then k.resetZeroA else k.resetNzA) else 0)
  let sub :=
    if curEqNew then 0
    else if origEqCur then 0
    else (if !origZero && curZero then k.clearRef else 0)
  let r1 := refund + add
  (base + (if cold then k.coldSurch else 0), if r1 < sub then 0 else r1 - sub)

/-- The spec's own `(cost, refundAdd, refundSub)` triple, abstracted over the
    predicates — Berlin's `eip2200` and London's `eip2200London` are the same
    tree with one constant swapped, so one definition serves both. -/
def specB2929 (k : Consts2929) (refund : Nat) (cold : Bool)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) : Nat × Nat :=
  let t : Nat × Nat × Nat :=
    if curEqNew then (k.warm, 0, 0)
    else if origEqCur then
      (if origZero then (k.set, 0, 0)
       else (k.reset, (if newZero then k.clearRef else 0), 0))
    else
      let cs : Nat × Nat :=
        if !origZero then
          (if curZero then (0, k.clearRef)
           else if newZero then (k.clearRef, 0)
           else (0, 0))
        else (0, 0)
      let addReset := if origEqNew then (if origZero then k.resetZeroA else k.resetNzA) else 0
      (k.warm, cs.1 + addReset, cs.2)
  let r1 := refund + t.2.1
  (t.1 + (if cold then k.coldSurch else 0), if r1 < t.2.2 then 0 else r1 - t.2.2)

/-- The tree, for arbitrary constants, arbitrary counter, both cold flags and
    every predicate combination. -/
theorem plan2929_eq_specB (k : Consts2929) (refund : Nat) (cold : Bool)
    (origZero curZero newZero origEqCur curEqNew origEqNew : Bool) :
    plan2929 k refund cold origZero curZero newZero origEqCur curEqNew origEqNew
      = specB2929 k refund cold origZero curZero newZero origEqCur curEqNew origEqNew := by
  simp only [plan2929, specB2929]
  cases origZero <;> cases curZero <;> cases newZero <;>
    cases origEqCur <;> cases curEqNew <;> cases origEqNew <;> simp

/-! #### Berlin -/

def berlinConsts : Consts2929 :=
  { warm       := (berlinP 0 false 1 1 1).1
    set        := (berlinP 0 false 0 0 1).1
    reset      := (berlinP 0 false 1 1 2).1
    coldSurch  := (berlinP 0 true 1 1 1).1 - (berlinP 0 false 1 1 1).1
    clearRef   := (berlinP 0 false 1 1 0).2
    resetZeroA := (berlinP 0 false 0 1 0).2
    resetNzA   := (berlinP 0 false 1 2 1).2 }

theorem berlin_warm_eq       : berlinConsts.warm       = 100   := by native_decide
theorem berlin_set_eq        : berlinConsts.set        = 20000 := by native_decide
theorem berlin_reset_eq      : berlinConsts.reset      = 2900  := by native_decide
theorem berlin_coldSurch_eq  : berlinConsts.coldSurch  = 2100  := by native_decide
theorem berlin_clearRef_eq   : berlinConsts.clearRef   = 15000 := by native_decide
theorem berlin_resetZeroA_eq : berlinConsts.resetZeroA = 19900 := by native_decide
theorem berlin_resetNzA_eq   : berlinConsts.resetNzA   = 2800  := by native_decide

/-- The INDIRECT probe for the subtracted clear refund recovers the same
    constant as the direct one — `big - (p big false 1 0 2).2 = clearRef`. -/
theorem berlin_subClear_eq :
    1000000 - (berlinP 1000000 false 1 0 2).2 = berlinConsts.clearRef := by native_decide

theorem berlin_factors (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    Evm.Berlin.Vm.Instructions.Storage.sstoreGas refund cold o c n
      = specB2929 berlinConsts refund cold
          (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
          (decide (o = c)) (decide (c = n)) (decide (o = n)) := by
  unfold Evm.Berlin.Vm.Instructions.Storage.sstoreGas
          Evm.Berlin.Vm.Instructions.Storage.cost
          Evm.Berlin.Vm.Instructions.Storage.eip2200 specB2929
  simp only [berlin_warm_eq, berlin_set_eq, berlin_reset_eq, berlin_coldSurch_eq,
             berlin_clearRef_eq, berlin_resetZeroA_eq, berlin_resetNzA_eq,
             Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.sstoreColdSurcharge,
             Evm.Berlin.Vm.Gas.coldSload,
             Evm.Berlin.Vm.Instructions.Storage.sstoreSet,
             Evm.Berlin.Vm.Instructions.Storage.sstoreReset,
             Evm.Berlin.Vm.Instructions.Storage.sstoreClearsRefund]
  -- The specs test `new = current`, `current = original`, `new = original`;
  -- the predicates are the other orientation. One-directional iffs, so simp can
  -- line them up without looping (plain `eq_comm` in a simp set does loop).
  have ecn : (n = c) ↔ (c = n) := eq_comm
  have eoc : (c = o) ↔ (o = c) := eq_comm
  have eon : (n = o) ↔ (o = n) := eq_comm
  by_cases hcn : c = n <;> by_cases hoc : o = c <;> by_cases ho : o = 0 <;>
    by_cases hc : c = 0 <;> by_cases hn : n = 0 <;> by_cases hon : o = n <;>
    simp_all [zero_eq_comm]

/-- **`_eita_sstore_gas_berlin` is `Berlin.sstoreGas`.** -/
theorem berlin_eq_spec (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    plan2929 berlinConsts refund cold
      (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
      (decide (o = c)) (decide (c = n)) (decide (o = n))
      = Evm.Berlin.Vm.Instructions.Storage.sstoreGas refund cold o c n := by
  rw [berlin_factors, plan2929_eq_specB]

/-! #### London (EIP-3529: the clears refund drops 15000 → 4800) -/

def londonConsts : Consts2929 :=
  { warm       := (londonP 0 false 1 1 1).1
    set        := (londonP 0 false 0 0 1).1
    reset      := (londonP 0 false 1 1 2).1
    coldSurch  := (londonP 0 true 1 1 1).1 - (londonP 0 false 1 1 1).1
    clearRef   := (londonP 0 false 1 1 0).2
    resetZeroA := (londonP 0 false 0 1 0).2
    resetNzA   := (londonP 0 false 1 2 1).2 }

theorem london_clearRef_eq   : londonConsts.clearRef   = 4800  := by native_decide
theorem london_warm_eq       : londonConsts.warm       = 100   := by native_decide
theorem london_set_eq        : londonConsts.set        = 20000 := by native_decide
theorem london_reset_eq      : londonConsts.reset      = 2900  := by native_decide
theorem london_coldSurch_eq  : londonConsts.coldSurch  = 2100  := by native_decide
theorem london_resetZeroA_eq : londonConsts.resetZeroA = 19900 := by native_decide
theorem london_resetNzA_eq   : londonConsts.resetNzA   = 2800  := by native_decide

theorem london_subClear_eq :
    1000000 - (londonP 1000000 false 1 0 2).2 = londonConsts.clearRef := by native_decide

/-- EIP-3529 is exactly the one substitution, and nothing else moved. -/
theorem london_is_berlin_with_lower_clears :
    londonConsts = { berlinConsts with clearRef := 4800 } := by native_decide

theorem london_factors (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    Evm.London.Vm.Effect.sstoreGas refund cold o c n
      = specB2929 londonConsts refund cold
          (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
          (decide (o = c)) (decide (c = n)) (decide (o = n)) := by
  unfold Evm.London.Vm.Effect.sstoreGas Evm.London.Vm.Effect.eip2200London specB2929
  simp only [london_warm_eq, london_set_eq, london_reset_eq, london_coldSurch_eq,
             london_clearRef_eq, london_resetZeroA_eq, london_resetNzA_eq,
             Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.sstoreColdSurcharge,
             Evm.Berlin.Vm.Gas.coldSload,
             Evm.Berlin.Vm.Instructions.Storage.sstoreSet,
             Evm.Berlin.Vm.Instructions.Storage.sstoreReset,
             Evm.London.Vm.Gas.sStoreClearRefund]
  -- The specs test `new = current`, `current = original`, `new = original`;
  -- the predicates are the other orientation. One-directional iffs, so simp can
  -- line them up without looping (plain `eq_comm` in a simp set does loop).
  have ecn : (n = c) ↔ (c = n) := eq_comm
  have eoc : (c = o) ↔ (o = c) := eq_comm
  have eon : (n = o) ↔ (o = n) := eq_comm
  by_cases hcn : c = n <;> by_cases hoc : o = c <;> by_cases ho : o = 0 <;>
    by_cases hc : c = 0 <;> by_cases hn : n = 0 <;> by_cases hon : o = n <;>
    simp_all [zero_eq_comm]

/-- **`_eita_sstore_gas_london` is `London.sstoreGas`.** -/
theorem london_eq_spec (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    plan2929 londonConsts refund cold
      (decide (o = 0)) (decide (c = 0)) (decide (n = 0))
      (decide (o = c)) (decide (c = n)) (decide (o = n))
      = Evm.London.Vm.Effect.sstoreGas refund cold o c n := by
  rw [london_factors, plan2929_eq_specB]


/-! ## End to end: prologue + tree = spec

The theorems above take the six predicates as given; `Evm.CL.ARM64.PredFold`
proves the prologue's limb folds produce exactly those. Composing them states
what the emitted routine actually does, from the three u256 pointers it is
handed to the `(cost, refund)` pair it stores — with no step taken on trust. -/

open Evm.CL.ARM64.PredFold (isZeroFold isEqFold isZeroFold_eq isEqFold_eq)

theorem legacy_routine (refund : Nat) (c n : Evm.U256) :
    planLegacy refund (isZeroFold c) (isZeroFold n)
      = Evm.Frontier.Vm.Instructions.sstoreGas refund c n := by
  rw [isZeroFold_eq, isZeroFold_eq, legacy_eq_spec]

theorem eip1283_routine (refund : Nat) (o c n : Evm.U256) :
    planEip1283 refund (isZeroFold o) (isZeroFold c) (isZeroFold n)
                       (isEqFold o c) (isEqFold c n) (isEqFold o n)
      = Evm.Constantinople.Vm.Instructions.sstoreGas refund o c n := by
  rw [isZeroFold_eq, isZeroFold_eq, isZeroFold_eq, isEqFold_eq, isEqFold_eq,
      isEqFold_eq, eip1283_eq_spec]

theorem eip2200_routine (refund : Nat) (o c n : Evm.U256) :
    planEip2200 refund (isZeroFold o) (isZeroFold c) (isZeroFold n)
                       (isEqFold o c) (isEqFold c n) (isEqFold o n)
      = Evm.Istanbul.Vm.Instructions.sstoreGas refund o c n := by
  rw [isZeroFold_eq, isZeroFold_eq, isZeroFold_eq, isEqFold_eq, isEqFold_eq,
      isEqFold_eq, eip2200_eq_spec]

theorem berlin_routine (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    plan2929 berlinConsts refund cold
      (isZeroFold o) (isZeroFold c) (isZeroFold n)
      (isEqFold o c) (isEqFold c n) (isEqFold o n)
      = Evm.Berlin.Vm.Instructions.Storage.sstoreGas refund cold o c n := by
  rw [isZeroFold_eq, isZeroFold_eq, isZeroFold_eq, isEqFold_eq, isEqFold_eq,
      isEqFold_eq, berlin_eq_spec]

theorem london_routine (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    plan2929 londonConsts refund cold
      (isZeroFold o) (isZeroFold c) (isZeroFold n)
      (isEqFold o c) (isEqFold c n) (isEqFold o n)
      = Evm.London.Vm.Effect.sstoreGas refund cold o c n := by
  rw [isZeroFold_eq, isZeroFold_eq, isZeroFold_eq, isEqFold_eq, isEqFold_eq,
      isEqFold_eq, london_eq_spec]

end Evm.CL.ARM64.SstoreGasDenote
