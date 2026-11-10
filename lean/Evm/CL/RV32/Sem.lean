/-
  Evm.CL.RV32.Sem — an rv32 machine semantics for the instructions the lowering
  emits, and the first proofs about its synthesised sequences.

  The counterpart of `AsmSem` (ARM64) and `X86Sem` (x86-64), with one
  structural difference that is the reason the rv32 lowering needs proving at
  all: **this machine has no flags.** ARM64's `Flags` and x86-64's `XFlags` are
  part of their state; here the carry is an ordinary register, produced by
  `sltu` and consumed by a branch. So a sequence like `adcs` is not a
  substitution of one instruction for another — it is a small program whose
  correctness is a claim about 32-bit arithmetic, and `RV32.Carry` is where
  that claim is discharged.

  Fragments, not routines: a lowered `AInstr` can branch forward to a label
  inside itself (the conditional skip in the carry sequences) or out of the
  fragment entirely (`_eita_oog`), so `exec` reports which.
-/

import Evm.CL.RV32.Asm
import Evm.CL.RV32.Carry

namespace Evm.CL.RV32.Sem

open Evm.CL.RV32.Asm Evm.CL.RV32.Carry

/-! ## The machine -/

/-- 32 registers of 32 bits and byte-addressed memory. No flags. -/
structure RS where
  regs : RvReg → BitVec 32
  mem  : BitVec 32 → BitVec 8

/-- `x0` reads as zero. The lowering leans on this: it is the high half of
    every 32-bit role (`Regs`), so a pointer's upper word is free. -/
def RS.get (s : RS) (r : RvReg) : BitVec 32 := if r = 0 then 0 else s.regs r

/-- …and writes to `x0` are discarded, which is what makes storing the high
    half of a 32-bit role a no-op rather than a corruption. -/
def RS.set (s : RS) (r : RvReg) (v : BitVec 32) : RS :=
  if r = 0 then s else { s with regs := fun r' => if r' = r then v else s.regs r' }

def ld32 (m : BitVec 32 → BitVec 8) (a : BitVec 32) : BitVec 32 :=
  (m (a + 3)) ++ (m (a + 2)) ++ (m (a + 1)) ++ (m a)

def st32 (m : BitVec 32 → BitVec 8) (a : BitVec 32) (v : BitVec 32) :
    BitVec 32 → BitVec 8 :=
  fun x =>
    if x = a then v.extractLsb' 0 8
    else if x = a + 1 then v.extractLsb' 8 8
    else if x = a + 2 then v.extractLsb' 16 8
    else if x = a + 3 then v.extractLsb' 24 8
    else m x

def RS.store32 (s : RS) (a v : BitVec 32) : RS := { s with mem := st32 s.mem a v }
def RS.store8 (s : RS) (a : BitVec 32) (v : BitVec 8) : RS :=
  { s with mem := fun x => if x = a then v else s.mem x }

def ofInt (i : Int) : BitVec 32 := BitVec.ofInt 32 i

/-- Where a fragment goes next. -/
inductive Outcome where
  | next   (s : RS)
  | branch (s : RS) (target : String)

/-! ## One instruction -/

def step (s : RS) : RvInsn → Option Outcome
  | .add d a b   => some (.next (s.set d (s.get a + s.get b)))
  | .sub d a b   => some (.next (s.set d (s.get a - s.get b)))
  | .orr d a b   => some (.next (s.set d (s.get a ||| s.get b)))
  | .andr d a b  => some (.next (s.set d (s.get a &&& s.get b)))
  | .xorr d a b  => some (.next (s.set d (s.get a ^^^ s.get b)))
  | .sltu d a b  => some (.next (s.set d (if (s.get a).ult (s.get b) then 1 else 0)))
  | .mul d a b   => some (.next (s.set d (s.get a * s.get b)))
  | .mulhu d a b =>
      some (.next (s.set d
        (((s.get a).zeroExtend 64 * (s.get b).zeroExtend 64).extractLsb' 32 32)))
  | .addi d a i  => some (.next (s.set d (s.get a + ofInt i)))
  | .sltiu d a i => some (.next (s.set d (if (s.get a).ult (BitVec.ofNat 32 i) then 1 else 0)))
  | .slli d a sh => some (.next (s.set d (s.get a <<< sh)))
  | .srli d a sh => some (.next (s.set d (s.get a >>> sh)))
  | .li d i      => some (.next (s.set d (ofInt i)))
  | .mv d a      => some (.next (s.set d (s.get a)))
  | .notr d a    => some (.next (s.set d (~~~ s.get a)))
  | .lw d o b    => some (.next (s.set d (ld32 s.mem (s.get b + ofInt o))))
  | .sw x o b    => some (.next (s.store32 (s.get b + ofInt o) (s.get x)))
  | .lbu d o b   => some (.next (s.set d ((s.mem (s.get b + ofInt o)).zeroExtend 32)))
  | .sb x o b    => some (.next (s.store8 (s.get b + ofInt o) ((s.get x).extractLsb' 0 8)))
  | .beqz a t    => some (if s.get a = 0 then .branch s t else .next s)
  | .bnez a t    => some (if s.get a ≠ 0 then .branch s t else .next s)
  | .beq a b t   => some (if s.get a = s.get b then .branch s t else .next s)
  | .bne a b t   => some (if s.get a ≠ s.get b then .branch s t else .next s)
  | .bltu a b t  => some (if (s.get a).ult (s.get b) then .branch s t else .next s)
  | .bgeu a b t  => some (if (s.get a).ult (s.get b) then .next s else .branch s t)
  | .blt a b t   => some (if (s.get a).slt (s.get b) then .branch s t else .next s)
  | .bge a b t   => some (if (s.get a).slt (s.get b) then .next s else .branch s t)
  | .j t         => some (.branch s t)
  -- leaving the fragment: a call or a return is the host's business, as the
  -- helper oracle is on the ARM side (`AsmRun.Helpers`)
  | .call _ | .jalr _ | .jr _ | .ret => none

/-! ## A fragment -/

/-- The items after a label, if the fragment defines it later on. -/
def seek (l : String) : List RvItem → Option (List RvItem)
  | [] => none
  | .label l' :: rest => if l' == l then some rest else seek l rest
  | _ :: rest => seek l rest

/-- Run a fragment: `some (s, none)` fell off the end, `some (s, some t)` left
    for `t`, `none` hit an unmodelled instruction or a marker. Fuel bounds the
    forward jumps; a lowered instruction's own labels are few. -/
def exec : Nat → List RvItem → RS → Option (RS × Option String)
  | _, [], s => some (s, none)
  | 0, _, _ => none
  | fuel + 1, it :: rest, s =>
      match it with
      | .label _ => exec fuel rest s
      | .unlowered _ => none
      | .insn i =>
          match step s i with
          | none => none
          | some (.next s') => exec fuel rest s'
          | some (.branch s' t) =>
              match seek t rest with
              | some rest' => exec fuel rest' s'
              | none => some (s', some t)


/-! ## Register bookkeeping -/

@[simp] theorem get_set_same (s : RS) (r : RvReg) (v : BitVec 32) (h : r ≠ 0) :
    (s.set r v).get r = v := by
  simp [RS.set, RS.get, h]

@[simp] theorem get_set_other (s : RS) (r r' : RvReg) (v : BitVec 32) (h : r' ≠ r) :
    (s.set r v).get r' = s.get r' := by
  unfold RS.set RS.get
  by_cases h0 : r = 0 <;> simp [h0, h]

/-! ## The carry sequences, proved on the machine

`Lower.addc32` with both a carry-in and a carry-out emits five instructions and
a label. This says what they compute — the claim `RV32.Carry` supplies the
arithmetic for, now tied to the machine that executes it. -/

/-- The emitted sequence, as items. (`Lower` prints exactly this text; the
    conversion of the printer to this type is form-by-form work in progress.) -/
def addc32I (lbl : String) (D P Q C : RvReg) : List RvItem :=
  [ .insn (.add D P C), .insn (.sltu C D C), .insn (.add D D Q),
    .insn (.bgeu D Q lbl), .insn (.addi C C 1), .label lbl ]

/-- What the lowering leaves in the carry register. -/
def carryOf (p q c : BitVec 32) : BitVec 32 :=
  (bit (wrapped (p + c) c) ||| bit (wrapped ((p + c) + q) q)).zeroExtend 32

/-- **The 32-bit add with carry-in and carry-out is correct**, with the carry
    in one register: the destination holds `p + q + c` and the carry register
    holds the true carry out. The conditional skip accumulates the second carry
    into the first, which is sound exactly because the two are mutually
    exclusive (`Carry.add_carries_exclusive`). -/
theorem addc32I_correct (lbl : String) (D P Q C : RvReg)
    (hD0 : D ≠ 0) (hC0 : C ≠ 0) (hDC : D ≠ C) (hDQ : D ≠ Q) (hQC : Q ≠ C)
    (s : RS) (hc : (s.get C).ule 1#32 = true) :
    (exec 8 (addc32I lbl D P Q C) s).map (fun r => (r.1.get D, r.1.get C, r.2))
      = some (s.get P + s.get Q + s.get C,
              carryOf (s.get P) (s.get Q) (s.get C), none) := by
  have hCD : C ≠ D := fun h => hDC h.symm
  have hQD : Q ≠ D := fun h => hDQ h.symm
  have hCQ : C ≠ Q := fun h => hQC h.symm
  -- the skip's condition must be resolved before the `Outcome` match can
  -- reduce, so split on it first; `hc` stays a hypothesis (it is in the
  -- BitVec fragment, so the decision procedure uses it directly — substituting
  -- it instead would rewrite the branch condition out from under `hw`)
  by_cases hw : (s.get P + s.get C + s.get Q).ult (s.get Q) = true
  · simp [addc32I, exec, step, seek, hw, get_set_same, get_set_other,
          hD0, hC0, hDC, hDQ, hQC, hCD, hQD, hCQ, carryOf, bit, wrapped, ofInt]
    bv_decide
  · simp only [Bool.not_eq_true] at hw
    simp [addc32I, exec, step, seek, hw, get_set_same, get_set_other,
          hD0, hC0, hDC, hDQ, hQC, hCD, hQD, hCQ, carryOf, bit, wrapped, ofInt]
    bv_decide

end Evm.CL.RV32.Sem
