/-
  Evm.CL.X86Xfer — a PROVEN liveness/provenance transfer for the lowering
  simulation: `xfer i L p` computes the exit annotation of a data instruction
  from its entry annotation (or `none` when the form has no simulation lemma
  under these operands), and `xfer_sound` turns a successful transfer into the
  `DataSim` obligation of `X86SemCtrl.Ok`. On top of it, `fragB` threads an
  annotation through a straight-line fragment with local labels, and
  `fragB_sound` yields the fragment's `Ok`-transfer — so a program built from
  pieces (such as the region flush) is certified piece by piece with symbolic
  immediates, the registers being concrete.
-/

import Evm.CL.X86SemCtrl

namespace Evm.CL.X86Xfer

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.X86Items Evm.CL.X86Sem Evm.CL.X86SemCtrl

/-! ## The transfer -/

def homed (r : Reg) : Bool := (xreg? r).isSome

/-- The exit annotation of a data instruction, when the lowering is simulated. -/
def xfer (i : AInstr) (L : List Reg) (p : Prov) : Option (List Reg × Prov) :=
  match i with
  | .movImm d _ => if homed d then some (upd L d, p) else none
  | .movzImm d _ => if homed d then some (upd L d, p) else none
  | .movReg d a => if homed d && decide (a ∈ L) then some (upd L d, p) else none
  | .addReg d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))) then some (upd L d, .unknown) else none
  | .orr3 d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))) then some (upd L d, .unknown) else none
  | .and3 d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))) then some (upd L d, .unknown) else none
  | .eor3 d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))) then some (upd L d, .unknown) else none
  | .subReg d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d != b && !clobbers d b)))) then some (upd L d, .unknown) else none
  | .adds d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))) then some (upd L d, .add) else none
  | .subsReg d a b => if homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d != b && !clobbers d b)))) then some (upd L d, .sub) else none
  | .adcs d a b => if p == .add && (homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b))))) then some (upd L d, .add) else none
  | .adc d a b => if p == .add && (homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b))))) then some (upd L d, .unknown) else none
  | .sbcs d a b => if p == .sub && (homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d != b && !clobbers d b))))) then some (upd L d, .sub) else none
  | .sbc d a b => if p == .sub && (homed d && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d != b && !clobbers d b))))) then some (upd L d, .unknown) else none
  | .subsImm d a _ => if homed d && (homed a && decide (a ∈ L)) then some (upd L d, .sub) else none
  | .cmpImm a _ => if homed a && decide (a ∈ L) then some (L, .sub) else none
  | .cmpImmWHex a _ => if homed a && decide (a ∈ L) then some (L, .sub) else none
  | .subsZr a b => if homed a && (decide (a ∈ L) && decide (b ∈ L)) then some (L, .sub) else none
  | .sbcsZr a b => if p == .sub && (decide (a ∈ L) && (decide (b ∈ L) && b != .x14)) then some (kill L .x14, .sub) else none
  | .lsrImm d a _ => if homed d && (homed a && decide (a ∈ L)) then some (upd L d, .unknown) else none
  | .lslImm d a _ => if homed d && (homed a && decide (a ∈ L)) then some (upd L d, .unknown) else none
  | .mulReg d a b => if homed d && (homed a && (homed b && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d b)))))) then some (upd L d, .unknown) else none
  | .addLsl d a b sh => if homed d && (homed a && (homed b && (decide (a ∈ L) && (decide (b ∈ L) && decide (sh ≤ 3))))) then some (upd L d, p) else none
  | .addLsr d a b _ => if d == b && (homed d && (homed a && (decide (a ∈ L) && (decide (d ∈ L) && xreg? a != xreg? d)))) then some (upd L d, .unknown) else none
  | .cselHi d a b => if p == .sub && (homed d && (homed a && (homed b && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d a))))))) then some (upd L d, .sub) else none
  | .csel d a b _ => if p == .sub && (homed d && (homed a && (homed b && (decide (a ∈ L) && (decide (b ∈ L) && (d == a || (d == b || !clobbers d a))))))) then some (upd L d, .sub) else none
  | .cset d _ => if p == .sub && homed d then some (upd L d, .sub) else none
  | .tstImm r _ => if homed r && decide (r ∈ L) then some (L, .logic) else none
  | .rev d a => if homed d && decide (a ∈ L) then some (upd L d, p) else none
  | .mvn d a => if homed d && decide (a ∈ L) then some (upd L d, p) else none
  | .ldrOff d b _ => if homed d && (homed b && decide (b ∈ L)) then some (upd L d, p) else none
  | .ldrBase d b => if homed d && (homed b && decide (b ∈ L)) then some (upd L d, p) else none
  | .ldpOff r1 r2 b _ => if homed r1 && (homed r2 && (homed b && (decide (b ∈ L) && (!clobbers r1 b && r1 != b)))) then some (upd (upd L r1) r2, p) else none
  | .stpOff r1 r2 b _ => if homed r1 && (homed r2 && (homed b && (decide (r1 ∈ L) && (decide (r2 ∈ L) && decide (b ∈ L))))) then some (updStore L, p) else none
  | .strbOff src b _ => if homed src && (homed b && (decide (src ∈ L) && decide (b ∈ L))) then some (updStore L, p) else none
  | .strZr b _ => if homed b && decide (b ∈ L) then some (updStore L, p) else none
  | .ldrbOff d b _ => if homed d && (homed b && decide (b ∈ L)) then some (upd L d, p) else none
  | .ldrbReg d b i => if homed d && (homed b && (homed i && (decide (b ∈ L) && decide (i ∈ L)))) then some (upd L d, p) else none
  | .addSp d _ => if homed d then some (upd L d, p) else none
  | .cmpReg a b => if decide (a ∈ L) && (decide (b ∈ L) && (homed a || (isNos a && homed b))) then some (L, .sub) else none
  | .strOff src b _ =>
      if homed b && (decide (src ∈ L) && decide (b ∈ L)) then
        (if homed src then some (updStore L, p)
         else if isNos src then some (updStore (killHome L (nosStoreTempX b none)), p) else none)
      else none
  | .spSub _ => some (L, .unknown)
  | .spAdd _ => some (L, .unknown)
  | .addImm d a _ =>
      if d == a then (if homed d && decide (d ∈ L) then some (upd L d, .unknown) else none)
      else if homed d && decide (a ∈ L) then
        (if homed a then some (upd L d, p) else if isNos a then some (upd L d, .unknown) else none)
      else none
  | .subImm d a _ =>
      if d == a then (if homed d && decide (d ∈ L) then some (upd L d, .unknown) else none)
      else if homed d && (homed a && decide (a ∈ L)) then some (upd L d, p) else none
  | _ => none

/-! ## Soundness -/

theorem homed_some (r : Reg) (h : homed r = true) : ∃ xr, xreg? r = some xr := by
  simp only [homed, Option.isSome_iff_exists] at h; exact h

theorem nos_some (r : Reg) (h : isNos r = true) : ∃ l, nosLimb r = some l := by
  simp only [isNos, Option.isSome_iff_exists] at h; exact h

theorem ite_some_inv {α : Type} {c : Prop} [Decidable c] {v w : α}
    (h : (if c then some v else none) = some w) : c ∧ v = w := by
  split at h
  · exact ⟨by assumption, Option.some.inj h⟩
  · cases h

theorem ite_eq_some_or {α : Type} {c : Prop} [Decidable c] {x y : Option α} {w : α}
    (h : (if c then x else y) = some w) : (c ∧ x = some w) ∨ (¬c ∧ y = some w) := by
  split at h
  · exact Or.inl ⟨by assumption, h⟩
  · exact Or.inr ⟨by assumption, h⟩

/-- One data instruction: a successful transfer is a `DataSim`. -/
theorem xfer_sound (i : AInstr) (L : List Reg) (p : Prov) (L' : List Reg) (p' : Prov)
    (h : xfer i L p = some (L', p')) :
    AsmRun.ctrl i = none ∧ i ≠ .brCont ∧ DataSim i L p L' p' := by
  cases i with
  | movImm d i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    have hhd := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_movImm L p s x hR d xd hd' i
    exact ⟨_, x', rfl, hx, hR'⟩
  | movzImm d i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    have hhd := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_movzImm L p s x hR d xd hd' i
    exact ⟨_, x', rfl, hx, hR'⟩
  | movReg d a =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_movReg L p s x hR d a xd hd' ha
    exact ⟨_, x', rfl, hx, hR'⟩
  | addReg d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_addReg L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | orr3 d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_orr3 L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | and3 d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_and3 L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | eor3 d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_eor3 L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | subReg d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_subReg L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | adds d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_adds L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | subsReg d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_subsReg L p s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | adcs d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_adcs L s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | adc d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_adc L s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | sbcs d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_sbcs L s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | sbc d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_sbc L s x hR d a b xd hd' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | subsImm d a i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hha, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_subsImm L p s x hR d a xd xa hd' ha' ha i
    exact ⟨_, x', rfl, hx, hR'⟩
  | cmpImm a i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hha, ha⟩ := hc
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_cmpImm L p s x hR a xa ha' ha i
    exact ⟨_, x', rfl, hx, hR'⟩
  | cmpImmWHex a i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hha, ha⟩ := hc
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_cmpImmWHex L p s x hR a xa ha' ha i
    exact ⟨_, x', rfl, hx, hR'⟩
  | subsZr a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hha, ha, hb⟩ := hc
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_subsZr L p s x hR a b xa ha' ha hb
    exact ⟨_, x', rfl, hx, hR'⟩
  | sbcsZr a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hc)
    obtain ⟨hp, ha, hb, hb14⟩ := hc
    subst hp
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_sbcsZr L s x hR a b ha hb hb14
    exact ⟨_, x', rfl, hx, hR'⟩
  | lsrImm d a sh =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hha, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_lsrImm L p s x hR d a xd xa hd' ha' ha sh
    exact ⟨_, x', rfl, hx, hR'⟩
  | lslImm d a sh =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hha, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_lslImm L p s x hR d a xd xa hd' ha' ha sh
    exact ⟨_, x', rfl, hx, hR'⟩
  | mulReg d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhd, hha, hhb, ha, hb, hside⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_mulReg L p s x hR d a b xd xa xb hd' ha' hb' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | addLsl d a b sh =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hha, hhb, ha, hb, hsh⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_addLsl_lea L p s x hR d a b xd xa xb hd' ha' hb' ha hb sh hsh
    exact ⟨_, x', rfl, hx, hR'⟩
  | addLsr d a b sh =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hc)
    obtain ⟨hdb, hhd, hha, ha, hdL, hne⟩ := hc
    subst hdb
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_addLsr_acc L p s x hR d a xd xa hd' ha' (fun e => hne (by rw [ha', hd', e])) ha hdL sh
    exact ⟨_, x', rfl, hx, hR'⟩
  | cselHi d a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, hha, hhb, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_cselHi L s x hR d a b xd xa xb hd' ha' hb' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | csel d a b c =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hp, hhd, hha, hhb, ha, hb, hside⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xa, ha'⟩ := homed_some a hha
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_csel L s x hR d a b c xd xa xb hd' ha' hb' ha hb hside
    exact ⟨_, x', rfl, hx, hR'⟩
  | cset d c =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, beq_iff_eq] at hc)
    obtain ⟨hp, hhd⟩ := hc
    subst hp
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_cset L s x hR d c xd hd'
    exact ⟨_, x', rfl, hx, hR'⟩
  | tstImm r i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhr, hr⟩ := hc
    obtain ⟨xr, hr'⟩ := homed_some r hhr
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_tstImm L p s x hR r xr hr' hr i
    exact ⟨_, x', rfl, hx, hR'⟩
  | rev d a =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_rev L p s x hR d a xd hd' ha
    exact ⟨_, x', rfl, hx, hR'⟩
  | mvn d a =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, ha⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_mvn L p s x hR d a xd hd' ha
    exact ⟨_, x', rfl, hx, hR'⟩
  | ldrOff d b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hhb, hb⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_ldrOff L p s x hR d b xd xb hd' hb' hb o
    exact ⟨_, x', rfl, hx, hR'⟩
  | ldrBase d b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hhb, hb⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_ldrBase L p s x hR d b xd xb hd' hb' hb
    exact ⟨_, x', rfl, hx, hR'⟩
  | ldpOff r1 r2 b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', decide_eq_true_eq] at hc)
    obtain ⟨hhr1, hhr2, hhb, hb, hcl, hne⟩ := hc
    obtain ⟨xr1, hr1'⟩ := homed_some r1 hhr1
    obtain ⟨xr2, hr2'⟩ := homed_some r2 hhr2
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_ldpOff L p s x hR r1 r2 b xr1 xr2 xb hr1' hr2' hb' hb o hcl hne
    exact ⟨_, x', rfl, hx, hR'⟩
  | stpOff r1 r2 b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhr1, hhr2, hhb, hr1, hr2, hb⟩ := hc
    obtain ⟨xr1, hr1'⟩ := homed_some r1 hhr1
    obtain ⟨xr2, hr2'⟩ := homed_some r2 hhr2
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_stpOff L p s x hR r1 r2 b xr1 xr2 xb hr1' hr2' hb' hr1 hr2 hb o
    exact ⟨_, x', rfl, hx, hR'⟩
  | strbOff src b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhsrc, hhb, hs, hb⟩ := hc
    obtain ⟨xsrc, hsrc'⟩ := homed_some src hhsrc
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_strbOff L p s x hR src b xsrc xb hsrc' hb' hs hb o
    exact ⟨_, x', rfl, hx, hR'⟩
  | strZr b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhb, hb⟩ := hc
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_strZr L p s x hR b xb hb' hb o
    exact ⟨_, x', rfl, hx, hR'⟩
  | ldrbOff d b o =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hhb, hb⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_ldrbOff L p s x hR d b xd xb hd' hb' hb o
    exact ⟨_, x', rfl, hx, hR'⟩
  | ldrbReg d b i =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    (try simp only [Bool.and_eq_true, decide_eq_true_eq] at hc)
    obtain ⟨hhd, hhb, hhi, hb, hi⟩ := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    obtain ⟨xi, hi'⟩ := homed_some i hhi
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_ldrbReg L p s x hR d b i xd xb xi hd' hb' hi' hb hi
    exact ⟨_, x', rfl, hx, hR'⟩
  | addSp d n =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    have hhd := hc
    obtain ⟨xd, hd'⟩ := homed_some d hhd
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_addSp L p s x hR d xd hd' n
    exact ⟨_, x', rfl, hx, hR'⟩
  | cmpReg a b =>
    simp only [xfer] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha, hb, hor⟩ := hc
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    rcases hor with hha | ⟨hna, hhb⟩
    · obtain ⟨xa, ha'⟩ := homed_some a hha
      obtain ⟨x', hx, hR'⟩ := sim_cmpReg L p s x hR a b xa ha' ha hb
      exact ⟨_, x', rfl, hx, hR'⟩
    · obtain ⟨la, hla⟩ := nos_some a hna
      obtain ⟨xb, hb'⟩ := homed_some b hhb
      obtain ⟨x', hx, hR'⟩ := sim_cmpReg_nos L p s x hR a b la xb hla hb' ha hb
      exact ⟨_, x', rfl, hx, hR'⟩
  | strOff src b o =>
    simp only [xfer] at h
    obtain ⟨hc, h1⟩ := (ite_eq_some_or h).resolve_right (fun ⟨_, h⟩ => by cases h)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hhb, hs, hb⟩ := hc
    obtain ⟨xb, hb'⟩ := homed_some b hhb
    rcases ite_eq_some_or h1 with ⟨hhs, hv⟩ | ⟨hns, h2⟩
    · cases hv
      obtain ⟨xs, hs'⟩ := homed_some src hhs
      refine ⟨rfl, nofun, fun s x hR => ?_⟩
      obtain ⟨x', hx, hR'⟩ := sim_strOff L p s x hR src b xs xb hs' hb' hs hb o
      exact ⟨_, x', rfl, hx, hR'⟩
    · obtain ⟨hn, hv⟩ := ite_some_inv h2; cases hv
      obtain ⟨ls, hls⟩ := nos_some src hn
      refine ⟨rfl, nofun, fun s x hR => ?_⟩
      obtain ⟨x', hx, hR'⟩ := sim_strOff_nos L p s x hR src b ls xb hls hb' hs hb o
      exact ⟨_, x', rfl, hx, hR'⟩
  | spSub n =>
    simp only [xfer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_spSub L p s x hR n
    exact ⟨_, x', rfl, hx, hR'⟩
  | spAdd n =>
    simp only [xfer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, nofun, fun s x hR => ?_⟩
    obtain ⟨x', hx, hR'⟩ := sim_spAdd L p s x hR n
    exact ⟨_, x', rfl, hx, hR'⟩
  | addImm d a i =>
    simp only [xfer] at h
    rcases ite_eq_some_or h with ⟨hda, h1⟩ | ⟨hda, h1⟩
    · rw [beq_iff_eq] at hda; subst hda
      obtain ⟨hc, hv⟩ := ite_some_inv h1; cases hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hhd, hdL⟩ := hc
      obtain ⟨xd, hd'⟩ := homed_some d hhd
      refine ⟨rfl, nofun, fun s x hR => ?_⟩
      obtain ⟨x', hx, hR'⟩ := sim_addImm_inplace L p s x hR d xd hd' hdL i
      exact ⟨_, x', rfl, hx, hR'⟩
    · rw [beq_iff_eq] at hda
      obtain ⟨hc, h2⟩ := (ite_eq_some_or h1).resolve_right (fun ⟨_, h⟩ => by cases h)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hhd, ha⟩ := hc
      obtain ⟨xd, hd'⟩ := homed_some d hhd
      rcases ite_eq_some_or h2 with ⟨hha, hv⟩ | ⟨hna, h3⟩
      · cases hv
        obtain ⟨xa, ha'⟩ := homed_some a hha
        refine ⟨rfl, nofun, fun s x hR => ?_⟩
        obtain ⟨x', hx, hR'⟩ := sim_addImm_lea L p s x hR d a xd xa hd' ha' ha hda i
        exact ⟨_, x', rfl, hx, hR'⟩
      · obtain ⟨hn, hv⟩ := ite_some_inv h3; cases hv
        obtain ⟨la, hla⟩ := nos_some a hn
        refine ⟨rfl, nofun, fun s x hR => ?_⟩
        obtain ⟨x', hx, hR'⟩ := sim_addImm_nos L p s x hR d a xd la hd' hla ha i
        exact ⟨_, x', rfl, hx, hR'⟩
  | subImm d a i =>
    simp only [xfer] at h
    rcases ite_eq_some_or h with ⟨hda, h1⟩ | ⟨hda, h1⟩
    · rw [beq_iff_eq] at hda; subst hda
      obtain ⟨hc, hv⟩ := ite_some_inv h1; cases hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hhd, hdL⟩ := hc
      obtain ⟨xd, hd'⟩ := homed_some d hhd
      refine ⟨rfl, nofun, fun s x hR => ?_⟩
      obtain ⟨x', hx, hR'⟩ := sim_subImm_inplace L p s x hR d xd hd' hdL i
      exact ⟨_, x', rfl, hx, hR'⟩
    · rw [beq_iff_eq] at hda
      obtain ⟨hc, hv⟩ := ite_some_inv h1; cases hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hhd, hha, ha⟩ := hc
      obtain ⟨xd, hd'⟩ := homed_some d hhd
      obtain ⟨xa, ha'⟩ := homed_some a hha
      refine ⟨rfl, nofun, fun s x hR => ?_⟩
      obtain ⟨x', hx, hR'⟩ := sim_subImm_lea L p s x hR d a xd xa hd' ha' ha hda i
      exact ⟨_, x', rfl, hx, hR'⟩
  | _ => simp [xfer] at h


/-! ## Annotations as a table -/

/-- A label's annotation; labels absent from the table assume nothing. -/
def annOf (tbl : List (String × (List Reg × Prov))) (t : String) : List Reg × Prov :=
  match tbl.find? (fun e => e.1 == t) with
  | some e => e.2
  | none => ([], .unknown)

def provLeB (p q : Prov) : Bool := q == .unknown || q == p

theorem provLeB_sound (p q : Prov) (h : provLeB p q = true) : provLe p q := by
  simpa [provLeB, provLe] using h

theorem provLe_refl (p : Prov) : provLe p p := Or.inr rfl

theorem provLe_trans {p2 p q : Prov} (h1 : provLe p2 p) (h2 : provLe p q) : provLe p2 q := by
  rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact h1

def atB (tbl : List (String × (List Reg × Prov))) (t : String) (L : List Reg) (p : Prov) : Bool :=
  (annOf tbl t).1.all (fun r => decide (r ∈ L)) && provLeB p (annOf tbl t).2

theorem atB_sound (tbl : List (String × (List Reg × Prov))) (t : String) (L : List Reg) (p : Prov)
    (h : atB tbl t L p = true) : At (annOf tbl) t L p := by
  simp only [atB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, provLeB_sound _ _ h.2⟩

def targetB (tbl : List (String × (List Reg × Prov))) (l : String) (L : List Reg) (p : Prov) : Bool :=
  tbl.all (fun e => !(l == e.1 || l == e.1 ++ "f") || atB tbl e.1 L p)

theorem targetB_sound (tbl : List (String × (List Reg × Prov))) (l : String) (L : List Reg) (p : Prov)
    (h : targetB tbl l L p = true) : Target (annOf tbl) l L p := by
  intro t ht
  cases hf : tbl.find? (fun e => e.1 == t) with
  | none =>
    refine ⟨fun r hr => ?_, Or.inl ?_⟩
    · simp [annOf, hf] at hr
    · simp [annOf, hf]
  | some e =>
    have hmem := List.mem_of_find?_eq_some hf
    have het : e.1 = t := by simpa using List.find?_some hf
    have := (List.all_eq_true.mp h) e hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rw [het] at this
    rcases this with hno | hat
    · rw [ht] at hno; cases hno
    · exact atB_sound tbl t L p hat

def condOkB (c : BCond) (p : Prov) : Bool :=
  p == .sub || ((c == .eq || (c == .ne || c == .lt)) && (p == .add || p == .logic))

theorem condOkB_sound (c : BCond) (p : Prov) (h : condOkB c p = true) : condOkP c p := by
  simpa [condOkB, condOkP] using h

theorem condOkP_mono {c : BCond} {p p2 : Prov} (h : condOkP c p) (hp : provLe p2 p) : condOkP c p2 := by
  rcases hp with rfl | rfl
  · rcases h with h | ⟨_, h | h⟩ <;> cases h
  · exact h

theorem at_mono {ann : String → List Reg × Prov} {t : String} {L L2 : List Reg} {p p2 : Prov}
    (h : At ann t L p) (hL : ∀ r ∈ L, r ∈ L2) (hp : provLe p2 p) : At ann t L2 p2 :=
  ⟨fun r hr => hL r (h.1 r hr), provLe_trans hp h.2⟩

theorem target_mono {ann : String → List Reg × Prov} {l : String} {L L2 : List Reg} {p p2 : Prov}
    (h : Target ann l L p) (hL : ∀ r ∈ L, r ∈ L2) (hp : provLe p2 p) : Target ann l L2 p2 :=
  fun t ht => at_mono (h t ht) hL hp

theorem end_mono {Lend L L2 : List Reg} {pend p p2 : Prov}
    (h : Dead L ∨ ((∀ r ∈ Lend, r ∈ L) ∧ provLe p pend)) (hL : ∀ r ∈ L, r ∈ L2) (hp : provLe p2 p) :
    Dead L2 ∨ ((∀ r ∈ Lend, r ∈ L2) ∧ provLe p2 pend) := by
  rcases h with hd | ⟨h1, h2⟩
  · exact Or.inl (hL _ hd)
  · exact Or.inr ⟨fun r hr => hL r (h1 r hr), provLe_trans hp h2⟩

theorem killCall_mono {L L2 : List Reg} (hL : ∀ r ∈ L, r ∈ L2) : ∀ r ∈ killCall L, r ∈ killCall L2 := by
  intro r hr
  simp only [killCall, List.mem_filter] at hr ⊢
  exact ⟨hL r hr.1, hr.2⟩

/-- `Ok` is monotone: a larger entry live set and a more precise provenance. -/
theorem Ok_mono (ann : String → List Reg × Prov) (Lend : List Reg) (pend : Prov) :
    ∀ (prog : List AInstr) (L : List Reg) (p : Prov) (L2 : List Reg) (p2 : Prov),
      Ok ann Lend pend prog L p → (∀ r ∈ L, r ∈ L2) → provLe p2 p → Ok ann Lend pend prog L2 p2
  | [], L, p, L2, p2, h, hL, hp => end_mono h hL hp
  | i :: rest, L, p, L2, p2, h, hL, hp => by
    cases i with
    | ret => exact ⟨end_mono h.1 hL hp, h.2⟩
    | label t => exact ⟨(h.1.imp (fun hd => hL _ hd) (fun ha => at_mono ha hL hp)), h.2⟩
    | bLbl l => exact ⟨target_mono h.1 hL hp, h.2⟩
    | bcLbl c l => exact ⟨condOkP_mono h.1 hp, target_mono h.2.1 hL hp, Ok_mono ann Lend pend rest L p L2 p2 h.2.2 hL hp⟩
    | blsLbl l =>
      obtain ⟨hs, hT, hr⟩ := h
      subst hs
      rcases hp with hp | hp
      · cases hp
      · subst hp
        exact ⟨rfl, target_mono hT hL (provLe_refl _), Ok_mono ann Lend pend rest L .sub L2 .sub hr hL (provLe_refl _)⟩
    | cbzLbl r l =>
      exact ⟨hL r h.1, h.2.1, target_mono h.2.2.1 hL (provLe_refl _),
             Ok_mono ann Lend pend rest L .unknown L2 .unknown h.2.2.2 hL (provLe_refl _)⟩
    | cbnzLbl r l =>
      exact ⟨hL r h.1, h.2.1, target_mono h.2.2.1 hL (provLe_refl _),
             Ok_mono ann Lend pend rest L .unknown L2 .unknown h.2.2.2 hL (provLe_refl _)⟩
    | cbzWLbl r l =>
      exact ⟨hL r h.1, h.2.1, target_mono h.2.2.1 hL (provLe_refl _),
             Ok_mono ann Lend pend rest L .unknown L2 .unknown h.2.2.2 hL (provLe_refl _)⟩
    | cbnzWLbl r l =>
      exact ⟨hL r h.1, h.2.1, target_mono h.2.2.1 hL (provLe_refl _),
             Ok_mono ann Lend pend rest L .unknown L2 .unknown h.2.2.2 hL (provLe_refl _)⟩
    | blSym sym =>
      exact ⟨hL _ h.1, hL _ h.2.1, hL _ h.2.2.1, fun ht => hL _ (h.2.2.2.1 ht),
             Ok_mono ann Lend pend rest _ _ _ _ h.2.2.2.2 (killCall_mono hL) (provLe_refl _)⟩
    | bTramp sym => exact h
    | bcTramp c sym => exact ⟨condOkP_mono h.1 hp, Ok_mono ann Lend pend rest L p L2 p2 h.2 hL hp⟩
    | _ =>
      obtain ⟨hc, hb, L', p', hD, hr⟩ := h
      exact ⟨hc, hb, L', p', fun s x hR => hD s x (relWeaken hR hL hp), hr⟩

/-! ## The fragment checker -/

def deadB (L : List Reg) : Bool := decide (Reg.x5 ∈ L)

/-- One instruction, control forms included. -/
def ctrlB (tbl : List (String × (List Reg × Prov))) (i : AInstr) (L : List Reg) (p : Prov) :
    Option (List Reg × Prov) :=
  match i with
  | .label t => if deadB L || atB tbl t L p then some (annOf tbl t) else none
  | .bcLbl c l => if condOkB c p && targetB tbl l L p then some (L, p) else none
  | .blsLbl l => if p == .sub && targetB tbl l L p then some (L, p) else none
  | .blSym sym =>
      if decide (Reg.x3 ∈ L) && (decide (Reg.x2 ∈ L) && (decide (Reg.x1 ∈ L) && (!ternary sym || decide (Reg.x14 ∈ L))))
      then some (killCall L, .unknown) else none
  | .bTramp _ => some (deadL, .unknown)
  | .bcTramp c _ => if condOkB c p then some (L, p) else none
  | i => xfer i L p

theorem ctrlB_sound (tbl : List (String × (List Reg × Prov))) (Lend : List Reg) (pend : Prov)
    (i : AInstr) (L : List Reg) (p : Prov) (L' : List Reg) (p' : Prov)
    (h : ctrlB tbl i L p = some (L', p')) (rest : List AInstr)
    (hOk : Ok (annOf tbl) Lend pend rest L' p') : Ok (annOf tbl) Lend pend (i :: rest) L p := by
  cases i with
  | label t =>
    simp only [ctrlB] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h
    refine ⟨?_, ?_⟩
    · simp only [Bool.or_eq_true, deadB, decide_eq_true_eq] at hc
      rcases hc with hd | ha
      · exact Or.inl hd
      · exact Or.inr (atB_sound tbl t L p ha)
    · rw [hv]; exact hOk
  | bcLbl c l =>
    simp only [ctrlB] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    simp only [Bool.and_eq_true] at hc
    exact ⟨condOkB_sound c p hc.1, targetB_sound tbl l L p hc.2, hOk⟩
  | blsLbl l =>
    simp only [ctrlB] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1, targetB_sound tbl l L p hc.2, hOk⟩
  | blSym sym =>
    simp only [ctrlB] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1, fun ht => hc.2.2.2.resolve_left (by simp [ht]), hOk⟩
  | bTramp sym =>
    simp only [ctrlB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hOk
  | bcTramp c sym =>
    simp only [ctrlB] at h
    obtain ⟨hc, hv⟩ := ite_some_inv h; cases hv
    exact ⟨condOkB_sound c p hc, hOk⟩
  | _ =>
    simp only [ctrlB] at h
    first
      | (obtain ⟨hc, hb, hD⟩ := xfer_sound _ _ _ _ _ h
         exact ⟨hc, hb, L', p', hD, hOk⟩)
      | (simp [xfer] at h)

/-- A straight-line fragment with local labels. -/
def fragB (tbl : List (String × (List Reg × Prov))) : List AInstr → List Reg → Prov → Option (List Reg × Prov)
  | [], L, p => some (L, p)
  | i :: rest, L, p =>
    match ctrlB tbl i L p with
    | some (L', p') => fragB tbl rest L' p'
    | none => none

theorem fragB_sound (tbl : List (String × (List Reg × Prov))) (Lend : List Reg) (pend : Prov) :
    ∀ (prog : List AInstr) (L : List Reg) (p : Prov) (L' : List Reg) (p' : Prov),
      fragB tbl prog L p = some (L', p') → ∀ rest, Ok (annOf tbl) Lend pend rest L' p' →
        Ok (annOf tbl) Lend pend (prog ++ rest) L p
  | [], L, p, L', p', h, rest, hOk => by
    simp only [fragB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hOk
  | i :: rest0, L, p, L', p', h, rest, hOk => by
    cases hm : ctrlB tbl i L p with
    | none => simp [fragB, hm] at h
    | some lp =>
      obtain ⟨L1, p1⟩ := lp
      have h' : fragB tbl rest0 L1 p1 = some (L', p') := by
        simp only [fragB] at h; rw [hm] at h; exact h
      rw [List.cons_append]
      exact ctrlB_sound tbl Lend pend i L p L1 p1 hm _ (fragB_sound tbl Lend pend rest0 L1 p1 L' p' h' rest hOk)

/-! ## Fragments as transfers -/

/-- `prog` takes annotation `(L, p)` to `(L', p')`: whatever is `Ok` after it
    from `(L', p')` is `Ok` with it from `(L, p)`. -/
def Frag (tbl : List (String × (List Reg × Prov))) (Lend : List Reg) (pend : Prov) (prog : List AInstr)
    (L : List Reg) (p : Prov) (L' : List Reg) (p' : Prov) : Prop :=
  ∀ rest, Ok (annOf tbl) Lend pend rest L' p' → Ok (annOf tbl) Lend pend (prog ++ rest) L p

namespace Frag

variable {tbl : List (String × (List Reg × Prov))} {Lend : List Reg} {pend : Prov}

theorem nil (L : List Reg) (p : Prov) : Frag tbl Lend pend [] L p L p := fun _ h => by simpa using h

theorem append {p1 p2 : List AInstr} {L : List Reg} {p : Prov} {L1 : List Reg} {q1 : Prov} {L2 : List Reg} {q2 : Prov}
    (h1 : Frag tbl Lend pend p1 L p L1 q1) (h2 : Frag tbl Lend pend p2 L1 q1 L2 q2) :
    Frag tbl Lend pend (p1 ++ p2) L p L2 q2 :=
  fun rest h => by rw [List.append_assoc]; exact h1 _ (h2 _ h)

theorem mono {prog : List AInstr} {L : List Reg} {p : Prov} {L' : List Reg} {p' : Prov}
    (h : Frag tbl Lend pend prog L p L' p') {L2 : List Reg} {p2 : Prov} {L2' : List Reg} {p2' : Prov}
    (hL : ∀ r ∈ L, r ∈ L2) (hp : provLe p2 p) (hL' : ∀ r ∈ L2', r ∈ L') (hp' : provLe p' p2') :
    Frag tbl Lend pend prog L2 p2 L2' p2' :=
  fun rest hOk => Ok_mono _ _ _ _ _ _ _ _ (h rest (Ok_mono _ _ _ _ _ _ _ _ hOk hL' hp')) hL hp

theorem ofB {prog : List AInstr} {L : List Reg} {p : Prov} {L' : List Reg} {p' : Prov}
    (h : fragB tbl prog L p = some (L', p')) : Frag tbl Lend pend prog L p L' p' :=
  fragB_sound tbl Lend pend prog L p L' p' h

/-- The workhorse: compute the exit annotation, keep only what the continuation needs. -/
theorem ofB_sup {prog : List AInstr} {L : List Reg} {p : Prov} {L' : List Reg} {p' : Prov} (Lo : List Reg)
    (h : fragB tbl prog L p = some (L', p')) (hsup : ∀ r ∈ Lo, r ∈ L') :
    Frag tbl Lend pend prog L p Lo .unknown :=
  (ofB h).mono (fun _ h => h) (provLe_refl _) hsup (Or.inl rfl)

theorem flatMap {α : Type} (f : α → List AInstr) (L : List Reg) (p : Prov) :
    ∀ (l : List α), (∀ a ∈ l, Frag tbl Lend pend (f a) L p L p) → Frag tbl Lend pend (l.flatMap f) L p L p
  | [], _ => by simpa [List.flatMap_nil] using nil L p
  | a :: l, h => by
    rw [List.flatMap_cons]
    exact append (h a (by simp)) (flatMap f L p l (fun b hb => h b (by simp [hb])))

theorem ite {c : Prop} [Decidable c] {p1 p2 : List AInstr} {L : List Reg} {p : Prov} {L' : List Reg} {p' : Prov}
    (h1 : c → Frag tbl Lend pend p1 L p L' p') (h2 : ¬c → Frag tbl Lend pend p2 L p L' p') :
    Frag tbl Lend pend (if c then p1 else p2) L p L' p' := by
  split
  · exact h1 (by assumption)
  · exact h2 (by assumption)

end Frag

theorem Ok_of_Frag {tbl : List (String × (List Reg × Prov))} {Lend : List Reg} {pend : Prov} {prog : List AInstr}
    {L : List Reg} {p : Prov} {L' : List Reg} {p' : Prov}
    (h : Frag tbl Lend pend prog L p L' p') (hend : Dead L' ∨ ((∀ r ∈ Lend, r ∈ L') ∧ provLe p' pend)) :
    Ok (annOf tbl) Lend pend prog L p := by
  have := h [] hend
  simpa using this

/-! ## Labels: `LabelsOk` for a fragment, from its own labels and the continuation's -/

def labelsOf : List AInstr → List String
  | [] => []
  | .label t :: rest => t :: labelsOf rest
  | _ :: rest => labelsOf rest

def found (l : String) (ls : List String) : Bool := ls.any (fun t => l == t || l == t ++ "f")

theorem found_append (l : String) (a b : List String) : found l (a ++ b) = (found l a || found l b) := by
  simp [found, List.any_append]

theorem labelsOf_append : ∀ (p q : List AInstr), labelsOf (p ++ q) = labelsOf p ++ labelsOf q
  | [], q => rfl
  | i :: rest, q => by
    cases i <;> simp only [List.cons_append, labelsOf, labelsOf_append rest q]

theorem skipTo_nil_iff (l : String) : ∀ (xs : List AInstr), AsmRun.skipTo l xs = [] ↔ found l (labelsOf xs) = false
  | [] => by simp [AsmRun.skipTo, found, labelsOf]
  | i :: rest => by
    cases i with
    | label t =>
      simp only [AsmRun.skipTo, labelsOf, found, List.any_cons]
      split
      · rename_i hc; simp [hc]
      · rename_i hc; simp only [Bool.not_eq_true] at hc
        rw [hc, Bool.false_or]
        exact skipTo_nil_iff l rest
    | _ => simp only [AsmRun.skipTo, labelsOf]; exact skipTo_nil_iff l rest

/-- The per-instruction label obligation, given the labels defined after it. -/
def lokStep (i : AInstr) (ls : List String) : Bool :=
  match i with
  | .bLbl l | .bcLbl _ l | .blsLbl l | .cbzLbl _ l | .cbnzLbl _ l | .cbzWLbl _ l | .cbnzWLbl _ l => found l ls
  | .bTramp sym | .bcTramp _ sym => !found (trampLabel sym) ls
  | _ => true

def lokB : List AInstr → List String → Bool
  | [], _ => true
  | i :: rest, ext => lokStep i (labelsOf rest ++ ext) && lokB rest ext

theorem lokB_append : ∀ (p q : List AInstr) (ext : List String),
    lokB (p ++ q) ext = (lokB p (labelsOf q ++ ext) && lokB q ext)
  | [], q, ext => by simp [lokB]
  | i :: rest, q, ext => by
    simp only [List.cons_append, lokB, lokB_append rest q ext, labelsOf_append, List.append_assoc, Bool.and_assoc]

theorem lokB_sound : ∀ (p q : List AInstr), lokB p (labelsOf q) = true → LabelsOk q → LabelsOk (p ++ q)
  | [], q, _, hq => by simpa using hq
  | i :: rest, q, h, hq => by
    simp only [lokB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [← labelsOf_append] at h1
    rw [List.cons_append]
    refine ⟨?_, lokB_sound rest q h2 hq⟩
    cases i <;> simp only [lokStep] at h1 <;> (try dsimp only) <;> first
      | trivial
      | (intro hnil; rw [skipTo_nil_iff] at hnil; rw [hnil] at h1; cases h1)
      | (rw [skipTo_nil_iff]; simpa using h1)

theorem LabelsOk_of_lokB (p : List AInstr) (h : lokB p [] = true) : LabelsOk p := by
  simpa using lokB_sound p [] (by simpa [labelsOf] using h) trivial

end Evm.CL.X86Xfer
