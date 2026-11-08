import Evm.CL.OpInstrs
import Evm.CL.AsmRunMem

namespace Evm.CL.CacheSound

open Evm.CL.AsmCore Evm.CL.OpInstrs Evm.CL.AsmRun
open Evm.CL.AsmSem (subFlags bcHolds)

/-- The `AsmRun.step` forms that write memory. -/
def storeForm : AInstr → Bool
  | .strOff .. | .strBase .. | .stpOff .. | .strZr .. | .strbOff .. | .strbBase .. | .strbReg ..
  | .stpFpLr => true
  | _ => false

set_option maxHeartbeats 4000000 in
/-- **`defs` is the register write set of the semantics**: every instruction
    `AsmRun.step` models leaves every register outside `defs i` alone. -/
theorem step_regs (m m' : RS) (i : AInstr) (h : AsmRun.step m i = some m') :
    ∀ r, r ∉ defs i → m'.regs r = m.regs r := by
  cases i <;> simp_all [AsmRun.step, AsmSem.step, defs, toRM, RS.set, RS.withFlags, RS.withSp,
    RS.store64, RS.store8, AsmSem.RM.set, AsmSem.RM.withFlags] <;> (try (obtain ⟨rfl⟩ := h)) <;>
    (try simp_all)

set_option maxHeartbeats 4000000 in
/-- …and one that is not a store leaves the memory alone. -/
theorem step_mem (m m' : RS) (i : AInstr) (h : AsmRun.step m i = some m') (hs : storeForm i = false) :
    m'.mem = m.mem := by
  cases i <;> simp_all [AsmRun.step, AsmSem.step, storeForm, toRM, RS.set, RS.withFlags, RS.withSp,
    AsmSem.RM.set, AsmSem.RM.withFlags] <;> (try (obtain ⟨rfl⟩ := h)) <;> (try simp_all)

/-! ## The abstract state, observed through `rv` / `mv` -/

theorem find_filter_ne {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List (α × β)) (r r' : α) :
    (l.filter (·.1 != r)).find? (·.1 == r') = if r' = r then none else l.find? (·.1 == r') := by
  induction l with
  | nil => split <;> rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hx : a = r
    · subst hx
      by_cases h : r' = a
      · subst h; simp [ih]
      · have : (a == r') = false := by simp; intro e; exact h e.symm
        simp [ih, h, this]
    · by_cases h : r' = r
      · subst h; have : (a == r') = false := by simp [hx]
        simp [hx, ih, this]
      · simp [hx, ih, h, List.find?_cons]

@[simp] theorem rv_x23 (s : CS) : s.rv .x23 = some (.idx s.off) := by simp [CS.rv]

theorem rv_setR (s : CS) (r r' : Reg) (v : Option CV) (h : r' ≠ .x23) :
    (s.setR r v).rv r' = if r' = r then v else s.rv r' := by
  have h' : (r' == .x23) = false := by simp [h]
  simp only [CS.rv, CS.setR, h', Bool.false_eq_true, if_false]
  cases v with
  | none => simp only [List.nil_append, find_filter_ne]; split <;> simp
  | some v =>
    simp only [List.singleton_append, List.find?_cons]
    by_cases e : r' = r
    · subst e; simp
    · have : (r == r') = false := by simp; exact fun x => e x.symm
      simp only [this, if_false, find_filter_ne, e]

@[simp] theorem setR_off (s : CS) (r : Reg) (v : Option CV) : (s.setR r v).off = s.off := rfl
@[simp] theorem setR_lt (s : CS) (r : Reg) (v : Option CV) : (s.setR r v).lt = s.lt := rfl
@[simp] theorem setR_fl (s : CS) (r : Reg) (v : Option CV) : (s.setR r v).fl = s.fl := rfl
@[simp] theorem setR_gen (s : CS) (r : Reg) (v : Option CV) : (s.setR r v).gen = s.gen := rfl
@[simp] theorem setR_mem (s : CS) (r : Reg) (v : Option CV) : (s.setR r v).mem = s.mem := rfl
@[simp] theorem setM_off (s : CS) (c : Int) (l : Nat) (v : CV) : (s.setM c l v).off = s.off := rfl
@[simp] theorem setM_lt (s : CS) (c : Int) (l : Nat) (v : CV) : (s.setM c l v).lt = s.lt := rfl
@[simp] theorem setM_fl (s : CS) (c : Int) (l : Nat) (v : CV) : (s.setM c l v).fl = s.fl := rfl
@[simp] theorem setM_gen (s : CS) (c : Int) (l : Nat) (v : CV) : (s.setM c l v).gen = s.gen := rfl
@[simp] theorem setM_regs (s : CS) (c : Int) (l : Nat) (v : CV) : (s.setM c l v).regs = s.regs := rfl

theorem mv_setR (s : CS) (r : Reg) (v : Option CV) (c : Int) (l : Nat) :
    (s.setR r v).mv c l = s.mv c l := rfl

theorem rv_setM (s : CS) (c : Int) (l : Nat) (v : CV) (r : Reg) : (s.setM c l v).rv r = s.rv r := rfl

theorem mv_setM (s : CS) (c c' : Int) (l l' : Nat) (v : CV) :
    (s.setM c l v).mv c' l' = if (c', l') = (c, l) then v else s.mv c' l' := by
  simp only [CS.mv, CS.setM, List.find?_cons]
  by_cases e : (c', l') = (c, l)
  · have : ((c, l) == (c', l')) = true := by simp [e]
    simp [e]
  · have : ((c, l) == (c', l')) = false := by simp; intro a b; exact e (by rw [a, b])
    simp only [this, e, if_false]
    rw [find_filter_ne]; simp [e]

theorem rv_s0 (s : CS) (r : Reg) : ({ s with fl := none } : CS).rv r = s.rv r := rfl
theorem mv_s0 (s : CS) (c : Int) (l : Nat) : ({ s with fl := none } : CS).mv c l = s.mv c l := rfl

/-- `writeAll`: each register `defs i` names gets a new name; the rest keep theirs. -/
theorem rv_writeAll (ds : List Reg) (j : Nat) (s : CS) (r : Reg) (h : r ≠ .x23) :
    (ds.foldl (fun s d => s.setR d (some (.fresh j d))) s).rv r =
      if r ∈ ds then some (.fresh j r) else s.rv r := by
  induction ds generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, rv_setR _ _ _ _ h, List.mem_cons]
    by_cases hx : r = x
    · subst hx; simp
    · simp [hx]

theorem writeAll_fields (ds : List Reg) (j : Nat) (s : CS) :
    let t := ds.foldl (fun s d => s.setR d (some (.fresh j d))) s
    t.off = s.off ∧ t.lt = s.lt ∧ t.fl = s.fl ∧ t.gen = s.gen ∧ ∀ c l, t.mv c l = s.mv c l := by
  induction ds generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨a, b, c, d, e⟩ := ih (s.setR x (some (.fresh j x)))
    exact ⟨a, b, c, d, fun c l => (e c l).trans (mv_setR _ _ _ _ _)⟩

theorem rv_kill (ks : List Reg) (s : CS) (r : Reg) (h : r ≠ .x23) :
    (ks.foldl (fun s r => s.setR r none) s).rv r = if r ∈ ks then none else s.rv r := by
  induction ks generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, rv_setR _ _ _ _ h, List.mem_cons]
    by_cases hx : r = x
    · subst hx; simp
    · simp [hx]

theorem kill_fields (ks : List Reg) (s : CS) :
    let t := ks.foldl (fun s r => s.setR r none) s
    t.off = s.off ∧ t.lt = s.lt ∧ t.fl = s.fl ∧ t.gen = s.gen ∧ t.mem = s.mem := by
  induction ks generalizing s with
  | nil => simp
  | cons x xs ih => exact ih _

/-! ## The machine around a body

`AsmRun.step` is the instruction semantics (registers, flags, sp, byte memory). Around
it: a call keeps only the callee-saved registers (AAPCS64; the callee may write any
memory), an instruction `AsmRun.step` does not model writes whatever it likes to
`defs i`, the flags, sp and the memory (`step_frame` checks `defs` against the modelled
ones), and the control forms move the pc. A conditional branch may go either way,
except `b.<c>` to a local label, which follows the flags. -/

def isCall : AInstr → Bool | .blSym _ | .blr _ | .blFar _ => true | _ => false

/-- Labels and branches: the data state does not change. -/
def isCtl (i : AInstr) : Bool :=
  (localBranch i).isSome || match i with
  | .label _ | .bSym .. | .cbnzSym .. | .cbnzSymW .. | .bcTramp .. | .cbnzOog _ | .bcsOog | .bhiOog
  | .bloOog => true
  | _ => false

/-- One non-call instruction, falling through. -/
def Exec (i : AInstr) (m m' : RS) : Prop :=
  if isCtl i then m' = m else
  match AsmRun.step m i with
  | some m'' => m' = m''
  | none => ∀ r, r ∉ defs i → m'.regs r = m.regs r

/-- A call (`bl`, `blr`): the callee keeps x18-x29 and sp (AAPCS64), nothing else. -/
def CallExec (m m' : RS) : Prop := ∀ r, AsmRun.callerSaved r = false → m'.regs r = m.regs r

/-- One step of a flattened body from instruction j; `br x27` (and every far exit) has none. -/
inductive CStep (is : List AInstr) : Nat → RS → Nat → RS → Prop
  | fall {j i m m'} : is[j]? = some i → noFallthrough i = false → isCall i = false → Exec i m m' →
      CStep is j m (j + 1) m'
  | call {j i m m'} : is[j]? = some i → isCall i = true → CallExec m m' → CStep is j m (j + 1) m'
  | jump {j i k m} : is[j]? = some i → (localBranch i).bind (labelTarget is j) = some k →
      (∀ c l, i = .bcLbl c l → bcHolds c m.flags = true) → CStep is j m k m

/-- The states a body reaches from its entry. -/
inductive Reach (is : List AInstr) (m₀ : RS) : Nat → RS → Prop
  | start : Reach is m₀ 0 m₀
  | step {j m k m'} : Reach is m₀ j m → CStep is j m k m' → Reach is m₀ k m'

/-! ## The stack and the cache -/

/-- sp at entry. -/
def sp₀ (m₀ : RS) : Int := (m₀.regs .x23).toInt

/-- The address of limb l of stack word i — what `sub x14, x23, #k ; add x14, x24, x14,
    lsl #5 ; ldp …, [x14, #8l]` forms. -/
def wordAt (base : BitVec 64) (i : BitVec 64) (l : Nat) : BitVec 64 := off (base + (i <<< 5)) (8 * l)

/-- The registers caching word sp-k hold its limbs, if that word exists (sp ≥ k). -/
def Caches (m : RS) (k : Nat) (rs : List Reg) : Prop :=
  (k : Int) ≤ (m.regs .x23).toInt → ∀ r l, (r, l) ∈ rs.zipIdx →
    m.regs r = ld64 m.mem (wordAt (m.regs .x24) (m.regs .x23 - BitVec.ofNat 64 k) l)

/-- **The stack-cache invariant** (ARM64): x6-x9 = stack[sp-1], x10-x13 = stack[sp-2]. -/
def Coherent (m : RS) : Prop := Caches m 1 tosRegs ∧ Caches m 2 nosRegs

/-- The words the analysis names: sp₀ + c for |c| ≤ `W`. -/
def W : Nat := cwin.natAbs + 2

def cellAddr (m₀ : RS) (c : Int) (l : Nat) : BitVec 64 :=
  wordAt (m₀.regs .x24) (BitVec.ofInt 64 (sp₀ m₀ + c)) l

/-- The analysis places a store when its base is a stack word. -/
def placed (s : CS) : AInstr → Bool
  | .stpOff _ _ b _ | .strOff _ b _ | .strBase _ b => (s.word b).isSome
  | _ => false

/-! ## Values -/

/-- What a symbolic value stands for, given the values `ρ` of the names. -/
def val (m₀ : RS) (ρ : CV → BitVec 64) : CV → BitVec 64
  | .idx c => BitVec.ofInt 64 (sp₀ m₀ + c)
  | .addr c => m₀.regs .x24 + (BitVec.ofInt 64 (sp₀ m₀ + c) <<< 5)
  | .when _ v => val m₀ ρ v
  | v => ρ v

/-- `x` is what `v` stands for (once its guards hold). -/
def Holds (m₀ : RS) (ρ : CV → BitVec 64) : CV → BitVec 64 → Prop
  | .when k v, x => k ≤ sp₀ m₀ → Holds m₀ ρ v x
  | v, x => x = val m₀ ρ v

/-- `v` is well formed at step d, generation g: its names are older than d (fresh) or
    from generation ≤ g (cells); its indices lie in the window. -/
def Fr (d g : Nat) : CV → Prop
  | .cell g' c _ => g' ≤ g ∧ c.natAbs ≤ W
  | .idx c | .addr c => c.natAbs ≤ cwin.natAbs
  | .fresh k _ => k < d
  | .when _ v => Fr d g v

/-- The names step d makes: `fresh d r` is r after the step, `cell (d+1)` the memory
    after the call at d. -/
def ext (m₀ : RS) (ρ : CV → BitVec 64) (d : Nat) (m' : RS) : CV → BitVec 64
  | .fresh k r => if k = d then m'.regs r else ρ (.fresh k r)
  | .cell g c l => if g = d + 1 then ld64 m'.mem (cellAddr m₀ c l) else ρ (.cell g c l)
  | v => ρ v

/-- **The invariant**: the abstract state `s` (after d steps) describes the machine `m`. -/
structure Inv (m₀ : RS) (ρ : CV → BitVec 64) (d : Nat) (s : CS) (m : RS) : Prop where
  off  : s.off.natAbs ≤ cwin.natAbs
  x23  : m.regs .x23 = BitVec.ofInt 64 (sp₀ m₀ + s.off)
  x24  : m.regs .x24 = m₀.regs .x24
  lt   : ∀ L, s.lt = some L → sp₀ m₀ + s.off < L
  fl   : ∀ k, s.fl = some k → m.flags = subFlags (m.regs .x23) (BitVec.ofNat 64 k)
  regs : ∀ r v, s.rv r = some v → Holds m₀ ρ v (m.regs r)
  mem  : ∀ c l, c.natAbs ≤ W → l < 4 → Holds m₀ ρ (s.mv c l) (ld64 m.mem (cellAddr m₀ c l))
  gen  : s.gen ≤ d
  frR  : ∀ r v, s.rv r = some v → Fr d s.gen v
  frM  : ∀ c l, c.natAbs ≤ W → Fr d s.gen (s.mv c l)

/-! ### Names: a step's names are new -/

theorem val_ext (m₀ : RS) (ρ : CV → BitVec 64) (d g : Nat) (m' : RS) (hg : g ≤ d) :
    ∀ v, Fr d g v → val m₀ (ext m₀ ρ d m') v = val m₀ ρ v
  | .cell g' c l, h => by simp only [val, ext, Fr] at h ⊢; rw [if_neg (by omega)]
  | .idx _, _ | .addr _, _ => rfl
  | .fresh k r, h => by simp only [val, ext, Fr] at h ⊢; rw [if_neg (by omega)]
  | .when _ v, h => by simp only [val, Fr] at h ⊢; exact val_ext m₀ ρ d g m' hg v h

theorem holds_ext (m₀ : RS) (ρ : CV → BitVec 64) (d g : Nat) (m' : RS) (hg : g ≤ d) :
    ∀ v x, Fr d g v → (Holds m₀ (ext m₀ ρ d m') v x ↔ Holds m₀ ρ v x)
  | .when k v, x, h => by
      simp only [Holds, Fr] at h ⊢; rw [holds_ext m₀ ρ d g m' hg v x h]
  | .cell .., x, h | .idx _, x, h | .addr _, x, h | .fresh .., x, h => by
      simp only [Holds]; rw [val_ext m₀ ρ d g m' hg _ h]

theorem fr_mono {d d' g g' : Nat} (hd : d ≤ d') (hg : g ≤ g') : ∀ v, Fr d g v → Fr d' g' v
  | .cell .., h => by simp only [Fr] at h ⊢; omega
  | .idx _, h | .addr _, h => h
  | .fresh .., h => by simp only [Fr] at h ⊢; omega
  | .when _ v, h => fr_mono hd hg v h

theorem holds_strip (m₀ : RS) (ρ : CV → BitVec 64) (t : Int) (ht : t ≤ sp₀ m₀) :
    ∀ v x, Holds m₀ ρ v x → v.okAt t = true → x = val m₀ ρ v.strip
  | .when k v, x, h, hok => by
      simp only [CV.okAt, Bool.and_eq_true, decide_eq_true_eq] at hok
      simp only [Holds] at h; simp only [CV.strip]
      exact holds_strip m₀ ρ t ht v x (h (by omega)) hok.2
  | .cell .., _, h, _ | .idx _, _, h, _ | .addr _, _, h, _ | .fresh .., _, h, _ => h

/-! ### Address arithmetic -/

theorem ofInt_shl5 (x : Int) : BitVec.ofInt 64 x <<< 5 = BitVec.ofInt 64 (32 * x) := by
  rw [BitVec.ofInt_mul, BitVec.shiftLeft_eq_mul_twoPow]; rw [BitVec.mul_comm]; rfl

theorem ofInt_ne (x y : Int) (h : x ≠ y) (h2 : (x - y).natAbs < 18446744073709551616) :
    BitVec.ofInt 64 x ≠ BitVec.ofInt 64 y := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofInt] at this
  omega

theorem cellAddr_eq (m₀ : RS) (c : Int) (l : Nat) :
    cellAddr m₀ c l = m₀.regs .x24 + BitVec.ofInt 64 (32 * (sp₀ m₀ + c) + 8 * l) := by
  simp only [cellAddr, wordAt, off, ofInt_shl5, BitVec.add_assoc]
  rw [BitVec.ofInt_add (32 * _), ← BitVec.ofInt_natCast]; push_cast; rfl

/-- Two named limbs never overlap (the window is far smaller than 2^64). -/
theorem cell_disj (m₀ : RS) (c c' : Int) (l l' : Nat) (hc : c.natAbs ≤ W) (hc' : c'.natAbs ≤ W)
    (hl : l < 4) (hl' : l' < 4) (hne : (c, l) ≠ (c', l')) :
    ∀ i < 8, ∀ j < 8, off (cellAddr m₀ c l) i ≠ off (cellAddr m₀ c' l') j := by
  intro i hi j hj e
  simp only [cellAddr_eq, off, BitVec.add_assoc, BitVec.add_right_inj] at e
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add, ← BitVec.ofInt_add] at e
  have hW : W = 65538 := by decide
  refine ofInt_ne _ _ ?_ ?_ e
  · intro h; apply hne; simp only [Prod.mk.injEq]; omega
  · omega

/-! ## One step -/

/-- The instructions `cstep` has an arm for; every other one is `writeAll`. -/
def special : AInstr → Bool
  | .label _ | .cmpImm .. | .subImm .. | .addImm .. | .addReg .. | .addLsl5 .. | .movReg ..
  | .ldpOff .. | .ldrOff .. | .ldrBase .. | .stpOff .. | .strOff .. | .strBase ..
  | .blSym _ | .blr _ | .blFar _ => true
  | _ => false

/-- What the analysis does with everything else. -/
def writeAll (j : Nat) (i : AInstr) (s : CS) : CS :=
  (defs i).foldl (fun s d => s.setR d (some (.fresh j d))) { s with fl := none }

set_option maxHeartbeats 4000000 in
theorem cstep_other (j : Nat) (i : AInstr) (s out : CS) (hsp : special i = false)
    (h : cstep j i s = some out) :
    out = writeAll j i s ∧ .x23 ∉ defs i ∧ .x24 ∉ defs i ∧ placed s i = false := by
  cases i <;> simp only [special] at hsp <;> simp only [cstep, writeAll, placed] at h ⊢ <;>
    (repeat' split at h) <;> simp_all [defs]

theorem storeForm_regs (m m' : RS) (i : AInstr) (h : AsmRun.step m i = some m') :
    ∀ r, r ∉ defs i → m'.regs r = m.regs r := step_regs m m' i h

/-- The data facts a fall-through step gives: registers outside `defs i` kept; the
    window kept, unless it is a placed store (the analysis follows those itself). -/
theorem exec_regs (i : AInstr) (m m' : RS) (h : Exec i m m') : ∀ r, r ∉ defs i → m'.regs r = m.regs r := by
  intro r hr
  unfold Exec at h
  split at h
  · subst h; rfl
  · split at h
    · rename_i m2 e; rw [h]; exact step_regs m m2 i e r hr
    · exact h r hr

/-- The window is kept: `Sep` where the instruction may write memory, the semantics elsewhere. -/
def WinKept (m₀ m m' : RS) : Prop :=
  ∀ c l, c.natAbs ≤ W → l < 4 → ld64 m'.mem (cellAddr m₀ c l) = ld64 m.mem (cellAddr m₀ c l)

/-- Where `Sep` is needed: a store form, or an instruction outside the modelled subset. -/
def mayWrite (i : AInstr) (m : RS) : Prop :=
  isCtl i = false ∧ (storeForm i = true ∨ AsmRun.step m i = none)

theorem exec_win (m₀ : RS) (i : AInstr) (m m' : RS) (h : Exec i m m') (hs : mayWrite i m → WinKept m₀ m m') :
    WinKept m₀ m m' := by
  unfold Exec at h
  by_cases hc : isCtl i = true
  · rw [if_pos hc] at h; subst h; intro _ _ _ _; rfl
  · rw [if_neg hc] at h
    split at h
    · rename_i m2 e
      by_cases hst : storeForm i = true
      · exact hs ⟨by simpa using hc, Or.inl hst⟩
      · rw [h]; intro c l _ _; rw [step_mem m m2 i e (by simpa using hst)]
    · rename_i e; exact hs ⟨by simpa using hc, Or.inr e⟩

/-- A step that names nothing new keeps the invariant (names of step d unused). -/
theorem inv_succ {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS} (m2 : RS)
    (h : Inv m₀ ρ d s m) : Inv m₀ (ext m₀ ρ d m2) (d + 1) s m where
  off := h.off
  x23 := h.x23
  x24 := h.x24
  lt := h.lt
  fl := h.fl
  regs r v hv := (holds_ext m₀ ρ d s.gen m2 h.gen v _ (h.frR r v hv)).2 (h.regs r v hv)
  mem c l hc hl := (holds_ext m₀ ρ d s.gen m2 h.gen _ _ (h.frM c l hc)).2 (h.mem c l hc hl)
  gen := by have := h.gen; omega
  frR r v hv := fr_mono (by omega) (Nat.le_refl _) v (h.frR r v hv)
  frM c l hc := fr_mono (by omega) (Nat.le_refl _) _ (h.frM c l hc)

/-- **The generic step**: `writeAll`, when the step kept every register outside `defs i`
    and the window. -/
theorem inv_writeAll {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} (i : AInstr)
    (h : Inv m₀ ρ d s m) (h23 : .x23 ∉ defs i) (h24 : .x24 ∉ defs i)
    (hregs : ∀ r, r ∉ defs i → m'.regs r = m.regs r) (hwin : WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) (writeAll d i s) m' := by
  obtain ⟨eoff, elt, efl, egen, emv⟩ := writeAll_fields (defs i) d { s with fl := none }
  have hs := inv_succ m' h
  have rvw : ∀ r, r ≠ .x23 → (writeAll d i s).rv r = if r ∈ defs i then some (.fresh d r) else s.rv r :=
    fun r hr => rv_writeAll _ _ _ r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [writeAll, eoff]; exact h.off
  · simp only [writeAll, eoff]; rw [hregs _ h23]; exact h.x23
  · rw [hregs _ h24]; exact h.x24
  · intro L hL; simp only [writeAll, elt, eoff] at hL ⊢; exact h.lt L hL
  · intro k hk; simp only [writeAll, efl] at hk; cases hk
  · intro r v hv
    by_cases e : r = .x23
    · subst e; simp only [rv_x23, writeAll, eoff, Option.some.injEq] at hv; subst hv
      simp only [Holds, val]; rw [hregs _ h23, h.x23]
    · rw [rvw r e] at hv
      split at hv
      · cases hv; simp only [Holds, val, ext, if_true]
      · rw [hregs r (by assumption)]; exact hs.regs r v hv
  · intro c l hc hl
    simp only [writeAll, emv, mv_s0]; rw [hwin c l hc hl]; exact hs.mem c l hc hl
  · simp only [writeAll, egen]; exact hs.gen
  · intro r v hv
    simp only [writeAll, egen]
    by_cases e : r = .x23
    · subst e; simp only [rv_x23, writeAll, eoff, Option.some.injEq] at hv; subst hv
      exact h.off
    · rw [rvw r e] at hv
      split at hv
      · cases hv; simp only [Fr]; omega
      · exact hs.frR r v hv
  · intro c l hc; simp only [writeAll, egen, emv, mv_s0]; exact hs.frM c l hc

theorem inv_s0 {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS} (h : Inv m₀ ρ d s m) :
    Inv m₀ ρ d { s with fl := none } m :=
  { h with fl := fun k hk => by cases hk }

/-- Set one register to a value it holds (sp and the stack base only to what they hold). -/
theorem inv_setR {m₀ : RS} {ρ : CV → BitVec 64} {D : Nat} {t : CS} {mm : RS} (h : Inv m₀ ρ D t mm)
    (r : Reg) (v : Option CV) (x : BitVec 64) (h23 : r = .x23 → x = mm.regs .x23)
    (h24 : r = .x24 → x = mm.regs .x24)
    (hv : ∀ w, v = some w → Holds m₀ ρ w x ∧ Fr D t.gen w) :
    Inv m₀ ρ D (t.setR r v) (mm.set r x) := by
  have e23 : (mm.set r x).regs .x23 = mm.regs .x23 := by
    simp only [set_regs]; split
    · rename_i e; exact h23 e.symm
    · rfl
  have e24 : (mm.set r x).regs .x24 = mm.regs .x24 := by
    simp only [set_regs]; split
    · rename_i e; exact h24 e.symm
    · rfl
  refine ⟨h.off, ?_, ?_, h.lt, ?_, ?_, h.mem, h.gen, ?_, h.frM⟩
  · rw [e23]; exact h.x23
  · rw [e24]; exact h.x24
  · intro k hk; rw [set_flags, e23]; exact h.fl k hk
  · intro r' w hw
    by_cases e : r' = .x23
    · subst e; rw [e23]; simp only [rv_x23, setR_off] at hw
      exact h.regs _ _ (by rw [rv_x23, hw])
    · rw [rv_setR _ _ _ _ e] at hw
      simp only [set_regs]
      split at hw
      · rename_i e'; subst e'; simp only [if_true]; exact (hv w hw).1
      · rename_i e'; simp only [if_neg e']; exact h.regs r' w hw
  · intro r' w hw
    by_cases e : r' = .x23
    · subst e; simp only [rv_x23, setR_off] at hw; exact h.frR _ _ (by rw [rv_x23, hw])
    · rw [rv_setR _ _ _ _ e] at hw
      split at hw
      · exact (hv w hw).2
      · exact h.frR r' w hw

/-- Store register r into a named limb. -/
theorem inv_store {m₀ : RS} {ρ : CV → BitVec 64} {D : Nat} {t : CS} {mm : RS} (h : Inv m₀ ρ D t mm)
    (j : Nat) (hj : j < D) (hρ : ∀ r, ρ (.fresh j r) = mm.regs r)
    (c : Int) (hc : c.natAbs ≤ cwin.natAbs) (l : Nat) (hl : l < 4) (r : Reg) :
    Inv m₀ ρ D (CS.store j t c l r) (mm.store64 (cellAddr m₀ c l) (mm.regs r)) := by
  have hW : W = cwin.natAbs + 2 := rfl
  -- the stored value, and the state before the limb is written
  obtain ⟨v, t1, ht1, hv, hfv, hstore⟩ : ∃ v t1, Inv m₀ ρ D t1 mm ∧ Holds m₀ ρ v (mm.regs r) ∧
      Fr D t1.gen v ∧ CS.store j t c l r = t1.setM c l v := by
    unfold CS.store
    split
    · rename_i v hv
      exact ⟨v, t, h, h.regs r v hv, h.frR r v hv, rfl⟩
    · rename_i hn
      have h23 : r ≠ .x23 := by intro e; subst e; simp at hn
      refine ⟨.fresh j r, t.setR r (some (.fresh j r)), ?_, by simp [Holds, val, hρ], by simp [Fr, hj], rfl⟩
      have := inv_setR h r (some (.fresh j r)) (mm.regs r) (fun e => by rw [e])
        (fun e => by rw [e]) (fun w hw => by cases hw; exact ⟨by simp [Holds, val, hρ], by simp [Fr, hj]⟩)
      rwa [set_eq_self _ _ _ rfl] at this
  rw [hstore]
  refine ⟨ht1.off, ht1.x23, ht1.x24, ht1.lt, ht1.fl, ?_, ?_, ht1.gen, ht1.frR, ?_⟩
  · intro r' w hw; rw [rv_setM] at hw; exact ht1.regs r' w hw
  · intro c' l' hc' hl'
    simp only [store64_mem, mv_setM]
    split
    · rename_i e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [ld64_st64_same]; exact hv
    · rename_i e
      rw [ld64_st64_disj]
      · exact ht1.mem c' l' hc' hl'
      · exact cell_disj m₀ c' c l' l hc' (by omega) hl' hl e
  · intro c' l' hc'; simp only [mv_setM]; split
    · exact hfv
    · exact ht1.frM c' l' hc'

theorem not_kill_callee (r : Reg) (h : r ∉ callKills false) : AsmRun.callerSaved r = false := by
  cases r <;> simp_all [callKills, OpInstrs.callerSaved, AsmRun.callerSaved]

/-- A call: the caller-saved registers and x30 forgotten, x0 named, the memory a new
    generation. -/
theorem inv_call_aux {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS}
    (h : Inv m₀ ρ d s m) (hx : CallExec m m') (K : CS) (eoff : K.off = s.off) (elt : K.lt = s.lt)
    (efl : K.fl = none) (erv : ∀ r, r ≠ .x23 → K.rv r = if r ∈ callKills false then none else s.rv r) :
    Inv m₀ (ext m₀ ρ d m') (d + 1)
      (({ K with mem := [], gen := d + 1 } : CS).setR .x0 (some (.fresh d .x0))) m' := by
  have hs := inv_succ m' h
  have k23 : m'.regs .x23 = m.regs .x23 := hx _ rfl
  have k24 : m'.regs .x24 = m.regs .x24 := hx _ rfl
  have ht : Inv m₀ (ext m₀ ρ d m') (d + 1) ({ K with mem := [], gen := d + 1 } : CS) m' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show K.off.natAbs ≤ _; rw [eoff]; exact h.off
    · show _ = BitVec.ofInt 64 (sp₀ m₀ + K.off); rw [eoff, k23]; exact h.x23
    · rw [k24]; exact h.x24
    · intro L hL; change K.lt = some L at hL; change sp₀ m₀ + K.off < L; rw [elt] at hL; rw [eoff]
      exact h.lt L hL
    · intro k hk; change K.fl = some k at hk; rw [efl] at hk; cases hk
    · intro r v hv
      change K.rv r = some v at hv
      by_cases e : r = .x23
      · subst e; rw [rv_x23, eoff] at hv; cases hv; simp only [Holds, val]; rw [k23]; exact h.x23
      · rw [erv _ e] at hv
        split at hv
        · cases hv
        · rename_i hk; rw [hx r (not_kill_callee r hk)]; exact hs.regs r v hv
    · intro c l hc hl; simp only [CS.mv, List.find?_nil, Option.map_none, Option.getD_none, Holds, val, ext,
        if_true]
    · exact Nat.le_refl _
    · intro r v hv
      change K.rv r = some v at hv
      by_cases e : r = .x23
      · subst e; rw [rv_x23, eoff] at hv; cases hv; exact h.off
      · rw [erv _ e] at hv
        split at hv
        · cases hv
        · exact fr_mono (by omega) (show s.gen ≤ d + 1 by have := h.gen; omega) v (h.frR r v hv)
    · intro c l hc; simp only [CS.mv, List.find?_nil, Option.map_none, Option.getD_none, Fr]
      exact ⟨Nat.le_refl _, hc⟩
  have := inv_setR ht .x0 (some (.fresh d .x0)) (m'.regs .x0) (by simp) (by simp)
    (fun w hw => by cases hw; exact ⟨by simp [Holds, val, ext], by simp [Fr]⟩)
  rwa [set_eq_self _ _ _ rfl] at this

theorem inv_call {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS}
    (h : Inv m₀ ρ d s m) (hx : CallExec m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1)
      (({ ((callKills false).foldl (fun s r => s.setR r none) { s with fl := none }) with
          mem := [], gen := d + 1 } : CS).setR .x0 (some (.fresh d .x0))) m' := by
  obtain ⟨eoff, elt, efl, _, _⟩ := kill_fields (callKills false) { s with fl := none }
  exact inv_call_aux h hx _ eoff elt efl (fun r e => rv_kill _ _ _ e)

theorem exec_some {i : AInstr} {m m' m2 : RS} (hc : isCtl i = false) (hs : AsmRun.step m i = some m2)
    (h : Exec i m m') : m' = m2 := by
  unfold Exec at h; rw [if_neg (by simp [hc]), hs] at h; exact h

theorem ofInt_sub' (x y : Int) : BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem fall_generic {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {i : AInstr}
    (h : Inv m₀ ρ d s m) (hex : Exec i m m') (hsep : mayWrite i m → placed s i = false → WinKept m₀ m m')
    (h23 : .x23 ∉ defs i) (h24 : .x24 ∉ defs i) (hpl : placed s i = false) :
    Inv m₀ (ext m₀ ρ d m') (d + 1) (writeAll d i s) m' :=
  inv_writeAll i h h23 h24 (exec_regs i m m' hex) (exec_win m₀ i m m' hex (fun hw => hsep hw hpl))

theorem rv_regs_eq' (t s : CS) (h : t.regs = s.regs) (r : Reg) (hr : r ≠ .x23) {v : CV}
    (hv : t.rv r = some v) : s.rv r = some v := by
  have : (r == .x23) = false := by simp [hr]
  simp only [CS.rv, this, h, Bool.false_eq_true, if_false] at hv ⊢; exact hv

theorem rv_regs_eq (s t : CS) (h : t.regs = s.regs) (r : Reg) (hr : r ≠ .x23) : t.rv r = s.rv r := by
  have : (r == .x23) = false := by simp [hr]
  simp only [CS.rv, this, h, Bool.false_eq_true, if_false]

/-- `sub|add x23, x23, #k`: sp moves by δ. -/
theorem inv_spadj {m₀ : RS} {ρ : CV → BitVec 64} {D : Nat} {s : CS} {m : RS} (h : Inv m₀ ρ D s m)
    (δ : Int) (hδ : (s.off + δ).natAbs ≤ cwin.natAbs) (x : BitVec 64)
    (hx : x = BitVec.ofInt 64 (sp₀ m₀ + (s.off + δ))) :
    Inv m₀ ρ D { off := s.off + δ, regs := s.regs, mem := s.mem, gen := s.gen,
                 lt := s.lt.map (· + δ), fl := none } (m.set .x23 x) := by
  refine ⟨hδ, by simp [hx], by simp [h.x24], ?_, by simp, ?_, ?_, h.gen, ?_, ?_⟩
  · intro L hL; simp only [Option.map_eq_some_iff] at hL; obtain ⟨L0, h0, rfl⟩ := hL
    have := h.lt L0 h0; show sp₀ m₀ + (s.off + δ) < L0 + δ; omega
  · intro r v hv
    by_cases e : r = .x23
    · subst e; simp only [rv_x23, Option.some.injEq] at hv; subst hv; simp [Holds, val, hx]
    · have hv' : s.rv r = some v := by refine rv_regs_eq' _ s ?_ r e hv; rfl
      simp only [set_regs, if_neg e]; exact h.regs r v hv'
  · intro c l hc hl; exact h.mem c l hc hl
  · intro r v hv
    by_cases e : r = .x23
    · subst e; simp only [rv_x23, Option.some.injEq] at hv; subst hv; exact hδ
    · have hv' : s.rv r = some v := by refine rv_regs_eq' _ s ?_ r e hv; rfl
      exact h.frR r v hv'
  · intro c l hc; exact h.frM c l hc

theorem fall_subImm {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (dd a : Reg) (k : Nat)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.subImm dd a k) s = some out) (hex : Exec (.subImm dd a k) m m')
    (hsep : mayWrite (.subImm dd a k) m → placed s (.subImm dd a k) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep, spWords, Bool.not_false, if_true, Option.map_some] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc
  · split at hc; · cases hc
    rename_i h23; cases hc
    exact fall_generic h hex hsep (by simpa using h23) (by simpa using h24) rfl
  · rename_i ha; have ha : a = .x23 := by simpa using ha
    subst ha
    have hm : m' = m.set dd (m.regs .x23 - BitVec.ofNat 64 k) := exec_some rfl (step_subImm ..) hex
    split at hc
    · rename_i hd; have hd : dd = .x23 := by simpa using hd
      subst hd hm
      split at hc
      · rename_i hw; cases hc
        have := inv_spadj hs (-(k : Int)) (by simpa [Int.sub_eq_add_neg] using hw)
          (m.regs .x23 - BitVec.ofNat 64 k) (by rw [h.x23, ← BitVec.ofInt_natCast, ← ofInt_sub']; congr 1; omega)
        simpa [Int.sub_eq_add_neg] using this
      · cases hc
    · rename_i hd; cases hc; subst hm
      have h24' : dd ≠ .x24 := by simpa [defs, eq_comm] using h24
      refine inv_setR (inv_s0 hs) dd _ _ (fun e => absurd e (by simpa using hd)) (fun e => absurd e h24') ?_
      intro w hw; cases hw
      simp only [idxOr]
      split
      · rename_i hw
        refine ⟨?_, hw⟩
        simp only [Holds, val]; rw [h.x23, ← BitVec.ofInt_natCast, ← ofInt_sub']; congr 1; omega
      · exact ⟨by simp [Holds, val, ext], by simp [Fr]⟩

theorem fall_addImm {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (dd a : Reg) (k : Nat)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.addImm dd a k) s = some out) (hex : Exec (.addImm dd a k) m m')
    (hsep : mayWrite (.addImm dd a k) m → placed s (.addImm dd a k) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep, spWords, Bool.not_false, if_true, Option.map_some] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc
  · split at hc; · cases hc
    rename_i h23; cases hc
    exact fall_generic h hex hsep (by simpa using h23) (by simpa using h24) rfl
  · rename_i ha; have ha : a = .x23 := by simpa using ha
    subst ha
    have hm : m' = m.set dd (m.regs .x23 + BitVec.ofNat 64 k) := exec_some rfl (step_addImm ..) hex
    split at hc
    · rename_i hd; have hd : dd = .x23 := by simpa using hd
      subst hd hm
      split at hc
      · rename_i hw; cases hc
        exact inv_spadj hs (k : Int) hw (m.regs .x23 + BitVec.ofNat 64 k)
          (by rw [h.x23, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]; congr 1; omega)
      · cases hc
    · rename_i hd; cases hc; subst hm
      have h24' : dd ≠ .x24 := by simpa [defs, eq_comm] using h24
      refine inv_setR (inv_s0 hs) dd _ _ (fun e => absurd e (by simpa using hd)) (fun e => absurd e h24') ?_
      intro w hw; cases hw
      simp only [idxOr]
      split
      · rename_i hw
        refine ⟨?_, hw⟩
        simp only [Holds, val]; rw [h.x23, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]; congr 1; omega
      · exact ⟨by simp [Holds, val, ext], by simp [Fr]⟩

theorem fall_addReg {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (dd b a : Reg)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.addReg dd b a) s = some out) (hex : Exec (.addReg dd b a) m m')
    (hsep : mayWrite (.addReg dd b a) m → placed s (.addReg dd b a) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  simp only [cstep, Bool.not_false, Bool.true_or, if_true] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc; · cases hc
  rename_i h23; cases hc
  exact fall_generic h hex hsep (by simpa using h23) (by simpa using h24) rfl

theorem fall_addLsl5 {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (dd b a : Reg)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.addLsl5 dd b a) s = some out) (hex : Exec (.addLsl5 dd b a) m m')
    (hsep : mayWrite (.addLsl5 dd b a) m → placed s (.addLsl5 dd b a) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc
  · split at hc; · cases hc
    rename_i h23; cases hc
    exact fall_generic h hex hsep (by simpa using h23) (by simpa using h24) rfl
  · rename_i hb; have hb : b = .x24 := by simpa using hb
    subst hb
    split at hc; · cases hc
    rename_i hd; cases hc
    have hm : m' = m.set dd (m.regs .x24 + (m.regs a <<< 5)) := exec_some rfl (step_addLsl5 ..) hex
    subst hm
    have h24' : dd ≠ .x24 := by simpa [defs, eq_comm] using h24
    refine inv_setR (inv_s0 hs) dd _ _ (fun e => absurd e (by simpa using hd)) (fun e => absurd e h24') ?_
    intro w hw
    split at hw
    · rename_i c hac; cases hw
      have ha := h.regs a _ hac; simp only [Holds, val] at ha
      have hf := h.frR a _ hac; simp only [Fr] at hf
      refine ⟨?_, hf⟩
      simp only [Holds, val]; rw [ha, h.x24]
    · cases hw; exact ⟨by simp [Holds, val, ext], by simp [Fr]⟩

theorem fall_movReg {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (dd a : Reg)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.movReg dd a) s = some out) (hex : Exec (.movReg dd a) m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc; · cases hc
  rename_i hd; cases hc
  have hm : m' = m.set dd (m.regs a) := exec_some rfl (step_movReg ..) hex
  subst hm
  have h24' : dd ≠ .x24 := by simpa [defs, eq_comm] using h24
  refine inv_setR (inv_s0 hs) dd _ _ (fun e => absurd e (by simpa using hd)) (fun e => absurd e h24') ?_
  intro w hw
  exact ⟨hs.regs a w hw, hs.frR a w hw⟩

theorem fall_cmpImm {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a : Reg) (k : Nat)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.cmpImm a k) s = some out) (hex : Exec (.cmpImm a k) m m')
    (hsep : mayWrite (.cmpImm a k) m → placed s (.cmpImm a k) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc
  · rename_i ha; have ha : a = .x23 := by simpa using ha
    subst ha; cases hc
    have hm : m' = m.withFlags (subFlags (m.regs .x23) (BitVec.ofNat 64 k)) :=
      exec_some rfl (step_cmpImm ..) hex
    subst hm
    exact ⟨hs.off, hs.x23, hs.x24, hs.lt, fun k' hk => by cases hk; rfl, hs.regs, hs.mem, hs.gen,
      hs.frR, hs.frM⟩
  · split at hc; · cases hc
    rename_i h23; cases hc
    exact fall_generic h hex hsep (by simpa using h23) (by simpa using h24) rfl

theorem word_some {s : CS} {b : Reg} {c : Int} (h : s.word b = some c) : s.rv b = some (.addr c) := by
  unfold CS.word at h; split at h <;> simp_all

theorem base_addr {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS} (h : Inv m₀ ρ d s m)
    {b : Reg} {c : Int} (hw : s.word b = some c) :
    (∀ l, m.regs b + BitVec.ofNat 64 (8 * l) = cellAddr m₀ c l) ∧ c.natAbs ≤ cwin.natAbs := by
  have hb := h.regs b _ (word_some hw); simp only [Holds, val] at hb
  have hf := h.frR b _ (word_some hw); simp only [Fr] at hf
  refine ⟨fun l => ?_, hf⟩
  rw [hb]; rfl

theorem fall_ldpOff {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a b base : Reg)
    (o : Nat) (h : Inv m₀ ρ d s m) (hc : cstep d (.ldpOff a b base o) s = some out)
    (hex : Exec (.ldpOff a b base o) m m')
    (hsep : mayWrite (.ldpOff a b base o) m → placed s (.ldpOff a b base o) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc; · cases hc
  rename_i hab
  have h24a : a ≠ .x24 := by intro e; subst e; simp [defs] at h24
  have h24b : b ≠ .x24 := by intro e; subst e; simp [defs] at h24
  have ha23 : a ≠ .x23 := by intro e; subst e; simp at hab
  have hb23 : b ≠ .x23 := by intro e; subst e; simp at hab
  have generic : ∀ {o'}, out = writeAll d (.ldpOff a b base o') s → o' = o →
      Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := fun e eo => by
    subst eo
    exact e ▸ fall_generic h hex hsep (by simp [defs, Ne.symm ha23, Ne.symm hb23])
      (by simp [defs, Ne.symm h24a, Ne.symm h24b]) rfl
  split at hc
  · rename_i c hw
    split at hc
    · rename_i ho; cases hc
      obtain ⟨hB, hcw⟩ := base_addr h hw
      have ho' : o = 8 * (o / 8) ∧ o + 8 = 8 * (o / 8 + 1) ∧ o / 8 + 1 < 4 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at ho; omega
      have hm : m' = (m.set a (ld64 m.mem (cellAddr m₀ c (o / 8)))).set b
          (ld64 m.mem (cellAddr m₀ c (o / 8 + 1))) := by
        rw [exec_some rfl (step_ldpOff ..) hex, ← hB, ← hB, ← ho'.1, ← ho'.2.1]
      subst hm
      have hW : W = cwin.natAbs + 2 := rfl
      have i1 := inv_setR (inv_s0 hs) a (some (s.mv c (o / 8))) (ld64 m.mem (cellAddr m₀ c (o / 8))) (fun e => absurd e ha23)
        (fun e => absurd e h24a) (fun w hw' => by
          cases hw'; exact ⟨hs.mem c _ (by omega) (by omega), hs.frM c _ (by omega)⟩)
      exact inv_setR i1 b (some (s.mv c (o / 8 + 1))) _ (fun e => absurd e hb23) (fun e => absurd e h24b) (fun w hw' => by
          cases hw'; exact ⟨hs.mem c _ (by omega) ho'.2.2, hs.frM c _ (by omega)⟩)
    · split at hc; · cases hc
      cases hc; exact generic rfl rfl
  · split at hc; · cases hc
    cases hc; exact generic rfl rfl

theorem fall_ldrOff {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a base : Reg)
    (o : Nat) (h : Inv m₀ ρ d s m) (hc : cstep d (.ldrOff a base o) s = some out)
    (hex : Exec (.ldrOff a base o) m m')
    (hsep : mayWrite (.ldrOff a base o) m → placed s (.ldrOff a base o) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc; · cases hc
  rename_i ha
  have h24a : a ≠ .x24 := by intro e; subst e; simp [defs] at h24
  have ha23 : a ≠ .x23 := by intro e; subst e; simp at ha
  have generic : out = writeAll d (.ldrOff a base o) s → Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := fun e =>
    e ▸ fall_generic h hex hsep (by simp [defs, Ne.symm ha23]) (by simp [defs, Ne.symm h24a]) rfl
  split at hc
  · rename_i c hw
    split at hc
    · rename_i ho; cases hc
      obtain ⟨hB, hcw⟩ := base_addr h hw
      have ho' : o = 8 * (o / 8) ∧ o / 8 < 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho; omega
      have hm : m' = m.set a (ld64 m.mem (cellAddr m₀ c (o / 8))) := by
        rw [exec_some rfl (step_ldrOff ..) hex, ← hB, ← ho'.1]
      subst hm
      have hW : W = cwin.natAbs + 2 := rfl
      exact inv_setR (inv_s0 hs) a (some (s.mv c (o / 8))) _ (fun e => absurd e ha23)
        (fun e => absurd e h24a) (fun w hw' => by
          cases hw'; exact ⟨hs.mem c _ (by omega) ho'.2, hs.frM c _ (by omega)⟩)
    · split at hc; · cases hc
      cases hc; exact generic rfl
  · split at hc; · cases hc
    cases hc; exact generic rfl

theorem fall_ldrBase {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a base : Reg)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.ldrBase a base) s = some out)
    (hex : Exec (.ldrBase a base) m m')
    (hsep : mayWrite (.ldrBase a base) m → placed s (.ldrBase a base) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  simp only [cstep] at hc
  split at hc; · cases hc
  rename_i h24
  split at hc; · cases hc
  split at hc; · cases hc
  rename_i ha
  have h24a : a ≠ .x24 := by intro e; subst e; simp [defs] at h24
  have ha23 : a ≠ .x23 := by intro e; subst e; simp at ha
  split at hc
  · rename_i c hw
    cases hc
    obtain ⟨hB, hcw⟩ := base_addr h hw
    have hm : m' = m.set a (ld64 m.mem (cellAddr m₀ c 0)) := by
      rw [exec_some rfl (show AsmRun.step m (.ldrBase a base) = some (m.set a (ld64 m.mem (m.regs base))) from rfl) hex, ← hB]; simp
    subst hm
    have hW : W = cwin.natAbs + 2 := rfl
    exact inv_setR (inv_s0 hs) a (some (s.mv c 0)) _ (fun e => absurd e ha23)
      (fun e => absurd e h24a) (fun w hw' => by
        cases hw'; exact ⟨hs.mem c _ (by omega) (by omega), hs.frM c _ (by omega)⟩)
  · split at hc; · cases hc
    cases hc
    exact fall_generic h hex hsep (by simp [defs, Ne.symm ha23]) (by simp [defs, Ne.symm h24a]) rfl

/-- A placed or unplaced store: the analysis's state is the machine's. -/
theorem store_regs {m m' : RS} {i : AInstr} (_hc : isCtl i = false) (hd : defs i = [])
    (hex : Exec i m m') : ∀ r, m'.regs r = m.regs r := fun r =>
  exec_regs i m m' hex r (by simp [hd])

theorem fall_stpOff {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a b base : Reg)
    (o : Nat) (h : Inv m₀ ρ d s m) (hc : cstep d (.stpOff a b base o) s = some out)
    (hex : Exec (.stpOff a b base o) m m')
    (hsep : mayWrite (.stpOff a b base o) m → placed s (.stpOff a b base o) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  have hr := store_regs rfl rfl hex
  simp only [cstep] at hc
  split at hc; · cases hc
  split at hc; · cases hc
  split at hc
  · rename_i c hw
    split at hc
    · rename_i ho; cases hc
      obtain ⟨hB, hcw⟩ := base_addr h hw
      have ho' : o = 8 * (o / 8) ∧ o + 8 = 8 * (o / 8 + 1) ∧ o / 8 + 1 < 4 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at ho; omega
      have hm : m' = (m.store64 (cellAddr m₀ c (o / 8)) (m.regs a)).store64
          (cellAddr m₀ c (o / 8 + 1)) (m.regs b) := by
        rw [exec_some rfl (step_stpOff ..) hex, ← hB, ← hB, ← ho'.1, ← ho'.2.1]
      have hρ : ∀ r, ext m₀ ρ d m' (.fresh d r) = m.regs r := fun r => by simp [ext, hr]
      subst hm
      have i1 := inv_store (inv_s0 hs) d (by omega) hρ c hcw (o / 8) (by omega) a
      exact inv_store i1 d (by omega) hρ c hcw (o / 8 + 1) ho'.2.2 b
    · cases hc
  · cases hc
    exact fall_generic h hex hsep (by simp [defs]) (by simp [defs]) (by simp [placed, *])

theorem fall_strOff {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a base : Reg)
    (o : Nat) (h : Inv m₀ ρ d s m) (hc : cstep d (.strOff a base o) s = some out)
    (hex : Exec (.strOff a base o) m m')
    (hsep : mayWrite (.strOff a base o) m → placed s (.strOff a base o) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  have hr := store_regs rfl rfl hex
  simp only [cstep] at hc
  split at hc; · cases hc
  split at hc; · cases hc
  split at hc
  · rename_i c hw
    split at hc
    · rename_i ho; cases hc
      obtain ⟨hB, hcw⟩ := base_addr h hw
      have ho' : o = 8 * (o / 8) ∧ o / 8 < 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho; omega
      have hm : m' = m.store64 (cellAddr m₀ c (o / 8)) (m.regs a) := by
        rw [exec_some rfl (step_strOff ..) hex, ← hB, ← ho'.1]
      have hρ : ∀ r, ext m₀ ρ d m' (.fresh d r) = m.regs r := fun r => by simp [ext, hr]
      subst hm
      exact inv_store (inv_s0 hs) d (by omega) hρ c hcw (o / 8) ho'.2 a
    · cases hc
  · cases hc
    exact fall_generic h hex hsep (by simp [defs]) (by simp [defs]) (by simp [placed, *])

theorem fall_strBase {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {out : CS} (a base : Reg)
    (h : Inv m₀ ρ d s m) (hc : cstep d (.strBase a base) s = some out)
    (hex : Exec (.strBase a base) m m')
    (hsep : mayWrite (.strBase a base) m → placed s (.strBase a base) = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have hs := inv_succ m' h
  have hr := store_regs rfl rfl hex
  simp only [cstep] at hc
  split at hc; · cases hc
  split at hc; · cases hc
  split at hc
  · rename_i c hw
    cases hc
    obtain ⟨hB, hcw⟩ := base_addr h hw
    have hm : m' = m.store64 (cellAddr m₀ c 0) (m.regs a) := by
      rw [exec_some rfl (step_strBase ..) hex, ← hB]; simp
    have hρ : ∀ r, ext m₀ ρ d m' (.fresh d r) = m.regs r := fun r => by simp [ext, hr]
    subst hm
    exact inv_store (inv_s0 hs) d (by omega) hρ c hcw 0 (by omega) a
  · cases hc
    exact fall_generic h hex hsep (by simp [defs]) (by simp [defs]) (by simp [placed, *])

set_option maxHeartbeats 4000000 in
/-- **One fall-through step keeps the invariant.** -/
theorem fall_inv {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m m' : RS} {i : AInstr} {out : CS}
    (h : Inv m₀ ρ d s m) (hc : cstep d i s = some out) (hcall : isCall i = false) (hex : Exec i m m')
    (hsep : mayWrite i m → placed s i = false → WinKept m₀ m m') :
    Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := by
  have generic : out = writeAll d i s → .x23 ∉ defs i → .x24 ∉ defs i → placed s i = false →
      Inv m₀ (ext m₀ ρ d m') (d + 1) out m' := fun e h23 h24 hpl => by
    subst e; exact inv_writeAll i h h23 h24 (exec_regs i m m' hex) (exec_win m₀ i m m' hex (fun hw => hsep hw hpl))
  by_cases hsp : special i = false
  · obtain ⟨e, h23, h24, hpl⟩ := cstep_other d i s out hsp hc
    exact generic e h23 h24 hpl
  cases i <;> simp [special] at hsp <;> simp only [isCall] at hcall <;> (try contradiction)
  all_goals first
    | exact fall_subImm _ _ _ h hc hex hsep
    | exact fall_addImm _ _ _ h hc hex hsep
    | exact fall_addReg _ _ _ h hc hex hsep
    | exact fall_addLsl5 _ _ _ h hc hex hsep
    | exact fall_movReg _ _ h hc hex
    | exact fall_cmpImm _ _ h hc hex hsep
    | exact fall_ldpOff _ _ _ _ h hc hex hsep
    | exact fall_ldrOff _ _ _ h hc hex hsep
    | exact fall_ldrBase _ _ h hc hex hsep
    | exact fall_stpOff _ _ _ _ h hc hex hsep
    | exact fall_strOff _ _ _ h hc hex hsep
    | exact fall_strBase _ _ h hc hex hsep
    | (simp [cstep, defs, storeAddrRegs] at hc; subst hc
       unfold Exec at hex; simp [isCtl] at hex; subst hex; exact inv_succ _ h)

/-! ## Branches, the entry, the exits -/

theorem toInt_sp {m₀ : RS} (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) {c : Int} (hc : c.natAbs ≤ W) :
    (BitVec.ofInt 64 (sp₀ m₀ + c)).toInt = sp₀ m₀ + c := by
  have hW : W = 65538 := by decide
  rw [BitVec.toInt_ofInt_eq_self (by omega)] <;> omega

/-- `b.lt` after `cmp a, b` is taken iff a < b (signed), for values far from overflow. -/
theorem lt_taken (x y : Int) (hx : x.natAbs ≤ 1048576) (hy : y.natAbs ≤ 1048576)
    (h : bcHolds .lt (subFlags (BitVec.ofInt 64 x) (BitVec.ofInt 64 y)) = true) : x < y := by
  have e : ∀ z : Int, z.natAbs ≤ 2097152 → (BitVec.ofInt 64 z).toInt = z := fun z hz => by
    rw [BitVec.toInt_ofInt_eq_self (by omega)] <;> omega
  simp only [bcHolds, subFlags, ← ofInt_sub', BitVec.msb_eq_toInt, e x (by omega),
    e y (by omega), e (x - y) (by omega)] at h
  revert h
  by_cases h1 : x - y < 0 <;> by_cases h2 : x < 0 <;> by_cases h3 : y < 0 <;> simp [h1, h2, h3] <;> omega

/-- The taken edge of a local branch keeps the invariant; on `b.lt` after `cmp x23, #k`,
    sp < k. -/
theorem jump_inv {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS} {i : AInstr} {out : CS} {l : String}
    (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (h : Inv m₀ ρ d s m) (hc : cstep d i s = some out)
    (hl : localBranch i = some l) (hb : ∀ c l, i = .bcLbl c l → bcHolds c m.flags = true) :
    Inv m₀ (ext m₀ ρ d m) (d + 1) (ctaken false i s out) m := by
  have hsp' : special i = false := by cases i <;> simp_all [localBranch, special]
  have hd : defs i = [] := by cases i <;> simp_all [localBranch, defs]
  obtain ⟨e, -, -, -⟩ := cstep_other d i s out hsp' hc
  have hout : out = { s with fl := none } := by rw [e, writeAll, hd]; rfl
  subst hout
  have h0 := inv_s0 (inv_succ m h)
  unfold ctaken
  split
  · rename_i c l' k hk
    split
    · rename_i hkw
      simp only [Option.bind_eq_some_iff, spWords, Bool.not_false, if_true, Option.some.injEq] at hk
      obtain ⟨k0, hk0, rfl⟩ := hk
      have hlt : sp₀ m₀ + s.off < k0 := by
        have hf := h.fl k0 hk0
        have := hb _ _ rfl
        rw [hf, h.x23, ← BitVec.ofInt_natCast] at this
        have hcw : cwin = 65536 := rfl
        exact lt_taken _ _ (by have := h.off; omega) (by omega) this
      exact { h0 with
        lt := fun L hL => by
          simp only [Option.some.injEq] at hL; subst hL
          show sp₀ m₀ + s.off < _
          cases e : s.lt with
          | none => exact hlt
          | some x => have := h.lt x e; simp only; omega }
    · exact h0
  · exact h0

theorem caches_of_ok {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS}
    (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (h : Inv m₀ ρ d s m) (k : Nat) (hk : k = 1 ∨ k = 2)
    (rs : List Reg) (hrs : ∀ r l, (r, l) ∈ rs.zipIdx → l < 4)
    (hok : (s.lt.any (· ≤ (k : Int)) || rs.zipIdx.all fun (r, l) => match s.rv r with
      | some v => v.strip == (s.mv (s.off - k) l).strip && v.okAt (-(s.off - k)) &&
                  (s.mv (s.off - k) l).okAt (-(s.off - k))
      | none => false) = true) :
    Caches m k rs := by
  have hW : W = cwin.natAbs + 2 := rfl
  have hoff := h.off
  intro hle r l hrl
  rw [h.x23, toInt_sp hsp (by omega)] at hle
  simp only [Bool.or_eq_true, Option.any_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  rcases hok with ⟨L, hL, hL1⟩ | hok
  · have := h.lt L hL; omega
  have := hok (r, l) hrl
  simp only at this
  split at this
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨heq, ok1⟩, ok2⟩ := this
    have hl := hrs r l hrl
    have hc : (s.off - k).natAbs ≤ W := by omega
    have e1 := holds_strip m₀ ρ _ (by omega) v _ (h.regs r v hv) ok1
    have e2 := holds_strip m₀ ρ _ (by omega) _ _ (h.mem _ l hc hl) ok2
    rw [e1, heq, ← e2, h.x23, h.x24, ← BitVec.ofInt_natCast, ← ofInt_sub']
    unfold cellAddr; congr 3; omega
  · cases this

/-- **At `br x27` the cache is coherent** whenever the exit check passed. -/
theorem coherent_of_exitOk {m₀ : RS} {ρ : CV → BitVec 64} {d : Nat} {s : CS} {m : RS}
    (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (h : Inv m₀ ρ d s m) (hok : exitOk s false = true) : Coherent m := by
  simp only [exitOk, Bool.false_or, Bool.and_eq_true] at hok
  have hz : ∀ (rs : List Reg), rs = tosRegs ∨ rs = nosRegs → ∀ r l, (r, l) ∈ rs.zipIdx → l < 4 := by
    intro rs hrs r l hm
    rcases hrs with rfl | rfl <;> simp [tosRegs, nosRegs, List.zipIdx] at hm <;> omega
  exact ⟨caches_of_ok hsp h 1 (Or.inl rfl) tosRegs (hz _ (Or.inl rfl)) (by simpa using hok.1),
         caches_of_ok hsp h 2 (Or.inr rfl) nosRegs (hz _ (Or.inr rfl)) (by simpa using hok.2)⟩

/-- The names at entry: each limb of the stack as it is. -/
def ρ₀ (m₀ : RS) : CV → BitVec 64
  | .cell _ c l => ld64 m₀.mem (cellAddr m₀ c l)
  | _ => 0

set_option maxHeartbeats 1000000 in
/-- **At entry** the abstract state describes a coherent machine. -/
theorem inv_entry (m₀ : RS) (hc : Coherent m₀) : Inv m₀ (ρ₀ m₀) 0 CS.entry m₀ := by
  have hW : W = cwin.natAbs + 2 := rfl
  have hx : ∀ k : Nat, BitVec.ofInt 64 (sp₀ m₀ + -(k : Int)) = m₀.regs .x23 - BitVec.ofNat 64 k := by
    intro k; rw [← Int.sub_eq_add_neg, ofInt_sub', BitVec.ofInt_natCast]; simp [sp₀]
  refine ⟨by decide, by simp [CS.entry, sp₀], rfl, (fun L hL => by cases hL), (fun k hk => by cases hk),
    ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · intro r v hv
    cases r <;> simp [CS.rv, CS.entry, tosRegs, nosRegs, List.zipIdx] at hv <;> subst hv <;>
      simp only [Holds, val, ρ₀] <;> (try simp [sp₀]) <;> intro hle
    all_goals first
      | (have := hc.1 (by simpa using hle); simp [tosRegs, List.zipIdx] at this
         rw [show (-1 : Int) = -((1 : Nat) : Int) by rfl, cellAddr, hx]; exact this _ _ (by simp))
      | (have := hc.2 (by simpa using hle); simp [nosRegs, List.zipIdx] at this
         rw [show (-2 : Int) = -((2 : Nat) : Int) by rfl, cellAddr, hx]; exact this _ _ (by simp))
  · intro c l _ _; simp [CS.mv, CS.entry, Holds, val, ρ₀]
  · intro r v hv
    cases r <;> simp [CS.rv, CS.entry, tosRegs, nosRegs, List.zipIdx] at hv <;> subst hv <;>
      simp [Fr, hW] <;> decide
  · intro c l hc'; simp [CS.mv, CS.entry, Fr, hc']

/-! ## The runs the analysis follows, and the one memory assumption -/

/-- A run of the body paired with the analysis's state along it (`d` steps in). -/
inductive JR (is : List AInstr) (m₀ : RS) : Nat → Nat → CS → RS → Prop
  | start : JR is m₀ 0 0 CS.entry m₀
  | fall {d j s m i out m'} : JR is m₀ d j s m → is[j]? = some i → cstep d i s = some out →
      noFallthrough i = false → isCall i = false → Exec i m m' → JR is m₀ (d + 1) (j + 1) out m'
  | call {d j s m i out m'} : JR is m₀ d j s m → is[j]? = some i → cstep d i s = some out →
      isCall i = true → CallExec m m' → JR is m₀ (d + 1) (j + 1) out m'
  | jump {d j s m i out k} : JR is m₀ d j s m → is[j]? = some i → cstep d i s = some out →
      (localBranch i).bind (labelTarget is j) = some k →
      (∀ c l, i = .bcLbl c l → bcHolds c m.flags = true) → JR is m₀ (d + 1) k (ctaken false i s out) m

/-- **Arena separation**, the one assumption about memory: on every run, an instruction
    that is not a call, that may write memory (a store form, or one outside the modelled
    subset), and that the analysis does not place in the stack — a store through a base
    that is not a stack-word address: EVM memory, the state, the C frame — leaves the
    stack words sp₀−W … sp₀+W unchanged. Calls need no such assumption: the analysis
    forgets the whole stack at a call. -/
def Sep (is : List AInstr) (m₀ : RS) : Prop :=
  ∀ d j s m i out m', JR is m₀ d j s m → is[j]? = some i → cstep d i s = some out →
    noFallthrough i = false → isCall i = false → Exec i m m' → mayWrite i m → placed s i = false →
    WinKept m₀ m m'

/-- `cwalk` found nothing on the paths from (d, j, s) within `F + 1` steps. -/
def Clean (is : List AInstr) (d j : Nat) (s : CS) : Prop := ∃ F, cwalk is false (F + 1) d j s = []

theorem clean_step {is : List AInstr} {d j : Nat} {s : CS} {i : AInstr} (hcl : Clean is d j s)
    (hi : is[j]? = some i) (hb : i ≠ .brCont) :
    ∃ out, cstep d i s = some out ∧ ∀ k e, (k, e) ∈ cedges is j i s out → Clean is (d + 1) k e := by
  obtain ⟨F, hF⟩ := hcl
  have e : cwalk is false (F + 1) d j s = (match cstep d i s false with
      | none => [j]
      | some out => (cedges is j i s out false).flatMap fun (k, e) => cwalk is false F (d + 1) k e) := by
    rw [cwalk, hi]; cases i <;> first | (exact absurd rfl hb) | rfl
  rw [e] at hF
  cases hout : cstep d i s false with
  | none => rw [hout] at hF; cases hF
  | some out =>
    rw [hout] at hF
    refine ⟨out, rfl, fun k e hke => ?_⟩
    have := List.flatMap_eq_nil_iff.mp hF (k, e) hke
    cases F with
    | zero => simp [cwalk] at this
    | succ F => exact ⟨F, this⟩

theorem clean_exit {is : List AInstr} {d j : Nat} {s : CS} (hcl : Clean is d j s)
    (hi : is[j]? = some .brCont) : exitOk s false = true := by
  obtain ⟨F, hF⟩ := hcl
  simp only [cwalk, hi] at hF
  split at hF
  · assumption
  · cases hF

theorem mem_fall {is : List AInstr} {j : Nat} {i : AInstr} {s out : CS} (h : noFallthrough i = false) :
    (j + 1, out) ∈ cedges is j i s out := by simp [cedges, h]

theorem mem_jump {is : List AInstr} {j k : Nat} {i : AInstr} {s out : CS}
    (h : (localBranch i).bind (labelTarget is j) = some k) :
    (k, ctaken false i s out) ∈ cedges is j i s out := by simp [cedges, h]

theorem call_fall {i : AInstr} (h : isCall i = true) : noFallthrough i = false := by
  cases i <;> simp_all [isCall, noFallthrough]

/-- **The simulation**: along every run the analysis follows, its state describes the machine. -/
theorem jr_inv {is : List AInstr} {m₀ : RS} (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (hc : Coherent m₀)
    (hsep : Sep is m₀) (hcl : Clean is 0 0 CS.entry) :
    ∀ {d j s m}, JR is m₀ d j s m → Clean is d j s ∧ ∃ ρ, Inv m₀ ρ d s m := by
  intro d j s m hjr
  induction hjr with
  | start => exact ⟨hcl, _, inv_entry m₀ hc⟩
  | @fall d j s m i out m' hjr hi hcs hnf hcall hex ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    have hb : i ≠ .brCont := by intro e; subst e; simp [noFallthrough] at hnf
    obtain ⟨out', hout', hall⟩ := clean_step hcl' hi hb
    rw [hcs] at hout'; cases hout'
    exact ⟨hall _ _ (mem_fall hnf), _, fall_inv hinv hcs hcall hex
      (fun hw hpl => hsep d j s m i out m' hjr hi hcs hnf hcall hex hw hpl)⟩
  | @call d j s m i out m' hjr hi hcs hcall hx ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    have hb : i ≠ .brCont := by intro e; subst e; simp [isCall] at hcall
    obtain ⟨out', hout', hall⟩ := clean_step hcl' hi hb
    rw [hcs] at hout'; cases hout'
    refine ⟨hall _ _ (mem_fall (call_fall hcall)), ext m₀ ρ d m', ?_⟩
    cases i <;> simp [isCall] at hcall <;> simp only [cstep, defs, storeAddrRegs] at hcs <;>
      simp at hcs <;> subst hcs <;> exact inv_call hinv hx
  | @jump d j s m i out k hjr hi hcs hk hbc ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    obtain ⟨l, hl⟩ : ∃ l, localBranch i = some l := by
      cases e : localBranch i with
      | none => simp [e] at hk
      | some l => exact ⟨l, rfl⟩
    have hb : i ≠ .brCont := by intro e; subst e; simp [localBranch] at hl
    obtain ⟨out', hout', hall⟩ := clean_step hcl' hi hb
    rw [hcs] at hout'; cases hout'
    exact ⟨hall _ _ (mem_jump hk), _, jump_inv hsp hinv hcs hl hbc⟩

theorem nf_ne {i : AInstr} (h : noFallthrough i = false) : i ≠ .brCont := by
  intro e; subst e; simp [noFallthrough] at h

theorem lb_ne {is : List AInstr} {j k : Nat} {i : AInstr} (h : (localBranch i).bind (labelTarget is j) = some k) :
    i ≠ .brCont := by
  intro e; subst e; simp [localBranch] at h

/-- Every concrete run is one the analysis follows (it has a state for every step). -/
theorem reach_jr {is : List AInstr} {m₀ : RS} (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (hc : Coherent m₀)
    (hsep : Sep is m₀) (hcl : Clean is 0 0 CS.entry) :
    ∀ {j m}, Reach is m₀ j m → ∃ d s, JR is m₀ d j s m := by
  intro j m hr
  induction hr with
  | start => exact ⟨0, _, .start⟩
  | step hr hst ih =>
    obtain ⟨d, s, hjr⟩ := ih
    obtain ⟨hcl', -⟩ := jr_inv hsp hc hsep hcl hjr
    cases hst with
    | fall hi hnf hcall hex =>
      obtain ⟨out, hout, -⟩ := clean_step hcl' hi (nf_ne hnf)
      exact ⟨_, _, .fall hjr hi hout hnf hcall hex⟩
    | call hi hcall hx =>
      obtain ⟨out, hout, -⟩ := clean_step hcl' hi (nf_ne (call_fall hcall))
      exact ⟨_, _, .call hjr hi hout hcall hx⟩
    | jump hi hk hbc =>
      obtain ⟨out, hout, -⟩ := clean_step hcl' hi (lb_ne hk)
      exact ⟨_, _, .jump hjr hi hout hk hbc⟩

theorem eraseDups_nil {α : Type} [BEq α] {l : List α} (h : l.eraseDups = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t => simp [List.eraseDups_cons] at h

/-- **Soundness of the stack-cache check** (ARM64). If `cacheIncoherent` finds nothing in
    a flattened body, then every run of it that starts with sp ∈ [0, 1024] and a coherent
    cache, and in which the stores the analysis does not place in the stack do not touch
    it (`Sep`), reaches every `br x27` with the cache coherent for the sp it leaves. -/
theorem cacheIncoherent_sound (is : List AInstr) (h : cacheIncoherent is = []) (m₀ : RS)
    (hsp : 0 ≤ sp₀ m₀ ∧ sp₀ m₀ ≤ 1024) (hc : Coherent m₀) (hsep : Sep is m₀) :
    ∀ j m, Reach is m₀ j m → is[j]? = some .brCont → Coherent m := by
  intro j m hr hb
  have hcl : Clean is 0 0 CS.entry := ⟨is.length, eraseDups_nil h⟩
  obtain ⟨d, s, hjr⟩ := reach_jr hsp hc hsep hcl hr
  obtain ⟨hcl', ρ, hinv⟩ := jr_inv hsp hc hsep hcl hjr
  exact coherent_of_exitOk hsp hinv (clean_exit hcl' hb)

/-! ## What the soundness proof made the check reject

The value numbering this replaced (a join over all paths with a `phi` per difference)
accepted each of these bodies, and each breaks the cache on some run: -/

/-- A join took the reloaded TOS of the sp ≥ 1 side for the sp < 1 side, and a push after
    the join made the stale word owed (sp₀ = 0: x6 is not stack[0] at exit). -/
theorem rejects_vacuous_join_then_push : (cacheIncoherent
    [ .cmpImm .x23 1, .bcLbl .lt "L",
      .movReg .x10 .x6, .movReg .x11 .x7, .movReg .x12 .x8, .movReg .x13 .x9,
      .addImm .x14 .x23 0, .addLsl5 .x14 .x24 .x14,
      .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
      .label "L", .addImm .x23 .x23 1, .brCont ]).isEmpty = false := by decide

/-- The TOS parked in callee-saved registers across a call that may rewrite stack[sp-1]
    (a helper writes its result through a stack pointer). -/
theorem rejects_tos_across_call : (cacheIncoherent
    [ .movReg .x19 .x6, .movReg .x25 .x7, .movReg .x28 .x8, .movReg .x29 .x9,
      .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .movReg .x26 .x14,
      .blSym "_eita_helper_mul",
      .movReg .x6 .x19, .movReg .x7 .x25, .movReg .x8 .x28, .movReg .x9 .x29,
      .ldpOff .x10 .x11 .x26 0, .ldpOff .x12 .x13 .x26 16, .brCont ]).isEmpty = false := by decide

/-- sp or the stack base written by anything but `sub|add x23, x23, #k`; a zero store
    into a stack word. -/
theorem rejects_untracked_sp_writes :
    (cacheIncoherent [ .movReg .x23 .x0, .brCont ]).isEmpty = false ∧
    (cacheIncoherent [ .addImm .x24 .x24 32, .brCont ]).isEmpty = false ∧
    (cacheIncoherent [ .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
                       .ldpOff .x23 .x15 .x14 0, .brCont ]).isEmpty = false ∧
    (cacheIncoherent [ .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
                       .strZr .x14 0, .brCont ]).isEmpty = false := by decide

end Evm.CL.CacheSound
