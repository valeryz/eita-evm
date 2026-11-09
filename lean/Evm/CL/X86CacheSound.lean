/-
  Evm.CL.X86CacheSound — the x86-64 stack-cache check (`X86Cache.xcacheIncoherent`) is
  sound against the x86-64 instruction semantics `X86Sem.xstep`: a lowered body it
  accepts, entered with sp ∈ [0, 1024] words and r8-r11 = stack[sp-1], reaches every
  dispatch exit (`ret`, `jmp [mem]`, `jmp reg`) with r8-r11 = stack[sp-1] for the sp it
  leaves. The register file is the x86 one (`XS.regs : XReg → BitVec 64`), so ARM names
  sharing a home are one register here, and every temporary the lowering writes is seen.

  Around `xstep` (the ARM64 proof's `AsmRun.step`): a call keeps only the SysV
  callee-saved registers (rbx, rbp, rsp, r12-r15) and may write any memory; an
  instruction `xstep` does not model writes whatever it likes to `wr i`, the flags and
  the memory; branches resolve as `X86Cache.target` does (`xskipTo`, and backward to a
  named label). `xrun_ret_coherent` restates the result for `X86Sem.xrun`.
-/

import Evm.CL.X86Cache
import Evm.CL.CacheSound
import Evm.CL.X86Interp

namespace Evm.CL.X86CacheSound

open Evm.CL.AsmRun Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Cache
open Evm.CL.X86Sem (XS XFlags xstep xcHolds subXF aluR xskipTo xCallerSaved ea)

/-! ## The machine around a body -/

/-- One instruction, falling through: `xstep` where it is defined, else anything that
    keeps the registers outside `wr i`. -/
def XExec (i : XInsn) (x x' : XS) : Prop :=
  match xstep x i with
  | some y => x' = y
  | none => ∀ r, r ∉ wr i → x'.regs r = x.regs r

/-- A call: the callee keeps the SysV callee-saved registers, nothing else. -/
def XCallExec (x x' : XS) : Prop := ∀ r, xCallerSaved r = false → x'.regs r = x.regs r

/-- One step of a lowered body (a suffix of it, and the machine). -/
inductive XStep (its : List XItem) : List XItem → XS → List XItem → XS → Prop
  | ins {i rest x x'} : isExit i = false → isCallI i = false → XExec i x x' →
      XStep its (.I i :: rest) x rest x'
  | call {it rest x x'} : isCallItem it = true → XCallExec x x' → XStep its (it :: rest) x rest x'
  | lea {it r rest x x'} : leaDst it = some r → (∀ r', r' ≠ r → x'.regs r' = x.regs r') →
      x'.mem = x.mem → XStep its (it :: rest) x rest x'
  | skip {it rest x} : isSkip it = true → XStep its (it :: rest) x rest x
  | take {c l rest q x} : xcHolds c x.flags = true → target its rest l = some q →
      XStep its (.Jcc c l :: rest) x q x
  | jmp {l rest q x} : target its rest l = some q → XStep its (.Jmp l :: rest) x q x

/-- The states a body reaches from its entry. -/
inductive XReach (its : List XItem) (x₀ : XS) : List XItem → XS → Prop
  | start : XReach its x₀ its x₀
  | step {p x q x'} : XReach its x₀ p x → XStep its p x q x' → XReach its x₀ q x'

/-! ## The stack and the cache -/

/-- **The x86-64 stack-cache invariant**: r8-r11 = stack[sp-1] (`[r12 + r13 - 32 + 8l]`),
    if that word exists (r13 ≥ 32). -/
def XCoherent (x : XS) : Prop :=
  32 ≤ (x.regs .r13).toInt → ∀ r l, (r, l) ∈ tosX.zipIdx →
    x.regs r = ld64 x.mem (x.regs .r12 + x.regs .r13 + BitVec.ofInt 64 (8 * (l : Int) - 32))

/-- sp at entry, in words. -/
def sp₀ (x₀ : XS) : Int := (((x₀.regs .r13).toNat / 32 : Nat) : Int)

/-- Entry sp: a whole number of words, at most 1024. -/
def SpOk (x₀ : XS) : Prop := (x₀.regs .r13).toNat % 32 = 0 ∧ (x₀.regs .r13).toNat ≤ 32768

def cellAddr (x₀ : XS) (c : Int) (l : Nat) : BitVec 64 :=
  x₀.regs .r12 + BitVec.ofInt 64 (32 * (sp₀ x₀ + c) + 8 * l)

/-! ## Values -/

def val (x₀ : XS) (ρ : XV → BitVec 64) : XV → BitVec 64
  | .idx c => BitVec.ofInt 64 (32 * (sp₀ x₀ + c))
  | .addr c => x₀.regs .r12 + BitVec.ofInt 64 (32 * (sp₀ x₀ + c))
  | .base => x₀.regs .r12
  | .when _ v => val x₀ ρ v
  | v => ρ v

def Holds (x₀ : XS) (ρ : XV → BitVec 64) : XV → BitVec 64 → Prop
  | .when k v, y => k ≤ sp₀ x₀ → Holds x₀ ρ v y
  | v, y => y = val x₀ ρ v

def Fr (d g : Nat) : XV → Prop
  | .cell g' c _ => g' ≤ g ∧ c.natAbs ≤ W
  | .idx c | .addr c => c.natAbs ≤ cwin.natAbs
  | .base => True
  | .fresh k => k < d
  | .when _ v => Fr d g v

/-- The names step d makes: `fresh d` is `v`, `cell (d+1)` the memory `mem'`. -/
def ext (x₀ : XS) (ρ : XV → BitVec 64) (d : Nat) (v : BitVec 64) (mem' : AsmRun.Mem) : XV → BitVec 64
  | .fresh k => if k = d then v else ρ (.fresh k)
  | .cell g c l => if g = d + 1 then ld64 mem' (cellAddr x₀ c l) else ρ (.cell g c l)
  | w => ρ w

structure Inv (x₀ : XS) (ρ : XV → BitVec 64) (d : Nat) (s : XCS) (x : XS) : Prop where
  off  : s.off.natAbs ≤ cwin.natAbs
  r13  : x.regs .r13 = BitVec.ofInt 64 (32 * (sp₀ x₀ + s.off))
  r12  : x.regs .r12 = x₀.regs .r12
  lt   : ∀ L, s.lt = some L → sp₀ x₀ + s.off < L
  fl   : ∀ k, s.fl = some k → x.flags = subXF (x.regs .r13) (BitVec.ofInt 64 k)
  regs : ∀ r v, s.rv r = some v → Holds x₀ ρ v (x.regs r)
  mem  : ∀ c l, c.natAbs ≤ W → l < 4 → Holds x₀ ρ (s.mv c l) (ld64 x.mem (cellAddr x₀ c l))
  gen  : s.gen ≤ d
  frR  : ∀ r v, s.rv r = some v → Fr d s.gen v
  frM  : ∀ c l, c.natAbs ≤ W → Fr d s.gen (s.mv c l)

/-! ### Names: a step's names are new -/

theorem val_ext (x₀ : XS) (ρ : XV → BitVec 64) (d g : Nat) (v : BitVec 64) (mem' : AsmRun.Mem) (hg : g ≤ d) :
    ∀ w, Fr d g w → val x₀ (ext x₀ ρ d v mem') w = val x₀ ρ w
  | .cell g' c l, h => by simp only [val, ext, Fr] at h ⊢; rw [ite_eq_right (by omega)]
  | .idx _, _ | .addr _, _ | .base, _ => rfl
  | .fresh k, h => by simp only [val, ext, Fr] at h ⊢; rw [ite_eq_right (by omega)]
  | .when _ w, h => by simp only [val, Fr] at h ⊢; exact val_ext x₀ ρ d g v mem' hg w h

theorem holds_ext (x₀ : XS) (ρ : XV → BitVec 64) (d g : Nat) (v : BitVec 64) (mem' : AsmRun.Mem) (hg : g ≤ d) :
    ∀ w y, Fr d g w → (Holds x₀ (ext x₀ ρ d v mem') w y ↔ Holds x₀ ρ w y)
  | .when k w, y, h => by
      simp only [Holds, Fr] at h ⊢; rw [holds_ext x₀ ρ d g v mem' hg w y h]
  | .cell .., y, h | .idx _, y, h | .addr _, y, h | .base, y, h | .fresh .., y, h => by
      simp only [Holds]; rw [val_ext x₀ ρ d g v mem' hg _ h]

theorem fr_mono {d d' g g' : Nat} (hd : d ≤ d') (hg : g ≤ g') : ∀ v, Fr d g v → Fr d' g' v
  | .cell .., h => by simp only [Fr] at h ⊢; omega
  | .idx _, h | .addr _, h | .base, h => h
  | .fresh .., h => by simp only [Fr] at h ⊢; omega
  | .when _ v, h => fr_mono hd hg v h

theorem holds_strip (x₀ : XS) (ρ : XV → BitVec 64) (t : Int) (ht : t ≤ sp₀ x₀) :
    ∀ v y, Holds x₀ ρ v y → v.okAt t = true → y = val x₀ ρ v.strip
  | .when k v, y, h, hok => by
      simp only [XV.okAt, Bool.and_eq_true, decide_eq_true_eq] at hok
      simp only [Holds] at h; simp only [XV.strip]
      exact holds_strip x₀ ρ t ht v y (h (by omega)) hok.2
  | .cell .., _, h, _ | .idx _, _, h, _ | .addr _, _, h, _ | .base, _, h, _ | .fresh .., _, h, _ => h

/-! ### The abstract state, observed through `rv` / `mv` -/

@[simp] theorem rv_r13 (s : XCS) : s.rv .r13 = some (.idx s.off) := by simp [XCS.rv]
@[simp] theorem rv_r12 (s : XCS) : s.rv .r12 = some .base := by simp [XCS.rv]

theorem rv_setR (s : XCS) (r r' : XReg) (v : Option XV) (h13 : r' ≠ .r13) (h12 : r' ≠ .r12) :
    (s.setR r v).rv r' = if r' = r then v else s.rv r' := by
  simp only [XCS.rv, XCS.setR, h13, h12, ite_false]
  cases v with
  | none => simp only [List.nil_append, Evm.CL.CacheSound.find_filter_ne]; split <;> simp
  | some v =>
    simp only [List.singleton_append, List.find?_cons]
    by_cases e : r' = r
    · subst e; simp
    · have : (r == r') = false := by simp; exact fun x => e x.symm
      simp only [this, ite_false, Evm.CL.CacheSound.find_filter_ne, e]

@[simp] theorem setR_off (s : XCS) (r : XReg) (v : Option XV) : (s.setR r v).off = s.off := rfl
@[simp] theorem setR_lt (s : XCS) (r : XReg) (v : Option XV) : (s.setR r v).lt = s.lt := rfl
@[simp] theorem setR_fl (s : XCS) (r : XReg) (v : Option XV) : (s.setR r v).fl = s.fl := rfl
@[simp] theorem setR_gen (s : XCS) (r : XReg) (v : Option XV) : (s.setR r v).gen = s.gen := rfl
@[simp] theorem setR_mem (s : XCS) (r : XReg) (v : Option XV) : (s.setR r v).mem = s.mem := rfl
@[simp] theorem setM_off (s : XCS) (c : Int) (l : Nat) (v : XV) : (s.setM c l v).off = s.off := rfl
@[simp] theorem setM_lt (s : XCS) (c : Int) (l : Nat) (v : XV) : (s.setM c l v).lt = s.lt := rfl
@[simp] theorem setM_fl (s : XCS) (c : Int) (l : Nat) (v : XV) : (s.setM c l v).fl = s.fl := rfl
@[simp] theorem setM_gen (s : XCS) (c : Int) (l : Nat) (v : XV) : (s.setM c l v).gen = s.gen := rfl
@[simp] theorem setM_regs (s : XCS) (c : Int) (l : Nat) (v : XV) : (s.setM c l v).regs = s.regs := rfl

theorem mv_setR (s : XCS) (r : XReg) (v : Option XV) (c : Int) (l : Nat) :
    (s.setR r v).mv c l = s.mv c l := rfl

theorem rv_setM (s : XCS) (c : Int) (l : Nat) (v : XV) (r : XReg) : (s.setM c l v).rv r = s.rv r := rfl

theorem mv_setM (s : XCS) (c c' : Int) (l l' : Nat) (v : XV) :
    (s.setM c l v).mv c' l' = if (c', l') = (c, l) then v else s.mv c' l' := by
  simp only [XCS.mv, XCS.setM, List.find?_cons]
  by_cases e : (c', l') = (c, l)
  · have : ((c, l) == (c', l')) = true := by simp [e]
    simp [e]
  · have : ((c, l) == (c', l')) = false := by simp; intro a b; exact e (by rw [a, b])
    simp only [this, e, ite_false]
    rw [Evm.CL.CacheSound.find_filter_ne]; simp [e]

theorem rv_kill (ks : List XReg) (s : XCS) (r : XReg) (h13 : r ≠ .r13) (h12 : r ≠ .r12) :
    (ks.foldl (fun s r => s.setR r none) s).rv r = if r ∈ ks then none else s.rv r := by
  induction ks generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, rv_setR _ _ _ _ h13 h12, List.mem_cons]
    by_cases hx : r = x
    · subst hx; simp
    · simp [hx]

theorem kill_fields (ks : List XReg) (s : XCS) :
    let t := ks.foldl (fun s r => s.setR r none) s
    t.off = s.off ∧ t.lt = s.lt ∧ t.fl = s.fl ∧ t.gen = s.gen ∧ t.mem = s.mem := by
  induction ks generalizing s with
  | nil => simp
  | cons x xs ih => exact ih _

/-! ## The instruction semantics: write sets -/

set_option maxHeartbeats 4000000 in
/-- **`wr` is the register write set of `xstep`.** -/
theorem xstep_regs (x x' : XS) (i : XInsn) (h : xstep x i = some x') :
    ∀ r, r ∉ wr i → x'.regs r = x.regs r := by
  intro r hr
  cases i <;> simp only [xstep] at h <;> (repeat' split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;>
    simp_all [wr, wdst, wkill, aluR, Evm.CL.X86Sem.alu, Evm.CL.X86Sem.XS.set, Evm.CL.X86Sem.XS.withFlags,
      Evm.CL.X86Sem.XS.store64, Evm.CL.X86Sem.XS.store8] <;> (try split) <;> simp_all <;>
    (try (intro e; subst e; simp_all))

set_option maxHeartbeats 4000000 in
/-- …and one that is not a store leaves the memory alone. -/
theorem xstep_mem (x x' : XS) (i : XInsn) (h : xstep x i = some x') (hs : storesX i = false) :
    x'.mem = x.mem := by
  cases i <;> simp only [xstep] at h <;> (repeat' split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;>
    simp_all [storesX, aluR, Evm.CL.X86Sem.alu, Evm.CL.X86Sem.XS.set, Evm.CL.X86Sem.XS.withFlags] <;>
    (try split) <;> simp_all

/-! ## One step -/

/-- The named words keep their limbs. -/
def WinKept (x₀ x x' : XS) : Prop :=
  ∀ c l, c.natAbs ≤ W → l < 4 → ld64 x'.mem (cellAddr x₀ c l) = ld64 x.mem (cellAddr x₀ c l)

/-- Where `Sep` is needed: a store form, or an instruction `xstep` does not model. -/
def mayWrite (i : XInsn) (x : XS) : Prop := storesX i = true ∨ xstep x i = none

/-- The analysis places a store when its operand is a stack address. -/
def placed (s : XCS) : XInsn → Bool
  | .movMR m _ => (s.wbase m).isSome
  | _ => false

theorem exec_regs {i : XInsn} {x x' : XS} (h : XExec i x x') : ∀ r, r ∉ wr i → x'.regs r = x.regs r := by
  intro r hr; unfold XExec at h
  cases e : xstep x i with
  | some y => rw [e] at h; subst h; exact xstep_regs x _ i e r hr
  | none => rw [e] at h; exact h r hr

theorem exec_win (x₀ : XS) {i : XInsn} {x x' : XS} (h : XExec i x x') (hs : mayWrite i x → WinKept x₀ x x') :
    WinKept x₀ x x' := by
  unfold XExec at h
  cases e : xstep x i with
  | some y =>
    rw [e] at h
    by_cases hst : storesX i = true
    · exact hs (Or.inl hst)
    · subst h; intro c l _ _; rw [xstep_mem x _ i e (by simpa using hst)]
  | none => exact hs (Or.inr e)

theorem exec_some {i : XInsn} {x x' y : XS} (hs : xstep x i = some y) (h : XExec i x x') : x' = y := by
  unfold XExec at h; rw [hs] at h; exact h

theorem inv_succ {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (v : BitVec 64) (mem' : AsmRun.Mem)
    (h : Inv x₀ ρ d s x) : Inv x₀ (ext x₀ ρ d v mem') (d + 1) s x where
  off := h.off
  r13 := h.r13
  r12 := h.r12
  lt := h.lt
  fl := h.fl
  regs r w hw := (holds_ext x₀ ρ d s.gen v mem' h.gen w _ (h.frR r w hw)).2 (h.regs r w hw)
  mem c l hc hl := (holds_ext x₀ ρ d s.gen v mem' h.gen _ _ (h.frM c l hc)).2 (h.mem c l hc hl)
  gen := by have := h.gen; omega
  frR r w hw := fr_mono (by omega) (Nat.le_refl _) w (h.frR r w hw)
  frM c l hc := fr_mono (by omega) (Nat.le_refl _) _ (h.frM c l hc)

theorem inv_s0 {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x) :
    Inv x₀ ρ d { s with fl := none } x :=
  { h with fl := fun k hk => by cases hk }

theorem inv_withFlags {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x)
    (hf : s.fl = none) (f : XFlags) : Inv x₀ ρ d s (x.withFlags f) :=
  { h with fl := fun k hk => by rw [hf] at hk; cases hk }

theorem isBase_r13 : isBase .r13 = true := rfl
theorem isBase_r12 : isBase .r12 = true := rfl

theorem ne_of_isBase {r : XReg} (h : isBase r = false) : r ≠ .r13 ∧ r ≠ .r12 := by
  constructor <;> (intro e; subst e; simp [isBase] at h)

/-- Set one register (not r12, r13) to a value it holds. -/
theorem inv_setR {x₀ : XS} {ρ : XV → BitVec 64} {D : Nat} {t : XCS} {xx : XS} (h : Inv x₀ ρ D t xx)
    (r : XReg) (v : Option XV) (y : BitVec 64) (hr : isBase r = false)
    (hv : ∀ w, v = some w → Holds x₀ ρ w y ∧ Fr D t.gen w) :
    Inv x₀ ρ D (t.setR r v) (xx.set r y) := by
  obtain ⟨h13, h12⟩ := ne_of_isBase hr
  have e13 : (xx.set r y).regs .r13 = xx.regs .r13 := by simp [Ne.symm h13]
  have e12 : (xx.set r y).regs .r12 = xx.regs .r12 := by simp [Ne.symm h12]
  refine ⟨h.off, ?_, ?_, h.lt, ?_, ?_, h.mem, h.gen, ?_, h.frM⟩
  · rw [e13]; exact h.r13
  · rw [e12]; exact h.r12
  · intro k hk; rw [Evm.CL.X86Sem.XS.set_flags, e13]; exact h.fl k hk
  · intro r' w hw
    by_cases a : r' = .r13
    · subst a; rw [e13]; simp only [rv_r13, setR_off] at hw; exact h.regs _ _ (by rw [rv_r13, hw])
    by_cases b : r' = .r12
    · subst b; rw [e12]; simp only [rv_r12] at hw; exact h.regs _ _ (by rw [rv_r12, hw])
    rw [rv_setR _ _ _ _ a b] at hw
    simp only [Evm.CL.X86Sem.XS.set_regs]
    split at hw
    · rename_i e; subst e; simp only [ite_true]; exact (hv w hw).1
    · rename_i e; simp only [ite_eq_right e]; exact h.regs r' w hw
  · intro r' w hw
    by_cases a : r' = .r13
    · subst a; simp only [rv_r13, setR_off] at hw; exact h.frR _ _ (by rw [rv_r13, hw])
    by_cases b : r' = .r12
    · subst b; simp only [rv_r12] at hw; exact h.frR _ _ (by rw [rv_r12, hw])
    rw [rv_setR _ _ _ _ a b] at hw
    split at hw
    · exact (hv w hw).2
    · exact h.frR r' w hw

/-- The generic write: `ks` forgotten, `dst` named `fresh d`, the flags unknown. -/
def writeSt (d : Nat) (dst : Option XReg) (ks : List XReg) (s : XCS) : XCS :=
  let t := ks.foldl (fun t r => t.setR r none) { s with fl := none }
  match dst with
  | some r => t.setR r (some (.fresh d))
  | none => t

theorem genSt_eq (d : Nat) (i : XInsn) (s : XCS) : genSt d i s = writeSt d (wdst i) (wkill i) s := rfl

theorem rv_writeSt (d : Nat) (dst : Option XReg) (ks : List XReg) (s : XCS) (r : XReg)
    (h13 : r ≠ .r13) (h12 : r ≠ .r12) :
    (writeSt d dst ks s).rv r = if dst = some r then some (.fresh d) else if r ∈ ks then none else s.rv r := by
  have k := rv_kill ks { s with fl := none } r h13 h12
  unfold writeSt
  cases dst with
  | none => simp only [k, reduceCtorEq, ite_false]; rfl
  | some r' =>
    simp only [rv_setR _ _ _ _ h13 h12, k, Option.some.injEq]
    by_cases e : r = r'
    · subst e; simp
    · simp only [e, ite_false, Ne.symm e]; rfl

theorem writeSt_fields (d : Nat) (dst : Option XReg) (ks : List XReg) (s : XCS) :
    let t := writeSt d dst ks s
    t.off = s.off ∧ t.lt = s.lt ∧ t.fl = none ∧ t.gen = s.gen ∧ ∀ c l, t.mv c l = s.mv c l := by
  obtain ⟨a, b, c, e, f⟩ := kill_fields ks { s with fl := none }
  unfold writeSt
  cases dst with
  | none => exact ⟨a, b, c, e, fun c l => by simp only [XCS.mv, f, e]⟩
  | some r => exact ⟨a, b, c, e, fun c l => by simp only [XCS.mv, setR_mem, setR_gen, f, e]⟩

/-- **The generic step**: registers outside `dst` and `ks` kept, and the window. -/
theorem inv_write {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x x' : XS}
    (dst : Option XReg) (ks : List XReg) (h : Inv x₀ ρ d s x)
    (hb : ∀ r, r ∈ dst.toList ++ ks → isBase r = false)
    (hregs : ∀ r, r ∉ dst.toList ++ ks → x'.regs r = x.regs r) (hwin : WinKept x₀ x x') :
    Inv x₀ (ext x₀ ρ d (x'.regs (dst.getD .rax)) x'.mem) (d + 1) (writeSt d dst ks s) x' := by
  obtain ⟨eoff, elt, efl, egen, emv⟩ := writeSt_fields d dst ks s
  have hs := inv_succ (x'.regs (dst.getD .rax)) x'.mem h
  have k13 : x'.regs .r13 = x.regs .r13 := hregs _ (fun m => absurd (hb _ m) (by simp [isBase]))
  have k12 : x'.regs .r12 = x.regs .r12 := hregs _ (fun m => absurd (hb _ m) (by simp [isBase]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eoff]; exact h.off
  · rw [eoff, k13]; exact h.r13
  · rw [k12]; exact h.r12
  · intro L hL; rw [elt] at hL; rw [eoff]; exact h.lt L hL
  · intro k hk; rw [efl] at hk; cases hk
  · intro r v hv
    by_cases a : r = .r13
    · subst a; simp only [rv_r13, eoff, Option.some.injEq] at hv; subst hv
      simp only [Holds, val]; rw [k13, h.r13]
    by_cases b : r = .r12
    · subst b; simp only [rv_r12, Option.some.injEq] at hv; subst hv
      simp only [Holds, val]; rw [k12, h.r12]
    rw [rv_writeSt _ _ _ _ _ a b] at hv
    split at hv
    · rename_i e; cases hv; subst e; simp [Holds, val, ext]
    · split at hv
      · cases hv
      · rename_i e1 e2
        have : r ∉ dst.toList ++ ks := by
          simp only [List.mem_append, Option.mem_toList, not_or]; exact ⟨fun e => e1 (by rw [e]), e2⟩
        rw [hregs r this]; exact hs.regs r v hv
  · intro c l hc hl; rw [emv, hwin c l hc hl]; exact hs.mem c l hc hl
  · rw [egen]; exact hs.gen
  · intro r v hv
    rw [egen]
    by_cases a : r = .r13
    · subst a; simp only [rv_r13, eoff, Option.some.injEq] at hv; subst hv; exact h.off
    by_cases b : r = .r12
    · subst b; simp only [rv_r12, Option.some.injEq] at hv; subst hv; trivial
    rw [rv_writeSt _ _ _ _ _ a b] at hv
    split at hv
    · cases hv; simp only [Fr]; omega
    · split at hv
      · cases hv
      · exact hs.frR r v hv
  · intro c l hc; rw [egen, emv]; exact hs.frM c l hc

/-! ### Address arithmetic -/

theorem ofInt_ne (x y : Int) (h : x ≠ y) (h2 : (x - y).natAbs < 18446744073709551616) :
    BitVec.ofInt 64 x ≠ BitVec.ofInt 64 y := Evm.CL.CacheSound.ofInt_ne x y h h2

/-- Two named limbs never overlap (the window is far smaller than 2^64). -/
theorem cell_disj (x₀ : XS) (c c' : Int) (l l' : Nat) (hc : c.natAbs ≤ W) (hc' : c'.natAbs ≤ W)
    (hl : l < 4) (hl' : l' < 4) (hne : (c, l) ≠ (c', l')) :
    ∀ i < 8, ∀ j < 8, off (cellAddr x₀ c l) i ≠ off (cellAddr x₀ c' l') j := by
  intro i hi j hj e
  simp only [cellAddr, off, BitVec.add_assoc, BitVec.add_right_inj] at e
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add, ← BitVec.ofInt_add] at e
  have hW : W = 65538 := rfl
  refine ofInt_ne _ _ ?_ ?_ e
  · intro h; apply hne; simp only [Prod.mk.injEq]; omega
  · omega

theorem ea_def (x : XS) (m : X86Encode.Mem) :
    ea x m = x.regs m.base + (match m.index with | some i => x.regs i * BitVec.ofNat 64 m.scale | none => 0) +
      BitVec.ofInt 64 m.disp := rfl

/-- An operand the analysis reads as a stack word's: its address. -/
theorem ea_wbase {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x)
    (m : X86Encode.Mem) {c : Int} (hw : s.wbase m = some c) :
    ea x m = x₀.regs .r12 + BitVec.ofInt 64 (32 * (sp₀ x₀ + c) + m.disp) ∧ c.natAbs ≤ cwin.natAbs := by
  obtain ⟨b, ix, sc, dp⟩ := m
  rw [ea_def]
  unfold XCS.wbase at hw
  cases ix with
  | none =>
    simp only at hw ⊢
    cases hb : s.rv b with
    | none => rw [hb] at hw; cases hw
    | some v =>
      rw [hb] at hw
      cases v <;> simp only [reduceCtorEq] at hw
      rename_i c'; cases hw
      have e := h.regs b _ hb; simp only [Holds, val] at e
      have hf := h.frR b _ hb; simp only [Fr] at hf
      refine ⟨?_, hf⟩
      rw [e, BitVec.ofInt_add]; simp [BitVec.add_assoc]
  | some i =>
    simp only at hw ⊢
    by_cases hs : sc = 1
    · subst hs
      simp only [ite_true] at hw
      cases hb : s.rv b with
      | none => rw [hb] at hw; cases hw
      | some vb =>
        cases hi : s.rv i with
        | none => rw [hb, hi] at hw; cases vb <;> cases hw
        | some vi =>
          rw [hb, hi] at hw
          have eb := h.regs b _ hb
          have ei := h.regs i _ hi
          have fb := h.frR b _ hb
          have fi := h.frR i _ hi
          cases vb <;> cases vi <;> simp only [reduceCtorEq, Option.some.injEq] at hw <;> subst hw <;>
            simp only [Holds, val, Fr] at eb ei fb fi <;> refine ⟨?_, by assumption⟩ <;>
            rw [eb, ei, BitVec.ofInt_add] <;> simp only [BitVec.mul_one] <;> ac_rfl
    · simp only [hs, ite_false] at hw; cases hw

theorem toNat_limb (dp : Int) : (((dp % 32 / 8).toNat : Nat) : Int) = dp % 32 / 8 :=
  Int.toNat_of_nonneg (Int.ediv_nonneg (Int.emod_nonneg _ (by decide)) (by decide))

/-- A whole limb of a named word. -/
theorem ea_cellOf {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x)
    (m : X86Encode.Mem) {c : Int} {l : Nat} (hc : s.cellOf m = some (c, l)) :
    ea x m = cellAddr x₀ c l ∧ c.natAbs ≤ W ∧ l < 4 := by
  unfold XCS.cellOf at hc
  cases hw : s.wbase m with
  | none => rw [hw] at hc; cases hc
  | some cb =>
    rw [hw] at hc
    simp only at hc
    split at hc
    · rename_i hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨he, -⟩ := ea_wbase h m hw
      have t := toNat_limb m.disp
      refine ⟨?_, hd.2, ?_⟩
      · rw [he, cellAddr]; congr 2; rw [t]; omega
      · omega
    · cases hc

theorem XS_set_self (x : XS) (r : XReg) : x.set r (x.regs r) = x := by
  cases x; simp only [Evm.CL.X86Sem.XS.set, XS.mk.injEq, and_true]
  funext r'; split <;> simp_all

/-- Store register r into a named limb. -/
theorem inv_store {x₀ : XS} {ρ : XV → BitVec 64} {D : Nat} {t : XCS} {xx : XS} (h : Inv x₀ ρ D t xx)
    (j : Nat) (hj : j < D) (r : XReg) (hρ : ρ (.fresh j) = xx.regs r)
    (c : Int) (hc : c.natAbs ≤ W) (l : Nat) (hl : l < 4) :
    Inv x₀ ρ D (XCS.store j t c l r) (xx.store64 (cellAddr x₀ c l) (xx.regs r)) := by
  obtain ⟨v, t1, ht1, hv, hfv, hstore⟩ : ∃ v t1, Inv x₀ ρ D t1 xx ∧ Holds x₀ ρ v (xx.regs r) ∧
      Fr D t1.gen v ∧ XCS.store j t c l r = t1.setM c l v := by
    unfold XCS.store
    split
    · rename_i v hv
      exact ⟨v, t, h, h.regs r v hv, h.frR r v hv, rfl⟩
    · rename_i hn
      have hb : isBase r = false := by
        cases r <;> simp_all [isBase]
      refine ⟨.fresh j, t.setR r (some (.fresh j)), ?_, by simp [Holds, val, hρ], by simp [Fr, hj], rfl⟩
      have := inv_setR h r (some (.fresh j)) (xx.regs r) hb
        (fun w hw => by cases hw; exact ⟨by simp [Holds, val, hρ], by simp [Fr, hj]⟩)
      rwa [XS_set_self] at this
  rw [hstore]
  refine ⟨ht1.off, ht1.r13, ht1.r12, ht1.lt, ht1.fl, ?_, ?_, ht1.gen, ht1.frR, ?_⟩
  · intro r' w hw; rw [rv_setM] at hw; exact ht1.regs r' w hw
  · intro c' l' hc' hl'
    simp only [Evm.CL.X86Sem.XS.store64_mem, mv_setM]
    split
    · rename_i e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [Evm.CL.AsmRun.ld64_st64_same]; exact hv
    · rename_i e
      rw [Evm.CL.AsmRun.ld64_st64_disj]
      · exact ht1.mem c' l' hc' hl'
      · exact cell_disj x₀ c' c l' l hc' hc hl' hl e
  · intro c' l' hc'; simp only [mv_setM]; split
    · exact hfv
    · exact ht1.frM c' l' hc'

/-! ### The instructions the analysis follows -/

theorem rv_moved (s : XCS) (o : Int) (lt : Option Int) (fl : Option Int) (r : XReg) (h : r ≠ .r13) :
    ({ s with off := o, lt := lt, fl := fl } : XCS).rv r = s.rv r := by
  simp [XCS.rv, h]

/-- `add|sub r13, #32k`: sp moves by δ words. -/
theorem inv_spAdj {x₀ : XS} {ρ : XV → BitVec 64} {D : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ D s x)
    (δ : Int) (hδ : (s.off + δ).natAbs ≤ cwin.natAbs) (y : BitVec 64)
    (hy : y = BitVec.ofInt 64 (32 * (sp₀ x₀ + (s.off + δ)))) (f : XFlags) :
    Inv x₀ ρ D { s with off := s.off + δ, lt := s.lt.map (· + δ), fl := none } ((x.set .r13 y).withFlags f) := by
  refine ⟨hδ, by simp [hy], by simp [h.r12], ?_, by simp, ?_, ?_, h.gen, ?_, ?_⟩
  · intro L hL; simp only [Option.map_eq_some_iff] at hL; obtain ⟨L0, h0, rfl⟩ := hL
    have := h.lt L0 h0; show sp₀ x₀ + (s.off + δ) < L0 + δ; omega
  · intro r v hv
    by_cases e : r = .r13
    · subst e; simp only [rv_r13, Option.some.injEq] at hv; subst hv; simp [Holds, val, hy]
    · rw [rv_moved _ _ _ _ _ e] at hv
      simp only [Evm.CL.X86Sem.XS.withFlags_regs, Evm.CL.X86Sem.XS.set_regs, ite_eq_right e]; exact h.regs r v hv
  · intro c l hc hl; exact h.mem c l hc hl
  · intro r v hv
    by_cases e : r = .r13
    · subst e; simp only [rv_r13, Option.some.injEq] at hv; subst hv; exact hδ
    · rw [rv_moved _ _ _ _ _ e] at hv; exact h.frR r v hv
  · intro c l hc; exact h.frM c l hc

theorem ofInt_sub' (a b : Int) : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b :=
  Evm.CL.CacheSound.ofInt_sub' a b

/-- An instruction that writes r12 or r13: only `add|sub r13, #32k` is followed. -/
theorem ins_base {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s t : XCS} {x x' : XS} {i : XInsn}
    (h : Inv x₀ ρ d s x) (hb : (wr i).any isBase = true) (hc : xcstep d i s = some t) (hex : XExec i x x') :
    Inv x₀ ρ d t x' := by
  simp only [xcstep, hb, ite_true] at hc
  cases i <;> simp only [reduceCtorEq] at hc
  rename_i o dd k
  split at hc
  · rename_i hk; obtain ⟨rfl, hk⟩ := hk
    cases o <;> simp only [reduceCtorEq] at hc
    · unfold spAdj at hc; split at hc
      · rename_i hw; cases hc
        rw [exec_some rfl hex]
        exact inv_spAdj h _ hw _ (by rw [h.r13, ← BitVec.ofInt_add]; congr 1; omega) _
      · cases hc
    · unfold spAdj at hc; split at hc
      · rename_i hw; cases hc
        rw [exec_some rfl hex]
        exact inv_spAdj h _ hw _ (by rw [h.r13, ← ofInt_sub']; congr 1; omega) _
      · cases hc
  · cases hc

/-- `cmp r13, #k`: the flags are those of sp − k. -/
theorem ins_cmp {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x x' : XS} (k : Int)
    (h : Inv x₀ ρ d s x) (hex : XExec (.aluRI .cmp .r13 k) x x') :
    Inv x₀ ρ d { s with fl := some k } x' := by
  rw [exec_some rfl hex]
  exact { h with fl := fun k' hk => by cases hk; rfl }

/-- Everything else: `genSt`, through the generic step. -/
theorem ins_other {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s t : XCS} {x x' : XS} {i : XInsn}
    (h : Inv x₀ ρ d s x) (hb : (wr i).any isBase = false)
    (ho : (if storesX i && ((storeMem i).bind s.wbase).isSome then none else some (genSt d i s)) = some t)
    (hex : XExec i x x') (hsep : mayWrite i x → placed s i = false → WinKept x₀ x x') (hpl : placed s i = false) :
    ∃ v, Inv x₀ (ext x₀ ρ d v x'.mem) (d + 1) t x' := by
  split at ho
  · cases ho
  · cases ho
    rw [genSt_eq]
    refine ⟨_, inv_write (wdst i) (wkill i) h ?_ (exec_regs hex) (exec_win x₀ hex (fun hw => hsep hw hpl))⟩
    intro r hr
    have := List.any_eq_false.mp hb r hr
    simpa using this

/-- What `lea` computes, when the analysis names it. -/
theorem leaV_holds {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x)
    (m : X86Encode.Mem) {w : XV} (hw : s.leaV m = some w) (ρ' : XV → BitVec 64) (D g : Nat) :
    Holds x₀ ρ' w (ea x m) ∧ Fr D g w := by
  unfold XCS.leaV at hw
  split at hw
  · cases hw
  rename_i hd
  have hd : m.disp % 32 = 0 := by simpa using hd
  cases hb : s.wbase m with
  | some c =>
    rw [hb] at hw; simp only at hw
    split at hw
    · rename_i hc; cases hw
      obtain ⟨he, -⟩ := ea_wbase h m hb
      refine ⟨?_, hc⟩
      simp only [Holds, val]; rw [he]; congr 2; omega
    · cases hw
  | none =>
    rw [hb] at hw; simp only at hw
    split at hw
    · rename_i c hix hbase
      split at hw
      · rename_i hc; cases hw
        have e := h.regs _ _ hbase; simp only [Holds, val] at e
        refine ⟨?_, hc⟩
        simp only [Holds, val]; rw [ea_def, hix, e]
        have : 32 * (sp₀ x₀ + (c + m.disp / 32)) = 32 * (sp₀ x₀ + c) + m.disp := by omega
        rw [this, BitVec.ofInt_add]; simp
      · cases hw
    · cases hw

/-- What `add d, a` computes, when the analysis names it. -/
theorem addV_holds {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (h : Inv x₀ ρ d s x)
    (dd a : XReg) (ρ' : XV → BitVec 64) (hρ : ρ' (.fresh d) = x.regs dd + x.regs a) :
    Holds x₀ ρ' (addV d (s.rv dd) (s.rv a)) (x.regs dd + x.regs a) ∧ Fr (d + 1) s.gen (addV d (s.rv dd) (s.rv a)) := by
  unfold addV
  split
  · rename_i c hd ha
    have e1 := h.regs _ _ hd; have e2 := h.regs _ _ ha; have f := h.frR _ _ hd
    simp only [Holds, val, Fr] at e1 e2 f ⊢
    exact ⟨by rw [e1, e2, BitVec.add_comm], f⟩
  · rename_i c hd ha
    have e1 := h.regs _ _ hd; have e2 := h.regs _ _ ha; have f := h.frR _ _ ha
    simp only [Holds, val, Fr] at e1 e2 f ⊢
    exact ⟨by rw [e1, e2], f⟩
  · simp [Holds, val, hρ, Fr]

theorem notBase_of {i : XInsn} {dd : XReg} (hb : (wr i).any isBase = false) (hd : dd ∈ wr i) : isBase dd = false := by
  have := List.any_eq_false.mp hb dd hd; simpa using this

set_option maxHeartbeats 1000000 in
theorem ins_inv_nb {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s t : XCS} {x x' : XS} {i : XInsn}
    (h : Inv x₀ ρ d s x) (hb' : (wr i).any isBase = false) (hc : xcstep d i s = some t) (hex : XExec i x x')
    (hsep : mayWrite i x → placed s i = false → WinKept x₀ x x') :
    ∃ v, Inv x₀ (ext x₀ ρ d v x'.mem) (d + 1) t x' := by
  cases i
  case aluRI o dd k =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false] at hc
    split at hc
    · rename_i hk; obtain ⟨rfl, rfl⟩ := hk; cases hc
      exact ⟨0, inv_succ 0 x'.mem (ins_cmp k h hex)⟩
    · exact ins_other h hb' hc hex hsep rfl
  case lea dd m =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false, Option.some.injEq] at hc; subst hc
    have hd := notBase_of (dd := dd) hb' (by simp [wr, wdst])
    rw [exec_some rfl hex]
    have hs := inv_succ ((x.set dd (ea x m)).regs dd) (x.set dd (ea x m)).mem h
    refine ⟨_, inv_setR (inv_s0 hs) dd _ _ hd ?_⟩
    intro w hw; cases hw
    cases e : s.leaV m with
    | some w => exact leaV_holds h m e _ _ _
    | none => simp [Holds, val, ext, Fr]
  case movRR dd a =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false, Option.some.injEq] at hc; subst hc
    have hd := notBase_of (dd := dd) hb' (by simp [wr, wdst])
    rw [exec_some rfl hex]
    have hs := inv_succ 0 (x.set dd (x.regs a)).mem h
    exact ⟨_, inv_setR (inv_s0 hs) dd _ _ hd (fun w hw => ⟨hs.regs a w hw, hs.frR a w hw⟩)⟩
  case aluRR o dd a =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false] at hc
    split at hc
    · rename_i ho; subst ho; cases hc
      have hd := notBase_of (dd := dd) hb' (by simp [wr, wdst])
      rw [exec_some rfl hex]
      have hs := inv_succ (x.regs dd + x.regs a) x.mem h
      refine ⟨_, inv_withFlags (inv_setR (inv_s0 hs) dd _ _ hd ?_) rfl _⟩
      intro w hw; cases hw
      exact addV_holds h dd a _ (by simp [ext])
    · exact ins_other h hb' hc hex hsep rfl
  case movRM dd m =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false, Option.some.injEq] at hc; subst hc
    have hd := notBase_of (dd := dd) hb' (by simp [wr, wdst])
    rw [exec_some rfl hex]
    have hs := inv_succ ((x.set dd (ld64 x.mem (ea x m))).regs dd) x.mem h
    refine ⟨_, inv_setR (inv_s0 hs) dd _ _ hd ?_⟩
    intro w hw; cases hw
    split
    · rename_i c l hcl
      obtain ⟨he, hcw, hl⟩ := ea_cellOf h m hcl
      have key := hs.mem c l hcw hl
      rw [← he] at key; exact ⟨key, hs.frM c l hcw⟩
    · simp [Holds, val, ext, Fr]
  case movMR m r =>
    simp only [xcstep, hb', Bool.false_eq_true, ite_false] at hc
    obtain rfl : x' = x.store64 (ea x m) (x.regs r) := exec_some rfl hex
    split at hc
    · rename_i cb c l hw hcl; cases hc
      obtain ⟨he, hcw, hl⟩ := ea_cellOf h m hcl
      have hs := inv_succ (x.regs r) (x.store64 (ea x m) (x.regs r)).mem h
      have := inv_store (inv_s0 hs) d (by omega) r (by simp [ext]) c hcw l hl
      rw [← he] at this
      exact ⟨_, this⟩
    · cases hc
    · rename_i hw; cases hc
      have hwin := hsep (Or.inl rfl) (by simp [placed, hw])
      exact ⟨_, inv_write none [] h (by simp) (fun r' _ => rfl) hwin⟩
  all_goals first
    | (simp only [xcstep, hb', Bool.false_eq_true, ite_false] at hc
       exact ins_other h hb' hc hex hsep rfl)
    | (simp only [xcstep, hb', Bool.false_eq_true, ite_false] at hc
       split at hc
       · cases hc
       · exact ins_other h hb' hc hex hsep rfl)

/-- **One instruction keeps the invariant.** -/
theorem ins_inv {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s t : XCS} {x x' : XS} {i : XInsn}
    (h : Inv x₀ ρ d s x) (hc : xcstep d i s = some t) (hex : XExec i x x')
    (hsep : mayWrite i x → placed s i = false → WinKept x₀ x x') :
    ∃ v, Inv x₀ (ext x₀ ρ d v x'.mem) (d + 1) t x' := by
  by_cases hb : (wr i).any isBase = true
  · exact ⟨0, inv_succ 0 x'.mem (ins_base h hb hc hex)⟩
  · exact ins_inv_nb h (by simpa using hb) hc hex hsep

/-! ## Calls, branches, the entry, the exits -/

theorem callee_saved_of (r : XReg) (h : r ∉ callerSavedX) : xCallerSaved r = false := by
  cases r <;> simp_all [callerSavedX, xCallerSaved]

/-- A call: the caller-saved registers forgotten, rax named, the memory a new generation. -/
theorem inv_call {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x x' : XS}
    (h : Inv x₀ ρ d s x) (hx : XCallExec x x') :
    Inv x₀ (ext x₀ ρ d (x'.regs .rax) x'.mem) (d + 1) (callSt d s) x' := by
  have hs := inv_succ (x'.regs .rax) x'.mem h
  have k13 : x'.regs .r13 = x.regs .r13 := hx _ rfl
  have k12 : x'.regs .r12 = x.regs .r12 := hx _ rfl
  obtain ⟨eoff, elt, efl, -, -⟩ := kill_fields callerSavedX { s with fl := none }
  let K := callerSavedX.foldl (fun t r => t.setR r none) { s with fl := none }
  have erv : ∀ r, r ≠ .r13 → r ≠ .r12 → K.rv r = if r ∈ callerSavedX then none else s.rv r :=
    fun r a b => rv_kill _ _ _ a b
  have ht : Inv x₀ (ext x₀ ρ d (x'.regs .rax) x'.mem) (d + 1) ({ K with mem := [], gen := d + 1 } : XCS) x' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show K.off.natAbs ≤ _; rw [eoff]; exact h.off
    · show _ = BitVec.ofInt 64 (32 * (sp₀ x₀ + K.off)); rw [eoff, k13]; exact h.r13
    · rw [k12]; exact h.r12
    · intro L hL; change K.lt = some L at hL; change sp₀ x₀ + K.off < L; rw [elt] at hL; rw [eoff]
      exact h.lt L hL
    · intro k hk; change K.fl = some k at hk; rw [efl] at hk; cases hk
    · intro r v hv
      change K.rv r = some v at hv
      by_cases a : r = .r13
      · subst a; rw [rv_r13, eoff] at hv; cases hv; simp only [Holds, val]; rw [k13]; exact h.r13
      by_cases b : r = .r12
      · subst b; rw [rv_r12] at hv; cases hv; simp only [Holds, val]; rw [k12]; exact h.r12
      rw [erv _ a b] at hv
      split at hv
      · cases hv
      · rename_i hk; rw [hx r (callee_saved_of r hk)]; exact hs.regs r v hv
    · intro c l hc hl; simp only [XCS.mv, List.find?_nil, Option.map_none, Option.getD_none, Holds, val, ext,
        ite_true]
    · exact Nat.le_refl _
    · intro r v hv
      change K.rv r = some v at hv
      by_cases a : r = .r13
      · subst a; rw [rv_r13, eoff] at hv; cases hv; exact h.off
      by_cases b : r = .r12
      · subst b; rw [rv_r12] at hv; cases hv; trivial
      rw [erv _ a b] at hv
      split at hv
      · cases hv
      · exact fr_mono (by omega) (show s.gen ≤ d + 1 by have := h.gen; omega) v (h.frR r v hv)
    · intro c l hc; simp only [XCS.mv, List.find?_nil, Option.map_none, Option.getD_none, Fr]
      exact ⟨Nat.le_refl _, hc⟩
  have := inv_setR ht .rax (some (.fresh d)) (x'.regs .rax) rfl
    (fun w hw => by cases hw; exact ⟨by simp [Holds, val, ext], by simp [Fr]⟩)
  rwa [XS_set_self] at this

theorem toInt_ofInt_small (z : Int) (h : z.natAbs ≤ 2 ^ 40) : (BitVec.ofInt 64 z).toInt = z := by
  rw [BitVec.toInt_ofInt_eq_self (by omega)] <;> omega

/-- `jl` after `cmp a, b` is taken iff a < b (signed), for values far from overflow. -/
theorem l_taken (a b : Int) (ha : a.natAbs ≤ 2 ^ 30) (hb : b.natAbs ≤ 2 ^ 30)
    (h : xcHolds .l (subXF (BitVec.ofInt 64 a) (BitVec.ofInt 64 b)) = true) : a < b := by
  have e := Evm.CL.X86Sem.cond_sub .lt _ _ (Evm.CL.X86Sem.subXF_rel (BitVec.ofInt 64 a) (BitVec.ofInt 64 b))
  have h' : Evm.CL.AsmSem.bcHolds .lt (Evm.CL.AsmSem.subFlags (BitVec.ofInt 64 a) (BitVec.ofInt 64 b)) = true := by
    rw [← e]; exact h
  simp only [Evm.CL.AsmSem.bcHolds, Evm.CL.AsmSem.subFlags, ← ofInt_sub', BitVec.msb_eq_toInt,
    toInt_ofInt_small a (by omega), toInt_ofInt_small b (by omega), toInt_ofInt_small (a - b) (by omega)] at h'
  revert h'
  by_cases h1 : a - b < 0 <;> by_cases h2 : a < 0 <;> by_cases h3 : b < 0 <;> simp [h1, h2, h3] <;> omega

theorem sp₀_range {x₀ : XS} (hsp : SpOk x₀) : 0 ≤ sp₀ x₀ ∧ sp₀ x₀ ≤ 1024 := by
  unfold sp₀; obtain ⟨_, h2⟩ := hsp; omega

/-- The taken edge of `jl`: after `cmp r13, #32k`, sp < k. -/
theorem take_inv {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS} (hsp : SpOk x₀)
    (h : Inv x₀ ρ d s x) (c : XCond) (hcond : xcHolds c x.flags = true) (v : BitVec 64) (mem' : AsmRun.Mem) :
    Inv x₀ (ext x₀ ρ d v mem') (d + 1) (takenSt c s) x := by
  have hs := inv_succ v mem' h
  unfold takenSt
  split
  · rename_i k hk
    split
    · rename_i hkw
      have hr := sp₀_range hsp
      have hoff := h.off
      have hcw : cwin.natAbs = 65536 := rfl
      have hlt : sp₀ x₀ + s.off < k / 32 := by
        rw [h.fl k hk, h.r13] at hcond
        have := l_taken _ _ (by omega) (by omega) hcond
        omega
      exact { hs with
        lt := fun L hL => by
          simp only [Option.some.injEq] at hL; subst hL
          show sp₀ x₀ + s.off < _
          cases e : s.lt with
          | none => exact hlt
          | some y => have := h.lt y e; simp only; omega }
    · exact hs
  · exact hs

/-- **At a dispatch exit the TOS cache is coherent** whenever the exit check passed. -/
theorem coherent_of_exitOk {x₀ : XS} {ρ : XV → BitVec 64} {d : Nat} {s : XCS} {x : XS}
    (hsp : SpOk x₀) (h : Inv x₀ ρ d s x) (hok : exitOk s = true) : XCoherent x := by
  have hr := sp₀_range hsp
  have hoff := h.off
  have hW : W = 65538 := rfl
  have hcw : cwin.natAbs = 65536 := rfl
  intro hle r l hrl
  rw [h.r13, toInt_ofInt_small _ (by omega)] at hle
  simp only [exitOk, Bool.or_eq_true, Option.any_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  rcases hok with ⟨L, hL, hL1⟩ | hok
  · have := h.lt L hL; omega
  have := hok (r, l) hrl
  simp only at this
  split at this
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨heq, ok1⟩, ok2⟩ := this
    have hl : l < 4 := by simp [tosX, List.zipIdx] at hrl; omega
    have hc : (s.off - 1).natAbs ≤ W := by omega
    have e1 := holds_strip x₀ ρ _ (by omega) v _ (h.regs r v hv) ok1
    have e2 := holds_strip x₀ ρ _ (by omega) _ _ (h.mem _ l hc hl) ok2
    rw [e1, heq, ← e2, h.r12, h.r13, cellAddr, BitVec.add_assoc, ← BitVec.ofInt_add]
    congr 3; omega
  · cases this

/-- The names at entry: each limb of the stack as it is. -/
def ρ₀ (x₀ : XS) : XV → BitVec 64
  | .cell _ c l => ld64 x₀.mem (cellAddr x₀ c l)
  | _ => 0

theorem r13_entry {x₀ : XS} (hsp : SpOk x₀) : x₀.regs .r13 = BitVec.ofInt 64 (32 * sp₀ x₀) := by
  apply BitVec.eq_of_toNat_eq
  obtain ⟨h1, h2⟩ := hsp
  have e : 32 * sp₀ x₀ = (((x₀.regs .r13).toNat : Nat) : Int) := by unfold sp₀; omega
  rw [e, BitVec.toNat_ofInt]
  have := (x₀.regs .r13).isLt
  omega

set_option maxHeartbeats 1000000 in
/-- **At entry** the abstract state describes a coherent machine. -/
theorem inv_entry (x₀ : XS) (hsp : SpOk x₀) (hc : XCoherent x₀) : Inv x₀ (ρ₀ x₀) 0 XCS.entry x₀ := by
  have hr := sp₀_range hsp
  have e13 := r13_entry hsp
  have hW : W = 65538 := rfl
  have hcw : cwin.natAbs = 65536 := rfl
  have hcoh : 1 ≤ sp₀ x₀ → ∀ (r : XReg) (l : Nat), (r, l) ∈ tosX.zipIdx →
      x₀.regs r = ld64 x₀.mem (cellAddr x₀ (-1) l) := by
    intro h1 r l hrl
    have := hc (by rw [e13, toInt_ofInt_small _ (by omega)]; omega) r l hrl
    rw [this, e13, cellAddr, BitVec.add_assoc, ← BitVec.ofInt_add]; congr 3; omega
  refine ⟨by decide, by simp [XCS.entry, e13], rfl, (fun L hL => by cases hL), (fun k hk => by cases hk),
    ?_, ?_, Nat.le_refl _, ?_, ?_⟩
  · intro r v hv
    by_cases a : r = .r13
    · subst a; simp only [rv_r13, Option.some.injEq] at hv; subst hv; simp [Holds, val, XCS.entry, e13]
    by_cases b : r = .r12
    · subst b; simp only [rv_r12, Option.some.injEq] at hv; subst hv; simp [Holds, val]
    cases r <;> simp [XCS.rv, XCS.entry, tosX, List.zipIdx] at hv a b <;> subst hv <;>
      simp only [Holds, val, ρ₀] <;> intro hle <;> exact hcoh hle _ _ (by simp [tosX, List.zipIdx])
  · intro c l _ _; simp [XCS.mv, XCS.entry, Holds, val, ρ₀]
  · intro r v hv
    by_cases a : r = .r13
    · subst a; simp only [rv_r13, Option.some.injEq] at hv; subst hv; simp [Fr, XCS.entry]
    by_cases b : r = .r12
    · subst b; simp only [rv_r12, Option.some.injEq] at hv; subst hv; trivial
    cases r <;> simp [XCS.rv, XCS.entry, tosX, List.zipIdx] at hv a b <;> subst hv <;>
      simp [Fr, hW]
  · intro c l hc'; simp [XCS.mv, XCS.entry, Fr, hc']

/-! ## The runs the analysis follows, and the one memory assumption -/

/-- A run of the body paired with the analysis's state along it (`d` steps in). -/
inductive JR (its : List XItem) (x₀ : XS) : Nat → List XItem → XCS → XS → Prop
  | start : JR its x₀ 0 its XCS.entry x₀
  | ins {d i rest s x t x'} : JR its x₀ d (.I i :: rest) s x → isExit i = false → isCallI i = false →
      xcstep d i s = some t → XExec i x x' → JR its x₀ (d + 1) rest t x'
  | call {d it rest s x x'} : JR its x₀ d (it :: rest) s x → isCallItem it = true → XCallExec x x' →
      JR its x₀ (d + 1) rest (callSt d s) x'
  | lea {d it r rest s x x'} : JR its x₀ d (it :: rest) s x → leaDst it = some r → isBase r = false →
      (∀ r', r' ≠ r → x'.regs r' = x.regs r') → x'.mem = x.mem →
      JR its x₀ (d + 1) rest ({ s with fl := none }.setR r (some (.fresh d))) x'
  | skip {d it rest s x} : JR its x₀ d (it :: rest) s x → isSkip it = true → JR its x₀ (d + 1) rest s x
  | take {d c l rest q s x} : JR its x₀ d (.Jcc c l :: rest) s x → xcHolds c x.flags = true →
      target its rest l = some q → JR its x₀ (d + 1) q (takenSt c s) x
  | jmp {d l rest q s x} : JR its x₀ d (.Jmp l :: rest) s x → target its rest l = some q →
      JR its x₀ (d + 1) q s x

/-- **Arena separation**, the one assumption about memory: on every run, an instruction
    that may write memory (a store form, or one `xstep` does not model) and that the
    analysis does not place in the stack — a store through an operand that is not a
    stack address: EVM memory, the state, the C frame, a `push` — leaves the stack words
    sp₀−W … sp₀+W unchanged. Calls need no such assumption: the analysis forgets the
    whole stack at a call. -/
def Sep (its : List XItem) (x₀ : XS) : Prop :=
  ∀ d i rest s x t x', JR its x₀ d (.I i :: rest) s x → isExit i = false → isCallI i = false →
    xcstep d i s = some t → XExec i x x' → mayWrite i x → placed s i = false → WinKept x₀ x x'

/-- `xcwalk` found nothing on the paths from (d, p, s) within `F + 1` steps. -/
def Clean (its : List XItem) (d : Nat) (p : List XItem) (s : XCS) : Prop :=
  ∃ F, xcwalk its (F + 1) d p s = []

theorem clean_of {its : List XItem} {F d : Nat} {q : List XItem} {t : XCS} (h : xcwalk its F d q t = []) :
    Clean its d q t := by
  cases F with
  | zero => simp [xcwalk] at h
  | succ F => exact ⟨F, h⟩

theorem clean_exit {its : List XItem} {d : Nat} {i : XInsn} {rest : List XItem} {s : XCS}
    (hcl : Clean its d (.I i :: rest) s) (h : isExit i = true) : exitOk s = true := by
  obtain ⟨F, hF⟩ := hcl
  simp only [xcwalk, h, ite_true] at hF
  split at hF
  · assumption
  · cases hF

theorem clean_ins {its : List XItem} {d : Nat} {i : XInsn} {rest : List XItem} {s : XCS}
    (hcl : Clean its d (.I i :: rest) s) (he : isExit i = false) (hc : isCallI i = false) :
    ∃ t, xcstep d i s = some t ∧ Clean its (d + 1) rest t := by
  obtain ⟨F, hF⟩ := hcl
  simp only [xcwalk, he, hc, Bool.false_eq_true, ite_false] at hF
  cases ht : xcstep d i s with
  | none => rw [ht] at hF; cases hF
  | some t => rw [ht] at hF; exact ⟨t, rfl, clean_of hF⟩

theorem clean_call {its : List XItem} {d : Nat} {it : XItem} {rest : List XItem} {s : XCS}
    (hcl : Clean its d (it :: rest) s) (h : isCallItem it = true) : Clean its (d + 1) rest (callSt d s) := by
  obtain ⟨F, hF⟩ := hcl
  cases it <;> (try simp only [isCallItem, reduceCtorEq] at h)
  case I i =>
    cases i <;> simp only [reduceCtorEq] at h
    simp only [xcwalk, isExit, isCallI, Bool.false_eq_true, ite_false, ite_true] at hF; exact clean_of hF
  case CallRip => simp only [xcwalk] at hF; exact clean_of hF
  case Call => simp only [xcwalk] at hF; exact clean_of hF

theorem clean_lea {its : List XItem} {d : Nat} {it : XItem} {r : XReg} {rest : List XItem} {s : XCS}
    (hcl : Clean its d (it :: rest) s) (h : leaDst it = some r) :
    isBase r = false ∧ Clean its (d + 1) rest ({ s with fl := none }.setR r (some (.fresh d))) := by
  obtain ⟨F, hF⟩ := hcl
  cases it <;> simp only [leaDst, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [xcwalk] at hF <;> split at hF <;> first | cases hF | exact ⟨by simpa using ‹¬isBase _ = true›, clean_of hF⟩

theorem clean_skip {its : List XItem} {d : Nat} {it : XItem} {rest : List XItem} {s : XCS}
    (hcl : Clean its d (it :: rest) s) (h : isSkip it = true) : Clean its (d + 1) rest s := by
  obtain ⟨F, hF⟩ := hcl
  cases it <;> (try simp only [isSkip, Bool.false_eq_true] at h)
  case L => simp only [xcwalk] at hF; exact clean_of hF
  case Jcc =>
    simp only [xcwalk] at hF
    split at hF
    · exact clean_of (List.append_eq_nil_iff.mp hF).1
    · split at hF
      · cases hF
      · exact clean_of hF
  case JccSym => simp only [xcwalk] at hF; exact clean_of hF

theorem clean_take {its : List XItem} {d : Nat} {c : XCond} {l : String} {rest q : List XItem} {s : XCS}
    (hcl : Clean its d (.Jcc c l :: rest) s) (ht : target its rest l = some q) :
    Clean its (d + 1) q (takenSt c s) := by
  obtain ⟨F, hF⟩ := hcl
  simp only [xcwalk, ht] at hF
  exact clean_of (List.append_eq_nil_iff.mp hF).2

theorem clean_jmp {its : List XItem} {d : Nat} {l : String} {rest q : List XItem} {s : XCS}
    (hcl : Clean its d (.Jmp l :: rest) s) (ht : target its rest l = some q) : Clean its (d + 1) q s := by
  obtain ⟨F, hF⟩ := hcl
  simp only [xcwalk, ht] at hF
  exact clean_of hF

/-- **The simulation**: along every run the analysis follows, its state describes the machine. -/
theorem jr_inv {its : List XItem} {x₀ : XS} (hsp : SpOk x₀) (hc : XCoherent x₀)
    (hsep : Sep its x₀) (hcl : Clean its 0 its XCS.entry) :
    ∀ {d p s x}, JR its x₀ d p s x → Clean its d p s ∧ ∃ ρ, Inv x₀ ρ d s x := by
  intro d p s x hjr
  induction hjr with
  | start => exact ⟨hcl, _, inv_entry x₀ hsp hc⟩
  | @ins d i rest s x t x' hjr he hcall hcs hex ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    obtain ⟨t', ht', hcl''⟩ := clean_ins hcl' he hcall
    rw [hcs] at ht'; cases ht'
    obtain ⟨v, hv⟩ := ins_inv hinv hcs hex (fun hw hpl => hsep d i rest s x t x' hjr he hcall hcs hex hw hpl)
    exact ⟨hcl'', _, hv⟩
  | @call d it rest s x x' hjr hit hx ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    exact ⟨clean_call hcl' hit, _, inv_call hinv hx⟩
  | @lea d it r rest s x x' hjr hl hb hregs hmem ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    refine ⟨(clean_lea hcl' hl).2, _, inv_write (some r) [] hinv (by simpa using hb)
      (fun r' hr' => hregs r' (by simpa using hr')) (fun c l _ _ => by rw [hmem])⟩
  | @skip d it rest s x hjr hs ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    exact ⟨clean_skip hcl' hs, _, inv_succ 0 x.mem hinv⟩
  | @take d c l rest q s x hjr hcond ht ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    exact ⟨clean_take hcl' ht, _, take_inv hsp hinv c hcond 0 x.mem⟩
  | @jmp d l rest q s x hjr ht ih =>
    obtain ⟨hcl', ρ, hinv⟩ := ih
    exact ⟨clean_jmp hcl' ht, _, inv_succ 0 x.mem hinv⟩

/-- Every concrete run is one the analysis follows. -/
theorem reach_jr {its : List XItem} {x₀ : XS} (hsp : SpOk x₀) (hc : XCoherent x₀)
    (hsep : Sep its x₀) (hcl : Clean its 0 its XCS.entry) :
    ∀ {p x}, XReach its x₀ p x → ∃ d s, JR its x₀ d p s x := by
  intro p x hr
  induction hr with
  | start => exact ⟨0, _, .start⟩
  | step hr hst ih =>
    obtain ⟨d, s, hjr⟩ := ih
    obtain ⟨hcl', -⟩ := jr_inv hsp hc hsep hcl hjr
    cases hst with
    | ins he hcall hex =>
      obtain ⟨t, ht, -⟩ := clean_ins hcl' he hcall
      exact ⟨_, _, .ins hjr he hcall ht hex⟩
    | call hit hx => exact ⟨_, _, .call hjr hit hx⟩
    | lea hl hregs hmem => exact ⟨_, _, .lea hjr hl (clean_lea hcl' hl).1 hregs hmem⟩
    | skip hs => exact ⟨_, _, .skip hjr hs⟩
    | take hcond ht => exact ⟨_, _, .take hjr hcond ht⟩
    | jmp ht => exact ⟨_, _, .jmp hjr ht⟩

/-- **Soundness of the x86-64 stack-cache check.** If `xcacheIncoherent` finds nothing in a
    lowered body, then every run of it that starts with sp a whole number of words in
    [0, 1024] and a coherent TOS cache, and in which the stores the analysis does not
    place in the stack do not touch it (`Sep`), reaches every dispatch exit (`ret`,
    `jmp [mem]`, `jmp reg`) with the cache coherent for the sp it leaves. -/
theorem xcacheIncoherent_sound (its : List XItem) (h : xcacheIncoherent its = []) (x₀ : XS)
    (hsp : SpOk x₀) (hc : XCoherent x₀) (hsep : Sep its x₀) :
    ∀ i rest x, XReach its x₀ (.I i :: rest) x → isExit i = true → XCoherent x := by
  intro i rest x hr he
  have hcl : Clean its 0 its XCS.entry := ⟨its.length, Evm.CL.CacheSound.eraseDups_nil h⟩
  obtain ⟨d, s, hjr⟩ := reach_jr hsp hc hsep hcl hr
  obtain ⟨hcl', ρ, hinv⟩ := jr_inv hsp hc hsep hcl hjr
  exact coherent_of_exitOk hsp hinv (clean_exit hcl' he)

/-! ## The same, for `X86Sem.xrun`

`xrun` is deterministic and models the helper calls (`xcall`); every transition it makes
is an `XStep`, so a run that `xrun` ends in `ret` is a run the theorem covers. -/

theorem xstep_some_notExit {x x' : XS} {i : XInsn} (h : xstep x i = some x') :
    isExit i = false ∧ isCallI i = false := by
  cases i <;> simp_all [xstep, isExit, isCallI]

theorem xrun_reach (HX : Evm.CL.X86Sem.XHelpers) (its : List XItem) (x₀ : XS) (y : XS) :
    ∀ n p x, p.length ≤ n → XReach its x₀ p x → Evm.CL.X86Sem.xrun HX p x = .ret y →
      ∃ rest, XReach its x₀ (.I .ret :: rest) y := by
  intro n
  induction n with
  | zero => intro p x hl _ hrun; cases p with
    | nil => simp at hrun
    | cons _ _ => simp at hl
  | succ n ih =>
    intro p x hl hr hrun
    cases p with
    | nil => simp at hrun
    | cons it rest =>
      have hl' : rest.length ≤ n := by simp at hl; omega
      have sub : ∀ {l : String} (q : List XItem), xskipTo l rest = some q → q.length ≤ n := fun q hq =>
        Nat.le_trans (Evm.CL.X86Sem.xskipTo_length_le _ _ _ hq) hl'
      have tgt : ∀ {l q}, xskipTo l rest = some q → target its rest l = some q := fun hq => by
        simp [target, hq]
      cases it with
      | I i =>
        by_cases hret : i = .ret
        · subst hret; rw [Evm.CL.X86Sem.xrun_cons_ret] at hrun; cases hrun; exact ⟨rest, hr⟩
        cases hx : xstep x i with
        | some x' =>
          rw [Evm.CL.X86Sem.xrun_cons_I HX i hret rest x x' hx] at hrun
          obtain ⟨he, hcall⟩ := xstep_some_notExit hx
          exact ih rest x' hl' (.step hr (.ins he hcall (by simp [XExec, hx]))) hrun
        | none =>
          exfalso; revert hrun
          cases i <;> simp_all [Evm.CL.X86Sem.xrun]
      | L l =>
        rw [Evm.CL.X86Sem.xrun_cons_L] at hrun
        exact ih rest x hl' (.step hr (.skip rfl)) hrun
      | Jcc c l =>
        by_cases hc : xcHolds c x.flags = true
        · cases hq : xskipTo l rest with
          | some q =>
            rw [Evm.CL.X86Sem.xrun_cons_Jcc_skip HX c l rest q x hc hq] at hrun
            exact ih q x (sub q hq) (.step hr (.take hc (tgt hq))) hrun
          | none => rw [Evm.CL.X86Sem.xrun_cons_Jcc_exit HX c l rest x hc hq] at hrun; cases hrun
        · rw [Evm.CL.X86Sem.xrun_cons_Jcc_not HX c l rest x (by simpa using hc)] at hrun
          exact ih rest x hl' (.step hr (.skip rfl)) hrun
      | Jmp l =>
        cases hq : xskipTo l rest with
        | some q =>
          rw [Evm.CL.X86Sem.xrun_cons_Jmp_skip HX l rest q x hq] at hrun
          exact ih q x (sub q hq) (.step hr (.jmp (tgt hq))) hrun
        | none => rw [Evm.CL.X86Sem.xrun_cons_Jmp_exit HX l rest x hq] at hrun; cases hrun
      | JccSym c sym =>
        rw [Evm.CL.X86Sem.xrun_cons_JccSym] at hrun
        split at hrun
        · cases hrun
        · exact ih rest x hl' (.step hr (.skip rfl)) hrun
      | CallRip slot =>
        rw [Evm.CL.X86Sem.xrun_cons_CallRip] at hrun
        refine ih rest _ hl' (.step hr (.call rfl ?_)) hrun
        intro r hr'; simp [Evm.CL.X86Sem.xcall, hr']
      | _ => simp [Evm.CL.X86Sem.xrun] at hrun

/-- **…and so for `xrun`**: a run of an accepted body that `X86Sem.xrun` (with any helper
    model) ends in `ret` ends with the cache coherent. -/
theorem xrun_ret_coherent (HX : Evm.CL.X86Sem.XHelpers) (its : List XItem) (h : xcacheIncoherent its = [])
    (x₀ : XS) (hsp : SpOk x₀) (hc : XCoherent x₀) (hsep : Sep its x₀) (y : XS)
    (hr : Evm.CL.X86Sem.xrun HX its x₀ = .ret y) : XCoherent y := by
  obtain ⟨rest, hy⟩ := xrun_reach HX its x₀ y its.length its x₀ (Nat.le_refl _) .start hr
  exact xcacheIncoherent_sound its h x₀ hsp hc hsep _ rest y hy rfl

/-! ## What the soundness proof made the check reject

The check this replaced read the `AInstr` body under ARM names (`OpInstrs.cacheIncoherent
… true`). It accepted each of the first four groups of bodies below, and on x86-64 each
breaks the cache on some run: -/

open Evm.CL.AsmCore in
/-- NOS read as a register after sp moved: x86-64 reads x10-x13 from memory at the
    CURRENT sp (`[r12 + r13 - 64]`), so after a pop `mov x6, x10` is stack[sp₀-3]. -/
theorem rejects_nos_after_pop : (xcacheIncoherent (progItems
    [ .subImm .x23 .x23 32, .movReg .x6 .x10, .movReg .x7 .x11, .movReg .x8 .x12, .movReg .x9 .x13,
      .brCont ])).isEmpty = false := by decide

open Evm.CL.AsmCore in
/-- Registers that share an x86 home: x1 and x15 are both rdx, so `mov x1, #0` clobbers the
    stack address in x15; a register with no home (x5) is written through rax. -/
theorem rejects_shared_homes :
    (xcacheIncoherent (progItems
      [ .subImm .x15 .x23 32, .addReg .x15 .x24 .x15, .movImm .x1 0,
        .ldpOff .x6 .x7 .x15 0, .ldpOff .x8 .x9 .x15 16, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems
      [ .subImm .x0 .x23 32, .addReg .x0 .x24 .x0, .movImm .x5 7,
        .ldpOff .x6 .x7 .x0 0, .ldpOff .x8 .x9 .x0 16, .brCont ])).isEmpty = false := by decide

open Evm.CL.AsmCore in
/-- The lowering's temporaries: a NOS-source store goes through rax (x0's home), and so
    does `csinv`'s all-ones. -/
theorem rejects_lowering_temporaries :
    (xcacheIncoherent (progItems
      [ .subImm .x0 .x23 32, .addReg .x0 .x24 .x0, .strOff .x10 .x20 0,
        .ldpOff .x6 .x7 .x0 0, .ldpOff .x8 .x9 .x0 16, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems
      [ .subImm .x0 .x23 32, .addReg .x0 .x24 .x0, .csinvEqZr .x15 .x15,
        .ldpOff .x6 .x7 .x0 0, .ldpOff .x8 .x9 .x0 16, .brCont ])).isEmpty = false := by decide

open Evm.CL.AsmCore in
/-- `ret` is a dispatch exit on x86-64 (it is what `brCont` lowers to), and was not checked. -/
theorem rejects_unchecked_ret :
    (xcacheIncoherent (progItems [ .movImm .x6 0, .ret ])).isEmpty = false := by decide

open Evm.CL.AsmCore in
/-- The ARM64 proof's classes (rejected before too), on x86-64: the TOS parked in callee-saved registers across a
    call that may rewrite stack[sp-1]; sp or the base written by anything but
    `add|sub r13, #32k` (here a part-word pop); a zero store into a stack word. -/
theorem rejects_arm64_classes :
    (xcacheIncoherent (progItems
      [ .movReg .x20 .x6, .movReg .x21 .x7, .movReg .x26 .x8, .movReg .x22 .x9,
        .blSym "_eita_helper_mul",
        .movReg .x6 .x20, .movReg .x7 .x21, .movReg .x8 .x26, .movReg .x9 .x22, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems [ .movReg .x23 .x0, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems [ .addImm .x24 .x24 32, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems [ .subImm .x23 .x23 8, .brCont ])).isEmpty = false ∧
    (xcacheIncoherent (progItems
      [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .strZr .x14 0, .brCont ])).isEmpty = false := by
  decide

open Evm.CL.AsmCore in
/-- …and it accepts the guarded reload after a pop. -/
theorem accepts_guarded_reload : (xcacheIncoherent (progItems
    [ .subImm .x23 .x23 32, .cmpImm .x23 32, .bcLbl .lt "5f",
      .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
      .label "5", .brCont ])).isEmpty = true := by decide

section Handlers
open Evm.CL.AsmCore Evm.CL.X86Interp Evm.CL.ARM64.Interp

/-! ## Every x86-64 handler keeps the TOS cache

The x86-64 counterpart of `ARM64.Interp.handler_stack_cache_coherent`: entered with
r8-r11 (x6-x9) = stack[sp-1], every dispatch exit leaves them equal to the top word for
the sp it leaves. Checked on the LOWERED bodies (`X86Cache.xcacheIncoherent`, the x86
register file: x1/x15, x2/x17, x3/x4/x16 are one register each there), in both forms the
file links: the flat one (`brCont` = `ret`, the JIT tier's `_f` twins) and the threaded
one (`brCont` = `nextItems`, whose `jmp [rax + rcx*8]` is the exit). -/

/-- A body lowered with `brCont` as the threaded continuation, as `x86Threaded` prints it. -/
def threadedItems (is : List AInstr) : List XItem :=
  is.flatMap fun i => if i == .brCont then nextItems else x86Items i

theorem x86_handler_tos_cache_coherent :
    handlerList.all (fun (_, suf, p) =>
      (xcacheIncoherent (progItems (handlerInstrs suf p))).isEmpty &&
      (xcacheIncoherent (threadedItems (handlerInstrs suf p))).isEmpty) = true := by
  native_decide

/-- **…and so every handler's runs keep it** (x86-64) — the verdict turned into a theorem
    through `xcacheIncoherent_sound` (proof by reflection): over `X86Sem.xstep`, every run
    of a handler's flat or threaded lowering entered with sp a whole number of words in
    [0, 1024] and r8-r11 = stack[sp-1] reaches every dispatch exit (`ret`, `jmp [mem]`)
    with r8-r11 = stack[sp-1] for the sp it leaves. Assumed: calls keep the SysV
    callee-saved registers (memory is not assumed kept), and `Sep` — the stores the
    analysis does not place in the stack (EVM memory, state, the C frame, `push`) and the
    instructions outside `xstep` do not write the stack words around sp. -/
theorem x86_handler_runs_cache_coherent :
    ∀ h ∈ handlerList, ∀ its ∈ [progItems (handlerInstrs h.2.1 h.2.2), threadedItems (handlerInstrs h.2.1 h.2.2)],
    ∀ x₀ : Evm.CL.X86Sem.XS, SpOk x₀ → XCoherent x₀ → Sep its x₀ →
    ∀ i rest x, XReach its x₀ (.I i :: rest) x → isExit i = true → XCoherent x := by
  intro h hh its hits x₀ hsp hc hsep
  have := List.all_eq_true.mp x86_handler_tos_cache_coherent h hh
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hits
  rcases hits with rfl | rfl
  · exact xcacheIncoherent_sound _ this.1 x₀ hsp hc hsep
  · exact xcacheIncoherent_sound _ this.2 x₀ hsp hc hsep

/-- …and it rejects a TOS left stale: DIV's helper result reloaded into r8-r11 but its
    low half never stored to the top word. -/
theorem x86_tos_coherence_rejects_unstored_result :
    (match (handlerProgs opCost).lookup "div" with
     | some p => (xcacheIncoherent (progItems ((handlerInstrs "" p).filter (· != .stpOff .x6 .x7 .x14 0)))).isEmpty
     | none => true) = false := by
  native_decide

end Handlers

end Evm.CL.X86CacheSound
