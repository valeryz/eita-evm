/-
  Evm.CL.ARM64.RegionBuild — the region builder keeps the regions well
  formed: every region reachable from `{}` by `Region.step` over the
  `regionStep` outcomes (fold / sym / store) satisfies `FlushMain.RegionWF`.
  This discharges the `RegionWF` hypothesis of `FlushMain.flush_run` for the
  regions `emitChunkGen` actually flushes.

  No side condition on the ops: `symStep` refuses `dup 0` (not an EVM op;
  the decoder produces `dup (opcode − 0x7f)`, 1..16) exactly as it refuses
  `swap 0`, so every DUP the builder absorbs is an entry read `need` covers.
-/

import Evm.CL.ARM64.FlushMain

namespace Evm.CL.ARM64.RegionBuild

open Evm.CL.ARM64.JIT Evm.CL.ARM64.DagSlots Evm.CL.ARM64.FlushMain
open Evm.CL.ARM64.MemCommitSem (wWidth)
open Evm.IR (Op)
open Evm.IR.SymExpr (Expr SymStack symStep symUnary symBinary symTernary)

/-! ## Entry-read bounds on expressions -/

/-- Every `stackAt k` leaf of the expression has `k < b`. -/
def LB (b : Nat) : Expr → Prop
  | .const _ => True
  | .stackAt k => k < b
  | .isZero a | .not_ a => LB b a
  | .addmod a c n | .mulmod a c n => LB b a ∧ LB b c ∧ LB b n
  | .add a c | .mul a c | .sub a c | .div a c | .sdiv a c
  | .mod_ a c | .smod_ a c | .signExtend a c
  | .lt a c | .gt a c | .slt a c | .sgt a c | .eq_ a c
  | .and_ a c | .or_ a c | .xor_ a c
  | .byte_ a c | .shl_ a c | .shr_ a c | .sar_ a c => LB b a ∧ LB b c

theorem LB.mono {b b' : Nat} (h : b ≤ b') : ∀ e, LB b e → LB b' e := by
  intro e
  induction e with
  | const _ => intro _; trivial
  | stackAt k => intro hk; simp only [LB] at hk ⊢; omega
  | isZero a ih | not_ a ih => intro hk; simp only [LB] at hk ⊢; exact ih hk
  | addmod a c n iha ihc ihn | mulmod a c n iha ihc ihn =>
    intro hk; simp only [LB] at hk ⊢; exact ⟨iha hk.1, ihc hk.2.1, ihn hk.2.2⟩
  | add a c iha ihc | mul a c iha ihc | sub a c iha ihc | div a c iha ihc | sdiv a c iha ihc
  | mod_ a c iha ihc | smod_ a c iha ihc | signExtend a c iha ihc
  | lt a c iha ihc | gt a c iha ihc | slt a c iha ihc | sgt a c iha ihc | eq_ a c iha ihc
  | and_ a c iha ihc | or_ a c iha ihc | xor_ a c iha ihc
  | byte_ a c iha ihc | shl_ a c iha ihc | shr_ a c iha ihc | sar_ a c iha ihc =>
    intro hk; simp only [LB] at hk ⊢; exact ⟨iha hk.1, ihc hk.2⟩

theorem LB.const (b : Nat) (v : Evm.U256) : LB b (.const v) := trivial

theorem LB.stackAt_lt {b k : Nat} (h : LB b (.stackAt k)) : k < b := by simpa [LB] using h

/-- `collectSlots` adds only subterms of `e`: the bound carries over. -/
theorem collect_lb (b : Nat) : ∀ (e : Expr) (acc : List Expr), (∀ x ∈ acc, LB b x) → LB b e →
    ∀ x ∈ collectSlots acc e, LB b x := by
  intro e
  induction e with
  | const _ | stackAt _ =>
    intro acc hacc he x hx
    unfold collectSlots at hx; split at hx
    · exact hacc x hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hacc x hx
      · exact he
  | isZero a ih | not_ a ih =>
    intro acc hacc he x hx
    unfold collectSlots at hx; split at hx
    · exact hacc x hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      simp only [LB] at he
      rcases hx with hx | rfl
      · exact ih acc hacc he x hx
      · simpa [LB] using he
  | addmod a c n iha ihc ihn | mulmod a c n iha ihc ihn =>
    intro acc hacc he x hx
    unfold collectSlots at hx; split at hx
    · exact hacc x hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      have he' := he
      simp only [LB] at he'
      rcases hx with hx | rfl
      · exact ihn _ (ihc _ (iha _ hacc he'.1) he'.2.1) he'.2.2 x hx
      · exact he
  | add a c iha ihc | mul a c iha ihc | sub a c iha ihc | div a c iha ihc | sdiv a c iha ihc
  | mod_ a c iha ihc | smod_ a c iha ihc | signExtend a c iha ihc
  | lt a c iha ihc | gt a c iha ihc | slt a c iha ihc | sgt a c iha ihc | eq_ a c iha ihc
  | and_ a c iha ihc | or_ a c iha ihc | xor_ a c iha ihc
  | byte_ a c iha ihc | shl_ a c iha ihc | shr_ a c iha ihc | sar_ a c iha ihc =>
    intro acc hacc he x hx
    unfold collectSlots at hx; split at hx
    · exact hacc x hx
    · simp only [List.mem_append, List.mem_singleton] at hx
      have he' := he
      simp only [LB] at he'
      rcases hx with hx | rfl
      · exact ihc _ (iha _ hacc he'.1) he'.2 x hx
      · exact he

theorem fold_lb (b : Nat) (roots : List Expr) : ∀ acc, (∀ x ∈ acc, LB b x) → (∀ e ∈ roots, LB b e) →
    ∀ x ∈ roots.foldl collectSlots acc, LB b x := by
  induction roots with
  | nil => intro acc hacc _ x hx; exact hacc x hx
  | cons r rs ih =>
    intro acc hacc hr x hx
    simp only [List.foldl_cons] at hx
    exact ih _ (collect_lb b r acc hacc (hr r (by simp))) (fun e he => hr e (by simp [he])) x hx

/-! ## Bounded symbolic stacks -/

/-- `consumed ≤ b` and every entry read in the explicit prefix is below `b`. -/
structure SB (b : Nat) (ss : SymStack) : Prop where
  cle : ss.consumed ≤ b
  lb  : ∀ e ∈ ss.exprs, LB b e

theorem SB.mono {b b' : Nat} {ss : SymStack} (h : b ≤ b') (hs : SB b ss) : SB b' ss :=
  ⟨Nat.le_trans hs.cle h, fun e he => LB.mono h e (hs.lb e he)⟩

theorem SB.empty : SB 0 ({} : SymStack) := ⟨Nat.le_refl 0, fun e he => by simp at he⟩

theorem push_sb {b : Nat} {ss : SymStack} {e : Expr} (hs : SB b ss) (he : LB b e) : SB b (ss.push e) :=
  ⟨hs.cle, fun x hx => by
    simp only [SymStack.push, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he
    · exact hs.lb x hx⟩

@[simp] theorem push_consumed (ss : SymStack) (e : Expr) : (ss.push e).consumed = ss.consumed := rfl

theorem pushAll_sb {b : Nat} {ss : SymStack} : ∀ (l : List Expr), SB b ss → (∀ e ∈ l, LB b e) → SB b (ss.pushAll l)
  | [], hs, _ => hs
  | e :: tl, hs, hl =>
    push_sb (pushAll_sb tl hs (fun x hx => hl x (by simp [hx]))) (hl e (by simp))

@[simp] theorem pushAll_consumed (ss : SymStack) : ∀ (l : List Expr), (ss.pushAll l).consumed = ss.consumed
  | [] => rfl
  | _ :: tl => by simp only [SymStack.pushAll, push_consumed]; exact pushAll_consumed ss tl

/-- One pop: the popped expression and the rest are bounded by the new consumed count. -/
theorem pop_sb {b : Nat} {ss : SymStack} (hs : SB b ss) :
    SB (max b (ss.pop).2.consumed) (ss.pop).2 ∧ LB (max b (ss.pop).2.consumed) (ss.pop).1 ∧
    ss.consumed ≤ (ss.pop).2.consumed := by
  obtain ⟨es, c⟩ := ss
  have hc := hs.cle
  have hl := hs.lb
  simp only at hc hl
  cases es with
  | nil =>
    simp only [SymStack.pop]
    refine ⟨⟨by show c + 1 ≤ max b (c + 1); omega, fun e he => by simp at he⟩, ?_, by show c ≤ c + 1; omega⟩
    show c < max b (c + 1); omega
  | cons e tl =>
    simp only [SymStack.pop]
    refine ⟨⟨by show c ≤ max b c; omega, fun x hx => LB.mono (Nat.le_max_left _ _) x (hl x (by simp [hx]))⟩,
            LB.mono (Nat.le_max_left _ _) e (hl e (by simp)), Nat.le_refl _⟩

theorem popN_sb {b : Nat} : ∀ (k : Nat) (ss : SymStack), SB b ss →
    SB (max b (ss.popN k).2.consumed) (ss.popN k).2 ∧
    (∀ e ∈ (ss.popN k).1, LB (max b (ss.popN k).2.consumed) e) ∧
    ss.consumed ≤ (ss.popN k).2.consumed
  | 0, ss, hs => ⟨SB.mono (Nat.le_max_left _ _) hs, fun e he => by simp [SymStack.popN] at he, Nat.le_refl _⟩
  | k + 1, ss, hs => by
    obtain ⟨h1, h2, h3⟩ := pop_sb hs
    obtain ⟨g1, g2, g3⟩ := popN_sb k (ss.pop).2 h1
    simp only [SymStack.popN]
    have hle : max (max b (ss.pop).2.consumed) ((ss.pop).2.popN k).2.consumed ≤
        max b ((ss.pop).2.popN k).2.consumed := by omega
    refine ⟨SB.mono hle g1, ?_, Nat.le_trans h3 g3⟩
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact LB.mono (by omega) _ h2
    · exact LB.mono hle _ (g2 e he)

theorem peek_lb_lt {b : Nat} {ss : SymStack} (n : Nat) (hn : n < ss.exprs.length) (hs : SB b ss) :
    LB b (ss.peek n) := by
  unfold SymStack.peek
  split
  · rename_i e he; exact hs.lb e (List.mem_of_getElem? he)
  · rename_i he; rw [List.getElem?_eq_none_iff] at he; omega

theorem peek_lb_ge {ss : SymStack} (n : Nat) (hn : ss.exprs.length ≤ n) :
    LB (ss.consumed + (n - ss.exprs.length) + 1) (ss.peek n) := by
  unfold SymStack.peek
  split
  · rename_i e he; obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp he; omega
  · simp only [LB]; omega

/-! ## One op -/

/-- The DUP peek-beyond-prefix term of `Region.step`, stated on the pre-state. -/
def dupNeedOf (op : Op) (ss : SymStack) : Nat :=
  match op with
  | .dup n => if n > ss.exprs.length then ss.consumed + n - ss.exprs.length else 0
  | _ => 0

theorem Region.step_eq (r : Region) (op : Op) (ss' : SymStack) :
    r.step op ss' = { ss := ss', need := max r.need (max ss'.consumed (dupNeedOf op r.ss)),
                      maxNet := max r.maxNet ((ss'.exprs.length : Int) - ss'.consumed),
                      writes := r.writes } := by
  cases op <;> rfl

/-- The bound a successor stack must satisfy for `Region.step` to keep the region bounded. -/
abbrev nextB (b : Nat) (op : Op) (ss ss' : SymStack) : Nat := max b (max ss'.consumed (dupNeedOf op ss))

theorem symBinary_sb {b : Nat} {ss : SymStack} (mk : Expr → Expr → Expr)
    (hmk : ∀ B x y, LB B x → LB B y → LB B (mk x y)) (hs : SB b ss) (op : Op) :
    SB (nextB b op ss (symBinary mk ss)) (symBinary mk ss) := by
  obtain ⟨h1, h2, h3⟩ := pop_sb hs
  obtain ⟨g1, g2, g3⟩ := pop_sb h1
  unfold symBinary
  simp only [nextB, push_consumed]
  have hle : max (max b (ss.pop).2.consumed) ((ss.pop).2.pop).2.consumed ≤
      max b (max ((ss.pop).2.pop).2.consumed (dupNeedOf op ss)) := by omega
  exact push_sb (SB.mono hle g1) (hmk _ _ _ (LB.mono (by omega) _ h2) (LB.mono hle _ g2))

theorem symUnary_sb {b : Nat} {ss : SymStack} (mk : Expr → Expr)
    (hmk : ∀ B x, LB B x → LB B (mk x)) (hs : SB b ss) (op : Op) :
    SB (nextB b op ss (symUnary mk ss)) (symUnary mk ss) := by
  obtain ⟨h1, h2, h3⟩ := pop_sb hs
  unfold symUnary
  simp only [nextB, push_consumed]
  have hle : max b (ss.pop).2.consumed ≤ max b (max (ss.pop).2.consumed (dupNeedOf op ss)) := by omega
  exact push_sb (SB.mono hle h1) (hmk _ _ (LB.mono hle _ h2))

theorem symTernary_sb {b : Nat} {ss : SymStack} (mk : Expr → Expr → Expr → Expr)
    (hmk : ∀ B x y z, LB B x → LB B y → LB B z → LB B (mk x y z)) (hs : SB b ss) (op : Op) :
    SB (nextB b op ss (symTernary mk ss)) (symTernary mk ss) := by
  obtain ⟨h1, h2, h3⟩ := pop_sb hs
  obtain ⟨g1, g2, g3⟩ := pop_sb h1
  obtain ⟨k1, k2, k3⟩ := pop_sb g1
  unfold symTernary
  simp only [nextB, push_consumed]
  have hle : max (max (max b (ss.pop).2.consumed) ((ss.pop).2.pop).2.consumed)
      (((ss.pop).2.pop).2.pop).2.consumed ≤
      max b (max (((ss.pop).2.pop).2.pop).2.consumed (dupNeedOf op ss)) := by omega
  exact push_sb (SB.mono hle k1)
    (hmk _ _ _ _ (LB.mono (by omega) _ h2) (LB.mono (by omega) _ g2) (LB.mono hle _ k2))

/-- The verified symbolic step keeps the stack bounded by `nextB`. -/
theorem symStep_sb {b : Nat} {ss ss' : SymStack} (op : Op) (h : symStep op ss = some ss')
    (hs : SB b ss) : SB (nextB b op ss ss') ss' := by
  have hb : b ≤ nextB b op ss ss' := Nat.le_max_left _ _
  have hbin : ∀ (mk : Expr → Expr → Expr), (∀ B x y, LB B x → LB B y → LB B (mk x y)) →
      symBinary mk ss = ss' → SB (nextB b op ss ss') ss' := by
    intro mk hmk he; subst he; exact symBinary_sb mk hmk hs op
  have hun : ∀ (mk : Expr → Expr), (∀ B x, LB B x → LB B (mk x)) →
      symUnary mk ss = ss' → SB (nextB b op ss ss') ss' := by
    intro mk hmk he; subst he; exact symUnary_sb mk hmk hs op
  have hter : ∀ (mk : Expr → Expr → Expr → Expr), (∀ B x y z, LB B x → LB B y → LB B z → LB B (mk x y z)) →
      symTernary mk ss = ss' → SB (nextB b op ss ss') ss' := by
    intro mk hmk he; subst he; exact symTernary_sb mk hmk hs op
  cases op <;> simp only [symStep, Option.some.injEq, reduceCtorEq] at h
  -- constant pushes
  case push _ _ | push0 | pc _ =>
    subst h; exact push_sb (SB.mono hb hs) trivial
  case jumpdest => subst h; exact SB.mono hb hs
  case pop =>
    subst h; obtain ⟨h1, _, _⟩ := pop_sb hs
    exact SB.mono (by simp only [nextB, dupNeedOf]; omega) h1
  case add => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case mul => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case sub => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case div => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case sdiv => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case mod => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case smod => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case addmod => exact hter _ (fun B x y z hx hy hz => by simp only [LB]; exact ⟨hx, hy, hz⟩) h
  case mulmod => exact hter _ (fun B x y z hx hy hz => by simp only [LB]; exact ⟨hx, hy, hz⟩) h
  case signextend => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case lt => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case gt => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case slt => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case sgt => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case eq => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case iszero => exact hun _ (fun B x hx => by simp only [LB]; exact hx) h
  case and_ => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case or_ => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case xor_ => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case not_ => exact hun _ (fun B x hx => by simp only [LB]; exact hx) h
  case byte => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case shl => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case shr => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case sar => exact hbin _ (fun B x y hx hy => by simp only [LB]; exact ⟨hx, hy⟩) h
  case dup n =>
    cases n with
    | zero => simp at h
    | succ n =>
    simp only [Option.some.injEq] at h
    subst h
    have hn : 1 ≤ n + 1 := Nat.succ_pos n
    simp only [nextB, push_consumed, dupNeedOf]
    refine push_sb (SB.mono (by omega) hs) ?_
    by_cases hlt : n + 1 - 1 < ss.exprs.length
    · exact LB.mono (by omega) _ (peek_lb_lt (n + 1 - 1) hlt hs)
    · have := peek_lb_ge (ss := ss) (n + 1 - 1) (by omega)
      refine LB.mono ?_ _ this
      rw [if_pos (by omega)]; omega
  case swap n =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨p1, p2, p3⟩ := popN_sb (n + 2) ss hs
      simp only [nextB, pushAll_consumed, dupNeedOf]
      have hle : max b (ss.popN (n + 2)).2.consumed ≤ max b (max (ss.popN (n + 2)).2.consumed 0) := by omega
      refine pushAll_sb _ (SB.mono hle p1) ?_
      have hmem : ∀ e ∈ (ss.popN (n + 2)).1.tail, LB (max b (ss.popN (n + 2)).2.consumed) e :=
        fun e he => p2 e (List.mem_of_mem_tail he)
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · -- rest.getD n (.const 0)
        rw [List.getD_eq_getElem?_getD]
        cases hg : (ss.popN (n + 2)).1.tail[n]? with
        | none => exact trivial
        | some x => exact LB.mono hle _ (hmem x (List.mem_of_getElem? hg))
      · rcases List.mem_or_eq_of_mem_set he with he | rfl
        · exact LB.mono hle _ (hmem e he)
        · -- top = headD
          cases hh : (ss.popN (n + 2)).1 with
          | nil => exact trivial
          | cons x xs =>
            simp only [List.headD_cons]
            exact LB.mono hle _ (p2 x (by rw [hh]; simp))

/-! ## The region -/

/-- The builder's invariant. -/
structure RInv (r : Region) : Prop where
  sb    : SB r.need r.ss
  netLe : (r.ss.exprs.length : Int) - r.ss.consumed ≤ r.maxNet
  /-- every buffered write value reads the entry stack below `need` -/
  wlb   : ∀ w ∈ r.writes, LB r.need w.val
  /-- every buffered write's end fits 64-bit address arithmetic -/
  woff  : ∀ w ∈ r.writes, w.off + wWidth w < 2 ^ 64

theorem rinv_empty : RInv ({} : Region) :=
  ⟨SB.empty, by simp, fun w hw => by simp at hw, fun w hw => by simp at hw⟩

theorem rinv_step (r : Region) (op : Op) (ss' : SymStack) (hI : RInv r)
    (hsb : SB (nextB r.need op r.ss ss') ss') : RInv (r.step op ss') := by
  rw [Region.step_eq]
  exact ⟨hsb, by simp only; omega, fun w hw => LB.mono (Nat.le_max_left _ _) _ (hI.wlb w hw), hI.woff⟩

/-- The successor stack of a non-flush outcome. -/
def resOf : RegStep → Option SymStack
  | .fold ss' _  => some ss'
  | .sym ss'     => some ss'
  | .store ss' _ => some ss'
  | .flush       => none

theorem regionStore_cases (ss : SymStack) (isByte : Bool) :
    regionStore ss isByte = .flush ∨ ∃ w, regionStore ss isByte = .store ((ss.pop).2.pop).2 w := by
  unfold regionStore
  split <;> (try split) <;> (try dsimp only) <;> (try split) <;> first | (left; rfl) | (right; exact ⟨_, rfl⟩)

/-- What `regionStep` hands back is bounded by `nextB` in every non-flush case. -/
theorem regionStep_sb (f : Evm.Fork) (r : Region) (op : Op) (ss' : SymStack)
    (h : resOf (regionStep f r.ss op) = some ss') (hs : SB r.need r.ss) :
    SB (nextB r.need op r.ss ss') ss' := by
  have hstore : ∀ isByte, resOf (regionStore r.ss isByte) = some ss' → SB (nextB r.need op r.ss ss') ss' := by
    intro isByte h
    rcases regionStore_cases r.ss isByte with h' | ⟨w, h'⟩ <;> rw [h'] at h <;>
      simp only [resOf, Option.some.injEq, reduceCtorEq] at h
    subst h
    obtain ⟨h1, _, _⟩ := pop_sb hs
    obtain ⟨g1, _, _⟩ := pop_sb h1
    exact SB.mono (by simp only [nextB]; omega) g1
  unfold regionStep at h
  split at h
  · exact hstore false h
  · exact hstore true h
  · try dsimp only at h
    cases hfold : foldStep (constPrefix r.ss.exprs) op with
    | some ks' =>
      -- fold: constants on top of a suffix of the old prefix
      rw [hfold] at h
      simp only [resOf, Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_trans hs.cle (Nat.le_max_left _ _), ?_⟩
      intro e he
      simp only [List.mem_append, List.mem_map] at he
      rcases he with ⟨v, _, rfl⟩ | he
      · trivial
      · exact LB.mono (Nat.le_max_left _ _) _ (hs.lb e (List.mem_of_mem_drop he))
    | none =>
      rw [hfold] at h
      cases hsym : symStep op r.ss with
      | some ss'' =>
        rw [hsym] at h
        simp only [resOf, Option.some.injEq] at h
        subst h
        exact symStep_sb op hsym hs
      | none => rw [hsym] at h; simp [resOf] at h

/-- An absorbed store: the stack after two pops, the value the second pop
    produced, and the end within 64-bit address arithmetic. -/
theorem regionStore_store (ss : SymStack) (isByte : Bool) (ss' : SymStack) (w : MemWrite)
    (h : regionStore ss isByte = .store ss' w) :
    ss' = ((ss.pop).2.pop).2 ∧ w.val = ((ss.pop).2.pop).1 ∧ w.off + wWidth w < 2 ^ 64 := by
  unfold regionStore at h
  split at h <;> (try split at h) <;> (try dsimp only at h) <;> (try split at h) <;>
    first
      | (simp only [RegStep.store.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨rfl, rfl, by simp_all [wWidth]⟩)
      | cases h

theorem regionStep_store (f : Evm.Fork) (r : Region) (op : Op) (ss' : SymStack) (w : MemWrite)
    (h : regionStep f r.ss op = .store ss' w) (hs : SB r.need r.ss) :
    SB (nextB r.need op r.ss ss') ss' ∧ LB (nextB r.need op r.ss ss') w.val ∧ w.off + wWidth w < 2 ^ 64 := by
  refine ⟨regionStep_sb f r op ss' (by rw [h]; rfl) hs, ?_⟩
  have hstore : ∀ isByte, regionStore r.ss isByte = .store ss' w →
      LB (nextB r.need op r.ss ss') w.val ∧ w.off + wWidth w < 2 ^ 64 := by
    intro isByte h
    obtain ⟨hss, hval, hoff⟩ := regionStore_store r.ss isByte ss' w h
    refine ⟨?_, hoff⟩
    obtain ⟨h1, _, _⟩ := pop_sb hs
    obtain ⟨g1, g2, _⟩ := pop_sb h1
    rw [hval]
    exact LB.mono (by subst hss; simp only [nextB]; omega) _ g2
  unfold regionStep at h
  split at h
  · exact hstore false h
  · exact hstore true h
  · try dsimp only at h
    cases hfold : foldStep (constPrefix r.ss.exprs) op with
    | some ks' => rw [hfold] at h; cases h
    | none =>
      rw [hfold] at h
      cases hsym : symStep op r.ss with
      | some ss'' => rw [hsym] at h; cases h
      | none => rw [hsym] at h; cases h

/-- Regions the builder produces: `{}`, then `Region.step` on each
    fold / sym / store outcome of `regionStep` (a `.flush` restarts at `{}`). -/
inductive Built (f : Evm.Fork) : Region → Prop
  | empty : Built f {}
  | fold {r : Region} {op : Op} {ss' : SymStack} {d : Nat} :
      Built f r → regionStep f r.ss op = .fold ss' d → Built f (r.step op ss')
  | sym {r : Region} {op : Op} {ss' : SymStack} :
      Built f r → regionStep f r.ss op = .sym ss' → Built f (r.step op ss')
  | store {r : Region} {op : Op} {ss' : SymStack} {w : MemWrite} :
      Built f r → regionStep f r.ss op = .store ss' w →
      Built f { r.step op ss' with writes := r.writes ++ [w] }

theorem built_inv {f : Evm.Fork} {r : Region} (h : Built f r) : RInv r := by
  induction h with
  | empty => exact rinv_empty
  | fold hb hstep ih =>
    exact rinv_step _ _ _ ih (regionStep_sb f _ _ _ (by rw [hstep]; rfl) ih.sb)
  | sym hb hstep ih =>
    exact rinv_step _ _ _ ih (regionStep_sb f _ _ _ (by rw [hstep]; rfl) ih.sb)
  | @store r op ss' w hb hstep ih =>
    obtain ⟨hsb, hlb, hoff⟩ := regionStep_store f r op ss' w hstep ih.sb
    rw [show ({ r.step op ss' with writes := r.writes ++ [w] } : Region) =
          { ss := ss', need := nextB r.need op r.ss ss',
            maxNet := max r.maxNet ((ss'.exprs.length : Int) - ss'.consumed),
            writes := r.writes ++ [w] } by rw [Region.step_eq]]
    refine ⟨hsb, by simp only; omega, ?_, ?_⟩
    · intro w' hw'
      simp only [List.mem_append, List.mem_singleton] at hw'
      rcases hw' with hw' | rfl
      · exact LB.mono (Nat.le_max_left _ _) _ (ih.wlb w' hw')
      · exact hlb
    · intro w' hw'
      simp only [List.mem_append, List.mem_singleton] at hw'
      rcases hw' with hw' | rfl
      · exact ih.woff w' hw'
      · exact hoff

/-- THE result: a built region is well formed for the flush. -/
theorem built_wf {f : Evm.Fork} {r : Region} (h : Built f r) : RegionWF r := by
  have hI := built_inv h
  refine ⟨hI.sb.cle, ?_, hI.netLe, hI.woff⟩
  intro e he k hk
  subst hk
  refine LB.stackAt_lt (fold_lb r.need (rootsOf r) [] (fun x hx => by simp at hx) ?_ _ he)
  intro e he
  simp only [rootsOf, List.mem_append, List.mem_map] at he
  rcases he with he | ⟨w, hw, rfl⟩
  · exact hI.sb.lb e he
  · exact hI.wlb w hw

end Evm.CL.ARM64.RegionBuild

namespace Evm.CL.ARM64.RegionBuild

open Evm.CL.ARM64.JIT Evm.CL.ARM64.FlushMain
open Evm.IR (Op Chunk)
open Evm.IR.SymExpr (SymStack)

/-! ## The regions `emitChunkGen` flushes

    `emitChunkGen` is polymorphic in its output algebra; at the algebra that
    collects the flushed regions and forgets everything else, its output is the
    list of regions whose flush code the real algebras emit. -/

/-- The region-collecting algebra. -/
def regionsOut : ChunkOut (List Region) where
  nil      := []
  cat      := (· ++ ·)
  head _   := []
  setPc _  := []
  gas _    := []
  flush _ r := [r]
  adrCont _ := []
  label _  := []
  callSym _ := []
  tailSym _ := []
  brCont   := []
  syncCont := []
  brk      := []

/-- The regions a chunk's lowering flushes, in order. -/
def flushedRegions (f : Evm.Fork) (c : Chunk) : List Region := emitChunkGen regionsOut f c

/-- The body-pass invariant: every flushed region and the open one are built. -/
def BodyInv (f : Evm.Fork) (st : BodySt (List Region)) : Prop :=
  (∀ r ∈ st.body, Built f r) ∧ Built f st.r

theorem bodyStep_inv (f : Evm.Fork) (id : Nat) (costs dynAt : List Nat) (st : BodySt (List Region))
    (op : Op) (hI : BodyInv f st) :
    BodyInv f (bodyStep regionsOut f id costs dynAt st op) := by
  obtain ⟨hb, hr⟩ := hI
  unfold bodyStep
  simp only
  refine ⟨?_, ?_⟩ <;> (cases hstep : regionStep f st.r.ss op <;> simp only)
  · exact hb
  · exact hb
  · exact hb
  · -- flush: the body grows by the open region only
    intro r hr'
    simp only [regionsOut, List.append_nil] at hr'
    split at hr' <;> split at hr' <;> simp only [List.mem_append, List.mem_singleton] at hr' <;>
      (rcases hr' with hr' | rfl; exact hb r hr'; exact hr)
  · exact Built.fold hr hstep
  · exact Built.sym hr hstep
  · exact Built.store hr hstep
  · exact Built.empty

theorem foldl_inv (f : Evm.Fork) (id : Nat) (costs dynAt : List Nat) :
    ∀ (ops : List Op) (st : BodySt (List Region)), BodyInv f st →
    BodyInv f (ops.foldl (bodyStep regionsOut f id costs dynAt) st)
  | [], st, hI => hI
  | op :: ops, st, hI => by
    simp only [List.foldl_cons]
    exact foldl_inv f id costs dynAt ops _ (bodyStep_inv f id costs dynAt st op hI)

/-- THE chunk-level result: every region `emitChunkGen` flushes is built, hence
    (`built_wf`) well formed for the flush once it is write-free. -/
theorem flushed_built (f : Evm.Fork) (c : Chunk) :
    ∀ r ∈ flushedRegions f c, Built f r := by
  intro r hr
  have hI := foldl_inv f c.startPc (c.ops.map Interp.chargedCost) (dynCosts f c.ops) c.ops
    { body := [], pc := c.startPc, i := 0, r := {}, uid := 0 }
    ⟨fun r hr => by simp at hr, Built.empty⟩
  obtain ⟨hb, hlast⟩ := hI
  unfold flushedRegions emitChunkGen at hr
  simp only [regionsOut, List.append_nil, List.nil_append, ite_self] at hr
  -- peel the head charge, the terminator, and the trailing flush
  have key : ∀ l, r ∈ l ++ [(c.ops.foldl (bodyStep regionsOut f c.startPc (c.ops.map Interp.chargedCost)
      (dynCosts f c.ops)) { body := [], pc := c.startPc, i := 0, r := {}, uid := 0 }).r] →
      (∀ x ∈ l, Built f x) → Built f r := by
    intro l hl hb
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact hb r hl
    · exact hlast
  split at hr <;>
    (try split at hr) <;>
    exact key _ hr hb

theorem flushed_wf (f : Evm.Fork) (c : Chunk) (r : Region) (hr : r ∈ flushedRegions f c) : RegionWF r :=
  built_wf (flushed_built f c r hr)

open Evm.CL.AsmRun Evm.CL.ARM64.FlushSem Evm.CL.ARM64.CoreSem Evm.CL.ARM64.MemCommitSem in
/-- `flush_run` for the regions a compiled chunk actually flushes: no
    well-formedness hypothesis left, only the layout and entry facts. -/
theorem chunk_flush_run (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (f : Evm.Fork) (c : Chunk) (r : Region)
    (hr : r ∈ flushedRegions f c) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List Evm.CL.AsmCore.AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base) (hes : es.length = d)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (htos : 1 ≤ d → lhs s = es.getD 0 0) (hnos : 2 ≤ d → rhs armRq s = es.getD 1 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H (emitRegionFlushT armFlush r ++ rest) s = run H rest s' ∧
      FlushOut r base d es (frameOf s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s' :=
  flush_run H hS hC r (flushed_wf f c r hr) s base d es st mb rest hL hM h23 h24 hes hstack htos hnos h20 hmb hok
    hcapOk hgasOk hneed hover

open Evm.CL.AsmRun Evm.CL.ARM64.FlushSem Evm.CL.ARM64.CoreSem Evm.CL.ARM64.MemCommitSem in
/-- … and its out-of-gas path. -/
theorem chunk_flush_run_oog (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (f : Evm.Fork) (c : Chunk) (r : Region)
    (hr : r ∈ flushedRegions f c) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List Evm.CL.AsmCore.AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hbad : ¬ (maxEndOf r.writes ≤ (capAt s.mem st).toNat ∧ memGas r s.mem st ≤ (s.regs .x22).toNat))
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ sf, run H (emitRegionFlushT armFlush r ++ rest) s = .fault "_eita_oog" sf :=
  flush_run_oog H hS hC r (flushed_wf f c r hr) s base d es st mb rest hL hM h23 h24 hstack h20 hmb hok hbad hneed hover

end Evm.CL.ARM64.RegionBuild
