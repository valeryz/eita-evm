/-
  Evm.CL.ARM64.DagSlots — what `ARM64.JIT.dagSlots` (its reference
  definition, the one `implemented_by` is trusted to agree with) guarantees:
  every root is a slot, the slots have no duplicates, every kid of a slot is
  an earlier slot, and the index function returns each slot's position.
  This is what `FlushSem.dag_loop` needs (`WFSlots`).
-/

import Evm.CL.ARM64.JIT

namespace Evm.CL.ARM64.DagSlots

open Evm.CL.ARM64.JIT
open Evm.IR.SymExpr (Expr)

/-- Kids are earlier slots. -/
def Closed (l : List Expr) : Prop :=
  ∀ i (h : i < l.length), ∀ k ∈ exprKids l[i], k ∈ l.take i

theorem closed_nil : Closed [] := by intro i h; simp at h

/-- Appending `e` whose kids are already in `l` keeps closure. -/
theorem closed_append (l : List Expr) (e : Expr) (hl : Closed l) (hk : ∀ k ∈ exprKids e, k ∈ l) :
    Closed (l ++ [e]) := by
  intro i hi k hk'
  rw [List.length_append, List.length_singleton] at hi
  by_cases h : i < l.length
  · rw [List.getElem_append_left h] at hk'
    rw [List.take_append_of_le_length (by omega)]
    exact hl i h k hk'
  · have hi' : i = l.length := by omega
    subst hi'
    rw [List.getElem_append_right (Nat.le_refl _)] at hk'
    simp at hk'
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    exact hk k hk'

/-- `collectSlots` only appends. -/
theorem collect_prefix (acc : List Expr) (e : Expr) : ∃ new, collectSlots acc e = acc ++ new := by
  induction e generalizing acc with
  | const _ | stackAt _ =>
    unfold collectSlots; split
    · exact ⟨[], by simp⟩
    · exact ⟨_, rfl⟩
  | isZero a ih | not_ a ih =>
    unfold collectSlots; split
    · exact ⟨[], by simp⟩
    · obtain ⟨n1, h1⟩ := ih acc
      simp only [h1]
      exact ⟨_, by simp only [List.append_assoc]; rfl⟩
  | addmod a b n iha ihb ihn | mulmod a b n iha ihb ihn =>
    unfold collectSlots; split
    · exact ⟨[], by simp⟩
    · obtain ⟨n1, h1⟩ := iha acc
      obtain ⟨n2, h2⟩ := ihb (acc ++ n1)
      obtain ⟨n3, h3⟩ := ihn (acc ++ n1 ++ n2)
      simp only [h1, h2, h3]
      exact ⟨_, by simp only [List.append_assoc]; rfl⟩
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb | sdiv a b iha ihb
  | mod_ a b iha ihb | smod_ a b iha ihb | signExtend a b iha ihb
  | lt a b iha ihb | gt a b iha ihb | slt a b iha ihb | sgt a b iha ihb | eq_ a b iha ihb
  | and_ a b iha ihb | or_ a b iha ihb | xor_ a b iha ihb
  | byte_ a b iha ihb | shl_ a b iha ihb | shr_ a b iha ihb | sar_ a b iha ihb =>
    unfold collectSlots; split
    · exact ⟨[], by simp⟩
    · obtain ⟨n1, h1⟩ := iha acc
      obtain ⟨n2, h2⟩ := ihb (acc ++ n1)
      simp only [h1, h2]
      exact ⟨_, by simp only [List.append_assoc]; rfl⟩

theorem mem_of_mem_prefix (acc new : List Expr) (x : Expr) (h : x ∈ acc) : x ∈ acc ++ new :=
  List.mem_append_left _ h

/-- The collected expression is in the result. -/
theorem collect_mem (acc : List Expr) (e : Expr) : e ∈ collectSlots acc e := by
  cases e <;> (unfold collectSlots; split) <;> first | (rename_i h; exact List.mem_of_elem_eq_true h) | simp

/-- Everything in `acc` stays. -/
theorem collect_sub (acc : List Expr) (e : Expr) (x : Expr) (hx : x ∈ acc) : x ∈ collectSlots acc e := by
  obtain ⟨new, h⟩ := collect_prefix acc e
  rw [h]; exact List.mem_append_left _ hx

/-- What `collectSlots acc e` adds is `e` and subterms of `e`: nothing larger. -/
theorem collect_new_size (acc : List Expr) (e : Expr) :
    ∀ x ∈ collectSlots acc e, x ∈ acc ∨ sizeOf x ≤ sizeOf e := by
  induction e generalizing acc with
  | const _ | stackAt _ =>
    intro x hx
    unfold collectSlots at hx; split at hx
    · exact Or.inl hx
    · rcases List.mem_append.mp hx with h | h
      · exact Or.inl h
      · simp at h; subst h; exact Or.inr (Nat.le_refl _)
  | isZero a ih | not_ a ih =>
    intro x hx
    unfold collectSlots at hx; split at hx
    · exact Or.inl hx
    · rcases List.mem_append.mp hx with h | h
      · rcases ih acc x h with h' | h'
        · exact Or.inl h'
        · right; simp; omega
      · simp at h; subst h; exact Or.inr (Nat.le_refl _)
  | addmod a b n iha ihb ihn | mulmod a b n iha ihb ihn =>
    intro x hx
    unfold collectSlots at hx; split at hx
    · exact Or.inl hx
    · rcases List.mem_append.mp hx with h | h
      · rcases ihn _ x h with h' | h'
        · rcases ihb _ x h' with h'' | h''
          · rcases iha _ x h'' with h3 | h3
            · exact Or.inl h3
            · right; simp; omega
          · right; simp; omega
        · right; simp; omega
      · simp at h; subst h; exact Or.inr (Nat.le_refl _)
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb | sdiv a b iha ihb
  | mod_ a b iha ihb | smod_ a b iha ihb | signExtend a b iha ihb
  | lt a b iha ihb | gt a b iha ihb | slt a b iha ihb | sgt a b iha ihb | eq_ a b iha ihb
  | and_ a b iha ihb | or_ a b iha ihb | xor_ a b iha ihb
  | byte_ a b iha ihb | shl_ a b iha ihb | shr_ a b iha ihb | sar_ a b iha ihb =>
    intro x hx
    unfold collectSlots at hx; split at hx
    · exact Or.inl hx
    · rcases List.mem_append.mp hx with h | h
      · rcases ihb _ x h with h' | h'
        · rcases iha _ x h' with h'' | h''
          · exact Or.inl h''
          · right; simp; omega
        · right; simp; omega
      · simp at h; subst h; exact Or.inr (Nat.le_refl _)

/-- Appending `e` to a collection of its kids keeps it duplicate-free: `e` is
    not in `acc` (the guard) and not among the kids' additions (too small). -/
theorem nodup_append_big (acc l : List Expr) (e : Expr) (hnd : l.Nodup)
    (hacc : e ∉ acc) (hsub : ∀ x ∈ l, x ∈ acc ∨ sizeOf x < sizeOf e) : (l ++ [e]).Nodup := by
  refine List.nodup_append.mpr ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
  intro x hx y hy hxy
  have hye : y = e := by simpa using hy
  subst hye; subst hxy
  rcases hsub x hx with h | h
  · exact hacc h
  · omega

/-- No duplicates, and kids before parents: the invariant `collectSlots` keeps. -/
theorem collect_wf (acc : List Expr) (e : Expr) (hnd : acc.Nodup) (hc : Closed acc) :
    (collectSlots acc e).Nodup ∧ Closed (collectSlots acc e) := by
  induction e generalizing acc with
  | const _ | stackAt _ =>
    unfold collectSlots; split
    · exact ⟨hnd, hc⟩
    · rename_i hg
      refine ⟨nodup_append_big acc acc _ hnd (by simpa using hg) (fun x hx => Or.inl hx),
              closed_append _ _ hc (by simp [exprKids])⟩
  | isZero a ih | not_ a ih =>
    unfold collectSlots; split
    · exact ⟨hnd, hc⟩
    · rename_i hg
      obtain ⟨nd1, c1⟩ := ih acc hnd hc
      refine ⟨nodup_append_big acc _ _ nd1 (by simpa using hg) ?_,
              closed_append _ _ c1 (by simp [exprKids, collect_mem])⟩
      intro x hx
      rcases collect_new_size acc a x hx with h | h
      · exact Or.inl h
      · right; simp; omega
  | addmod a b n iha ihb ihn | mulmod a b n iha ihb ihn =>
    unfold collectSlots; split
    · exact ⟨hnd, hc⟩
    · rename_i hg
      obtain ⟨nd1, c1⟩ := iha acc hnd hc
      obtain ⟨nd2, c2⟩ := ihb _ nd1 c1
      obtain ⟨nd3, c3⟩ := ihn _ nd2 c2
      refine ⟨nodup_append_big acc _ _ nd3 (by simpa using hg) ?_,
              closed_append _ _ c3 ?_⟩
      · intro x hx
        rcases collect_new_size _ n x hx with h | h
        · rcases collect_new_size _ b x h with h' | h'
          · rcases collect_new_size _ a x h' with h'' | h''
            · exact Or.inl h''
            · right; simp; omega
          · right; simp; omega
        · right; simp; omega
      · intro k hk
        simp only [exprKids, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact collect_sub _ _ _ (collect_sub _ _ _ (collect_mem _ _))
        · exact collect_sub _ _ _ (collect_mem _ _)
        · exact collect_mem _ _
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb | sdiv a b iha ihb
  | mod_ a b iha ihb | smod_ a b iha ihb | signExtend a b iha ihb
  | lt a b iha ihb | gt a b iha ihb | slt a b iha ihb | sgt a b iha ihb | eq_ a b iha ihb
  | and_ a b iha ihb | or_ a b iha ihb | xor_ a b iha ihb
  | byte_ a b iha ihb | shl_ a b iha ihb | shr_ a b iha ihb | sar_ a b iha ihb =>
    unfold collectSlots; split
    · exact ⟨hnd, hc⟩
    · rename_i hg
      obtain ⟨nd1, c1⟩ := iha acc hnd hc
      obtain ⟨nd2, c2⟩ := ihb _ nd1 c1
      refine ⟨nodup_append_big acc _ _ nd2 (by simpa using hg) ?_,
              closed_append _ _ c2 ?_⟩
      · intro x hx
        rcases collect_new_size _ b x hx with h | h
        · rcases collect_new_size _ a x h with h' | h'
          · exact Or.inl h'
          · right; simp; omega
        · right; simp; omega
      · intro k hk
        simp only [exprKids, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · exact collect_sub _ _ _ (collect_mem _ _)
        · exact collect_mem _ _

/-! ## The fold over the roots, and the index function -/

/-- `roots.foldl collectSlots acc`: duplicate-free, closed, and every root and
    every element of `acc` is in it. -/
theorem fold_wf (roots : List Expr) : ∀ (acc : List Expr), acc.Nodup → Closed acc →
    (roots.foldl collectSlots acc).Nodup ∧ Closed (roots.foldl collectSlots acc) ∧
    (∀ x ∈ acc, x ∈ roots.foldl collectSlots acc) ∧ (∀ r ∈ roots, r ∈ roots.foldl collectSlots acc) := by
  induction roots with
  | nil => intro acc hnd hc; exact ⟨hnd, hc, fun x hx => hx, fun r hr => by simp at hr⟩
  | cons r roots ih =>
    intro acc hnd hc
    obtain ⟨nd1, c1⟩ := collect_wf acc r hnd hc
    obtain ⟨nd2, c2, sub2, roots2⟩ := ih (collectSlots acc r) nd1 c1
    refine ⟨by simpa using nd2, by simpa using c2, ?_, ?_⟩
    · intro x hx; simp only [List.foldl_cons]; exact sub2 x (collect_sub acc r x hx)
    · intro r' hr'
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact sub2 r' (collect_mem acc r')
      · exact roots2 r' hr'

/-- The index of a slot, as `dagSlots` computes it. -/
def slotIdx (slots : List Expr) (e : Expr) : Nat := (slots.findIdx? (· == e)).getD 0

theorem slotIdx_spec (slots : List Expr) (e : Expr) (he : e ∈ slots) :
    ∃ h : slotIdx slots e < slots.length, slots[slotIdx slots e] = e := by
  have hi := List.findIdx?_eq_some_of_exists (p := (· == e)) ⟨e, he, by simp⟩
  obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  refine ⟨by simp [slotIdx, hi, hlt], ?_⟩
  simp only [slotIdx, hi, Option.getD_some]
  simpa using hp

/-- Distinct slots have distinct indices (and conversely), when the list is
    duplicate-free: `slots[slotIdx e] = e`. -/
theorem slotIdx_inj (slots : List Expr) (e e' : Expr) (he : e ∈ slots) (he' : e' ∈ slots)
    (h : slotIdx slots e = slotIdx slots e') : e = e' := by
  obtain ⟨h1, g1⟩ := slotIdx_spec slots e he
  obtain ⟨h2, g2⟩ := slotIdx_spec slots e' he'
  rw [← g1, ← g2]
  simp only [h]

/-- `dagSlots`, read off its reference definition. -/
theorem dagSlots_eq (roots : List Expr) :
    dagSlots roots = ((roots.foldl collectSlots []).toArray, slotIdx (roots.foldl collectSlots [])) := rfl

end Evm.CL.ARM64.DagSlots
