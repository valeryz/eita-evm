import Evm.CL.EffectEndTx
import Evm.CL.EffectSettleProof

/-! # CL/EffectEndTxProof — `EffectEndTx.endTx` IS every fork's end of tx

* `endTx_refines`: for every fork ordinal, the derived end of tx (destroy the
  accounts_to_delete, then — Spurious Dragon on — destroy the touched dead accounts)
  agrees (existence, accounts, storage) with the fork's `destroyAccounts` (to Tangerine
  Whistle) / `finishTx` (from Spurious Dragon), the functions every `processTransaction`
  calls, and changes nothing else. Assumption: only existing accounts carry storage (`WF`).
* `destroy_perm`, `sweep_perm`: the result depends on the sets only as sets — so the CL's
  walk of `*selfdestructed*` / `*touched*` (per-tx lists of account ids, `tx-set-addrs`), in
  whatever order, is the term's list fold.
* `sd_form_closes` — the stage-1 open item (docs/effect-layer-derivation.md §5.3). The
  SELFDESTRUCT handlers from Spurious Dragon on skip a zero credit to the beneficiary and
  touch it unconditionally; EELS credits it always (creating an absent one) and touches it
  only when it is then an existing empty account. At the end of the tx the two leave the
  same state, whatever else was destroyed or touched.

The proofs go through one closed form (`fold_obs`): folding "destroy `a` if `P`" over a
list leaves an address destroyed iff it is in the list and `P` held of it at the start —
deletions of other addresses never change what `P` sees. -/

namespace Evm.CL.EffectEndTx

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.CL.EffectSelfdestruct (getAccount_setAccount accountExists_setAccount
  getStorage_setAccount getAccount_absent acc_eta)
open Evm.CL.EffectSettle (SAgree WF accountExists_deleteAccount getAccount_deleteAccount
  getStorage_deleteAccount acc_add0 u256_add0)

/-! ## Observations and the closed form of a deleting fold -/

/-- Everything an observation sees of `x`: existence, the account, the storage. -/
def obs (s : State) (x : Evm.Address) : Bool × Account × (Evm.U256 → Evm.U256) :=
  (s.accountExists x, s.getAccount x, fun k => s.getStorage x k)

/-- What a destroyed address looks like. -/
def gone : Bool × Account × (Evm.U256 → Evm.U256) := (false, Account.empty, fun _ => 0)

theorem sagree_of_obs {s t : State} (h : ∀ x, obs s x = obs t x) : SAgree s t :=
  ⟨fun x => congrArg Prod.fst (h x), fun x => congrArg (fun p => p.2.1) (h x),
   fun x k => congrFun (congrArg (fun p => p.2.2) (h x)) k⟩

theorem obs_delete (s : State) (a x : Evm.Address) :
    obs (s.deleteAccount a) x = if x = a then gone else obs s x := by
  unfold obs gone
  by_cases h : x = a
  · simp [h, accountExists_deleteAccount, getAccount_deleteAccount, getStorage_deleteAccount]
  · simp [h, accountExists_deleteAccount, getAccount_deleteAccount, getStorage_deleteAccount]

/-- Destroy `a` when `P` holds of it. -/
def stepP (P : State → Evm.Address → Bool) (s : State) (a : Evm.Address) : State :=
  if P s a then s.deleteAccount a else s

/-- **The closed form.** If deleting `a` never changes what `P` sees of another address,
    folding `stepP P` over `l` destroys exactly the members of `l` that `P` held of at
    the start; every other address is untouched. -/
theorem fold_obs (P : State → Evm.Address → Bool)
    (hP : ∀ s a x, x ≠ a → P (s.deleteAccount a) x = P s x) :
    ∀ (l : List Evm.Address) (s : State) (x : Evm.Address),
      obs (l.foldl (stepP P) s) x = if x ∈ l ∧ P s x = true then gone else obs s x := by
  intro l
  induction l with
  | nil => intro s x; simp
  | cons a l ih =>
      intro s x
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hxa : x = a
      · subst hxa
        by_cases hp : P s x = true
        · have hg : obs (stepP P s x) x = gone := by simp [stepP, hp, obs_delete]
          simp only [hg, hp, List.mem_cons, true_or, and_self, ite_true, ite_self]
        · have hs : stepP P s x = s := by simp [stepP, hp]
          simp [hs, hp]
      · have hob : obs (stepP P s a) x = obs s x := by
          unfold stepP; split
          · rw [obs_delete, ite_eq_right hxa]
          · rfl
        have hpx : P (stepP P s a) x = P s x := by
          unfold stepP; split
          · exact hP s a x hxa
          · rfl
        simp [hob, hpx, hxa]

theorem exists_delete_ne (s : State) (a x : Evm.Address) (h : x ≠ a) :
    (s.deleteAccount a).accountExists x = s.accountExists x := by
  simp [accountExists_deleteAccount, h]
theorem account_delete_ne (s : State) (a x : Evm.Address) (h : x ≠ a) :
    (s.deleteAccount a).getAccount x = s.getAccount x := by
  simp [getAccount_deleteAccount, h]

/-- The spec's three folds, as `stepP` folds. -/
def pDestroy : State → Evm.Address → Bool := fun _ _ => true
def pSweep : State → Evm.Address → Bool := fun s a => s.accountExists a && (s.getAccount a).isEmpty
def pDead : State → Evm.Address → Bool := fun s a => isDead s a

theorem destroy_eq (s : State) (l : List Evm.Address) :
    Evm.Frontier.destroyAccounts s l = l.foldl (stepP pDestroy) s := by
  unfold Evm.Frontier.destroyAccounts
  congr 1

theorem sweep_eq (s : State) (l : List Evm.Address) :
    Evm.SpuriousDragon.sweepEmptyAccounts s l = l.foldl (stepP pSweep) s := by
  unfold Evm.SpuriousDragon.sweepEmptyAccounts
  congr 1; funext st a; simp only [stepP, pSweep, Bool.and_eq_true]

theorem hP_destroy : ∀ s a x, x ≠ a → pDestroy (State.deleteAccount s a) x = pDestroy s x :=
  fun _ _ _ _ => rfl
theorem hP_sweep : ∀ s a x, x ≠ a → pSweep (State.deleteAccount s a) x = pSweep s x := by
  intro s a x h; simp only [pSweep, exists_delete_ne s a x h, account_delete_ne s a x h]
theorem hP_dead : ∀ s a x, x ≠ a → pDead (State.deleteAccount s a) x = pDead s x := by
  intro s a x h; simp only [pDead, isDead, exists_delete_ne s a x h, account_delete_ne s a x h]

theorem WF.fold (P : State → Evm.Address → Bool) :
    ∀ (l : List Evm.Address) (s : State), WF s → WF (l.foldl (stepP P) s) := by
  intro l; induction l with
  | nil => intro s h; exact h
  | cons a l ih =>
      intro s h; simp only [List.foldl_cons]; apply ih
      unfold stepP; split
      · exact h.deleteAccount a
      · exact h

/-! ## The term's meaning -/

def ctxOf (k : Nat) : Ctx := { fork := k, addr := fun _ => 0 }

theorem run_forEach_delete (P : State → Evm.Address → Bool) (c : Ctx) (body : Stmt)
    (hb : ∀ (c' : Ctx) h', body.run c' h' = { h' with state := stepP P h'.state (c'.addr "a") }) :
    ∀ (l : List Evm.Address) (h : HState),
      l.foldl (fun h' a => body.run { c with addr := fun y => if y = "a" then a else c.addr y } h') h
        = { h with state := l.foldl (stepP P) h.state } := by
  intro l; induction l with
  | nil => intro h; rfl
  | cons a l ih => intro h; simp only [List.foldl_cons]; rw [hb, ih]; simp

theorem run_destroy (c : Ctx) (h : HState) :
    destroyTerm.run c h = { h with state := Evm.Frontier.destroyAccounts h.state h.destroyed } := by
  rw [destroy_eq]
  exact run_forEach_delete pDestroy c (.deleteAccount acct)
    (fun c' h' => by simp [Stmt.run, AExp.eval, stepP, pDestroy]) h.destroyed h

set_option backward.isDefEq.respectTransparency false in
theorem run_sweep (c : Ctx) (h : HState) :
    sweepTerm.run c h =
      if 4 ≤ c.fork then { h with state := h.touched.foldl (stepP pDead) h.state } else h := by
  simp only [sweepTerm, Stmt.run, BExp.eval, TxSet.get, decide_eq_true_eq, ge_iff_le]
  split
  · exact run_forEach_delete pDead c (.ite (.dead acct) (.deleteAccount acct) .skip)
      (fun c' h' => by simp only [Stmt.run, BExp.eval, AExp.eval, stepP, pDead]; split <;> rfl) h.touched h
  · rfl

/-! ## The theorem -/

/-- The fork's end of tx, as its `processTransaction` calls it. -/
def specEndTx (k : Nat) (s : State) (destroyed touched : List Evm.Address) : State :=
  if 4 ≤ k then Evm.SpuriousDragon.finishTx s destroyed touched
  else Evm.Frontier.destroyAccounts s destroyed

/-- Absent addresses look destroyed in a well-formed state. -/
theorem obs_absent (s : State) (x : Evm.Address) (hwf : WF s) (hx : s.accountExists x = false) :
    obs s x = gone := by
  unfold obs gone
  rw [hx, getAccount_absent s x (by simp [hx])]
  congr; funext k; exact hwf x k hx

/-- **The derived end of tx is every fork's.** -/
theorem endTx_refines (k : Nat) (h : HState) (hwf : WF h.state) :
    let R := endTx.run (ctxOf k) h
    SAgree (specEndTx k h.state h.destroyed h.touched) R.state ∧
      R.destroyed = h.destroyed ∧ R.touched = h.touched ∧ R.accessed = h.accessed ∧
      R.created = h.created ∧ R.refund = h.refund ∧ R.gas = h.gas ∧ R.facts = h.facts := by
  intro R
  have hR : R = if 4 ≤ k then
        { h with state := h.touched.foldl (stepP pDead) (Evm.Frontier.destroyAccounts h.state h.destroyed) }
      else { h with state := Evm.Frontier.destroyAccounts h.state h.destroyed } := by
    simp only [R, endTx, Stmt.run, run_destroy, run_sweep, ctxOf]
  refine ⟨?_, by rw [hR]; split <;> simp⟩
  rw [hR]
  unfold specEndTx Evm.SpuriousDragon.finishTx
  split
  · simp only
    apply sagree_of_obs
    intro x
    have hwf1 : WF (Evm.Frontier.destroyAccounts h.state h.destroyed) := by
      rw [destroy_eq]; exact WF.fold _ _ _ hwf
    generalize Evm.Frontier.destroyAccounts h.state h.destroyed = s1 at *
    rw [sweep_eq, fold_obs pSweep hP_sweep, fold_obs pDead hP_dead]
    simp only [pSweep, pDead, isDead]
    by_cases hm : x ∈ h.touched
    · by_cases hex : s1.accountExists x = true
      · simp [hm, hex]
      · have hex' : s1.accountExists x = false := by simpa using hex
        simp [hm, hex', obs_absent s1 x hwf1 hex']
    · simp [hm]
  · exact SAgree.refl _

/-- **Walk order is irrelevant**: the CL's `maphash` may visit the set in any order. -/
theorem destroy_perm (s : State) (l l' : List Evm.Address) (hp : l.Perm l') :
    SAgree (Evm.Frontier.destroyAccounts s l) (Evm.Frontier.destroyAccounts s l') := by
  apply sagree_of_obs; intro x
  rw [destroy_eq, destroy_eq, fold_obs _ hP_destroy, fold_obs _ hP_destroy]; simp only [hp.mem_iff]

theorem sweep_perm (s : State) (l l' : List Evm.Address) (hp : l.Perm l') :
    SAgree (l.foldl (stepP pDead) s) (l'.foldl (stepP pDead) s) := by
  apply sagree_of_obs; intro x
  rw [fold_obs _ hP_dead, fold_obs _ hP_dead]; simp only [hp.mem_iff]

/-! ## The SELFDESTRUCT beneficiary: the Spurious Dragon form equals EELS at tx end -/

theorem obs_finishTx (X : State) (D L : List Evm.Address) (x : Evm.Address) :
    obs (Evm.SpuriousDragon.finishTx X D L) x =
      if x ∈ D then gone
      else if x ∈ L ∧ X.accountExists x = true ∧ (X.getAccount x).isEmpty = true then gone
      else obs X x := by
  unfold Evm.SpuriousDragon.finishTx
  rw [sweep_eq, fold_obs _ hP_sweep]
  have hd := fold_obs pDestroy hP_destroy D X x
  rw [← destroy_eq] at hd
  simp only [pDestroy, and_true] at hd
  by_cases hxD : x ∈ D
  · simp only [hxD, ite_true] at hd ⊢
    have hex : (Evm.Frontier.destroyAccounts X D).accountExists x = false := congrArg Prod.fst hd
    simp only [pSweep, hex, Bool.false_and, Bool.false_eq_true, and_false, ite_false]; exact hd
  · simp only [hxD, ite_false] at hd ⊢
    have hex : (Evm.Frontier.destroyAccounts X D).accountExists x = X.accountExists x := congrArg Prod.fst hd
    have hac : (Evm.Frontier.destroyAccounts X D).getAccount x = X.getAccount x := congrArg (fun p => p.2.1) hd
    simp only [pSweep, hex, hac, Bool.and_eq_true]; rw [hd]

/-- **The open item of stage 1, closed at the tx boundary.** At Spurious Dragon and after,
    the SELFDESTRUCT handlers credit the beneficiary `b` only a non-zero `v` and touch it
    always; EELS (spurious_dragon … london `vm/instructions/system.py`) credits it always —
    an absent `b` comes into existence — and touches it only if it is then an existing
    empty account. Whatever else the tx destroyed (`D`) or touched (`T`), the end of the
    tx leaves the same state. (Between the SELFDESTRUCT and the end of the tx the two
    differ only in whether an empty beneficiary exists, which no rule from Spurious
    Dragon on can observe: every gas rule asks `is_account_dead`, EXTCODEHASH answers 0
    for both (EIP-1052) — the residual assumption, stated in the doc.) -/
theorem sd_form_closes (s : State) (hwf : WF s) (b : Evm.Address) (v : Evm.U256)
    (D T : List Evm.Address) :
    let eels := s.addBalance b v
    let eelsT := if eels.accountExists b && (eels.getAccount b).isEmpty then T ++ [b] else T
    let sd := if v = 0 then s else s.addBalance b v
    SAgree (Evm.SpuriousDragon.finishTx eels D eelsT) (Evm.SpuriousDragon.finishTx sd D (T ++ [b])) := by
  intro eels eelsT sd
  apply sagree_of_obs; intro x
  rw [obs_finishTx, obs_finishTx]
  by_cases hxD : x ∈ D
  · simp [hxD]
  simp only [hxD, ite_false]
  by_cases hxb : x = b
  · subst hxb
    by_cases hv : v = 0
    · subst hv
      have hsd : sd = s := by simp [sd]
      rw [hsd]
      have he : eels.accountExists x = true := by
        simp [eels, State.addBalance, accountExists_setAccount]
      have ha : eels.getAccount x = s.getAccount x := by
        simp [eels, State.addBalance, getAccount_setAccount]
      by_cases hsx : s.accountExists x = true
      · have ho : obs eels x = obs s x := by
          unfold obs; rw [he, hsx, ha]; rfl
        by_cases hem : (s.getAccount x).isEmpty = true
        · simp [eelsT, he, ha, hem, hsx]
        · simp [eelsT, he, ha, hem, ho]
      · have hsx' : s.accountExists x = false := by simpa using hsx
        have hem : (s.getAccount x).isEmpty = true := by
          rw [getAccount_absent s x hsx]; rfl
        simp [eelsT, he, ha, hem, hsx', obs_absent s x hwf hsx']
    · have hsd : sd = eels := by
        show (if v = 0 then s else s.addBalance x v) = s.addBalance x v; rw [ite_eq_right hv]
      rw [hsd]
      by_cases hc : (eels.accountExists x && (eels.getAccount x).isEmpty) = true
      · simp only [eelsT, hc, ite_true]
      · simp only [eelsT, hc, Bool.false_eq_true, ite_false]
        simp only [Bool.and_eq_true] at hc
        simp only [List.mem_append, List.mem_singleton, or_true, true_and]
        rw [ite_eq_right hc]
        split
        · rename_i hh; exact absurd hh.2 hc
        · rfl
  · have ho : obs eels x = obs sd x := by
      simp only [sd]; split
      · simp only [obs, eels, State.addBalance, accountExists_setAccount, getAccount_setAccount,
          getStorage_setAccount, hxb, decide_false, Bool.false_or, ite_false]
      · rfl
    have hm : (x ∈ eelsT) ↔ (x ∈ T ++ [b]) := by
      simp only [eelsT]; split <;> simp [hxb]
    have hex : eels.accountExists x = sd.accountExists x := congrArg Prod.fst ho
    have hac : eels.getAccount x = sd.getAccount x := congrArg (fun p => p.2.1) ho
    simp only [hm, hex, hac, ho]

end Evm.CL.EffectEndTx
