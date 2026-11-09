import Evm.CL.EffectSettle
import Evm.CL.EffectSelfdestructProof
import Evm.SpuriousDragon.Fork
import Evm.Parallel.Reads

/-! # CL/EffectSettleProof — `EffectSettle.settle` IS every fork's fee settlement

`settle_refines`: for every fork ordinal `k`, the derived settlement (the sender's refund
delta, then the coinbase's fee delta and its EIP-161 / pre-Spurious zero-fee rule) leaves
a state that agrees — existence, every account, every storage slot — with the fork's
`settleFees` (`Frontier.settleFees` before Spurious Dragon, `SpuriousDragon.settleFees`
from it), the function each fork's `processTransaction` calls, with
`refundWei = (gas-limit − gas-used) × egp` and `minerWei = gas-used × (egp − base fee)`.

Stated assumptions: `gas-used ≤ gas-limit` and `base fee ≤ egp` (tx validity: EELS
rejects `max_fee_per_gas < base_fee_per_gas`); the sender exists (its nonce was bumped);
only existing accounts carry storage (`WF`);
a non-zero fee does not wrap the coinbase balance to zero (`hnowrap`: total supply ≪
2^256 — the spec compares the wrapped sum, the delta never reads the balance).

`delta_fold_balance` / `delta_fold_perm`: a sequence of deltas (one per tx, in index order)
leaves each balance at base + the sum of its deltas, whatever the order — the State-level
counterpart of `Evm.Parallel.Reads.applyDeltas_get` / `applyDeltas_ext`, to which
`delta_fold_reads` connects it (balances as a Reads storage, mod 2^256). -/

namespace Evm.CL.EffectSettle

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.CL.EffectSelfdestruct (getAccount_setAccount accountExists_setAccount
  getStorage_setAccount getAccount_absent acc_eta)

/-! ## State lemmas -/

section lemmas
variable (s : State) (a x : Evm.Address)

theorem accountExists_deleteAccount :
    (s.deleteAccount a).accountExists x = (!decide (x = a) && s.accountExists x) := by
  unfold State.deleteAccount State.accountExists
  by_cases h : x = a
  · subst h; simp
  · have hp : (fun p : Evm.Address × Account => !decide (p.1 = a) && decide (p.1 = x))
        = fun p => decide (p.1 = x) := by
      funext p; by_cases hx : p.1 = x
      · simp [hx, h]
      · simp [hx]
    simp [List.find?_filter, h, hp]

theorem getAccount_deleteAccount :
    (s.deleteAccount a).getAccount x = if x = a then Account.empty else s.getAccount x := by
  unfold State.deleteAccount State.getAccount
  by_cases h : x = a
  · subst h
    have : (s.accounts.filter (fun p : Evm.Address × Account => p.1 ≠ x)).find? (fun p => p.1 = x) = none := by
      rw [List.find?_eq_none]; intro p hp; simp at hp; simp [hp.2]
    simp only [this, ite_true]
  · have hp : (fun p : Evm.Address × Account => !decide (p.1 = a) && decide (p.1 = x))
        = fun p => decide (p.1 = x) := by
      funext p; by_cases hx : p.1 = x
      · simp [hx, h]
      · simp [hx]
    simp [List.find?_filter, h, hp]

theorem getStorage_deleteAccount (k : Evm.U256) :
    (s.deleteAccount a).getStorage x k = if x = a then 0 else s.getStorage x k := by
  unfold State.deleteAccount State.getStorage
  by_cases h : x = a
  · subst h
    have : (s.storage.filter (fun p : (Evm.Address × Evm.U256) × Evm.U256 => p.1.1 ≠ x)).find?
        (fun p => p.1 = (x, k)) = none := by
      rw [List.find?_eq_none]; intro p hp
      simp only [List.mem_filter] at hp
      simp only [decide_eq_true_eq]; intro he; rw [he] at hp; simp at hp
    simp only [this, ite_true]
  · have hp : (fun p : (Evm.Address × Evm.U256) × Evm.U256 => !decide (p.1.1 = a) && decide (p.1 = (x, k)))
        = fun p => decide (p.1 = (x, k)) := by
      funext p; by_cases hx : p.1 = (x, k)
      · simp [hx, h]
      · simp [hx]
    simp [List.find?_filter, h, hp]

/-- An account with a non-zero balance exists (absent accounts read as empty). -/
theorem exists_of_balance (h : (s.getAccount x).balance ≠ 0) : s.accountExists x = true := by
  cases hb : s.accountExists x
  · exact absurd (by rw [getAccount_absent s x (by simp [hb])]; rfl) h
  · rfl

end lemmas

theorem u256_add0 (x : Evm.U256) : x + 0 = x := BitVec.add_zero x
theorem acc_add0 (A : Account) :
    ({ nonce := A.nonce, balance := A.balance + 0, code := A.code } : Account) = A := by
  rw [u256_add0]

theorem ofNat_toNat' (w : Evm.U256) : BitVec.ofNat 256 (BitVec.toNat w) = w := by simp

theorem ofNat_sub (a b : Nat) (h : b ≤ a) :
    BitVec.ofNat 256 a - BitVec.ofNat 256 b = BitVec.ofNat 256 (a - b) := by
  have : BitVec.ofNat 256 a = BitVec.ofNat 256 (a - b) + BitVec.ofNat 256 b := by
    rw [BitVec.ofNat_add_ofNat, Nat.sub_add_cancel h]
  rw [this, BitVec.add_sub_cancel]

/-! ## The settlement theorem -/

/-- Two states agree on everything an observation can see: existence, accounts, storage.
    (The spec's association lists may differ in order.) -/
structure SAgree (s t : State) : Prop where
  exists_ : ∀ x, s.accountExists x = t.accountExists x
  account : ∀ x, s.getAccount x = t.getAccount x
  storage : ∀ x k, s.getStorage x k = t.getStorage x k

/-- Only existing accounts carry storage (EELS: an account's storage is its own trie, and
    `destroy_account` removes both). Every state the replay or the spec builds from a
    well-formed genesis by `setAccount`/`deleteAccount`/`setStorage` on existing accounts
    keeps it; the end-of-tx proofs assume it of the state they start from. -/
def WF (s : State) : Prop := ∀ x k, s.accountExists x = false → s.getStorage x k = 0

theorem WF.setAccount {s : State} (h : WF s) (a : Evm.Address) (acc : Account) : WF (s.setAccount a acc) := by
  intro x k hx
  rw [accountExists_setAccount] at hx; simp only [Bool.or_eq_false_iff] at hx
  rw [getStorage_setAccount]; exact h x k hx.2
theorem WF.addBalance {s : State} (h : WF s) (a : Evm.Address) (d : Evm.U256) : WF (s.addBalance a d) :=
  h.setAccount a _
theorem WF.deleteAccount {s : State} (h : WF s) (a : Evm.Address) : WF (s.deleteAccount a) := by
  intro x k hx
  rw [getStorage_deleteAccount]; split
  · rfl
  · rename_i hxa; rw [accountExists_deleteAccount] at hx; simp [hxa] at hx; exact h x k hx

namespace SAgree
theorem refl (s : State) : SAgree s s := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
theorem symm {s t : State} (h : SAgree s t) : SAgree t s :=
  ⟨fun x => (h.exists_ x).symm, fun x => (h.account x).symm, fun x k => (h.storage x k).symm⟩
theorem trans {s t u : State} (h1 : SAgree s t) (h2 : SAgree t u) : SAgree s u :=
  ⟨fun x => (h1.exists_ x).trans (h2.exists_ x), fun x => (h1.account x).trans (h2.account x),
   fun x k => (h1.storage x k).trans (h2.storage x k)⟩
theorem setAccount {s t : State} (h : SAgree s t) (a : Evm.Address) (acc : Account) :
    SAgree (s.setAccount a acc) (t.setAccount a acc) :=
  ⟨fun x => by simp [accountExists_setAccount, h.exists_ x],
   fun x => by simp [getAccount_setAccount, h.account x],
   fun x k => by simp [getStorage_setAccount, h.storage x k]⟩
theorem addBalance {s t : State} (h : SAgree s t) (a : Evm.Address) (d : Evm.U256) :
    SAgree (s.addBalance a d) (t.addBalance a d) := by
  unfold State.addBalance; rw [h.account a]; exact h.setAccount a _
theorem deleteAccount {s t : State} (h : SAgree s t) (a : Evm.Address) :
    SAgree (s.deleteAccount a) (t.deleteAccount a) :=
  ⟨fun x => by simp [accountExists_deleteAccount, h.exists_ x],
   fun x => by simp [getAccount_deleteAccount, h.account x],
   fun x k => by simp [getStorage_deleteAccount, h.storage x k]⟩
theorem touchAccount {s t : State} (h : SAgree s t) (a : Evm.Address) :
    SAgree (s.touchAccount a) (t.touchAccount a) := by
  unfold State.touchAccount; rw [h.exists_ a]; split
  · exact h
  · exact h.setAccount a _
theorem ite {P : Prop} [Decidable P] {a b c d : State} (h1 : SAgree a b) (h2 : SAgree c d) :
    SAgree (if P then a else c) (if P then b else d) := by
  split
  · exact h1
  · exact h2
/-- Re-setting an existing account to itself changes no observation. -/
theorem setAccount_self (s : State) (a : Evm.Address) (hex : s.accountExists a = true) :
    SAgree (s.setAccount a (s.getAccount a)) s :=
  ⟨fun x => by by_cases hx : x = a <;> simp [accountExists_setAccount, hx, hex],
   fun x => by by_cases hx : x = a <;> simp [getAccount_setAccount, hx],
   fun x k => by simp [getStorage_setAccount]⟩
/-- Destroying an absent account changes no observation in a well-formed state. -/
theorem delete_absent (s : State) (a : Evm.Address) (hwf : WF s) (hx : s.accountExists a = false) :
    SAgree (s.deleteAccount a) s :=
  ⟨fun x => by by_cases hxa : x = a <;> simp [accountExists_deleteAccount, hxa, hx],
   fun x => by by_cases hxa : x = a <;> simp [getAccount_deleteAccount, hxa, getAccount_absent s a (by simp [hx])],
   fun x k => by by_cases hxa : x = a <;> simp [getStorage_deleteAccount, hxa]; subst hxa; exact (hwf x k hx).symm⟩
end SAgree

/-- The fork's fee settlement, as its `processTransaction` calls it (`settleFees`): the
    pre-Spurious form to Tangerine Whistle (ordinal 3), the EIP-161 form from Spurious
    Dragon (4) on. -/
def specSettle (k : Nat) (s : State) (sender coinbase : Evm.Address) (refundWei minerWei : Nat) : State :=
  if 4 ≤ k then Evm.SpuriousDragon.settleFees s sender coinbase refundWei minerWei
  else Evm.Frontier.settleFees s sender coinbase refundWei minerWei

/-- The callback inputs: fork ordinal, the two addresses, the four words. -/
def ctxOf (k : Nat) (sender coinbase : Evm.Address) (gl gu egp bf : Nat) : Ctx :=
  { fork := k, addr := fun x => if x = "sender" then sender else coinbase,
    word := fun x => if x = "gas-limit" then BitVec.ofNat 256 gl
      else if x = "gas-used" then BitVec.ofNat 256 gu
      else if x = "egp" then BitVec.ofNat 256 egp
      else if x = "base-fee" then BitVec.ofNat 256 bf else 0 }

attribute [local simp] Stmt.run BExp.eval WExp.eval AExp.eval isDead
  getAccount_setAccount accountExists_setAccount getStorage_setAccount State.addBalance
  State.touchAccount accountExists_deleteAccount getAccount_deleteAccount getStorage_deleteAccount

/-- What the two terms do to the state (they change nothing else). -/
def refundState (s : State) (sender : Evm.Address) (rw : Evm.U256) : State :=
  if rw = 0 then s else s.addBalance sender rw
def coinbaseState (k : Nat) (s : State) (coinbase : Evm.Address) (fw : Evm.U256) : State :=
  if fw = 0 then
    if 4 ≤ k then
      (if isDead s coinbase = true then s.deleteAccount coinbase else s)
    else s.touchAccount coinbase
  else s.addBalance coinbase fw

theorem run_settle (k : Nat) (h : HState) (sender coinbase : Evm.Address) (gl gu egp bf : Nat) :
    settle.run (ctxOf k sender coinbase gl gu egp bf) h =
      { h with state := coinbaseState k (refundState h.state sender
                          ((BitVec.ofNat 256 gl - BitVec.ofNat 256 gu) * BitVec.ofNat 256 egp)) coinbase
                          (BitVec.ofNat 256 gu * (BitVec.ofNat 256 egp - BitVec.ofNat 256 bf)) } := by
  cases h
  simp only [settle, refundTerm, coinbaseTerm, Stmt.run, WExp.eval, AExp.eval, BExp.eval, ctxOf,
    String.reduceEq, ite_true, ite_false, refundState, coinbaseState]
  by_cases hr : (BitVec.ofNat 256 gl - BitVec.ofNat 256 gu) * BitVec.ofNat 256 egp = 0 <;>
  by_cases hf : BitVec.ofNat 256 gu * (BitVec.ofNat 256 egp - BitVec.ofNat 256 bf) = 0 <;>
  by_cases hk : 4 ≤ k <;> simp [hr, hf, hk] <;>
    (repeat' split) <;> first | rfl | simp_all

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The derived settlement is every fork's.** -/
theorem settle_refines (k : Nat) (h : HState) (sender coinbase : Evm.Address) (gl gu egp bf : Nat)
    (hgu : gu ≤ gl) (hbf : bf ≤ egp)
    (hsender : h.state.accountExists sender = true) (hwf : WF h.state)
    (hnowrap : ((h.state.addBalance sender (BitVec.ofNat 256 ((gl - gu) * egp))).getAccount coinbase).balance
                 + BitVec.ofNat 256 (gu * (egp - bf)) = 0 → BitVec.ofNat 256 (gu * (egp - bf)) = 0) :
    let R := settle.run (ctxOf k sender coinbase gl gu egp bf) h
    SAgree (specSettle k h.state sender coinbase ((gl - gu) * egp) (gu * (egp - bf))) R.state ∧
      R.destroyed = h.destroyed ∧ R.touched = h.touched ∧ R.accessed = h.accessed ∧
      R.created = h.created ∧ R.refund = h.refund ∧ R.gas = h.gas ∧ R.facts = h.facts := by
  intro R
  have hw1 : (BitVec.ofNat 256 gl - BitVec.ofNat 256 gu) * BitVec.ofNat 256 egp
      = BitVec.ofNat 256 ((gl - gu) * egp) := by rw [ofNat_sub _ _ hgu, BitVec.ofNat_mul_ofNat]
  have hw2 : BitVec.ofNat 256 gu * (BitVec.ofNat 256 egp - BitVec.ofNat 256 bf)
      = BitVec.ofNat 256 (gu * (egp - bf)) := by rw [ofNat_sub _ _ hbf, BitVec.ofNat_mul_ofNat]
  refine ⟨?_, by simp [R, run_settle]⟩
  simp only [R, run_settle, hw1, hw2]
  simp only [specSettle, Evm.SpuriousDragon.settleFees, Evm.SpuriousDragon.payCoinbase,
    Evm.Frontier.settleFees, coinbaseState, refundState, Evm.U256.ofNat]
  generalize BitVec.ofNat 256 ((gl - gu) * egp) = RW at *
  generalize BitVec.ofNat 256 (gu * (egp - bf)) = FW at *
  generalize h.state = s0 at *
  -- the refund: a zero delta is no effect, the spec's zero credit to the (existing) sender
  -- re-sets it to itself
  have h1 : SAgree (s0.addBalance sender RW) (if RW = 0 then s0 else s0.addBalance sender RW) := by
    split
    · rename_i hr; subst hr
      have : s0.addBalance sender 0 = s0.setAccount sender (s0.getAccount sender) := by
        simp only [State.addBalance, acc_add0]
      rw [this]; exact SAgree.setAccount_self s0 sender hsender
    · exact SAgree.refl _
  generalize (if RW = 0 then s0 else s0.addBalance sender RW) = t1 at *
  generalize hs1 : s0.addBalance sender RW = s1 at *
  -- the coinbase term only observes `t1`, which agrees with `s1`
  have hc : SAgree
      (if FW = 0 then
        if 4 ≤ k then
          (if isDead s1 coinbase = true then s1.deleteAccount coinbase else s1)
        else s1.touchAccount coinbase
      else s1.addBalance coinbase FW)
      (if FW = 0 then
        if 4 ≤ k then
          (if isDead t1 coinbase = true then t1.deleteAccount coinbase else t1)
        else t1.touchAccount coinbase
      else t1.addBalance coinbase FW) := by
    simp only [isDead, h1.exists_ coinbase, h1.account coinbase]
    by_cases hf : FW = 0 <;> by_cases hk : 4 ≤ k <;> simp only [hf, hk, ite_true, ite_false]
    · exact SAgree.ite (h1.deleteAccount _) h1
    · exact h1.touchAccount _
    · exact h1.addBalance _ _
    · exact h1.addBalance _ _
  refine SAgree.trans ?_ hc
  have hwf1 : WF s1 := hs1 ▸ hwf.addBalance sender RW
  clear hc h1 hs1
  by_cases hf : FW = 0
  · subst hf
    by_cases hk : 4 ≤ k
    · simp only [hk, ite_true, u256_add0, isDead, ne_eq]
      by_cases hb : (s1.getAccount coinbase).balance = 0
      · simp only [hb, not_true_eq_false, ite_false]
        by_cases hex : s1.accountExists coinbase = true
        · simp [hex]; exact SAgree.refl _
        · simp only [hex, Bool.false_eq_true, false_and, ite_false, ite_true]
          exact (SAgree.delete_absent s1 coinbase hwf1 (by simpa using hex)).symm
      · have hex := exists_of_balance s1 coinbase hb
        have hne : (s1.getAccount coinbase).isEmpty = false := by
          simp only [Account.isEmpty, hb, false_and, and_false, decide_false]
        simp only [hb, not_false_eq_true, ite_true, hex, hne]
        exact SAgree.setAccount_self s1 coinbase hex
    · simp only [hk, ite_false, ite_true, State.addBalance, State.touchAccount, acc_add0]
      by_cases hex : s1.accountExists coinbase = true
      · simp only [hex, ite_true]; exact SAgree.setAccount_self s1 coinbase hex
      · simp only [hex, Bool.false_eq_true, ite_false]
        rw [getAccount_absent s1 coinbase hex]; exact SAgree.refl _
  · have hnz : (s1.getAccount coinbase).balance + FW ≠ 0 := fun h0 => hf (hnowrap h0)
    by_cases hk : 4 ≤ k
    · simp only [hk, ite_true, hf, ite_false, hnz, ne_eq, not_false_eq_true]
      exact SAgree.refl _
    · simp only [hk, ite_false, hf]; exact SAgree.refl _

/-! ## Deltas: the serial read-modify-write, folded like `Evm.Parallel.Reads` deltas -/

/-- A non-zero delta IS the serial read-modify-write `balance := balance + w`. -/
theorem delta_is_rmw (c : Ctx) (h : HState) (a : AExp) (w : WExp) (hw : w.eval c h ≠ 0) :
    (Stmt.delta a w).run c h = (Stmt.setBalance a (.add (.balance a) w)).run c h := by
  simp only [Stmt.run, ite_eq_right hw, WExp.eval, State.getBalance, State.addBalance]

/-- Settlement deltas of a block's txs, folded in index order with `Stmt.delta`'s meaning. -/
def foldDeltas (s : State) (ds : List (Evm.Address × Evm.U256)) : State :=
  ds.foldl (fun s d => if d.2 = 0 then s else s.addBalance d.1 d.2) s

/-- The same deltas in the `Evm.Parallel.Reads` model: key = the address, amount = the word. -/
def readsDeltas (ds : List (Evm.Address × Evm.U256)) : List (Evm.Parallel.BlockSTM.Key × Nat) :=
  ds.map (fun d => (BitVec.toNat d.1, BitVec.toNat d.2))

theorem foldDeltas_balance (ds : List (Evm.Address × Evm.U256)) (s : State) (x : Evm.Address) :
    (foldDeltas s ds).getBalance x
      = s.getBalance x + BitVec.ofNat 256 (Evm.Parallel.Reads.sumDeltas (readsDeltas ds) x.toNat) := by
  induction ds generalizing s with
  | nil => simp [foldDeltas, readsDeltas, Evm.Parallel.Reads.sumDeltas]
  | cons d ds ih =>
      obtain ⟨a, w⟩ := d
      have hstep := ih (if w = 0 then s else s.addBalance a w)
      simp only [foldDeltas, List.foldl_cons] at hstep ⊢
      rw [hstep]
      simp only [readsDeltas, List.map_cons, Evm.Parallel.Reads.sumDeltas]
      rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
      congr 1
      have hk : (BitVec.toNat a = BitVec.toNat x) ↔ a = x := BitVec.toNat_inj
      by_cases hax : a = x
      · subst hax
        rw [ite_eq_left rfl, ofNat_toNat']
        by_cases hw0 : w = 0
        · subst hw0; rw [ite_eq_left rfl, u256_add0]
        · rw [ite_eq_right hw0]; simp only [State.getBalance, State.addBalance, getAccount_setAccount, ite_true]
      · rw [ite_eq_right (fun h => hax (hk.mp h)), show BitVec.ofNat 256 0 = (0 : Evm.U256) from rfl, u256_add0]
        by_cases hw0 : w = 0
        · rw [ite_eq_left hw0]
        · rw [ite_eq_right hw0]
          simp only [State.getBalance, State.addBalance, getAccount_setAccount, ite_eq_right (Ne.symm hax)]

/-- **The settlement deltas are `Reads` deltas.** If a Reads storage `σ` holds each balance
    (mod 2^256), folding the deltas with the term's meaning leaves each balance at
    `Reads.applyDeltas σ` of the same deltas (mod 2^256) — so `Reads.applyDeltas_comm` /
    `applyDeltas_ext` (any order or grouping with the same per-key sums) and
    `deltas_deferred` (a key only ever delta'd may be settled once, with the sum) hold of
    the coinbase credits the emitted CL makes. -/
theorem delta_fold_reads (ds : List (Evm.Address × Evm.U256)) (s : State)
    (σ : Evm.Parallel.BlockSTM.Storage)
    (hσ : ∀ x : Evm.Address, σ (BitVec.toNat x) % 2 ^ 256 = BitVec.toNat (s.getBalance x)) (x : Evm.Address) :
    BitVec.toNat ((foldDeltas s ds).getBalance x)
      = Evm.Parallel.Reads.applyDeltas σ (readsDeltas ds) (BitVec.toNat x) % 2 ^ 256 := by
  rw [foldDeltas_balance, Evm.Parallel.Reads.applyDeltas_get, BitVec.toNat_add, BitVec.toNat_ofNat,
    ← hσ x, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  exact (Nat.add_mod_mod _ _ _)

/-- **Order is irrelevant.** Two delta lists with the same per-key sums (any permutation,
    any grouping — the hypothesis of `Reads.applyDeltas_ext`) leave every balance equal. -/
theorem delta_fold_order (ds ds' : List (Evm.Address × Evm.U256)) (s : State)
    (h : ∀ k, Evm.Parallel.Reads.sumDeltas (readsDeltas ds) k = Evm.Parallel.Reads.sumDeltas (readsDeltas ds') k)
    (x : Evm.Address) : (foldDeltas s ds).getBalance x = (foldDeltas s ds').getBalance x := by
  rw [foldDeltas_balance, foldDeltas_balance, h]

end Evm.CL.EffectSettle
