import Evm.CL.EffectSstore
import Evm.CL.EffectSettleProof
import Evm.IR.Dispatch

/-! # CL/EffectSstoreProof — `EffectSstore.term` IS each fork's SSTORE

`sstore_refines`: for every fork, the SSTORE handler the IR binds (`Op.handler f .sstore`,
`sstore_binding`) and the derived callback agree — every slot, the refund counter, the
accessed slots, the original-value cache (Berlin+, where the spec keeps one) — and the
opcode's gas is what the callback returns, with out-of-gas exactly when the gas left is
below it. Assumptions, stated: the native handler passed its own checks (not static; from
Istanbul, more than 2300 gas left — EIP-2200/EIP-1706's sentry); at Constantinople and
Istanbul, whose handlers read `originalState` (the tx-start state), the callback's
original-value cache answers the same (`horig`: the seam contract of `orig-get!`, which
records every slot at its first read or write in the tx). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectSstore

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception)
open Evm.CL.EffectSettle (SAgree)

/-! ## Lemmas -/

theorem getStorage_setStorage (s : State) (a x : Evm.Address) (k j v : Evm.U256) :
    (s.setStorage a k v).getStorage x j = if (x, j) = (a, k) then v else s.getStorage x j := by
  unfold State.setStorage State.getStorage
  dsimp only
  have hp : ∀ q : Evm.Address × Evm.U256, q ≠ (a, k) →
      (fun p : (Evm.Address × Evm.U256) × Evm.U256 => !decide (p.1 = (a, k)) && decide (p.1 = q))
        = fun p => decide (p.1 = q) := by
    intro q hq; funext p; by_cases hx : p.1 = q
    · simp [hx, hq]
    · simp [hx]
  by_cases hv : v = 0
  · rw [ite_eq_left hv]
    by_cases h : (x, j) = (a, k)
    · rw [ite_eq_left h, hv]
      have : (s.storage.filter (fun p : (Evm.Address × Evm.U256) × Evm.U256 => decide (p.1 ≠ (a, k)))).find?
          (fun p => decide (p.1 = (x, j))) = none := by
        rw [List.find?_eq_none]; intro p hp'
        simp only [List.mem_filter] at hp'
        simp only [decide_eq_true_eq]; intro he; rw [he, h] at hp'; simp at hp'
      simp only [this]
    · rw [ite_eq_right h]; simp [List.find?_filter, hp (x, j) h]
  · rw [ite_eq_right hv]
    by_cases h : (x, j) = (a, k)
    · rw [ite_eq_left h]; simp [h]
    · rw [ite_eq_right h]; simp [List.find?_filter, hp (x, j) h, Ne.symm h]

theorem setStorage_sagree_self (s : State) (a : Evm.Address) (k : Evm.U256) :
    SAgree (s.setStorage a k (s.getStorage a k)) s :=
  ⟨fun _ => rfl, fun _ => rfl, fun x j => by
    rw [getStorage_setStorage]; split
    · rename_i h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    · rfl⟩

theorem getOrig_eq (e : Environment) (a : Evm.Address) (k fb : Evm.U256) :
    getOrig e.storageOriginals a k fb = Evm.Berlin.Vm.Effect.getOriginal e a k fb := rfl

theorem putOrig_eq (e : Environment) (a : Evm.Address) (k v : Evm.U256) :
    (Evm.Berlin.Vm.Effect.cacheOriginal e a k v).storageOriginals = putOrig e.storageOriginals a k v := by
  unfold Evm.Berlin.Vm.Effect.cacheOriginal putOrig; split <;> rfl

/-! ## The term's meaning in closed form -/

def ctxOf (k : Nat) (self : Evm.Address) (key new : Evm.U256) : Ctx :=
  { fork := k, addr := fun _ => self, word := fun x => if x = "key" then key else new }

/-- Whether the callback finds the slot cold (Berlin+). -/
def coldOf (k : Nat) (e : Environment) (self : Evm.Address) (key : Evm.U256) : Bool :=
  decide (k ≥ 10) && !e.accessedStorageKeys.contains (self, key)

/-- The plan the callback runs. -/
def planOf (k : Nat) (e : Environment) (self : Evm.Address) (key new : Evm.U256) : Nat × Nat :=
  let cur := e.state.getStorage self key
  sstorePlan k e.refundCounter (getOrig (putOrig e.storageOriginals self key cur) self key cur) cur new
    (coldOf k e self key)

/-- The term's result in closed form. -/
def closed (k : Nat) (e : Environment) (self : Evm.Address) (key new : Evm.U256) : HState :=
  let cur := e.state.getStorage self key
  { HState.ofEnv e with
    state := if new = cur then e.state else e.state.setStorage self key new
    refund := (planOf k e self key new).2, gas := (planOf k e self key new).1
    slots := if k ≥ 10 ∧ ¬ e.accessedStorageKeys.contains (self, key)
             then e.accessedStorageKeys ++ [(self, key)] else e.accessedStorageKeys
    origs := putOrig e.storageOriginals self key cur }

theorem run_term (k : Nat) (e : Environment) (self : Evm.Address) (key new : Evm.U256) :
    term.run (ctxOf k self key new) (HState.ofEnv e) = closed k e self key new := by
  simp only [term, Stmt.run, BExp.eval, WExp.eval, AExp.eval, ctxOf, HState.ofEnv, String.reduceEq,
    ite_true, ite_false, coldOf, closed, planOf]
  by_cases hk : k ≥ 10 <;> by_cases hc : e.accessedStorageKeys.contains (self, key) = true <;>
    by_cases hn : new = e.state.getStorage self key <;>
    simp [hk, hc, hn]

/-! ## Agreement and the theorem -/

/-- The spec environment after SSTORE and the term's state agree on what the callback
    changes: every slot (and account), the refund counter, the accessed slots; the
    original-value cache from Berlin (before, the spec reads `originalState` instead);
    nothing else changed. -/
structure Agree (k : Nat) (e : Environment) (h : HState) : Prop where
  state     : SAgree e.state h.state
  refund    : e.refundCounter = h.refund
  slots     : e.accessedStorageKeys = h.slots
  origs     : k ≥ 10 → e.storageOriginals = h.origs
  rest      : e.selfDestructSet = h.destroyed ∧ e.touched = h.touched ∧
              e.accessedAddresses = h.accessed ∧ e.createdAccounts = h.created

def Refines (k : Nat) (spec : Except Exception Evm) (g : Nat) (R : HState) : Prop :=
  (∀ evm', spec = .ok evm' → Agree k evm'.env R ∧ g = evm'.gasLeft + R.gas) ∧
  (∀ e, spec = .error e → e = .outOfGas ∧ g < R.gas)

/-- Each fork's SSTORE as the IR binds it (`sstore_binding`). -/
def specSstore : Evm.Fork → Evm → Except Exception Evm
  | .constantinople => Evm.Constantinople.Vm.Instructions.sstore
  | .istanbul | .muirGlacier => Evm.Istanbul.Vm.Instructions.sstore
  | .berlin => Evm.Berlin.Vm.Effect.doSstorePure
  | .london | .arrowGlacier | .grayGlacier | .paris | .shanghai | .cancun | .prague | .osaka
  | .bpo1 | .bpo2 | .amsterdam => Evm.London.Vm.Effect.doSstoreLondon
  | _ => Evm.Frontier.Vm.Instructions.sstore

theorem sstore_binding (f : Evm.Fork) :
    Evm.IR.Dispatch.Op.handler f .sstore = some (specSstore f) := by
  cases f <;> rfl

theorem charge_cases (g c : Nat) :
    (c ≤ g ∧ Evm.Frontier.Vm.Gas.charge g c = .ok (g - c)) ∨
    (g < c ∧ Evm.Frontier.Vm.Gas.charge g c = .error .outOfGas) := by
  unfold Evm.Frontier.Vm.Gas.charge
  by_cases h : g < c
  · right; simp [h]
  · left; simp [h]; omega

/-- The shared tail: a handler that charges `cost` then writes `new` and sets the refund
    counter refines the term, given the term's plan is that cost and refund and the
    environment it ends in matches field by field. -/
theorem tail_refines (k : Nat) (evm : Evm) (s : Stack) (cost refund : Nat) (env' : Environment)
    (R : HState) (hgas : R.gas = cost) (hagree : Agree k { env' with refundCounter := refund } R) :
    Refines k (do
        let gasLeft ← Evm.Frontier.Vm.Gas.charge evm.gasLeft cost
        return { evm with gasLeft := gasLeft, stack := s, env := { env' with refundCounter := refund }, pc := evm.pc + 1 }) evm.gasLeft R := by
  rcases charge_cases evm.gasLeft cost with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨hagree, by simp; omega⟩
    · simp [hc, bind, Except.bind, pure, Except.pure] at h
  · refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp [hc, bind, Except.bind] at h
    · simp only [hc, bind, Except.bind, Except.error.injEq] at h
      exact ⟨h.symm, by omega⟩

/-- The spec's storage after the write and the term's agree (the term skips an unchanged
    write; the spec re-sets the slot to its own value). -/
theorem state_agree (st : State) (self : Evm.Address) (key new : Evm.U256) :
    SAgree (st.setStorage self key new)
      (if new = st.getStorage self key then st else st.setStorage self key new) := by
  split
  · rename_i h; rw [h]; exact setStorage_sagree_self st self key
  · exact SAgree.refl _

set_option hygiene false in
/-- Unfold a handler down to its charge, and split on the charge. -/
macro "ss_open" : tactic => `(tactic| (
  simp only [hstack, hstatic, Stack.pop2, Stack.pop, bind, Except.bind, pure, Except.pure,
    Bool.false_eq_true, ite_false, ite_false]))

set_option maxHeartbeats 4000000 in
theorem refines_frontier (k : Nat) (hk : k < 8) (h6 : k ≠ 6) (evm : Evm) (key new : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = key :: new :: rest)
    (hstatic : evm.message.isStatic = false) :
    Refines k (Evm.Frontier.Vm.Instructions.sstore evm) evm.gasLeft
      (closed k evm.env evm.message.currentTarget key new) := by
  have hp : planOf k evm.env evm.message.currentTarget key new =
      Evm.Frontier.Vm.Instructions.sstoreGas evm.env.refundCounter
        (evm.env.state.getStorage evm.message.currentTarget key) new := by
    simp [planOf, sstorePlan, SstoreSched.ofFork, SstoreSched.plan, h6, hk]
  unfold Evm.Frontier.Vm.Instructions.sstore
  ss_open
  rcases charge_cases evm.gasLeft (Evm.Frontier.Vm.Instructions.sstoreGas evm.env.refundCounter
      (evm.env.state.getStorage evm.message.currentTarget key) new).1 with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact state_agree _ _ _ _
      · simp [closed, hp]
      · simp [closed]; omega
      · intro h10; omega
      · simp [closed, HState.ofEnv]
      · simp [closed, hp]; omega
    · cases h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed, hp]; omega⟩

theorem getOrig_putOrig (o : List ((Evm.Address × Evm.U256) × Evm.U256)) (a : Evm.Address) (k c : Evm.U256) :
    getOrig (putOrig o a k c) a k c = getOrig o a k c := by
  unfold putOrig
  split
  · rfl
  · rename_i h
    have hn : o.find? (fun p => decide (p.1 = (a, k))) = none := by
      rw [List.find?_eq_none]; intro p hp hq
      exact h (List.any_eq_true.mpr ⟨p, hp, by simpa using hq⟩)
    unfold getOrig
    simp [List.find?_append, hn]

theorem putOrig_getOrig (o : List ((Evm.Address × Evm.U256) × Evm.U256)) (a : Evm.Address) (k c : Evm.U256) :
    putOrig o a k (getOrig o a k c) = putOrig o a k c := by
  unfold putOrig
  split
  · rfl
  · rename_i h
    have hn : o.find? (fun p => decide (p.1 = (a, k))) = none := by
      rw [List.find?_eq_none]; intro p hp hq
      exact h (List.any_eq_true.mpr ⟨p, hp, by simpa using hq⟩)
    simp [getOrig, hn]

set_option maxHeartbeats 4000000 in
theorem refines_constantinople (evm : Evm) (key new : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = key :: new :: rest)
    (hstatic : evm.message.isStatic = false)
    (horig : getOrig (putOrig evm.env.storageOriginals evm.message.currentTarget key
                (evm.env.state.getStorage evm.message.currentTarget key))
              evm.message.currentTarget key (evm.env.state.getStorage evm.message.currentTarget key)
        = evm.env.originalState.getStorage evm.message.currentTarget key) :
    Refines 6 (Evm.Constantinople.Vm.Instructions.sstore evm) evm.gasLeft
      (closed 6 evm.env evm.message.currentTarget key new) := by
  have hp : planOf 6 evm.env evm.message.currentTarget key new =
      Evm.Constantinople.Vm.Instructions.sstoreGas evm.env.refundCounter
        (evm.env.originalState.getStorage evm.message.currentTarget key)
        (evm.env.state.getStorage evm.message.currentTarget key) new := by
    simp only [planOf, sstorePlan, SstoreSched.ofFork, SstoreSched.plan, ite_true]; rw [horig]
  unfold Evm.Constantinople.Vm.Instructions.sstore
  ss_open
  rcases charge_cases evm.gasLeft (Evm.Constantinople.Vm.Instructions.sstoreGas evm.env.refundCounter
      (evm.env.originalState.getStorage evm.message.currentTarget key)
      (evm.env.state.getStorage evm.message.currentTarget key) new).1 with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact state_agree _ _ _ _
      · simp [closed, hp]
      · simp [closed]
      · intro h10; omega
      · simp [closed, HState.ofEnv]
      · simp [closed, hp]; omega
    · cases h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed, hp]; omega⟩

set_option maxHeartbeats 4000000 in
theorem refines_istanbul (k : Nat) (hk : k = 8 ∨ k = 9) (evm : Evm) (key new : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = key :: new :: rest)
    (hstatic : evm.message.isStatic = false) (hsentry : 2300 < evm.gasLeft)
    (horig : getOrig (putOrig evm.env.storageOriginals evm.message.currentTarget key
                (evm.env.state.getStorage evm.message.currentTarget key))
              evm.message.currentTarget key (evm.env.state.getStorage evm.message.currentTarget key)
        = evm.env.originalState.getStorage evm.message.currentTarget key) :
    Refines k (Evm.Istanbul.Vm.Instructions.sstore evm) evm.gasLeft
      (closed k evm.env evm.message.currentTarget key new) := by
  have hp : planOf k evm.env evm.message.currentTarget key new =
      Evm.Istanbul.Vm.Instructions.sstoreGas evm.env.refundCounter
        (evm.env.originalState.getStorage evm.message.currentTarget key)
        (evm.env.state.getStorage evm.message.currentTarget key) new := by
    have h1 : k ≠ 6 := by omega
    have h2 : ¬ k < 8 := by omega
    have h3 : k < 10 := by omega
    simp only [planOf, sstorePlan, SstoreSched.ofFork, SstoreSched.plan, h1, h2, h3, ite_true, ite_false]; rw [horig]
  have hs : ¬ evm.gasLeft ≤ Evm.Istanbul.Vm.Gas.sstoreSentryGas := by
    simp [Evm.Istanbul.Vm.Gas.sstoreSentryGas]; omega
  unfold Evm.Istanbul.Vm.Instructions.sstore
  ss_open
  simp only [hs, ite_false]
  rcases charge_cases evm.gasLeft (Evm.Istanbul.Vm.Instructions.sstoreGas evm.env.refundCounter
      (evm.env.originalState.getStorage evm.message.currentTarget key)
      (evm.env.state.getStorage evm.message.currentTarget key) new).1 with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [hstatic, Bool.false_eq_true, ite_false, Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact state_agree _ _ _ _
      · simp [closed, hp]
      · simp [closed]; omega
      · intro h10; omega
      · simp [closed, HState.ofEnv]
      · simp [closed, hp]; omega
    · simp [hstatic] at h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed, hp]; omega⟩

section warm
variable (e : Environment) (a : Evm.Address) (k v : Evm.U256)
open Evm.Berlin.Vm.Effect (warmSlot cacheOriginal isSlotWarm getOriginal)
@[simp] theorem ws_refund : (warmSlot e a k).1.refundCounter = e.refundCounter := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_state : (warmSlot e a k).1.state = e.state := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_origs : (warmSlot e a k).1.storageOriginals = e.storageOriginals := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_sd : (warmSlot e a k).1.selfDestructSet = e.selfDestructSet := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_touched : (warmSlot e a k).1.touched = e.touched := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_accessed : (warmSlot e a k).1.accessedAddresses = e.accessedAddresses := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_created : (warmSlot e a k).1.createdAccounts = e.createdAccounts := by unfold warmSlot; split <;> rfl
@[simp] theorem ws_slots : (warmSlot e a k).1.accessedStorageKeys =
    if e.accessedStorageKeys.contains (a, k) then e.accessedStorageKeys else e.accessedStorageKeys ++ [(a, k)] := by
  unfold warmSlot; split <;> simp_all
@[simp] theorem co_refund : (cacheOriginal e a k v).refundCounter = e.refundCounter := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_state : (cacheOriginal e a k v).state = e.state := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_slots : (cacheOriginal e a k v).accessedStorageKeys = e.accessedStorageKeys := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_sd : (cacheOriginal e a k v).selfDestructSet = e.selfDestructSet := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_touched : (cacheOriginal e a k v).touched = e.touched := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_accessed : (cacheOriginal e a k v).accessedAddresses = e.accessedAddresses := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_created : (cacheOriginal e a k v).createdAccounts = e.createdAccounts := by unfold cacheOriginal; split <;> rfl
@[simp] theorem co_origs : (cacheOriginal e a k v).storageOriginals = putOrig e.storageOriginals a k v := putOrig_eq e a k v
end warm

set_option maxHeartbeats 4000000 in
theorem refines_berlin (k : Nat) (hk : k = 10) (evm : Evm) (key new : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = key :: new :: rest)
    (hstatic : evm.message.isStatic = false) (hsentry : 2300 < evm.gasLeft) :
    Refines k (Evm.Berlin.Vm.Effect.doSstorePure evm) evm.gasLeft
      (closed k evm.env evm.message.currentTarget key new) := by
  have hp : planOf k evm.env evm.message.currentTarget key new =
      Evm.Berlin.Vm.Instructions.Storage.sstoreGas evm.env.refundCounter
        (!evm.env.accessedStorageKeys.contains (evm.message.currentTarget, key))
        (getOrig evm.env.storageOriginals evm.message.currentTarget key
          (evm.env.state.getStorage evm.message.currentTarget key))
        (evm.env.state.getStorage evm.message.currentTarget key) new := by
    subst hk; simp [planOf, sstorePlan, SstoreSched.ofFork, SstoreSched.plan, coldOf, getOrig_putOrig]
  have hs : ¬ evm.gasLeft ≤ Evm.Frontier.Vm.Gas.callStipend := by
    simp [Evm.Frontier.Vm.Gas.callStipend]; omega
  have hk10 : k ≥ 10 := by omega
  unfold Evm.Berlin.Vm.Effect.doSstorePure
  ss_open
  simp only [hs, ite_false, ws_refund, co_refund, Evm.Berlin.Vm.Effect.isSlotWarm, co_slots, ← getOrig_eq,
    decide_not, Bool.decide_eq_true]
  rw [← hp]
  rcases charge_cases evm.gasLeft (planOf k evm.env evm.message.currentTarget key new).1
    with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [ws_state, co_state]; exact state_agree _ _ _ _
      · simp [closed]
      · simp [closed, hk10]
      · intro _; simp only [closed, ws_origs, co_origs]; exact putOrig_getOrig _ _ _ _
      · simp [closed, HState.ofEnv]
      · simp [closed]; omega
    · cases h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed]; omega⟩

set_option maxHeartbeats 4000000 in
theorem refines_london (k : Nat) (hk : 11 ≤ k) (evm : Evm) (key new : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = key :: new :: rest)
    (hstatic : evm.message.isStatic = false) (hsentry : 2300 < evm.gasLeft) :
    Refines k (Evm.London.Vm.Effect.doSstoreLondon evm) evm.gasLeft
      (closed k evm.env evm.message.currentTarget key new) := by
  have hp : planOf k evm.env evm.message.currentTarget key new =
      Evm.London.Vm.Effect.sstoreGas evm.env.refundCounter
        (!evm.env.accessedStorageKeys.contains (evm.message.currentTarget, key))
        (getOrig evm.env.storageOriginals evm.message.currentTarget key
          (evm.env.state.getStorage evm.message.currentTarget key))
        (evm.env.state.getStorage evm.message.currentTarget key) new := by
    have h1 : k ≠ 6 := by omega
    have h2 : ¬ k < 8 := by omega
    have h3 : ¬ k < 10 := by omega
    have h4 : k ≠ 10 := by omega
    have h5 : k ≥ 10 := by omega
    simp [planOf, sstorePlan, SstoreSched.ofFork, SstoreSched.plan, coldOf, getOrig_putOrig, h1, h2, h3, h4, h5]
  have hs : ¬ evm.gasLeft ≤ Evm.Frontier.Vm.Gas.callStipend := by
    simp [Evm.Frontier.Vm.Gas.callStipend]; omega
  have hk10 : k ≥ 10 := by omega
  unfold Evm.London.Vm.Effect.doSstoreLondon
  ss_open
  simp only [hs, ite_false, ws_refund, co_refund, Evm.Berlin.Vm.Effect.isSlotWarm, co_slots, ← getOrig_eq,
    decide_not, Bool.decide_eq_true]
  rw [← hp]
  rcases charge_cases evm.gasLeft (planOf k evm.env evm.message.currentTarget key new).1
    with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [ws_state, co_state]; exact state_agree _ _ _ _
      · simp [closed]
      · simp [closed, hk10]
      · intro _; simp only [closed, ws_origs, co_origs]; exact putOrig_getOrig _ _ _ _
      · simp [closed, HState.ofEnv]
      · simp [closed]; omega
    · cases h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed]; omega⟩

set_option maxHeartbeats 4000000 in
/-- **The derived SSTORE callback is every fork's SSTORE.** -/
theorem sstore_refines (f : Evm.Fork) (evm : Evm) (key new : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hsentry : f.ord ≥ 8 → 2300 < evm.gasLeft)
    (horig : (f.ord = 6 ∨ f.ord = 8 ∨ f.ord = 9) →
      getOrig (putOrig evm.env.storageOriginals evm.message.currentTarget key
                (evm.env.state.getStorage evm.message.currentTarget key))
              evm.message.currentTarget key (evm.env.state.getStorage evm.message.currentTarget key)
        = evm.env.originalState.getStorage evm.message.currentTarget key) :
    Refines f.ord (specSstore f evm) evm.gasLeft
      (term.run (ctxOf f.ord evm.message.currentTarget key new) (HState.ofEnv evm.env)) := by
  rw [run_term]
  cases f <;> simp only [specSstore, Evm.Fork.ord] at hsentry horig ⊢
  all_goals first
    | exact refines_frontier _ (by decide) (by decide) evm key new rest hstack hstatic
    | exact refines_constantinople evm key new rest hstack hstatic (horig (by decide))
    | exact refines_istanbul _ (by decide) evm key new rest hstack hstatic (hsentry (by decide))
        (horig (by decide))
    | exact refines_berlin _ rfl evm key new rest hstack hstatic (hsentry (by decide))
    | exact refines_london _ (by decide) evm key new rest hstack hstatic (hsentry (by decide))

end Evm.CL.EffectSstore
