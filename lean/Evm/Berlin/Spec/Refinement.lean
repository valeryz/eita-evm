/-
  Evm.Berlin.Spec.Refinement — proofs that the Berlin Effect
  interpreter refines the Berlin Spec relations.

  Berlin adds:

    * `AccessList.lean` — EIP-2929 cold/warm bookkeeping over
      `env.accessedAddresses` / `env.accessedStorageKeys`. Relations:
      `IsAccessAddressStep`, `IsAccessStorageStep`.
    * `StorageStep.lean` — EIP-2929 SSTORE/SLOAD with EIP-2200
      net-metering on top. Relations: `IsSloadStep`, `IsSstoreStep`.

  The access-list helpers (`warmAddr` / `warmSlot`) are proved; SLOAD /
  SSTORE are still open.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Berlin.Spec.AccessList
import Evm.Berlin.Spec.StorageStep
import Evm.Berlin.Vm.Effect
import Evm.Constantinople.Spec.RefundInv
import Mathlib.Tactic.SplitIfs

namespace Evm.Berlin.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Berlin.Spec
open Evm.Berlin.Vm.Effect (getOriginal cacheOriginal warmSlot isSlotWarm)

/-! ## EIP-2929 access-list bookkeeping refinement -/

/-- `warmAddr` (the EIP-2929 address warm-up every Berlin+ access opcode runs) is an
    `IsAccessAddressStep`: cold iff absent, and a cold address is added. EELS
    `forks/berlin/vm/instructions/environment.py::balance` 65-68 (`if address in
    evm.accessed_addresses: … else: evm.accessed_addresses.add(address)`), the same clause
    in every account-access opcode. -/
theorem accessAddress_sound
    (env : Environment) (addr : Evm.Address) (env' : Environment) (wasCold : Bool) :
    Evm.Berlin.Vm.Effect.warmAddr env addr = (env', wasCold) →
    IsAccessAddressStep env addr env' wasCold := by
  unfold Evm.Berlin.Vm.Effect.warmAddr
  intro h
  by_cases hm : addr ∈ env.accessedAddresses
  · have hc : env.accessedAddresses.contains addr = true := by simpa using hm
    rw [ite_eq_left hc] at h; injection h with h1 h2; subst h1 h2
    exact ⟨by simp [hm], by simp [hm]⟩
  · have hc : ¬ env.accessedAddresses.contains addr = true := by simpa using hm
    rw [ite_eq_right hc] at h; injection h with h1 h2; subst h1 h2
    exact ⟨by simp [hm], by simp [hm]⟩

/-- `warmSlot` (the EIP-2929 slot warm-up of SLOAD / SSTORE) is an `IsAccessStorageStep`.
    EELS `forks/berlin/vm/instructions/storage.py::sload` 38-41 (`if (current_target, key)
    in evm.accessed_storage_keys: … else: evm.accessed_storage_keys.add(…)`). -/
theorem accessStorage_sound
    (env : Environment) (addr : Evm.Address) (slot : Evm.U256)
    (env' : Environment) (wasCold : Bool) :
    Evm.Berlin.Vm.Effect.warmSlot env addr slot = (env', wasCold) →
    IsAccessStorageStep env addr slot env' wasCold := by
  unfold Evm.Berlin.Vm.Effect.warmSlot
  intro h
  by_cases hm : (addr, slot) ∈ env.accessedStorageKeys
  · have hc : env.accessedStorageKeys.contains (addr, slot) = true := by simpa using hm
    rw [ite_eq_left hc] at h; injection h with h1 h2; subst h1 h2
    exact ⟨by simp [hm], by simp [hm]⟩
  · have hc : ¬ env.accessedStorageKeys.contains (addr, slot) = true := by simpa using hm
    rw [ite_eq_right hc] at h; injection h with h1 h2; subst h1 h2
    exact ⟨by simp [hm], by simp [hm]⟩

/-! ### The original-value cache (`OrigInv`) -/

/-- The implementation's lookup at the current value is the spec's `cachedOriginal`. -/
theorem getOriginal_current (env : Environment) (a : Evm.Address) (k : Evm.U256) :
    getOriginal env a k (env.state.getStorage a k) = cachedOriginal env a k := rfl

private theorem find_none_of_any_false (l : List ((Evm.Address × Evm.U256) × Evm.U256))
    (q : Evm.Address × Evm.U256) (h : ¬ (l.any (fun (p, _) => p = q)) = true) :
    l.find? (fun (p, _) => p = q) = none := by
  rw [List.find?_eq_none]; intro x hx hq
  exact h (List.any_eq_true.mpr ⟨x, hx, hq⟩)

/-- Caching a slot's tx-start value (`cacheOriginal`) and touching no other slot keeps
    the cache honest. The shape of both SLOAD (caches the current value, which is the
    original by `OrigInv` when uncached) and SSTORE (caches the looked-up original,
    then writes the slot). -/
theorem origInv_cache (env env' : Environment) (a : Evm.Address) (k : Evm.U256)
    (h : OrigInv env)
    (hO : env'.originalState = env.originalState)
    (hC : env'.storageOriginals =
      (cacheOriginal env a k (env.originalState.getStorage a k)).storageOriginals)
    (hS : ∀ x j, (x, j) ≠ (a, k) → env'.state.getStorage x j = env.state.getStorage x j) :
    OrigInv env' := by
  intro x j
  have hx := h x j
  unfold cachedOriginal at hx ⊢
  rw [hC, hO]
  unfold cacheOriginal
  by_cases hany : (env.storageOriginals.any (fun (p, _) => p = (a, k))) = true
  · rw [ite_eq_left hany]
    by_cases hq : (x, j) = (a, k)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      obtain ⟨y, hy, hyq⟩ := List.any_eq_true.mp hany
      have : (env.storageOriginals.find? (fun (p, _) => p = (x, j))).isSome := by
        rw [List.find?_isSome]; exact ⟨y, hy, hyq⟩
      revert hx; split
      · intro hx; exact hx
      · rename_i hn; rw [hn] at this; simp at this
    · revert hx; split
      · intro hx; exact hx
      · intro hx; rw [hS x j hq]; exact hx
  · rw [ite_eq_right hany]
    dsimp only
    rw [List.find?_append]
    have hn := find_none_of_any_false _ _ hany
    by_cases hq : (x, j) = (a, k)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      rw [hn]; simp
    · have hn2 : [((a, k), env.originalState.getStorage a k)].find?
          (fun (p, _) => p = (x, j)) = none := by
        simp only [List.find?_cons, List.find?_nil]
        rw [show (decide ((a, k) = (x, j))) = false from decide_eq_false (Ne.symm hq)]
      revert hx; split
      · rename_i v hv; rw [hv]; intro hx; exact hx
      · rename_i hv; rw [hv, hn2]; intro hx; simp only [Option.none_or]; rw [hS x j hq]; exact hx

/-- The cache is honest at tx start: empty, and the world's storage is the tx-start
    world's (`Tx.env0`: `storageOriginals := []`; the charge touches only accounts). -/
theorem env0_origInv (k : Nat) (benv : Environment) (st : Evm.Frontier.State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    OrigInv (Evm.Frontier.Vm.Tx.env0 k benv st sender tx) := by
  intro a j; rfl

/-- `warmSlot` as a record update. -/
theorem warmSlot_fst (e : Environment) (a : Evm.Address) (k : Evm.U256) :
    (warmSlot e a k).1 = { e with accessedStorageKeys :=
      if e.accessedStorageKeys.contains (a, k) then e.accessedStorageKeys
      else e.accessedStorageKeys ++ [(a, k)] } := by
  unfold warmSlot; split <;> simp_all

/-- `cacheOriginal` as a record update (only the cache moves). -/
theorem cacheOriginal_eq (e : Environment) (a : Evm.Address) (k v : Evm.U256) :
    cacheOriginal e a k v =
      { e with storageOriginals := (cacheOriginal e a k v).storageOriginals } := by
  unfold cacheOriginal; split <;> rfl

/-- For an honest cache, caching the current value is caching the original. -/
theorem cacheOriginal_current (e : Environment) (a : Evm.Address) (k : Evm.U256)
    (hO : OrigInv e) :
    (cacheOriginal e a k (e.state.getStorage a k)).storageOriginals =
      (cacheOriginal e a k (e.originalState.getStorage a k)).storageOriginals := by
  have hcur := hO a k
  unfold cacheOriginal
  by_cases hany : (e.storageOriginals.any (fun (p, _) => p = (a, k))) = true
  · rw [ite_eq_left hany, ite_eq_left hany]
  · rw [ite_eq_right hany, ite_eq_right hany]
    unfold cachedOriginal at hcur
    rw [find_none_of_any_false _ _ hany] at hcur
    simp only at hcur
    simp only [hcur]

/-! ## EIP-2929 SSTORE / SLOAD refinement -/

/-- 0x54 SLOAD at Berlin refines `IsSloadStep`: cold 2100 / warm 100, the slot warmed,
    the current value pushed, and the original-value cache kept honest. EELS
    `forks/berlin/vm/instructions/storage.py::sload` 34-50. Precondition `OrigInv`
    (the cache honest before the step; `env0_origInv` at tx start). -/
theorem sload_sound (evm evm' : Evm) (hO : OrigInv evm.env) :
    Evm.Berlin.Vm.Effect.doSloadPure evm = .ok evm' →
    IsSloadStep evm evm' := by
  intro h
  unfold Evm.Berlin.Vm.Effect.doSloadPure at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨key, rest⟩, hp, g, hg, s', hpush, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨key, rest, hStack, hlt, ?_⟩
  rw [cacheOriginal_eq, warmSlot_fst]
  simp only [Evm.Berlin.Vm.Effect.isSlotWarm, Evm.Berlin.Vm.Gas.coldSload,
    Evm.Berlin.Vm.Gas.warmAccess, coldSloadCost, coldStorageCost, warmAccessCost] at hle ⊢
  refine ⟨hle, ?_, ?_⟩
  · refine origInv_cache evm.env _ evm.message.currentTarget key hO rfl ?_ ?_
    · simp only
      rw [show (cacheOriginal { evm.env with accessedStorageKeys := _ }
            evm.message.currentTarget key (evm.env.state.getStorage evm.message.currentTarget key)).storageOriginals
          = (cacheOriginal evm.env evm.message.currentTarget key
            (evm.env.state.getStorage evm.message.currentTarget key)).storageOriginals from by
        unfold cacheOriginal; split <;> split <;> simp_all]
      exact cacheOriginal_current _ _ _ hO
    · intro x j _; rfl
  · by_cases hc : evm.env.accessedStorageKeys.contains (evm.message.currentTarget, key) = true
    · simp only [hc, ite_true, not_true_eq_false, ite_false]
    · simp only [hc, ite_false, Bool.false_eq_true, not_false_eq_true, ite_true]

set_option maxHeartbeats 1000000 in
/-- The EIP-2929 SSTORE cost/refund table, case by case: the implementation's
    `Storage.sstoreGas` (add, then subtract floored at 0) is the relation's
    `(cold + main, R + delta)` once the cancel branch is covered
    (`o ≠ 0 → c = 0 → 15000 ≤ R`). -/
theorem sstoreGas_eq (R : Nat) (cold : Bool) (o c v : Evm.U256)
    (hR : o ≠ 0 → c = 0 → 15000 ≤ R) :
    Evm.Berlin.Vm.Instructions.Storage.sstoreGas R cold o c v =
      ((if cold then 2100 else 0) +
        (if o = c ∧ c ≠ v then (if o = (0 : Evm.U256) then 20000 else 2900) else 100),
       ((R : Int) +
         (if c ≠ v then
            (if o ≠ (0 : Evm.U256) ∧ c ≠ (0 : Evm.U256) ∧ v = (0 : Evm.U256) then (15000 : Int)
             else 0) +
            (if o ≠ (0 : Evm.U256) ∧ c = (0 : Evm.U256) then -(15000 : Int) else 0) +
            (if o = v then (if o = (0 : Evm.U256) then (19900 : Int) else (2800 : Int)) else 0)
          else 0)).toNat) ∧
    0 ≤ (R : Int) +
         (if c ≠ v then
            (if o ≠ (0 : Evm.U256) ∧ c ≠ (0 : Evm.U256) ∧ v = (0 : Evm.U256) then (15000 : Int)
             else 0) +
            (if o ≠ (0 : Evm.U256) ∧ c = (0 : Evm.U256) then -(15000 : Int) else 0) +
            (if o = v then (if o = (0 : Evm.U256) then (19900 : Int) else (2800 : Int)) else 0)
          else 0) := by
  unfold Evm.Berlin.Vm.Instructions.Storage.sstoreGas Evm.Berlin.Vm.Instructions.Storage.cost
    Evm.Berlin.Vm.Instructions.Storage.eip2200
  simp only [Evm.Berlin.Vm.Instructions.Storage.sstoreSet,
    Evm.Berlin.Vm.Instructions.Storage.sstoreReset,
    Evm.Berlin.Vm.Instructions.Storage.sstoreClearsRefund,
    Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldSload,
    Evm.Berlin.Vm.Gas.sstoreColdSurcharge, Nat.reduceSub]
  by_cases hcv : c = v
  · subst hcv
    cases cold <;> split_ifs <;> (try dsimp only at *) <;> (try simp only [Prod.mk.injEq, true_and]) <;>
      first | omega | (exfalso; tauto) | (subst_vars; first | omega | (exfalso; tauto) | (exfalso; simp_all))
  · by_cases hoc0 : o ≠ 0 ∧ c = 0
    · have hR15 : 15000 ≤ R := hR hoc0.1 hoc0.2
      obtain ⟨ho, rfl⟩ := hoc0
      clear hR
      cases cold <;> split_ifs <;> (try dsimp only at *) <;> (try simp only [Prod.mk.injEq, true_and]) <;>
        first | omega | (exfalso; tauto) | (subst_vars; first | omega | (exfalso; tauto) | (exfalso; simp_all))
    · clear hR
      cases cold <;> split_ifs <;> (try dsimp only at *) <;> (try simp only [Prod.mk.injEq, true_and]) <;>
        first | omega | (exfalso; tauto) | (subst_vars; first | omega | (exfalso; tauto) | (exfalso; simp_all))

/-- 0x55 SSTORE at Berlin refines `IsSstoreStep`: static check, the EIP-2200 sentry,
    the EIP-2929 cold surcharge, the EIP-2200 cost branch at the Berlin prices, the
    three refund deltas as EELS's integer sum, the write, the slot warmed, the cache
    kept honest. EELS `forks/berlin/vm/instructions/storage.py::sstore` 53-128.

    Preconditions, both tx-level invariants this step preserves:
    `RefundInv 15000` (`sstoreStep_refundInv`; it makes the implementation's floored
    subtraction EELS's integer one) and `OrigInv` (the cache is the tx-start world, so
    the implementation's `getOriginal` is EELS's `get_storage_original`). -/
theorem sstore_sound (evm evm' : Evm)
    (hInv : Evm.Constantinople.Spec.RefundInv 15000 evm.env.originalState evm.env.state
      evm.env.refundCounter)
    (hO : OrigInv evm.env) :
    Evm.Berlin.Vm.Effect.doSstorePure evm = .ok evm' →
    IsSstoreStep evm evm' := by
  intro h
  unfold Evm.Berlin.Vm.Effect.doSstorePure at h
  by_cases hs : evm.message.isStatic = true
  · simp [hs, bind, Except.bind] at h
  have hs' : evm.message.isStatic = false := by simpa using hs
  simp only [hs', Bool.false_eq_true, ite_false, bind,
    Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨key, value, rest⟩, hp, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
  by_cases ht : evm.gasLeft ≤ Gas.callStipend
  · simp [ht, Except.bind] at h
  simp only [ht, ite_false] at h
  have horig : getOriginal evm.env evm.message.currentTarget key
      (evm.env.state.getStorage evm.message.currentTarget key)
      = evm.env.originalState.getStorage evm.message.currentTarget key := hO _ _
  have hR : evm.env.originalState.getStorage evm.message.currentTarget key ≠ 0 →
      evm.env.state.getStorage evm.message.currentTarget key = 0 →
      15000 ≤ evm.env.refundCounter :=
    fun ho hc => Evm.Constantinople.Spec.refundInv_slot hInv _ _ ho hc
  rw [horig, cacheOriginal_eq, warmSlot_fst] at h
  simp only [isSlotWarm] at h
  rw [(sstoreGas_eq evm.env.refundCounter _
    (evm.env.originalState.getStorage evm.message.currentTarget key)
    (evm.env.state.getStorage evm.message.currentTarget key) value hR).1] at h
  have hnn := (sstoreGas_eq evm.env.refundCounter false
    (evm.env.originalState.getStorage evm.message.currentTarget key)
    (evm.env.state.getStorage evm.message.currentTarget key) value hR).2
  simp only [Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, h⟩
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨key, value, rest, hStack, Nat.lt_of_not_le ht, by simp [hs'], ?_⟩
  simp only [coldSloadCost, coldStorageCost, warmAccessCost, sstoreSet, sstoreReset,
    sstoreClearRefund, Nat.reduceSub] at hle ⊢
  refine ⟨?_, hnn, ?_, ?_⟩
  · by_cases hc : evm.env.accessedStorageKeys.contains (evm.message.currentTarget, key) = true
      <;> simp only [hc] at hle ⊢ <;> simpa using hle
  · refine origInv_cache evm.env _ evm.message.currentTarget key hO rfl ?_ ?_
    · rfl
    · intro x j hq
      simp only
      rw [Evm.Frontier.State.getStorage_setStorage, ite_eq_right hq]
  · by_cases hc : evm.env.accessedStorageKeys.contains (evm.message.currentTarget, key) = true
    · simp only [hc, ite_true, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rfl
    · simp only [hc, Bool.false_eq_true, not_false_eq_true, decide_true, ite_true, ite_false]
      rfl

/-- The Berlin SSTORE step keeps the refund invariant (`refundInv_setStorage`). -/
theorem sstoreStep_refundInv (evm evm' : Evm) (h : IsSstoreStep evm evm')
    (hInv : Evm.Constantinople.Spec.RefundInv 15000 evm.env.originalState evm.env.state
      evm.env.refundCounter) :
    Evm.Constantinople.Spec.RefundInv 15000 evm'.env.originalState evm'.env.state
      evm'.env.refundCounter := by
  obtain ⟨key, value, rest, _, _, _, _, hnn, _, hE⟩ := h
  rw [hE]
  simp only at hnn ⊢
  apply Evm.Constantinople.Spec.refundInv_setStorage hInv
  generalize evm.env.originalState.getStorage evm.message.currentTarget key = o at hnn ⊢
  generalize evm.env.state.getStorage evm.message.currentTarget key = c at hnn ⊢
  generalize evm.env.refundCounter = R at hnn ⊢
  simp only [sstoreSet, sstoreReset, sstoreClearRefund, coldSloadCost, coldStorageCost,
    warmAccessCost, Nat.reduceSub] at hnn ⊢
  by_cases hcv : c = value
  · subst hcv; split_ifs at hnn ⊢ <;> first | omega | (exfalso; tauto)
  · rcases eq_or_ne o 0 with rfl | ho <;> rcases eq_or_ne c 0 with rfl | hc <;>
      rcases eq_or_ne value 0 with rfl | hv <;> split_ifs at hnn ⊢ <;>
      first | omega | (exfalso; tauto) | (subst_vars; first | omega | (exfalso; tauto))

/-! EIP-2718's envelope (`IsBerlinTxEncoding`) was a parse-validity predicate with no
    Lean decoder to refine (transactions are decoded by the host); deleted 2026-11-09
    rather than kept as a `P → P` placeholder. -/

/-! ## Notes

    - The pre-Berlin `Frontier.Spec.IsSloadStep` / `IsSstoreStep`
      relations are *replaced* at Berlin (not extended) — pre-Berlin
      Refinement.lean files no longer apply to 0x54 / 0x55 at this
      fork.

    - `AccessList.lean` exposes two `*_monotonic` and one
      `wasCold_unique` lemmas (the third is fully proven there);
      those don't need to be restated here.

    - The CALL family (EIP-2929 access, warm-ups) is `Evm.Frontier.Vm.Call`, proved
      against the derived cb-call in `Evm.CL.EffectCallProof`. -/

end Evm.Berlin.Spec.Refinement
