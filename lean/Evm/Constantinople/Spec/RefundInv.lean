/-
  Evm.Constantinople.Spec.RefundInv — the tx-level refund invariant that makes
  net-metered SSTORE's natural-number refund counter equal EELS's integer one.

  EELS keeps `evm.refund_counter` as a Python `int` and the net-metering SSTOREs
  (EIP-1283 at Constantinople, EIP-2200 at Istanbul, EIP-2929 at Berlin) SUBTRACT
  `REFUND_STORAGE_CLEAR` when a slot cleared earlier in the tx is written non-zero
  again (`forks/berlin/vm/instructions/storage.py::sstore` 101-103:
  `if original_value != 0 and current_value == 0: evm.refund_counter -=
  GasCosts.REFUND_STORAGE_CLEAR`). The subtraction never takes the tx total below
  zero because the slot was cleared by an earlier SSTORE of the same tx, which
  added that refund. Lean's counter is a `Nat`, so the implementations clamp; the
  clamp is invisible exactly when the invariant below holds.

  `RefundInv clear orig cur R`: the refund counter covers one `clear` credit for
  every slot that is non-zero in the tx-start world `orig` and zero in the current
  world `cur`:

      clear · |{ (a, k) : orig[a][k] ≠ 0 ∧ cur[a][k] = 0 }| ≤ R.

  It holds at tx start (`refundInv_init`: `cur = orig` up to reads, `R = 0`), its
  slot-local consequence is what each SSTORE refinement needs (`refundInv_slot`),
  and each fork's SSTORE relation preserves it (`sstoreStep_refundInv` in the fork's
  refinement file, via `refundInv_setStorage`). Steps that change neither storage
  nor `originalState` and do not lower the counter preserve it (`refundInv_mono`).
-/

import Evm.Frontier.State
import Evm.Frontier.Vm.Tx
import Mathlib.Data.Finset.Card

namespace Evm.Constantinople.Spec

open Evm.Frontier (State)

/-- The slots non-zero at tx start and zero now (keys drawn from `orig`'s storage
    list: a slot with `orig.getStorage ≠ 0` is necessarily one of its keys). -/
def clearedSlots (orig cur : State) : Finset (Evm.Address × Evm.U256) :=
  (orig.storage.map Prod.fst).toFinset.filter
    (fun p => orig.getStorage p.1 p.2 ≠ 0 ∧ cur.getStorage p.1 p.2 = 0)

/-- The tx-level refund invariant (module docstring). -/
def RefundInv (clear : Nat) (orig cur : State) (R : Nat) : Prop :=
  clear * (clearedSlots orig cur).card ≤ R

theorem mem_keys_of_getStorage_ne (s : State) (a : Evm.Address) (k : Evm.U256)
    (h : s.getStorage a k ≠ 0) : (a, k) ∈ (s.storage.map Prod.fst).toFinset := by
  unfold State.getStorage at h
  split at h
  · rename_i p v hp
    have hm := List.mem_of_find?_eq_some hp
    have he := List.find?_some hp
    simp only [decide_eq_true_eq] at he
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨_, hm, he⟩
  · exact absurd rfl h

/-- Slot-local consequence: a slot non-zero at tx start and zero now is covered. -/
theorem refundInv_slot {clear : Nat} {orig cur : State} {R : Nat} (h : RefundInv clear orig cur R)
    (a : Evm.Address) (k : Evm.U256) (ho : orig.getStorage a k ≠ 0) (hc : cur.getStorage a k = 0) :
    clear ≤ R := by
  have hm : (a, k) ∈ clearedSlots orig cur := by
    unfold clearedSlots
    rw [Finset.mem_filter]
    exact ⟨mem_keys_of_getStorage_ne orig a k ho, ho, hc⟩
  have h1 : 1 ≤ (clearedSlots orig cur).card := Finset.card_pos.mpr ⟨_, hm⟩
  unfold RefundInv at h
  calc clear = clear * 1 := (Nat.mul_one _).symm
    _ ≤ clear * (clearedSlots orig cur).card := Nat.mul_le_mul_left _ h1
    _ ≤ R := h

/-- At tx start the current world reads as the original one and the counter is 0. -/
theorem refundInv_init (clear : Nat) (orig cur : State)
    (h : ∀ a k, cur.getStorage a k = orig.getStorage a k) : RefundInv clear orig cur 0 := by
  unfold RefundInv clearedSlots
  rw [Finset.filter_false_of_mem]
  · simp
  · intro p _ hp; exact hp.1 (by rw [← h]; exact hp.2)

/-- The invariant holds in the environment every transaction starts in: the tx charge
    (`Tx.charged`) touches only the sender's account, so the world's storage is the
    tx-start world's, and the counter starts at 0 (EELS `TransactionEnvironment`,
    `refund_counter = 0`). -/
theorem env0_refundInv (clear k : Nat) (benv : Evm.Frontier.Vm.Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    let e := Evm.Frontier.Vm.Tx.env0 k benv st sender tx
    RefundInv clear e.originalState e.state e.refundCounter :=
  refundInv_init clear _ _ (fun _ _ => rfl)

/-- Counting one slot apart: a filter's size is its size off the slot plus the slot's
    own indicator. -/
private theorem card_filter_split (S : Finset (Evm.Address × Evm.U256)) (q : Evm.Address × Evm.U256)
    (P : Evm.Address × Evm.U256 → Prop) [DecidablePred P] :
    (S.filter P).card = ((S.erase q).filter P).card + (if q ∈ S ∧ P q then 1 else 0) := by
  by_cases hq : q ∈ S
  · have hS : S = insert q (S.erase q) := (Finset.insert_erase hq).symm
    conv_lhs => rw [hS]
    by_cases hp : P q
    · rw [Finset.filter_insert, ite_eq_left hp, Finset.card_insert_of_notMem
        (by simp [Finset.mem_filter]), ite_eq_left ⟨hq, hp⟩]
    · rw [Finset.filter_insert, ite_eq_right hp, ite_eq_right (fun h => hp h.2), Nat.add_zero]
  · rw [Finset.erase_eq_of_notMem hq, ite_eq_right (fun h => hq h.1), Nat.add_zero]

/-- How one storage write moves the cleared-slot count: the written slot's indicator is
    replaced, every other slot keeps its own. -/
theorem card_clearedSlots_setStorage (orig cur : State) (a : Evm.Address) (k v : Evm.U256) :
    (clearedSlots orig (cur.setStorage a k v)).card
      + (if orig.getStorage a k ≠ 0 ∧ cur.getStorage a k = 0 then 1 else 0)
    = (clearedSlots orig cur).card
      + (if orig.getStorage a k ≠ 0 ∧ v = 0 then 1 else 0) := by
  unfold clearedSlots
  rw [card_filter_split _ (a, k), card_filter_split (S := (orig.storage.map Prod.fst).toFinset) (q := (a, k))]
  have hoff : ((orig.storage.map Prod.fst).toFinset.erase (a, k)).filter
        (fun p => orig.getStorage p.1 p.2 ≠ 0 ∧ (cur.setStorage a k v).getStorage p.1 p.2 = 0)
      = ((orig.storage.map Prod.fst).toFinset.erase (a, k)).filter
        (fun p => orig.getStorage p.1 p.2 ≠ 0 ∧ cur.getStorage p.1 p.2 = 0) := by
    apply Finset.filter_congr
    intro p hp
    have hne : (p.1, p.2) ≠ (a, k) := by simpa using (Finset.ne_of_mem_erase hp)
    rw [State.getStorage_setStorage, ite_eq_right hne]
  rw [hoff]
  have hset : (cur.setStorage a k v).getStorage a k = v := by
    rw [State.getStorage_setStorage, ite_eq_left rfl]
  simp only [hset]
  by_cases ho : orig.getStorage a k = 0
  · simp [ho]
  · have hm := mem_keys_of_getStorage_ne orig a k ho
    by_cases hc : cur.getStorage a k = 0 <;> by_cases hv : v = 0 <;> simp [hc, hv, hm] <;> omega

/-- Preservation by one storage write `cur[a][k] := v` whose refund move `R → R'`
    pays one `clear` for a newly cleared slot and takes at most one back for an
    un-cleared one (the shape every net-metered SSTORE has). -/
theorem refundInv_setStorage {clear : Nat} {orig cur : State} {R R' : Nat}
    (h : RefundInv clear orig cur R) (a : Evm.Address) (k v : Evm.U256)
    (hR : R + clear * (if orig.getStorage a k ≠ 0 ∧ v = 0 then 1 else 0)
          ≤ R' + clear * (if orig.getStorage a k ≠ 0 ∧ cur.getStorage a k = 0 then 1 else 0)) :
    RefundInv clear orig (cur.setStorage a k v) R' := by
  unfold RefundInv at *
  have hc := card_clearedSlots_setStorage orig cur a k v
  have : clear * ((clearedSlots orig (cur.setStorage a k v)).card
      + (if orig.getStorage a k ≠ 0 ∧ cur.getStorage a k = 0 then 1 else 0))
      = clear * ((clearedSlots orig cur).card
      + (if orig.getStorage a k ≠ 0 ∧ v = 0 then 1 else 0)) := by rw [hc]
  rw [Nat.mul_add, Nat.mul_add] at this
  omega

/-- Frame lemma: a step that leaves every storage read (current and original) alone and
    does not lower the counter preserves the invariant. -/
theorem refundInv_mono {clear : Nat} {orig cur cur' : State} {R R' : Nat}
    (h : RefundInv clear orig cur R) (hs : ∀ a k, cur'.getStorage a k = cur.getStorage a k)
    (hR : R ≤ R') : RefundInv clear orig cur' R' := by
  unfold RefundInv clearedSlots at *
  have : (orig.storage.map Prod.fst).toFinset.filter
        (fun p => orig.getStorage p.1 p.2 ≠ 0 ∧ cur'.getStorage p.1 p.2 = 0)
      = (orig.storage.map Prod.fst).toFinset.filter
        (fun p => orig.getStorage p.1 p.2 ≠ 0 ∧ cur.getStorage p.1 p.2 = 0) := by
    apply Finset.filter_congr; intro p _; rw [hs]
  rw [this]; omega

end Evm.Constantinople.Spec
