/-
  Evm.Istanbul.Spec.Refinement — proofs that the Istanbul Effect
  interpreter refines the Istanbul Spec relations.

  Istanbul adds:

    * `Blake2fStep.lean` — EIP-152 BLAKE2F precompile (0x09).
    * `ChainidStep.lean` — EIP-1344 CHAINID (0x46).
    * `GasConstants.lean` — EIP-1884 SLOAD/BALANCE/EXTCODEHASH reprice.
    * `SelfbalanceStep.lean` — EIP-1884 SELFBALANCE (0x47).
    * `SstoreStep.lean` — EIP-2200 net SSTORE.

  CHAINID and SELFBALANCE are nullary-push opcodes; refinement is a
  one-liner via `Frontier.Spec.Refinement.nullaryPush_sound`. SSTORE
  is the heavy state-touching opcode (`sorry`-deferred). Blake2f
  is a precompile whose body is `opaque` in the spec; the gas / size
  obligations are statable but the cryptographic output is axiomatic.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Istanbul.Spec.Blake2fStep
import Evm.Istanbul.Spec.ChainidStep
import Evm.Istanbul.Spec.GasConstants
import Evm.Istanbul.Spec.SelfbalanceStep
import Evm.Istanbul.Spec.SstoreStep
import Evm.Istanbul.Vm.Instructions.Block
import Evm.Istanbul.Vm.Instructions.Environment
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Effect
import Evm.Constantinople.Spec.RefundInv
import Mathlib.Tactic.SplitIfs

namespace Evm.Istanbul.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Istanbul.Spec

/-! ## EIP-1344 CHAINID (0x46) -/

/-- CHAINID is a NullaryPushStep over `env.chainId`. One-line proof
    via the `nullaryPush_sound` shape lemma in
    `Frontier/Spec/Refinement.lean`. -/
theorem chainid_sound (evm evm' : Evm) :
    Evm.Istanbul.Vm.Instructions.chainid evm = .ok evm' →
    IsChainidStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => e.env.chainId) evm evm' h

/-! ## EIP-1884 SELFBALANCE (0x47) -/

/-- SELFBALANCE is a NullaryPushStep over `state.getBalance
    currentTarget`. State-reading but no mutation; refinement
    reduces to the same shape lemma as CHAINID. -/
theorem selfbalance_sound (evm evm' : Evm) :
    Evm.Istanbul.Vm.Instructions.selfbalance evm = .ok evm' →
    IsSelfbalanceStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => e.env.state.getBalance e.message.currentTarget)
    evm evm' h

/-! ## EIP-2200 SSTORE (0x55) — net-metering, EIP-1706 trip-wire -/

/-- The EIP-2200 table, case by case: the implementation's `sstoreGas` (each
    refund delta clamped in turn) is the relation's `(cost, R + delta)` once the
    cancel branch is covered (`o ≠ 0 → c = 0 → 15000 ≤ R`); then no clamp fires.
    Without that bound the two differ (refund 0, o ≠ 0, c = 0, new = o:
    implementation 4200, EELS −10800). -/
theorem sstoreGas_eq (R : Nat) (o c v : Evm.U256)
    (hR : o ≠ 0 → c = 0 → 15000 ≤ R) :
    Evm.Istanbul.Vm.Instructions.sstoreGas R o c v =
      ((if o = c ∧ c ≠ v then
          (if o = (0 : Evm.U256) then Evm.Istanbul.Vm.Gas.sstoreSet
           else Evm.Istanbul.Vm.Gas.sstoreReset)
        else Evm.Istanbul.Vm.Gas.sLoad),
       ((R : Int) +
         (if c = v then 0
          else
            (if o ≠ (0 : Evm.U256) ∧ c ≠ (0 : Evm.U256) ∧ v = (0 : Evm.U256) then
               (Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int) else 0) +
            (if o ≠ (0 : Evm.U256) ∧ c = (0 : Evm.U256) then
               -(Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int) else 0) +
            (if o = v then
               (if o = (0 : Evm.U256) then
                  ((Evm.Istanbul.Vm.Gas.sstoreSet - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
                else
                  ((Evm.Istanbul.Vm.Gas.sstoreReset - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int))
             else 0))).toNat) ∧
    0 ≤ (R : Int) +
         (if c = v then 0
          else
            (if o ≠ (0 : Evm.U256) ∧ c ≠ (0 : Evm.U256) ∧ v = (0 : Evm.U256) then
               (Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int) else 0) +
            (if o ≠ (0 : Evm.U256) ∧ c = (0 : Evm.U256) then
               -(Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int) else 0) +
            (if o = v then
               (if o = (0 : Evm.U256) then
                  ((Evm.Istanbul.Vm.Gas.sstoreSet - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
                else
                  ((Evm.Istanbul.Vm.Gas.sstoreReset - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int))
             else 0)) := by
  have hadj : ∀ (n : Nat) (d : Int),
      Evm.Istanbul.Vm.Instructions.adjustRefund n d = ((n : Int) + d).toNat := by
    intro n d; unfold Evm.Istanbul.Vm.Instructions.adjustRefund
    by_cases hd : d ≥ 0
    · rw [ite_eq_left hd]; omega
    · rw [ite_eq_right hd]; dsimp only; split <;> omega
  unfold Evm.Istanbul.Vm.Instructions.sstoreGas
  simp only [hadj, Evm.Istanbul.Vm.Gas.sstoreSet, Evm.Istanbul.Vm.Gas.sstoreReset,
    Evm.Istanbul.Vm.Gas.sLoad, Evm.Istanbul.Vm.Gas.sstoreClearRefund]
  by_cases hoc0 : o ≠ 0 ∧ c = 0
  · have hR15 : 15000 ≤ R := hR hoc0.1 hoc0.2
    obtain ⟨ho, rfl⟩ := hoc0
    clear hR
    split_ifs <;> (try simp only [Prod.mk.injEq, true_and]) <;>
      first | omega | (exfalso; tauto)
  · clear hR
    split_ifs <;> (try simp only [Prod.mk.injEq, true_and]) <;>
      first | omega | (exfalso; tauto)

/-- 0x55 SSTORE under EIP-2200 refines `IsSstoreStep`: EIP-1706 trip-wire
    (`gas_left ≤ 2300` raises), the cost branch, the three refund deltas as one
    integer sum, the static check, the write. EELS `forks/istanbul/vm/instructions/
    storage.py::sstore` 53-112.

    Precondition: the tx-level refund invariant `RefundInv` (one 15000 credit per
    slot non-zero at tx start and zero now; `env0_refundInv` at tx start,
    `sstoreStep_refundInv` across this step). It is what makes the
    implementation's clamp-each-delta counter equal EELS's integer one. -/
theorem sstore_sound (evm evm' : Evm)
    (hInv : Evm.Constantinople.Spec.RefundInv 15000 evm.env.originalState evm.env.state
      evm.env.refundCounter) :
    Evm.Istanbul.Vm.Instructions.sstore evm = .ok evm' →
    IsSstoreStep evm evm' := by
  intro h
  unfold Evm.Istanbul.Vm.Instructions.sstore at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨key, value, rest⟩, hp, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
  by_cases ht : evm.gasLeft ≤ Evm.Istanbul.Vm.Gas.sstoreSentryGas
  · simp [ht, Except.bind] at h
  · simp only [ht, ite_false] at h
    have hR : evm.env.originalState.getStorage evm.message.currentTarget key ≠ 0 →
        evm.env.state.getStorage evm.message.currentTarget key = 0 →
        15000 ≤ evm.env.refundCounter :=
      fun ho hc => Evm.Constantinople.Spec.refundInv_slot hInv _ _ ho hc
    obtain ⟨hgas, hnn⟩ := sstoreGas_eq evm.env.refundCounter
      (evm.env.originalState.getStorage evm.message.currentTarget key)
      (evm.env.state.getStorage evm.message.currentTarget key) value hR
    rw [hgas] at h
    simp only [Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    rcases h with ⟨g, hg, h⟩
    obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
    by_cases hs : evm.message.isStatic = true
    · simp [hs, Except.bind] at h
    · have hs' : evm.message.isStatic = false := by simpa using hs
      simp only [hs', Bool.false_eq_true, ite_false, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      exact ⟨key, value, rest, hStack, hs', Nat.lt_of_not_le ht, hle, hnn, rfl⟩

/-- The EIP-2200 step keeps the refund invariant (`refundInv_setStorage`): every
    branch pays 15000 for a newly cleared slot and takes at most 15000 back for an
    un-cleared one. -/
theorem sstoreStep_refundInv (evm evm' : Evm) (h : IsSstoreStep evm evm')
    (hInv : Evm.Constantinople.Spec.RefundInv 15000 evm.env.originalState evm.env.state
      evm.env.refundCounter) :
    Evm.Constantinople.Spec.RefundInv 15000 evm'.env.originalState evm'.env.state
      evm'.env.refundCounter := by
  obtain ⟨key, value, rest, _, _, _, _, hnn, rfl⟩ := h
  simp only at hnn ⊢
  apply Evm.Constantinople.Spec.refundInv_setStorage hInv
  generalize evm.env.originalState.getStorage evm.message.currentTarget key = o at hnn ⊢
  generalize evm.env.state.getStorage evm.message.currentTarget key = c at hnn ⊢
  generalize evm.env.refundCounter = R at hnn ⊢
  simp only [Evm.Istanbul.Vm.Gas.sstoreSet, Evm.Istanbul.Vm.Gas.sstoreReset,
    Evm.Istanbul.Vm.Gas.sLoad, Evm.Istanbul.Vm.Gas.sstoreClearRefund] at hnn ⊢
  by_cases hcv : c = value
  · subst hcv; split_ifs at hnn ⊢ <;> first | omega | (exfalso; tauto)
  · split_ifs at hnn ⊢ <;> first | omega | (exfalso; tauto) | (exfalso; simp_all)

/-! ## EIP-152 BLAKE2F precompile (0x09)

    Not a step opcode but a precompile invoked via the trampoline.
    The spec relation `IsBlake2fStep` is `(input, gas, output, gas')`
    -shaped; the impl's `Blake2f` precompile stub returns 64 zero
    bytes pending FFI. Soundness of the gas / size checks is
    statable now; the cryptographic output identity awaits the
    `blake2bCompress` binding. -/

/-- BLAKE2F (0x09): the spec's `IsBlake2fStep` uses an opaque
    `blake2bCompress` for the output; the impl stub returns zeros.
    State the relation; defer the cryptographic equality. -/
theorem blake2f_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasLeft : Nat) :
    IsBlake2fStep input gas output gasLeft →
    IsBlake2fStep input gas output gasLeft := by
  -- The spec relation is its own statement; refinement against the
  -- impl precompile requires plumbing `Evm.Istanbul.Vm.Precompiled
  -- Contracts.blake2f` through a `(input, gas) → Except Exception
  -- (output, gas')` form.
  intro h; exact h

/-! ## Notes

    - GasConstants.lean defines named constants only; nothing to
      refine here beyond the (already trivial) definitional equality
      with `Evm.Istanbul.Vm.Gas`. No theorem needed.

    - CHAINID / SELFBALANCE now collapse to one-liners via
      `nullaryPush_sound`, analogous to `runBinary_sound` for
      arithmetic ops. -/

end Evm.Istanbul.Spec.Refinement
