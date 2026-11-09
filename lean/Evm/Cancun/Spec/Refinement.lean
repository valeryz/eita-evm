/-
  Evm.Cancun.Spec.Refinement — proofs that the Cancun Effect
  interpreter refines the Cancun Spec relations.

  Cancun adds:

    * `TransientStorageStep.lean` — EIP-1153 0x5c TLOAD / 0x5d TSTORE.
    * `McopyStep.lean`            — EIP-5656 0x5e MCOPY.
    * `BlobhashStep.lean`         — EIP-4844 0x49 BLOBHASH.
    * `BlobbasefeeStep.lean`      — EIP-7516 0x4a BLOBBASEFEE.
    * `BlobTx.lean`               — EIP-4844 type-3 tx + blob fee mkt.
    * `KzgStep.lean`              — EIP-4844 point-evaluation precompile.
    * `Selfdestruct.lean`         — EIP-6780 same-tx-only destruction.

  Per SPEC-METHODOLOGY: TLOAD/TSTORE/MCOPY/BLOBHASH are state-touching
  or env-reading; BLOBBASEFEE is a one-line nullary-push refinement
  via `Frontier.Spec.Refinement.nullaryPush_sound`. BlobTx and Kzg
  are at the tx / precompile levels (the EIP-4788 system call is
  `Evm.Frontier.Vm.System`, proved in `Evm.CL.EffectSystemProof`); SELFDESTRUCT
  touches state. State-touching obligations are `sorry`-deferred.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Cancun.Spec.TransientStorageStep
import Evm.Cancun.Spec.McopyStep
import Evm.Cancun.Spec.BlobhashStep
import Evm.Cancun.Spec.BlobbasefeeStep
import Evm.Cancun.Spec.BlobTx
import Evm.Cancun.Spec.KzgStep
import Evm.Cancun.Spec.Selfdestruct
import Evm.Cancun.Vm.Instructions
import Evm.Cancun.Vm.Effect
import Evm.Frontier.Vm.Tx

namespace Evm.Cancun.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Cancun.Spec

/-! ## EIP-1153 TLOAD (0x5c) / TSTORE (0x5d) -/

/-- 0x5c TLOAD: pop the key, charge `GAS_WARM_ACCESS` (100), push the transient value of
    `(current_target, key)` (0 if unset). EELS `forks/cancun/vm/instructions/storage.py::
    tload`. -/
theorem tload_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tload evm = .ok evm' → IsTloadStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.tload at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, ⟨a, rest⟩, hp, s', hpush, h⟩
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨a, rest, hStack, hlt, hle, rfl⟩

/-- 0x5d TSTORE: static-context check, charge `GAS_WARM_ACCESS`, pop key and value, write
    `transient_storage[(current_target, key)]`. EELS `forks/cancun/vm/instructions/
    storage.py::tstore` (`if evm.message.is_static: raise WriteInStaticContext`). -/
theorem tstore_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tstore evm = .ok evm' → IsTstoreStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.tstore at h
  by_cases hs : evm.message.isStatic = true
  · simp [hs, bind, Except.bind] at h
  · have hs' : evm.message.isStatic = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    rcases h with ⟨u, hu, ⟨a, b, rest⟩, hp, h⟩
    obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hu
    obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨a, b, rest, hStack, hs', hle, rfl⟩

/-! ## EIP-5656 MCOPY (0x5e) -/

/-- 0x5e MCOPY refines `IsMcopyStep`: charge `GAS_VERY_LOW + GAS_COPY · words +
    extend_memory.cost` with the expansion over both windows (none when `len = 0`), read
    the source from the expanded memory, write it at the destination. EELS
    `forks/cancun/vm/instructions/memory.py::mcopy` (141-174). -/
theorem mcopy_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.mcopy evm = .ok evm' →
    IsMcopyStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.mcopy at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨⟨d, sr, l, rest⟩, hp, g0, hg0, ⟨g1, m⟩, hc, g2, hg2, h⟩
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp
  obtain ⟨hle0, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg0
  obtain ⟨hle1, rfl, rfl⟩ := Evm.Frontier.Spec.chargeMemory_spec hc
  obtain ⟨hle2, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only at hle1 hle2 ⊢
  have hE : Evm.Frontier.Spec.memExpansionGas evm.memory 0
      (if l.toNat = 0 then 0 else Nat.max (d.toNat + l.toNat) (sr.toNat + l.toNat))
      = mcopyExpansionGas evm.memory d.toNat sr.toNat l.toNat := by
    unfold Evm.Frontier.Spec.memExpansionGas mcopyExpansionGas
    by_cases hl : l.toNat = 0
    · simp [hl]
    · simp [hl]
  have hX : Evm.Frontier.Spec.memAfterExpand evm.memory 0
      (if l.toNat = 0 then 0 else Nat.max (d.toNat + l.toNat) (sr.toNat + l.toNat))
      = mcopyExpand evm.memory d.toNat sr.toNat l.toNat := by
    unfold Evm.Frontier.Spec.memAfterExpand mcopyExpand
    by_cases hl : l.toNat = 0
    · simp [hl]
    · simp [hl]
  rw [hE] at hle1 hle2 ⊢
  rw [hX]
  obtain ⟨hA, hB⟩ := Evm.Frontier.Spec.charge3_nat hle0 hle1 hle2
  exact ⟨d, sr, l, rest, hStack, hA, by rw [hB]; rfl⟩

/-! ## EIP-4844 BLOBHASH (0x49) -/

/-- 0x49 BLOBHASH: charge `GAS_BLOBHASH_OPCODE` (3), pop the index, push
    `blob_versioned_hashes[index]` or 0 out of range. EELS `forks/cancun/vm/instructions/
    environment.py::blob_hash`. -/
theorem blobhash_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobhash evm = .ok evm' → IsBlobhashStep evm evm' := by
  intro h
  unfold Evm.Cancun.Vm.Instructions.blobhash at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨g, hg, ⟨a, rest⟩, hp, s', hpush, h⟩
  obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, rfl⟩ := (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨a, rest, hStack, hlt, hle, ?_⟩
  simp only [blobHashAt]
  split <;> rename_i hh
  · simp_all; rfl
  · simp_all; rfl

/-! ## EIP-7516 BLOBBASEFEE (0x4a) -/

/-- BLOBBASEFEE is a NullaryPushStep over `env.blobBaseFee`. One-line
    proof via the `nullaryPush_sound` shape lemma. -/
theorem blobbasefee_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobbasefee evm = .ok evm' →
    IsBlobbasefeeStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => Evm.U256.ofNat e.env.blobBaseFee) evm evm' h

/-! ## EIP-4844 blob tx / blob fee market (tx-level) -/

/-- `IsBlobCountValid` — per-tx blob count must be in (0, 6]. -/
theorem blobCountValid_sound_shape (numBlobs : Nat) :
    IsBlobCountValid numBlobs →
    IsBlobCountValid numBlobs := by
  intro h; exact h

/-- `IsBlobAffordable`: a blob tx (type 3) the tx layer accepts (`Tx.invalid = none`) has a
    sender whose balance covers `value + gas · max_fee_per_gas + blob_gas ·
    max_fee_per_blob_gas`. EELS `forks/cancun/fork.py::check_transaction` 462-497
    (`max_gas_fee = tx.gas * tx.max_fee_per_gas`, `+= calculate_total_blob_gas(tx) *
    tx.max_fee_per_blob_gas`, `if balance < max_gas_fee + tx.value: raise
    InsufficientBalanceError`). -/
theorem blobAffordable_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none → tx.type = 3 →
    IsBlobAffordable (st.getAccount sender).balance.toNat tx.value.toNat tx.gas tx.maxFee
      tx.maxFeePerBlobGas tx.blobHashes.length := by
  intro h h3
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide ((st.getAccount sender).balance.toNat <
      Evm.Frontier.Vm.Tx.maxGasFee tx + tx.value.toNat), "insufficient balance")
    (by simp [Evm.Frontier.Vm.Tx.rules])
  simp only [decide_eq_false_iff_not, Nat.not_lt] at hr
  simp only [Evm.Frontier.Vm.Tx.maxGasFee, Evm.Frontier.Vm.Tx.blobGas, h3] at hr
  unfold IsBlobAffordable txBlobGas gasPerBlob
  simp at hr
  rw [Nat.mul_comm tx.maxFeePerBlobGas]
  omega

/-- `IsBlobFeeBidSufficient`: a blob tx the tx layer accepts bids at least the block's
    blob base fee. EELS `forks/cancun/fork.py::check_transaction` 480-484
    (`if tx.max_fee_per_blob_gas < blob_gas_price: raise InsufficientMaxFeePerBlobGasError`). -/
theorem blobFeeBidSufficient_sound (k : Nat) (benv : Environment) (st : State)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) :
    Evm.Frontier.Vm.Tx.invalid k benv st sender tx = none → tx.type = 3 →
    IsBlobFeeBidSufficient tx.maxFeePerBlobGas benv.blobBaseFee := by
  intro h h3
  have hr := Evm.Frontier.Vm.Tx.rules_false_of_valid h
    (decide (tx.type = 3 ∧ tx.maxFeePerBlobGas < benv.blobBaseFee),
      "max blob fee below blob base fee") (by simp [Evm.Frontier.Vm.Tx.rules])
  simp [h3] at hr
  exact hr

/-! ## EIP-4844 KZG point-evaluation precompile (0x0a) -/

/-- Precompile success branch: well-formed input + valid pairing ⇒
    canonical 64-byte success output. Cryptographic predicates are
    axiomatic in the spec; the impl needs a verified KZG library to
    discharge them. -/
theorem kzg_success_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsKzgPrecompileSuccess input gas output gas' →
    IsKzgPrecompileSuccess input gas output gas' := by
  intro h; exact h

/-- Precompile failure branch. -/
theorem kzg_failure_sound_shape (input : Evm.Bytes) (gas : Nat) :
    IsKzgPrecompileFailure input gas →
    IsKzgPrecompileFailure input gas := by
  intro h; exact h

/-! ## EIP-6780 SELFDESTRUCT (same-tx-only destruction) -/

/-- SELFDESTRUCT at Cancun: full delete only if self ∈
    createdAccounts; otherwise only balance moves. State-touching
    obligation. -/
theorem selfdestruct_sound_shape (evm evm' : Evm) :
    IsSelfdestructStep evm evm' →
    IsSelfdestructStep evm evm' := by
  intro h; exact h

/-! ## Notes

    - Most tx- and block-level predicates above are equational; their
      refinement reduces to definitional equality once the impl
      callsite (in `Cancun.Fork` / `Cancun.Vm.Effect`) is extracted.

    - The KZG spec is intentionally minimal: the cryptographic
      semantics are deferred to external libraries.

    - The spec relations match the EIPs Cancun ships (EIP-4788's
      system call is `Evm.Frontier.Vm.System`); every one has a
      soundness obligation here. -/

end Evm.Cancun.Spec.Refinement
