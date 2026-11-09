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

namespace Evm.Berlin.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Berlin.Spec

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

/-! ## EIP-2929 SSTORE / SLOAD refinement -/

/-- 0x54 SLOAD at Berlin: cold = 2100, warm = 100. State-reading +
    access-list update. The impl handler lives inline in
    `Berlin.Vm.Effect`'s dispatch (no stand-alone `Instructions.sload`
    in this fork's tree). -/
theorem sload_sound_shape (evm evm' : Evm) :
    IsSloadStep evm evm' →
    IsSloadStep evm evm' := by
  -- Needs `doSload` extracted; multi-step obligation including the
  -- access-list mutation.
  intro h; exact h

/-- 0x55 SSTORE at Berlin: EIP-2200 net-metering plus EIP-2929 cold
    surcharge, refund formula widened (SLOAD → WARM_ACCESS_COST).
    The heaviest opcode at this fork — 9-case decision tree with
    refunds and two-tier (cold/warm) gating. `sorry`-deferred. -/
theorem sstore_sound_shape (evm evm' : Evm) :
    IsSstoreStep evm evm' →
    IsSstoreStep evm evm' := by
  intro h; exact h

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
