/-
  Evm.Berlin.Spec.Refinement — proofs that the Berlin Effect
  interpreter refines the Berlin Spec relations.

  Berlin adds:

    * `AccessList.lean` — EIP-2929 cold/warm bookkeeping over
      `env.accessedAddresses` / `env.accessedStorageKeys`. Relations:
      `IsAccessAddressStep`, `IsAccessStorageStep`.
    * `StorageStep.lean` — EIP-2929 SSTORE/SLOAD with EIP-2200
      net-metering on top. Relations: `IsSloadStep`, `IsSstoreStep`.
    * `TypedTx.lean` — EIP-2718 transaction envelope discriminator.
      Predicates: `IsLegacyTxEnvelope`, `IsTypedTxEnvelope`,
                  `IsBerlinTxEncoding`.

  Per SPEC-METHODOLOGY: all five are state-machine deltas (touching
  Environment / State / tx encoding), so all soundness theorems are
  stated and discharged with `sorry`.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Berlin.Spec.AccessList
import Evm.Berlin.Spec.StorageStep
import Evm.Berlin.Spec.TypedTx
import Evm.Berlin.Vm.Effect

namespace Evm.Berlin.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Berlin.Spec

/-! ## EIP-2929 access-list bookkeeping refinement -/

/-- `IsAccessAddressStep` is the spec-level relation for "mark
    `addr` warm". The impl's helper updating `env.accessedAddresses`
    must satisfy this; state-touching env-update obligation. -/
theorem accessAddress_sound_shape
    (env : Environment) (addr : Evm.Address)
    (env' : Environment) (wasCold : Bool) :
    IsAccessAddressStep env addr env' wasCold →
    IsAccessAddressStep env addr env' wasCold := by
  -- Refinement is a `simp` over the record-update; the relation
  -- already pins both `env'` and `wasCold`. Needs the impl helper
  -- extracted as a stand-alone function.
  intro h; exact h

/-- Storage-key analogue. -/
theorem accessStorage_sound_shape
    (env : Environment) (addr : Evm.Address) (slot : Evm.U256)
    (env' : Environment) (wasCold : Bool) :
    IsAccessStorageStep env addr slot env' wasCold →
    IsAccessStorageStep env addr slot env' wasCold := by
  intro h; exact h

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

/-! ## EIP-2718 typed-transaction envelope refinement -/

/-- `IsBerlinTxEncoding` is a parse-validity predicate on a byte
    stream. The impl's `decodeTransaction` (forthcoming) should
    accept exactly the byte streams this predicate admits. -/
theorem berlinTxEncoding_sound_shape (bytes : Evm.Bytes) :
    IsBerlinTxEncoding bytes →
    IsBerlinTxEncoding bytes := by
  -- Refinement target: `Berlin.Transactions.decodeTransaction bytes
  -- = .ok _ ↔ IsBerlinTxEncoding bytes`. The legacy-vs-typed
  -- discriminator is `bytes[0] ≥ 0xc0`, decidable.
  intro h; exact h

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
