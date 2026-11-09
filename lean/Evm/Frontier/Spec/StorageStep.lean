/-
  Evm.Frontier.Spec.StorageStep — SLOAD / SSTORE specs.

  Storage ops are where buggy implementations most often go wrong:
    1. SSTORE has a refund schedule that depends on the OLD value
       (cleared slots refund 15000).
    2. SSTORE cost depends on the OLD value (write-to-empty costs
       20000, write-to-non-empty costs 5000).
    3. Both ops index storage by `(currentTarget, slot)`, NOT by
       `(target, slot)` — distinct from CALLCODE/DELEGATECALL.

  These three points are explicit clauses in the spec so the
  refinement proof has to actually verify them, and an
  implementation that omits the refund or uses the wrong cost
  table is rejected.

  Later forks (Tangerine Whistle: SLOAD 50→200; Istanbul: EIP-2200
  refactor) change the gas/refund tables. Those forks declare
  their own `IsSloadStep` / `IsSstoreStep` with updated formulas.
  This file is the Frontier baseline.
-/

import Evm.Frontier.Vm
import Evm.Frontier.State

namespace Evm.Frontier.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-! ## SLOAD (0x54)

    Charge `sLoad` (= 50 at Frontier), pop slot, push the storage
    value at `(currentTarget, slot)`. State is unchanged. -/

def IsSloadStep (evm evm' : Evm) : Prop :=
  ∃ slot rest,
    evm.stack = slot :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.sLoad ∧
    let v := evm.env.state.getStorage evm.message.currentTarget slot
    evm' = { evm with
      stack   := v :: rest,
      gasLeft := evm.gasLeft - Gas.sLoad,
      pc      := evm.pc + 1 }

/-! ## SSTORE (0x55) — Frontier semantics

    Pop slot and new value, look up old value at `(currentTarget,
    slot)`. Cost depends on transition:

      old = 0, new ≠ 0  → 20000 gas (sSet)
      old ≠ 0, new ≠ 0  → 5000 gas (sReset)
      old ≠ 0, new = 0  → 5000 gas (sReset), refund 15000 (sClearRefund)
      old = 0, new = 0  → 5000 gas (sReset)

    The refund is added to `env.refundCounter`, which is applied
    (capped at gasUsed/2) at the end of the transaction. -/

def IsSstoreStep (evm evm' : Evm) : Prop :=
  ∃ slot value rest,
    evm.stack = slot :: value :: rest ∧
    let addr := evm.message.currentTarget
    let oldValue := evm.env.state.getStorage addr slot
    let cost :=
      if oldValue = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256)
      then Gas.sSet else Gas.sReset
    let refundDelta :=
      if oldValue ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256)
      then Gas.sClearRefund else 0
    evm.gasLeft ≥ cost ∧
    -- Post: stack popped twice, gas charged, refund accumulated,
    -- storage updated, pc advanced.
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - cost,
      env     := { evm.env with
        state         := evm.env.state.setStorage addr slot value,
        refundCounter := evm.env.refundCounter + refundDelta },
      pc      := evm.pc + 1 }

/-! ## Storage invariants for refinement

    Two structural invariants any correct SSTORE implementation
    must satisfy. Stated as theorems against `IsSstoreStep`. -/

/-- An SSTORE only ever ADDS to the refund counter (never
    subtracts). Refunds in Frontier go up monotonically; the cap
    at gasUsed/2 is applied at the tx level. -/
theorem sstore_refund_monotonic (evm evm' : Evm)
    (h : IsSstoreStep evm evm') :
    evm'.env.refundCounter ≥ evm.env.refundCounter := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  rw [hEvm]
  -- evm'.env.refundCounter = evm.env.refundCounter + (0 or 15000)
  -- which is ≥ evm.env.refundCounter.
  show evm.env.refundCounter + _ ≥ evm.env.refundCounter
  exact Nat.le_add_right _ _

/-- An SSTORE never touches storage of any address other than
    `currentTarget`. This is the spec form of "no cross-account
    storage leak". -/
theorem sstore_only_current_storage (evm evm' : Evm)
    (h : IsSstoreStep evm evm') :
    ∀ addr slot,
      addr ≠ evm.message.currentTarget →
      evm'.env.state.getStorage addr slot =
      evm.env.state.getStorage addr slot := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  intro addr slot hne
  rw [hEvm]
  -- evm'.env.state = evm.env.state.setStorage currentTarget slot' value;
  -- getStorage on a different address is unchanged.
  show (evm.env.state.setStorage evm.message.currentTarget _ _).getStorage addr slot
       = evm.env.state.getStorage addr slot
  rw [State.getStorage_setStorage, if_neg]
  intro he; exact hne (Prod.mk.inj he).1

/-! ## Notes

    - `getStorage` and `setStorage` are part of the State API.
      The spec uses them by name rather than reaching into the
      account/storage representation. An implementation can use
      any storage representation as long as it provides functions
      satisfying these names with the obvious specifications.

    - The Frontier refund schedule has just one rule (sClearRefund
      = 15000 on non-zero → zero transition). Istanbul (EIP-2200)
      replaces this with a more elaborate state-machine — different
      spec, different file when that fork's spec is built out.

    - The Berlin EIP-2929 cold/warm distinction adds 2100 gas for
      cold reads. Pre-Berlin (this file) has no such concept.

    - `sstore_refund_monotonic` and `sstore_only_current_storage`
      are *invariant theorems* of the kind described in
      `Invariants.lean`. They get caught at proof time if an
      implementation forgets to accumulate the refund or
      accidentally writes to the wrong slot. -/

end Evm.Frontier.Spec
