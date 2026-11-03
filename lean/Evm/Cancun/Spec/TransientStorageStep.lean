/-
  Evm.Cancun.Spec.TransientStorageStep — EIP-1153 TLOAD / TSTORE.

  EELS reference: `forks/cancun/vm/instructions/storage.py` `tload`
  and `tstore`, with gas costs `GAS_WARM_ACCESS = 100` in
  `forks/cancun/vm/gas.py`.

  EIP-1153 introduces a *second* per-account storage map that lives
  entirely within a single transaction:

    * Persists across call frames (a TSTORE in a sub-frame is visible
      to the parent on success).
    * Cleared at the end of the *transaction*, not at the end of a
      frame — even on REVERT mid-frame, the parent retains the
      sub-frame's TSTORE writes performed BEFORE the revert? No: the
      EIP says transient storage is reverted on REVERT just like
      regular storage. We follow EELS exactly: TSTORE writes are
      part of the per-frame state that gets unwound on REVERT, and
      the per-tx clear happens at the very end of `apply_transaction`.

    * Gas cost is a flat `100` per operation (= `GAS_WARM_ACCESS`),
      irrespective of value. No refund.

  The transient-storage map lives in `Evm.Frontier.Vm.Environment`
  as `transientStorage : List ((Address × U256) × U256)` so that the
  Frontier-shaped frame can carry it without a fork-specific
  Environment.

  Inheritance: applies unchanged at Prague.
-/

import Evm.Frontier.Vm

namespace Evm.Cancun.Spec

open Evm.Frontier.Vm

/-- EELS `GAS_WARM_ACCESS` (Cancun, EIP-1153). Both TLOAD and TSTORE
    charge this constant. -/
def gasTransientAccess : Nat := 100

/-! ## Transient-storage map helpers

    Lookup / update operations on the environment's
    `transientStorage` list, mirroring `Evm.Frontier.State.getStorage`
    / `setStorage` shape. We keep these here (rather than in
    `Evm.Frontier.Vm`) so they live next to the opcode that uses them. -/

/-- Read the transient slot at `(addr, slot)`, defaulting to 0. -/
def tloadValue (env : Environment) (addr : Evm.Address) (slot : Evm.U256) :
    Evm.U256 :=
  match env.transientStorage.find? (fun (k, _) => k = (addr, slot)) with
  | some (_, v) => v
  | none        => 0

/-- Write `(addr, slot) ↦ value` into transient storage. Writing zero
    removes the entry (kept structurally minimal, matches EELS). -/
def tstoreSet (env : Environment) (addr : Evm.Address) (slot value : Evm.U256) :
    Environment :=
  let pruned := env.transientStorage.filter (fun (k, _) => k ≠ (addr, slot))
  { env with
      transientStorage :=
        if value = (0 : Evm.U256) then pruned
        else ((addr, slot), value) :: pruned }

/-! ## TLOAD (0x5c)

    Pop slot, charge 100 gas, push `tload(currentTarget, slot)`. State
    is unchanged (only the env's transient map is read). -/

def IsTloadStep (evm evm' : Evm) : Prop :=
  ∃ slot rest,
    evm.stack = slot :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ gasTransientAccess ∧
    let v := tloadValue evm.env evm.message.currentTarget slot
    evm' = { evm with
      stack   := v :: rest,
      gasLeft := evm.gasLeft - gasTransientAccess,
      pc      := evm.pc + 1 }

/-! ## TSTORE (0x5d)

    Pop slot and value, charge 100 gas, write `(currentTarget, slot)
    ↦ value` into transient storage. No refund. Reverts on static
    context. -/

def IsTstoreStep (evm evm' : Evm) : Prop :=
  ∃ slot value rest,
    evm.stack = slot :: value :: rest ∧
    -- Static-context guard: TSTORE is a write operation. EELS
    -- `tstore` raises `WriteInStaticContext` when `evm.message.is_static`.
    evm.message.isStatic = false ∧
    evm.gasLeft ≥ gasTransientAccess ∧
    let addr := evm.message.currentTarget
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - gasTransientAccess,
      env     := tstoreSet evm.env addr slot value,
      pc      := evm.pc + 1 }

/-! ## Invariants

    Distinguished structural properties of TLOAD/TSTORE that any
    correct implementation must preserve. -/

/-- TLOAD never mutates state, env, or memory. -/
theorem tload_pure (evm evm' : Evm) (h : IsTloadStep evm evm') :
    evm'.env = evm.env ∧ evm'.memory = evm.memory ∧
    evm'.message = evm.message := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  rw [hEvm]
  exact ⟨rfl, rfl, rfl⟩

/-- TSTORE only writes to transient storage at the current target.
    No persistent storage, no balance, no other field of state is
    touched. -/
theorem tstore_transient_only (evm evm' : Evm) (h : IsTstoreStep evm evm') :
    evm'.env.state = evm.env.state ∧
    evm'.env.refundCounter = evm.env.refundCounter ∧
    evm'.env.logs = evm.env.logs := by
  obtain ⟨_, _, _, _, _, _, hEvm⟩ := h
  rw [hEvm]
  -- Post-state: env := tstoreSet evm.env addr slot value, which only
  -- mutates `transientStorage`. The other three fields are preserved
  -- by the record-update syntax of `tstoreSet`.
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Evm.Cancun.Spec
