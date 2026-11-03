/-
  Evm.Berlin.Spec.AccessList — EIP-2929 warm/cold accounting predicate.

  EELS reference: `forks/berlin/state.py` (helpers
  `mark_account_warm` / `mark_storage_key_warm`) plus the per-opcode
  call sites in `forks/berlin/vm/instructions/storage.py`,
  `forks/berlin/vm/instructions/environment.py`, and
  `forks/berlin/vm/instructions/system.py`.

  EIP-2929 introduces two warm sets, both scoped to the current
  transaction (they reset on tx start; sub-frames share with the
  parent — the warm set is part of `Environment`, not per-frame):

    * `accessed_addresses : set[Address]`
      Seeded with `[origin, target, all precompiles]` at tx start
      (see EELS `forks/berlin/fork.py` `process_transaction` lines
      around the access-list expansion). Any account touched by
      BALANCE / EXT* / CALL-family / SELFDESTRUCT is added if not
      already present.

    * `accessed_storage_keys : set[(Address, U256)]`
      Seeded with the EIP-2930 access-list entries from the typed tx.
      Augmented by every SLOAD / SSTORE.

  When a touch is "cold" (first time this tx), the opcode pays a
  surcharge: 2600 gas for accounts (`ACCESS_LIST_ADDRESS_COST`),
  2100 for storage slots (`ACCESS_LIST_STORAGE_KEY_COST`). Subsequent
  "warm" touches pay 100 gas (`WARM_ACCESS_COST`). The warm cost
  REPLACES the previous fork's access cost — i.e., SLOAD's Istanbul
  price of 800 vanishes and is replaced by `2100 cold | 100 warm`.

  This file specs the cold→warm STATE TRANSITION as a pure predicate
  over the access-list portion of `Environment`. The per-opcode gas
  charges are tracked in `StorageStep.lean` (SSTORE/SLOAD) and
  `CallStep.lean` (CALL family); both consult these predicates and
  surface the resulting `wasCold : Bool` to drive the cost branch.

  ## What's encoded vs glossed

  * Encoded: the set membership relation; the post-state's
    `accessedAddresses` (resp. `accessedStorageKeys`) equals the
    pre-state's plus the freshly-warmed key.
  * Encoded: the `Bool` output flag accurately reports cold vs warm
    (true ↔ key was NOT in pre-state's set).
  * Glossed: the tx-start seed (origin / target / precompiles /
    EIP-2930 access-list contents). The seed belongs to the tx-level
    spec (Berlin's `processTransaction`), not the per-step predicate.
  * Glossed: the 2600/2100/100 numeric values themselves; this file
    exports them as `coldAddressCost`, `coldStorageCost`,
    `warmAccessCost` so other spec files can reference by name. The
    actual gas charge is wired in those files.

  Pre-Berlin forks have these fields permanently empty, so any
  cold-warm transition for them is vacuous (everything is cold every
  time, but the surcharge isn't paid). Berlin is the first fork that
  actually consults the fields. Shanghai (EIP-3651) pre-warms the
  coinbase address; see `Shanghai/Spec/WarmCoinbase.lean`.
-/

import Evm.Frontier.Vm
import Evm.Forks
import Evm.Istanbul.Spec.GasConstants

namespace Evm.Berlin.Spec

open Evm.Frontier.Vm

/-! ## EIP-2929 cost constants

    Names taken from EELS `forks/berlin/vm/gas.py` `GasCosts`. Each
    constant is one of: cold address surcharge (2600), cold storage
    surcharge (2100), warm access flat cost (100). -/

/-- EIP-2929 `ACCESS_LIST_ADDRESS_COST` (2600). Charged the first time
    an address is touched by a tx (cold access). Replaces the
    Istanbul/TW per-opcode account-access price for BALANCE / EXT* /
    CALL-family / SELFDESTRUCT. -/
def coldAddressCost : Nat := 2600

/-- EIP-2929 `ACCESS_LIST_STORAGE_KEY_COST` (2100). Charged the first
    time an `(address, slot)` pair is touched by a tx. Surcharged ON
    TOP of the (warm) SLOAD / SSTORE base price. -/
def coldStorageCost : Nat := 2100

/-- EIP-2929 `WARM_ACCESS_COST` (100). The flat cost for any
    subsequent access to an already-warm key. SLOAD warm = 100;
    BALANCE/EXT*/CALL warm-target surcharge = 100 above the call
    base. -/
def warmAccessCost : Nat := 100

/-! ## Cold/warm transition relations

    Each relation says: given a pre-`Environment` and a key, produce
    a post-`Environment` and a `wasCold` flag, such that the
    access-list field is updated correctly. The relations are
    `Prop`-valued so refinement can match either branch by case. -/

/-- `IsAccessAddressStep env addr env' wasCold` holds iff
      * the only field of `env` that differs in `env'` is
        `accessedAddresses`,
      * `env'.accessedAddresses` contains exactly the addresses of
        `env.accessedAddresses` plus `addr`,
      * `wasCold = true`  iff `addr ∉ env.accessedAddresses`,
      * `wasCold = false` iff `addr ∈ env.accessedAddresses`.

    Mirrors the EELS pattern
      `is_cold = addr not in accessed_addresses`
      `if is_cold: accessed_addresses.add(addr)`
    that appears in every BALANCE / EXT* / CALL-family opcode at
    Berlin. -/
def IsAccessAddressStep (env : Environment) (addr : Evm.Address)
                        (env' : Environment) (wasCold : Bool) : Prop :=
  let cold := ¬ env.accessedAddresses.contains addr
  wasCold = cold ∧
  env' = { env with
    accessedAddresses :=
      if cold then env.accessedAddresses ++ [addr]
      else env.accessedAddresses }

/-- `IsAccessStorageStep env addr slot env' wasCold` — the storage-
    key analogue. Membership is by exact (address, slot) match.

    EELS `forks/berlin/vm/instructions/storage.py` `sload` consults
    `(evm.message.current_target, key)` against
    `accessed_storage_keys`; SSTORE does the same with the same key
    shape. We mirror that here.

    Note that the warming is keyed by `(addr, slot)` — warming
    `(A, 7)` does NOT warm `(A, 8)` nor `(B, 7)`. -/
def IsAccessStorageStep (env : Environment) (addr : Evm.Address)
                        (slot : Evm.U256)
                        (env' : Environment) (wasCold : Bool) : Prop :=
  let cold := ¬ env.accessedStorageKeys.contains (addr, slot)
  wasCold = cold ∧
  env' = { env with
    accessedStorageKeys :=
      if cold then env.accessedStorageKeys ++ [(addr, slot)]
      else env.accessedStorageKeys }

/-! ## Properties — sanity-check theorems that any correct
    implementation of the access list MUST satisfy. They are not part
    of the relation itself (which already constrains things tightly)
    but make refinement obligations easier to discharge by hand.

    Statements only — proofs deferred to the Berlin refinement
    drop. The same pattern was used for `sstore_only_current_storage`
    in `Frontier/Spec/StorageStep.lean` (one `sorry` left there as a
    placeholder for an obvious obligation on the State API). -/

/-- The address access predicate is *monotonic*: every address that
    was warm pre-step is still warm post-step. -/
theorem access_address_monotonic
    (env : Environment) (addr : Evm.Address)
    (env' : Environment) (wasCold : Bool)
    (h : IsAccessAddressStep env addr env' wasCold) :
    ∀ a, env.accessedAddresses.contains a →
         env'.accessedAddresses.contains a := by
  obtain ⟨_, hEq⟩ := h
  intro a ha
  rw [hEq]
  -- Post = pre ++ [addr] (cold) or pre (warm). In both cases `a ∈ pre`
  -- implies `a ∈ post`.
  have haMem : a ∈ env.accessedAddresses := by simpa using ha
  -- After `rw [hEq]`, the goal is about the if-then-else over `Bool`.
  -- Simp unfolds the membership through .contains; both branches
  -- preserve membership.
  simp only []
  by_cases hCold : addr ∈ env.accessedAddresses
  · simp [hCold, haMem]
  · simp [hCold, List.mem_append, haMem]

/-- Storage access predicate is monotonic. -/
theorem access_storage_monotonic
    (env : Environment) (addr : Evm.Address) (slot : Evm.U256)
    (env' : Environment) (wasCold : Bool)
    (h : IsAccessStorageStep env addr slot env' wasCold) :
    ∀ k, env.accessedStorageKeys.contains k →
         env'.accessedStorageKeys.contains k := by
  obtain ⟨_, hEq⟩ := h
  intro k hk
  rw [hEq]
  have hkMem : k ∈ env.accessedStorageKeys := by simpa using hk
  simp only []
  by_cases hCold : (addr, slot) ∈ env.accessedStorageKeys
  · simp [hCold, hkMem]
  · simp [hCold, List.mem_append, hkMem]

/-- The `wasCold` flag is uniquely determined by `env` and `addr`. -/
theorem access_address_wasCold_unique
    (env : Environment) (addr : Evm.Address)
    (env'₁ env'₂ : Environment) (c₁ c₂ : Bool)
    (h₁ : IsAccessAddressStep env addr env'₁ c₁)
    (h₂ : IsAccessAddressStep env addr env'₂ c₂) :
    c₁ = c₂ := by
  obtain ⟨he₁, _⟩ := h₁
  obtain ⟨he₂, _⟩ := h₂
  -- Both `c₁` and `c₂` equal `¬ env.accessedAddresses.contains addr`,
  -- decidable Bool, so eq-trans through that intermediate.
  cases c₁ <;> cases c₂ <;> simp_all

/-! ## Fork-conditional value (iff form)

    The defining behaviour of EIP-2929 is that SLOAD (and the
    address-touching opcodes) get a `cold | warm` price branch
    at Berlin. Pre-Berlin everything is flat. We state that as
    a single iff over `Fork`: the per-SLOAD cost depends on the
    warm-status of the slot iff the fork is Berlin-or-later. -/

/-- Per-SLOAD gas cost as a function of fork and warm-status. -/
def sloadCostAt (f : Evm.Fork) (isWarm : Bool) : Nat :=
  if f.atLeast .berlin then (if isWarm then warmAccessCost else coldStorageCost)
  else if f.atLeast .istanbul         then Evm.Istanbul.Spec.gSload    -- 800
  else if f.atLeast .tangerineWhistle then 200                          -- EIP-150
  else                                     50                            -- Frontier

/-- EIP-2929 activation: SLOAD's cost branches on `isWarm` iff the
    fork is Berlin-or-later. Pre-Berlin the cost is flat regardless. -/
theorem sload_branches_iff_berlin (f : Evm.Fork) :
    sloadCostAt f true ≠ sloadCostAt f false ↔ f.atLeast .berlin := by
  unfold sloadCostAt
  cases f <;> decide

end Evm.Berlin.Spec
