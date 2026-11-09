/-
  Evm.Berlin.Spec.StorageStep — EIP-2929 SSTORE / SLOAD pricing.

  EELS reference: `forks/berlin/vm/instructions/storage.py`
  (`sload`, `sstore`). The shape of EELS Istanbul's `sstore` is
  preserved exactly (same EIP-2200 net-metering refund logic);
  Berlin only changes the cost branch by interleaving a cold/warm
  surcharge from `accessed_storage_keys`.

  ## SLOAD pricing (delta vs Istanbul)

  Istanbul (and TW before it): flat `SLOAD = 800` (resp. 200).
  Berlin: `2100 cold | 100 warm`. The base SLOAD price (800)
  *disappears* — Berlin's table is `cold = 2100, warm = 100`, not
  `800 + (2100|100)`. See EELS `sload` body:
  ```
  if (current_target, key) in evm.accessed_storage_keys:
      charge_gas(WARM_ACCESS_COST)              # 100
  else:
      charge_gas(COLD_SLOAD_COST)               # 2100
      evm.accessed_storage_keys.add(...)
  ```
  (`forks/berlin/vm/instructions/storage.py` `sload`.)

  ## SSTORE pricing (delta vs Istanbul)

  The Istanbul EIP-2200 cost branch is preserved verbatim. Berlin
  layers a cold surcharge ON TOP:
  ```
  if (current_target, key) not in evm.accessed_storage_keys:
      charge_gas(COLD_SLOAD_COST)               # 2100
      evm.accessed_storage_keys.add(...)
  # … then EIP-2200 cost calc (SLOAD/SSTORE_SET/SSTORE_RESET)
  # but with WARM_ACCESS_COST (100) replacing SLOAD (800) as the
  # "no-op / dirty" price …
  ```
  (`forks/berlin/vm/instructions/storage.py` `sstore`.)

  ### The "lazy pre-warm of originalValue" mentioned in the brief

  EIP-2200 needs `original_value` (the slot's value at TX start) to
  decide cost branch. EELS pulls it from `state._snapshots[0]`. In
  our spec, `env.originalState` plays that role: the
  `processTransaction` relation snaps the state before kicking off
  the call. SSTORE here does NOT re-snap; it just reads the field.
  That's why the cold-surcharge accounting only mutates
  `accessedStorageKeys` (and gas / refund / state), not
  `originalState`.

  ## Encoded vs glossed in this file

  * Encoded: the cold surcharge timing (paid BEFORE the EIP-2200
    branch); the post-state's `accessedStorageKeys` extended by
    `(currentTarget, slot)`; the EIP-2200 refund formula carried
    over from Istanbul.
  * Encoded: the EIP-2200 trip-wire (`gasLeft > 2300` else
    `OutOfGas`) — Berlin keeps it; the EIP-3529 refund-cap change
    is at London.
  * Glossed: the SLOAD spec because it's degenerately simple — we
    state it inline. The `IsSstoreStep` body grew enough that the
    Istanbul "signed refund delta" pattern is repeated; we deduplicate
    via a helper.
-/

import Evm.Frontier.Vm
import Evm.Berlin.Spec.AccessList

namespace Evm.Berlin.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-! ### Constants reused at SSTORE/SLOAD pricing

    EIP-2929 introduced one new name for the cold SSTORE surcharge:
    `COLD_SLOAD_COST = 2100`. EELS calls the same constant for both
    "first cold SLOAD" and "SSTORE cold surcharge", since both
    happen to be 2100. -/

/-- EIP-2929 `COLD_SLOAD_COST` (2100). Same constant gates the cold
    SSTORE surcharge. EELS `forks/berlin/vm/gas.py` `GasCosts`. -/
abbrev coldSloadCost : Nat := coldStorageCost

/-! ## The original-value cache

    EELS reads `original_value` from the tx-start snapshot
    (`get_storage_original`, `forks/berlin/state.py`). The implementation keeps a
    per-tx cache `env.storageOriginals` instead: the first SLOAD/SSTORE of a slot
    records its value, and an uncached slot's original is its current value. The
    cache means the snapshot exactly when `OrigInv` holds — every cached value is
    the tx-start value and every uncached slot is unchanged since tx start. The
    relations below leave the cache's representation free and pin its meaning:
    `OrigInv` of the post-environment. -/

/-- The implementation's original-value lookup: the cached entry, else the current
    value (`Evm.Berlin.Vm.Effect.getOriginal env a k (env.state.getStorage a k)`). -/
def cachedOriginal (env : Environment) (a : Evm.Address) (k : Evm.U256) : Evm.U256 :=
  match env.storageOriginals.find? (fun (p, _) => p = (a, k)) with
  | some (_, v) => v
  | none        => env.state.getStorage a k

/-- The cache agrees with the tx-start world on every slot. -/
def OrigInv (env : Environment) : Prop :=
  ∀ a k, cachedOriginal env a k = env.originalState.getStorage a k

/-! ## SLOAD (0x54) — Berlin

    Pop slot, push value at `(currentTarget, slot)`. Gas:
      `cold = 2100, warm = 100`. The pre-Berlin `SLOAD = 800` is
    completely replaced (not surcharged). Also warms the key for
    later opcodes in the same tx.

    EELS: `forks/berlin/vm/instructions/storage.py` `sload`. -/

def IsSloadStep (evm evm' : Evm) : Prop :=
  ∃ slot rest,
    evm.stack = slot :: rest ∧
    rest.length < stackLimit ∧
    let addr := evm.message.currentTarget
    let wasCold := ¬ evm.env.accessedStorageKeys.contains (addr, slot)
    let cost := if wasCold then coldSloadCost else warmAccessCost
    evm.gasLeft ≥ cost ∧
    let v := evm.env.state.getStorage addr slot
    OrigInv evm'.env ∧
    evm' = { evm with
      stack   := v :: rest,
      gasLeft := evm.gasLeft - cost,
      env     := { evm.env with
        accessedStorageKeys :=
          if wasCold then evm.env.accessedStorageKeys ++ [(addr, slot)]
          else evm.env.accessedStorageKeys,
        storageOriginals := evm'.env.storageOriginals },
      pc      := evm.pc + 1 }

/-! ## SSTORE (0x55) — Berlin (EIP-2929 on top of EIP-2200)

    The Istanbul EIP-2200 cost/refund machinery is unchanged in
    shape; the BERLIN delta is:

    (1) A *cold surcharge* of 2100 charged BEFORE everything else,
        if `(currentTarget, slot) ∉ accessedStorageKeys`. This
        surcharge is independent of whether the SSTORE actually
        mutates the slot — even a no-op SSTORE pays it the first
        time per tx.
    (2) The "no-op / dirty slot" tier price changes from
        `SLOAD = 800` to `WARM_ACCESS_COST = 100`, and the clean→reset
        price drops by the cold surcharge it now includes:
        `COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS = 5000 - 2100 = 2900`
        (clean→set stays 20000).
    (3) The refund on slot-restoration: Istanbul refunded
        `STORAGE_SET - SLOAD = 19200` or `RESET - SLOAD = 4200`;
        Berlin refunds `STORAGE_SET - WARM_ACCESS = 19900` and
        `COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS - WARM_ACCESS = 2800`.

    EELS `forks/berlin/vm/instructions/storage.py::sstore` 78-115
    (execution-specs 636b5f1). Corrected 2026-11-09: this relation
    used to charge 5000 and refund 4900 on the reset path (the EIP-2200
    numbers without EIP-2929's subtraction); the implementation was right.

    Trip-wire (`gasLeft > 2300` else `OutOfGas`) and static-context
    check are inherited from Istanbul; EELS preserves them at
    Berlin.

    Refund counter: EELS's `int` arithmetic — the relation states
    `R' = R + delta` with `0 ≤ R + delta` (no clamp); the refinement gets
    the bound from the tx-level `Evm.Constantinople.Spec.RefundInv`.
    Corrected 2026-11-09: the relation used to clamp each delta in turn
    (the implementation's discipline), not EELS's integer sum.

    `original` is EELS's tx-start value (`originalState`); the
    implementation's cache must agree (`OrigInv`, a precondition of the
    refinement and a conjunct of the post-state).

    Refund-cap reduction (1/2 → 1/5) is at London (EIP-3529); see
    `London/Spec/RefundCap.lean`. -/

/-- EIP-2200 trip-wire, unchanged at Berlin. EELS preserves the
    `if evm.gas_left <= GasCosts.CALL_STIPEND: raise OutOfGasError`
    guard at the top of `sstore`. -/
def sstoreSentryGas : Nat := 2300

/-- EIP-2200 SSTORE_SET (20000) — clean slot 0 → non-zero. Unchanged
    at Berlin. -/
def sstoreSet : Nat := 20000

/-- EIP-2200 SSTORE_RESET (5000) — clean slot non-zero → other.
    Unchanged at Berlin. EELS still calls it `COLD_STORAGE_WRITE`
    (the EIP-2929 cold/warm vocabulary is unrelated to this constant
    name, which predates EIP-2929). -/
def sstoreReset : Nat := 5000

/-- EIP-2200 REFUND_STORAGE_CLEAR (15000). Unchanged at Berlin;
    drops to 4800 at London via EIP-3529. -/
def sstoreClearRefund : Nat := 15000

def IsSstoreStep (evm evm' : Evm) : Prop :=
  ∃ slot value rest,
    evm.stack = slot :: value :: rest ∧
    evm.gasLeft > sstoreSentryGas ∧
    ¬ evm.message.isStatic ∧
    let addr := evm.message.currentTarget
    let original := evm.env.originalState.getStorage addr slot
    let current  := evm.env.state.getStorage addr slot
    -- EIP-2929 cold surcharge: paid first, regardless of mutation.
    let wasCold := ¬ evm.env.accessedStorageKeys.contains (addr, slot)
    let coldDelta : Nat := if wasCold then coldSloadCost else 0
    -- EIP-2200 cost branch — with WARM_ACCESS_COST replacing SLOAD
    -- as the no-op / dirty tier price.
    let mainCost : Nat :=
      if original = current ∧ current ≠ value then
        if original = (0 : Evm.U256) then sstoreSet else sstoreReset - coldSloadCost
      else
        warmAccessCost
    let totalCost := coldDelta + mainCost
    evm.gasLeft ≥ totalCost ∧
    -- EIP-2200 refund branch (EELS 99-116): one integer sum of the three
    -- deltas, the restore-to-original delta in WARM_ACCESS terms.
    let refundDelta : Int :=
      if current ≠ value then
        (if original ≠ (0 : Evm.U256) ∧ current ≠ (0 : Evm.U256) ∧
            value = (0 : Evm.U256) then (sstoreClearRefund : Int) else 0) +
        (if original ≠ (0 : Evm.U256) ∧ current = (0 : Evm.U256) then
            -(sstoreClearRefund : Int) else 0) +
        (if original = value then
            (if original = (0 : Evm.U256) then ((sstoreSet - warmAccessCost : Nat) : Int)
             else ((sstoreReset - coldSloadCost - warmAccessCost : Nat) : Int))
          else 0)
      else 0
    0 ≤ (evm.env.refundCounter : Int) + refundDelta ∧
    OrigInv evm'.env ∧
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - totalCost,
      env     := { evm.env with
        state         := evm.env.state.setStorage addr slot value,
        refundCounter := ((evm.env.refundCounter : Int) + refundDelta).toNat,
        accessedStorageKeys :=
          if wasCold then evm.env.accessedStorageKeys ++ [(addr, slot)]
          else evm.env.accessedStorageKeys,
        storageOriginals := evm'.env.storageOriginals },
      pc      := evm.pc + 1 }

end Evm.Berlin.Spec
