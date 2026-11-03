/-
  Evm.Berlin.Vm.Instructions.Storage — SSTORE under EIP-2200 + EIP-2929.

  EELS reference: `forks/berlin/vm/instructions/storage.py` (sstore).

  The SSTORE schedule at Berlin is the composition of two rules:

  (1) EIP-2200 "net gas metering" (introduced at Istanbul) — gas + refund
      depend on the triple `(original, current, new)` where
        * `original` = slot value at the start of the transaction
        * `current`  = slot value before this SSTORE
        * `new`      = value being written
      and the costs / refunds are the canonical EIP-2200 table:

        if new == current:                              # no-op
          cost   = SLOAD_GAS (warm = 100 in Berlin's case via the SSTORE
                              warm path; see EIP-2200's `SLOAD_GAS`)
          refund = 0
        elif current == original:                       # clean slot
          if original == 0:
            cost = SSTORE_SET_GAS (20000)
          else:
            cost = SSTORE_RESET_GAS (5000 - COLD_SLOAD = 2900 in Berlin)
            if new == 0:
              refund += SSTORE_CLEARS_SCHEDULE
        else:                                           # dirty slot
          cost = SLOAD_GAS (warm 100)
          # refund adjustments per EIP-2200's net-metering table:
          if original != 0:
            if   current == 0: refund -= SSTORE_CLEARS_SCHEDULE
            elif new == 0:     refund += SSTORE_CLEARS_SCHEDULE
          if new == original:
            if original == 0:
              refund += SSTORE_SET_GAS    - SLOAD_GAS
            else:
              refund += SSTORE_RESET_GAS  - SLOAD_GAS

  (2) EIP-2929 cold surcharge — if the `(address, slot)` pair is *cold*
      at SSTORE entry, charge an additional COLD_SLOAD_COST (2100) on
      top of whatever (1) computes; then mark the slot warm.

  Refund cap (EIP-2929/EIP-3529 deferred — EIP-3529 ships at London):
  Berlin keeps the EIP-2200 cap at `gasUsed / 2`. London (next fork)
  drops it to `/5` via EIP-3529. We use `/2` here.

  EIP-2929 numeric note: `SSTORE_RESET_GAS` at Berlin is `5000 -
  COLD_SLOAD_COST = 2900` (EIP-2929 §"Gas cost changes", final
  paragraph), because the cold charge is being levied separately as
  the surcharge above. EELS encodes this as
  `SSTORE_RESET_GAS = 5000 - COLD_SLOAD_COST`.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Gas
import Evm.Berlin.Vm.Gas

namespace Evm.Berlin.Vm.Instructions.Storage

open Evm.Frontier
open Evm.Frontier.Vm

/-- EIP-2200 `SSTORE_SET_GAS` (writing nonzero to a previously-zero
    clean slot). Unchanged from Frontier's `sSet`. -/
def sstoreSet : Nat := 20000

/-- EIP-2929-adjusted `SSTORE_RESET_GAS = 5000 - COLD_SLOAD_COST`.
    The 5000 is the original net-metering reset; we subtract the
    cold surcharge because Berlin levies it as a separate charge. -/
def sstoreReset : Nat := 5000 - Berlin.Vm.Gas.coldSload  -- 2900

/-- EIP-2200 / EIP-3529 refund granted on a non-zero→zero clear of a
    clean slot. Stays at 15000 in Berlin; London (EIP-3529) drops it
    to 4800 = `SSTORE_RESET_GAS + ACCESS_LIST_STORAGE_KEY_COST`. -/
def sstoreClearsRefund : Nat := 15000

/-- The EIP-2200 / EIP-2929 SSTORE result: how much gas to charge and
    how to adjust the refund counter. Returning a signed delta on
    `refund` would be cleaner; we instead return separate `add` and
    `sub` so the caller can floor to 0 (refund counter is unsigned in
    EELS too).

    Inputs:
      `isCold`   — true iff `(addr, slot)` was not in
                   `accessedStorageKeys` at entry.
      `original` — slot value at start of tx (snapshot).
      `current`  — slot value right before this SSTORE.
      `new`      — value being written. -/
structure SstoreCost where
  /-- Gas to charge for this SSTORE. -/
  cost      : Nat
  /-- Refund counter increase. -/
  refundAdd : Nat
  /-- Refund counter decrease — applied AFTER `refundAdd` and floored
      at 0. Per EIP-2200, "dirty slot then back to zero" can subtract
      the previously-granted clear refund. -/
  refundSub : Nat
  deriving Inhabited

/-- The EIP-2200 net-gas-metering decision (without the EIP-2929 cold
    surcharge). Returns `(cost, refundAdd, refundSub)` as described
    above. Pulled out so the Effect's `resumeSstore` can layer the
    cold surcharge cleanly.

    Note that the "no-op" cost (`new = current`) is `warmAccess` (100)
    in Berlin — this is the post-2929 update to EIP-2200's `SLOAD_GAS`
    parameter, made explicit in EIP-2929 §"Gas cost changes". -/
def eip2200 (original current new_ : Evm.U256) : Nat × Nat × Nat :=
  if new_ = current then
    -- No-op SSTORE — Berlin warm-access cost.
    (Berlin.Vm.Gas.warmAccess, 0, 0)
  else if current = original then
    -- Clean slot (no other SSTORE has touched it in this tx).
    if original = (0 : Evm.U256) then
      (sstoreSet, 0, 0)
    else
      let refundAdd := if new_ = (0 : Evm.U256) then sstoreClearsRefund else 0
      (sstoreReset, refundAdd, 0)
  else
    -- Dirty slot — same SLOAD/warm cost, refund accounting per EIP-2200.
    let cost := Berlin.Vm.Gas.warmAccess
    -- Step 1: clear-refund adjustments if `original ≠ 0`.
    let (addClear, subClear) : Nat × Nat :=
      if original ≠ (0 : Evm.U256) then
        if      current = (0 : Evm.U256) then (0, sstoreClearsRefund)
        else if new_    = (0 : Evm.U256) then (sstoreClearsRefund, 0)
        else (0, 0)
      else (0, 0)
    -- Step 2: "back to original" refunds.
    let addReset : Nat :=
      if new_ = original then
        if original = (0 : Evm.U256) then
          sstoreSet   - Berlin.Vm.Gas.warmAccess
        else
          sstoreReset - Berlin.Vm.Gas.warmAccess
      else 0
    (cost, addClear + addReset, subClear)

/-- Full EIP-2929 SSTORE: layer the cold surcharge on top of the
    EIP-2200 result. Cold surcharge is unconditional on first touch
    of the slot in this tx; it's not refunded. -/
def cost (isCold : Bool) (original current new_ : Evm.U256) : SstoreCost :=
  let (c, a, sub) := eip2200 original current new_
  let surcharge := if isCold then Berlin.Vm.Gas.sstoreColdSurcharge else 0
  { cost := c + surcharge, refundAdd := a, refundSub := sub }

/-- Pure Berlin SSTORE gas + refund: `(cost, newRefundCounter)`.
    Folds `cost`'s add/sub pair into the counter with Berlin's
    discipline: add first, then subtract floored at 0. -/
def sstoreGas (refund : Nat) (isCold : Bool)
    (original current new_ : Evm.U256) : Nat × Nat :=
  let r := cost isCold original current new_
  let r1 := refund + r.refundAdd
  (r.cost, if r1 < r.refundSub then 0 else r1 - r.refundSub)

end Evm.Berlin.Vm.Instructions.Storage
