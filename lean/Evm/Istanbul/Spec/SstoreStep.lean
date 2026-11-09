/-
  Evm.Istanbul.Spec.SstoreStep — EIP-2200 net SSTORE relation.

  EELS reference: `forks/istanbul/vm/instructions/storage.py` function
  `sstore` (lines 53-112). The corresponding implementation in this
  repo: `Evm.Istanbul.Vm.Instructions.Storage.sstore`.

  EIP-2200 is the *revised* version of EIP-1283 — same overall shape
  (clean-slot vs. dirty-slot cost; refund cancellations on dirty
  rewrites) with three substantive changes vs. Constantinople-1283:

    1. **Trip-wire (EIP-1706 / EIP-2200 §line 66-67)**: if
       `gas_left ≤ CALL_STIPEND` (2300) BEFORE any work, raise
       OutOfGasError. Prevents a 2300-stipend reentrancy attack on
       contracts that assumed a 5000-gas SSTORE floor.

    2. **Repricing for SLOAD (EIP-1884)**: the "no-op" / "dirty"
       tier is now 800 (the new SLOAD price) instead of 200.

    3. **Cleaner cost branch**: cost depends ONLY on whether the
       slot is clean AND being changed. The no-op case
       `current == newValue` falls into the SLOAD-priced branch
       (same as Constantinople-1283).

  ## Decision tree (EELS-faithful, line by line)

    ```
    if gas_left <= 2300:                                      # 66-67
        raise OutOfGasError                                    # trip-wire

    original = originalState[addr][key]                       # 70-72
    current  = state[addr][key]                               # 73

    # COST (lines 75-81)
    if original == current and current != newValue:
        cost = STORAGE_SET   if original == 0  else COLD_WRITE
    else:
        cost = SLOAD

    # REFUND (lines 84-104, only fires when current != newValue)
    if current != newValue:
        if original != 0 and current != 0 and newValue == 0:  # 85-87
            refund += REFUND_STORAGE_CLEAR
        if original != 0 and current == 0:                    # 89-91
            refund -= REFUND_STORAGE_CLEAR
        if original == newValue:                              # 93
            if original == 0:
                refund += STORAGE_SET - SLOAD   # 19200
            else:
                refund += COLD_WRITE - SLOAD    #  4200

    charge_gas(evm, cost)                                     # 106
    if is_static: raise WriteInStaticContext                  # 107-108
    set_storage(addr, key, newValue)                          # 109
    ```

  ## What this relation covers
    * The trip-wire as an explicit pre-condition (`gas_left >
      sentryGas`), so the relation only describes the SUCCESSFUL
      path (no relation needed for OOG — those go to a halting
      relation).
    * The full nine-case cost / refund table.
    * Static-context check, lifted into a pre-condition (mirrors
      how `Frontier.Spec.IsSstoreStep` handles it — see file
      docstring there).

  ## What this relation does NOT cover
    * The implementation runs `charge_gas` BEFORE the static check.
      That means an OOG (cost > gas_left) takes precedence over the
      static check. The spec doesn't observe this ordering because
      both branches end in "raise" — only the successful (non-error)
      branch is described.
    * Berlin (EIP-2929) cold/warm surcharge: layered ON TOP of EIP-2200
      one fork later, not here.

  ## Refund counter: EELS's integer arithmetic, no clamp
  EELS represents `refund` as a signed `int` and adds the three deltas
  (`storage.py` 84-104). The relation states `R' = R + delta` with
  `0 ≤ R + delta`: the "cancel earlier clear" subtraction (89-91) never
  goes below zero at the tx level because the earlier clear of the same
  slot in the same tx paid it. The refinement proves this from the
  tx-level invariant `Evm.Constantinople.Spec.RefundInv`, which the step
  preserves. (Corrected 2026-11-09: the relation used to clamp the sum at
  0; the implementation clamps each delta in turn. The two disagree when
  the counter is below 15000 on the cancel branch, e.g. refund 0,
  original ≠ 0, current = 0, new = original: clamp-in-turn 4200, clamp-
  once 0, EELS −10800 — a state the invariant rules out.)
-/

import Evm.Frontier.Vm
import Evm.Frontier.State
import Evm.Frontier.Spec.StepShapes
import Evm.Istanbul.Vm.Gas

namespace Evm.Istanbul.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-- 0x55 SSTORE under EIP-2200 (Istanbul).

    Pre-conditions:
      * `evm.stack = key :: newValue :: rest`
      * `evm.message.isStatic = false`
      * `evm.gasLeft > 2300` (EIP-1706 trip-wire)
      * `evm.gasLeft ≥ cost` (cost depends on the slot's state)

    Post-state: stack popped twice, gas charged, storage updated,
    refund counter moved by the integer delta (which keeps it ≥ 0), pc
    advanced by 1.

    See file docstring for the full nine-case cost / refund table. -/
def IsSstoreStep (evm evm' : Evm) : Prop :=
  ∃ key newValue rest,
    evm.stack = key :: newValue :: rest ∧
    evm.message.isStatic = false ∧
    -- EIP-1706 trip-wire: STRICT >, since EELS uses `<=` for the
    -- failure check.
    evm.gasLeft > Evm.Istanbul.Vm.Gas.sstoreSentryGas ∧
    let addr     := evm.message.currentTarget
    let current  := evm.env.state.getStorage addr key
    let original := evm.env.originalState.getStorage addr key
    let cost : Nat :=
      if original = current ∧ current ≠ newValue then
        if original = (0 : Evm.U256) then Evm.Istanbul.Vm.Gas.sstoreSet
        else Evm.Istanbul.Vm.Gas.sstoreReset
      else
        Evm.Istanbul.Vm.Gas.sLoad
    -- Refund delta as a signed int, zero unless `current != newValue`.
    let refundDelta : Int :=
      if current = newValue then 0
      else
        let dClear : Int :=
          if original ≠ (0 : Evm.U256) ∧ current ≠ (0 : Evm.U256) ∧
             newValue = (0 : Evm.U256) then
            (Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int)
          else 0
        let dUnclear : Int :=
          if original ≠ (0 : Evm.U256) ∧ current = (0 : Evm.U256) then
            -(Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int)
          else 0
        let dResetToOrig : Int :=
          if original = newValue then
            if original = (0 : Evm.U256) then
              ((Evm.Istanbul.Vm.Gas.sstoreSet -
                  Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
            else
              ((Evm.Istanbul.Vm.Gas.sstoreReset -
                  Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
          else 0
        dClear + dUnclear + dResetToOrig
    evm.gasLeft ≥ cost ∧
    0 ≤ (evm.env.refundCounter : Int) + refundDelta ∧
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - cost,
      env     := { evm.env with
        state         := evm.env.state.setStorage addr key newValue,
        refundCounter := ((evm.env.refundCounter : Int) + refundDelta).toNat },
      pc      := evm.pc + 1 }

end Evm.Istanbul.Spec
