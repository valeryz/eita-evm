/-
  Evm.Constantinople.Spec.SstoreStep — EIP-1283 "net SSTORE" relation.

  EELS reference: EIP-1283 specification (the Constantinople-era flavour
  of SSTORE that was DEPLOYED then immediately patched-out on mainnet
  by Petersburg). Upstream `forks/constantinople/vm/instructions/
  storage.py` on EELS master collapses Constantinople and Petersburg
  into the pre-1283 schedule, so we follow the EIP directly:

      https://eips.ethereum.org/EIPS/eip-1283

  The matching implementation lives at
  `Evm.Constantinople.Vm.Instructions.Storage.sstore`. This file is
  the *relation* form of that decision tree.

  ## Three storage values
  * `original` — slot at the start of the *transaction*. Read from
    `evm.env.originalState`.
  * `current`  — slot just before this SSTORE. Read from
    `evm.env.state`.
  * `value`    — new value to write (top of stack after `key`).

  ## Decision tree (EIP-1283 §Specification, line-for-line)

  1. `current == value` (no-op) → 200 gas, no refund delta.
  2. `current != value`
     a. `original == current` (clean slot):
        * `original == 0`             → 20000 gas
        * `original != 0`             → 5000 gas
          + 15000 refund if `value == 0`
     b. `original != current` (dirty slot): 200 gas, plus refund
        adjustments:
        * if `original != 0`:
            - if `current == 0`: refund -= 15000  (cancel earlier clear)
            - if `value   == 0`: refund += 15000  (issue a fresh clear)
        * if `original == value` (slot being reset):
            - if `original == 0`:    refund += 19800  (`sSetRefund`)
            - if `original != 0`:    refund += 4800   (`sResetRefund`)

  ## Refund-counter clamping
  The on-chain refund counter is unsigned (a `Nat`). EIP-1283 emits
  negative deltas (the "cancel earlier clear" branch) but guarantees
  the running total can't go below 0 if the earlier credit was issued
  in the same transaction. We mirror the implementation's clamp at 0.

  ## What this relation does NOT cover
  * EIP-1706 stipend trip-wire — a Petersburg / Istanbul-era addition,
    NOT shipped in Constantinople-with-1283. Omitted.
  * EIP-214 static-context check — covered by the implementation but
    not lifted into this relation; once the static check fails the
    handler raises, so this relation only describes the *successful*
    branch. (Frontier's `IsSstoreStep` does the same.)
-/

import Evm.Frontier.Vm
import Evm.Frontier.State
import Evm.Frontier.Spec.StepShapes
import Evm.Constantinople.Vm.Gas

namespace Evm.Constantinople.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-- Signed-counter add over `Nat`, clamping at 0 on underflow.
    EIP-1283 issues then occasionally cancels 15000-gas refunds. -/
private def adjustRefund (n : Nat) (delta : Int) : Nat :=
  if delta ≥ 0 then n + delta.toNat
  else
    let sub := (-delta).toNat
    if n ≥ sub then n - sub else 0

/-- 0x55 SSTORE under EIP-1283 (Constantinople flavour).

    Pre-conditions:
      * `evm.stack = key :: value :: rest`
      * `evm.message.isStatic = false` (the EIP-214 check; not
        lifted into the relation directly — see file docstring)
      * `evm.gasLeft ≥ cost`, where `cost` is determined by the
        EIP-1283 decision tree below.

    Post-state:
      * stack popped twice, gas charged, storage updated, refund
        counter adjusted (clamped at 0), pc advanced by 1.

    See file docstring for the full nine-case branching. -/
def IsSstoreStep (evm evm' : Evm) : Prop :=
  ∃ key value rest,
    evm.stack = key :: value :: rest ∧
    evm.message.isStatic = false ∧
    let addr     := evm.message.currentTarget
    let current  := evm.env.state.getStorage addr key
    let original := evm.env.originalState.getStorage addr key
    let cost : Nat :=
      if current = value then
        Evm.Constantinople.Vm.Gas.sLoadGas
      else
        if original = current then
          if original = (0 : Evm.U256) then Gas.sSet else Gas.sReset
        else
          Evm.Constantinople.Vm.Gas.sLoadGas
    let refundDelta : Int :=
      if current = value then 0
      else
        if original = current then
          -- Clean slot branch.
          if original ≠ (0 : Evm.U256) ∧ value = (0 : Evm.U256) then
            (Gas.sClearRefund : Int)
          else 0
        else
          -- Dirty slot branch: two independent adjustments.
          let dCancelOrIssue : Int :=
            if original ≠ (0 : Evm.U256) then
              (if current = (0 : Evm.U256)
                  then -(Gas.sClearRefund : Int) else 0) +
              (if value = (0 : Evm.U256)
                  then (Gas.sClearRefund : Int) else 0)
            else 0
          let dResetToOrig : Int :=
            if original = value then
              if original = (0 : Evm.U256)
                then (Evm.Constantinople.Vm.Gas.sSetRefund : Int)
                else (Evm.Constantinople.Vm.Gas.sResetRefund : Int)
            else 0
          dCancelOrIssue + dResetToOrig
    evm.gasLeft ≥ cost ∧
    evm' = { evm with
      stack   := rest,
      gasLeft := evm.gasLeft - cost,
      env     := { evm.env with
        state         := evm.env.state.setStorage addr key value,
        refundCounter := adjustRefund evm.env.refundCounter refundDelta },
      pc      := evm.pc + 1 }

end Evm.Constantinople.Spec
