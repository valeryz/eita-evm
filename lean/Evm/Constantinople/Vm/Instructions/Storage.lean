/-
  Evm.Constantinople.Vm.Instructions.Storage — EIP-1283 net SSTORE gas
  metering.

  EELS reference: ethereum/forks/constantinople/vm/instructions/storage.py
  (current master collapses Constantinople and Petersburg into a single
  reduced model; this implementation follows the *original* EIP-1283
  specification at
  https://eips.ethereum.org/EIPS/eip-1283 — Constantinople shipped
  EIP-1283 net metering, which Petersburg later reverted).

  Three storage values participate:
    * `original` — slot value at the start of the *transaction*. Read
      from `evm.env.originalState`, which is captured by the tx-level
      `processTransaction`.
    * `current`  — slot value just before this SSTORE. Read from the
      live `evm.env.state`.
    * `value`    — the new value to write (top of stack).

  Gas / refund decision tree (per EIP-1283 §Specification):

    1. current == value  (no-op)         ⇒ 200 gas
    2. current != value
       a. original == current            (slot is "fresh"/clean)
          - original == 0                ⇒ 20000 gas
          - original != 0                ⇒ 5000 gas
                                            + 15000 refund if value=0
       b. original != current            (slot is "dirty")
                                         ⇒ 200 gas, with refund adjust:
          - if original != 0:
              if current == 0            ⇒ refund -= 15000
                                            (we previously refunded for
                                             clearing; that's now wrong)
              if value    == 0           ⇒ refund += 15000
          - if original == value        (slot is being reset)
              if original == 0           ⇒ refund += 19800
              else                       ⇒ refund += 4800

  EIP-1706 (the SSTORE-stipend guard introduced together with EIP-2200)
  does NOT apply here: EIP-1706 was a Petersburg-era fix. Constantinople
  shipped without it. We omit it from this implementation.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Constantinople.Vm.Gas

namespace Evm.Constantinople.Vm.Instructions

open Evm.Frontier
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- Pure EIP-1283 SSTORE gas + refund: `(cost, newRefundCounter)`.
    The refund delta is computed as one signed sum and clamped at 0
    once — Constantinople's own discipline (Istanbul's EIP-2200
    clamps per step instead). -/
def sstoreGas (refund : Nat) (original current value : Evm.U256) :
    Nat × Nat :=
  let (cost, refundDelta) : Nat × Int :=
    if current = value then
      -- No-op.
      (Evm.Constantinople.Vm.Gas.sLoadGas, 0)
    else
      -- current != value
      if original = current then
        -- Fresh slot.
        if original = (0 : Evm.U256) then
          (Gas.sSet, 0)
        else
          let r : Int :=
            if value = (0 : Evm.U256)
              then (Gas.sClearRefund : Int)
              else 0
          (Gas.sReset, r)
      else
        -- Dirty slot: base cost is 200 gas, plus refund bookkeeping.
        let r1 : Int :=
          if original ≠ (0 : Evm.U256) then
            -- Cancel a previously-issued clear refund if `current = 0`
            -- (we previously gave back 15000 for clearing it, but now
            -- it's being changed back to non-zero, so reclaim that).
            (if current = (0 : Evm.U256)
                then -(Gas.sClearRefund : Int) else 0) +
            -- Issue a clear refund if `value = 0` (we're now clearing
            -- it to zero).
            (if value = (0 : Evm.U256)
                then (Gas.sClearRefund : Int) else 0)
          else 0
        let r2 : Int :=
          if original = value then
            -- The slot is being reset to its tx-entry value: refund
            -- the difference between the "fresh" charge and the 200
            -- dirty re-charge that's being applied right now.
            if original = (0 : Evm.U256)
              then (Evm.Constantinople.Vm.Gas.sSetRefund : Int)
              else (Evm.Constantinople.Vm.Gas.sResetRefund : Int)
          else 0
        (Evm.Constantinople.Vm.Gas.sLoadGas, r1 + r2)
  -- Refund counter is `Nat`. EIP-1283 §Specification guarantees the
  -- counter never goes below 0 at the tx level, but at a per-frame
  -- level the *delta* can be negative (a dirty re-write that cancels
  -- a prior refund). We clamp at 0 here — same as EELS, which uses an
  -- unsigned counter and depends on the proof that the negative
  -- excursion never exceeds the current refund balance.
  let newRefund : Int := (refund : Int) + refundDelta
  (cost, if newRefund < 0 then 0 else newRefund.toNat)

/-- 0x55 SSTORE — Constantinople net metering (EIP-1283).

    EELS reference: the canonical clause-by-clause translation of
    EIP-1283's §Specification (lines 56-77 of the EIP). The current
    EELS master `forks/constantinople/vm/instructions/storage.py`
    does NOT implement EIP-1283 because Constantinople was reverted
    on mainnet; we restore the original Constantinople semantics
    here so that the Constantinople test corpus exercises the
    intended behaviour. Petersburg overrides this with the simpler
    pre-1283 schedule. -/
def sstore : Handler := fun evm => do
  -- EIP-214 (Byzantium+): SSTORE is forbidden in a static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (key, value, s) ← Stack.pop2 evm.stack
  let addr     := evm.message.currentTarget
  let current  := evm.env.state.getStorage addr key
  let original := evm.env.originalState.getStorage addr key
  let (cost, refundCounter) :=
    sstoreGas evm.env.refundCounter original current value
  let gasLeft ← Gas.charge evm.gasLeft cost
  let state := evm.env.state.setStorage addr key value
  return { evm with
    gasLeft := gasLeft, stack := s,
    env := { evm.env with state := state, refundCounter := refundCounter },
    pc := evm.pc + 1 }

end Evm.Constantinople.Vm.Instructions
