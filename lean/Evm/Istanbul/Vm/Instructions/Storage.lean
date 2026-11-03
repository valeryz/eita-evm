/-
  Evm.Istanbul.Vm.Instructions.Storage — EIP-2200 net SSTORE metering,
  EIP-1884 SLOAD reprice.

  EELS reference: `forks/istanbul/vm/instructions/storage.py`. SLOAD
  is unchanged in shape — only the gas price climbs from 200 to 800
  (`GasCosts.SLOAD`). SSTORE is the complicated one: original/current/
  new triples drive a net-metering rule with refund accounting.

  ## EIP-2200 SSTORE (line-by-line from EELS storage.py)

  ```
  if evm.gas_left <= GasCosts.CALL_STIPEND:        # 66-67
      raise OutOfGasError                          # trip-wire (EIP-1706)
  original = get_storage_original(...)             # 70-72
  current  = get_storage(...)                      # 73

  # cost branch
  if original == current and current != new:       # 75
      gas_cost = STORAGE_SET   if original == 0    # 76-77
                 COLD_STORAGE_WRITE  otherwise     # 78-79
  else:
      gas_cost = SLOAD                              # 81

  # refund branch (only if current != new)         # 84
  if original != 0 and current != 0 and new == 0:  # 85-87
      refund += REFUND_STORAGE_CLEAR
  if original != 0 and current == 0:               # 89-91
      refund -= REFUND_STORAGE_CLEAR
  if original == new:                              # 93
      if original == 0:                            # 95
          refund += STORAGE_SET - SLOAD            # 19200
      else:                                        # 100
          refund += COLD_STORAGE_WRITE - SLOAD     # 4200

  charge_gas(evm, gas_cost)                        # 106
  if evm.message.is_static: raise WIS              # 107-108
  set_storage(...)                                 # 109
  ```

  Notes / pitfalls:
    * Trip-wire is `CALL_STIPEND` (2300), NOT `SLOAD` (800). The
      project brief said 800; EELS says 2300. EIP-2200 + EIP-1706 also
      say 2300. We trust EELS.
    * The "no-op" branch (current == new) charges SLOAD whether or
      not we're on a clean slot — falls into the `else` of line 75.
    * The static-context check runs AFTER the cost charge (line 107),
      not before; this matters in edge-case fuzzing where the SSTORE
      would be priced even though it ultimately reverts. We mirror.
    * `refund` is a signed counter (EELS uses `int`). Our spec stores
      a `Nat`; we clamp at 0 on subtraction.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Istanbul.Vm.Gas

namespace Evm.Istanbul.Vm.Instructions

open Evm.Frontier
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- 0x54 SLOAD — load a storage slot. EELS `sload`. Only difference
    from earlier forks: gas is 800 (was 200 at TW). -/
def sload : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Istanbul.Vm.Gas.sLoad
  let (key, s) ← Stack.pop evm.stack
  let value := evm.env.state.getStorage evm.message.currentTarget key
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Signed-counter add over `Nat`: `n + d` clamps to 0 on underflow.
    EIP-2200 issues then reverses 15000-gas refunds, so this is the
    natural shape.

    Public because the ARM64
    emitter's denotation (`Evm.CL.ARM64.SstoreGasDenote`) has to prove the
    emitted `add` / `subs`+`csel lo` sequence implements exactly this, and the
    SEQUENTIAL clamping is the part that differs from EIP-1283. -/
def adjustRefund (n : Nat) (delta : Int) : Nat :=
  if delta ≥ 0 then n + delta.toNat
  else
    let sub := (-delta).toNat
    if n ≥ sub then n - sub else 0

/-- Pure EIP-2200 SSTORE gas + refund: `(cost, newRefundCounter)`.
    NOTE the clamp discipline: each refund adjustment is applied
    through `adjustRefund` (clamped at 0) SEQUENTIALLY — this is NOT
    equivalent to summing the deltas and clamping once (EIP-1283's
    discipline) when the counter transiently hits 0. The EIP-1706
    `gasLeft ≤ 2300` trip-wire stays in the handler — it needs
    `gasLeft`, which is not this function's business. -/
def sstoreGas (refund : Nat) (original current newValue : Evm.U256) :
    Nat × Nat :=
  -- COST BRANCH (lines 75-81).
  let gasCost : Nat :=
    if original = current ∧ current ≠ newValue then
      if original = (0 : Evm.U256) then Evm.Istanbul.Vm.Gas.sstoreSet
      else Evm.Istanbul.Vm.Gas.sstoreReset
    else
      Evm.Istanbul.Vm.Gas.sLoad

  -- REFUND BRANCH (lines 84-104): only fires when the slot value
  -- actually changes.
  let refundCounter : Nat :=
    if current ≠ newValue then
      let r0 := refund
      -- (line 85) clearing a non-zero slot to 0 for the first time
      let r1 :=
        if original ≠ (0 : Evm.U256) ∧ current ≠ (0 : Evm.U256) ∧
           newValue = (0 : Evm.U256) then
          adjustRefund r0
            (Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int)
        else r0
      -- (line 89) reversing an earlier clear (writing non-zero into a
      -- slot that was cleared earlier in this tx)
      let r2 :=
        if original ≠ (0 : Evm.U256) ∧ current = (0 : Evm.U256) then
          adjustRefund r1
            (- (Evm.Istanbul.Vm.Gas.sstoreClearRefund : Int))
        else r1
      -- (line 93) restoring the slot to its original value: take back
      -- the difference between the cost we (must have) paid earlier
      -- and the SLOAD price we're paying now.
      if original = newValue then
        if original = (0 : Evm.U256) then
          adjustRefund r2
            ((Evm.Istanbul.Vm.Gas.sstoreSet - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
        else
          adjustRefund r2
            ((Evm.Istanbul.Vm.Gas.sstoreReset - Evm.Istanbul.Vm.Gas.sLoad : Nat) : Int)
      else r2
    else refund
  (gasCost, refundCounter)

/-- 0x55 SSTORE under EIP-2200 net metering.

    EELS reference: `forks/istanbul/vm/instructions/storage.py`
    `sstore` (lines 53-112). See the module docstring for the full
    pseudocode that this body mirrors. -/
def sstore : Handler := fun evm => do
  -- STACK: pop key then new_value.
  let (key, newValue, s) ← Stack.pop2 evm.stack
  -- TRIP-WIRE (EIP-1706, line 66-67): refuse if we don't have more
  -- than the call stipend left. Runs BEFORE original/current are
  -- read.
  if evm.gasLeft ≤ Evm.Istanbul.Vm.Gas.sstoreSentryGas then
    .error .outOfGas
  let addr     := evm.message.currentTarget
  let original := evm.env.originalState.getStorage addr key
  let current  := evm.env.state.getStorage addr key
  let (gasCost, refundCounter) :=
    sstoreGas evm.env.refundCounter original current newValue

  -- Charge the gas (line 106) — must succeed; the trip-wire above
  -- guarantees `gasLeft > 2300 ≥ sLoad = 800`, so the worst case
  -- (SLOAD branch) has headroom. The 20000-gas SSTORE_SET / 5000-gas
  -- COLD_STORAGE_WRITE branches still need an explicit gas check.
  let gasLeft ← Gas.charge evm.gasLeft gasCost

  -- EIP-214 static-context check (line 107-108): runs after the
  -- gas charge, before the state mutation.
  if evm.message.isStatic then
    .error .writeInStaticContext

  let state := evm.env.state.setStorage addr key newValue
  return { evm with
    gasLeft := gasLeft, stack := s,
    env := { evm.env with state := state, refundCounter := refundCounter },
    pc := evm.pc + 1 }

end Evm.Istanbul.Vm.Instructions
