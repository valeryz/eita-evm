/-
  Evm.Frontier.Vm.Instructions.Storage — opcodes 0x54 SLOAD, 0x55 SSTORE.

  EELS reference: ethereum/frontier/vm/instructions/storage.py.

  Frontier SSTORE schedule (pre-EIP-1283 / EIP-2200 / EIP-2929):
    - 20000 gas if writing non-zero to a previously-zero slot
    - 5000 gas otherwise
    - +15000 refund if clearing a non-zero slot to zero
  SLOAD costs 50 gas (raised to 200 at TangerineWhistle / 800 cold at Berlin).

  Storage is read/written against `evm.message.currentTarget`, which is
  the running contract (differs from `target` for CALLCODE).
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier
open Evm.Frontier.Vm

/-- 0x54 SLOAD -/
def sload : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Gas.sLoad
  let (key, s) ← Stack.pop evm.stack
  let value := evm.env.state.getStorage evm.message.currentTarget key
  let s ← Stack.push s value
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- Pure Frontier SSTORE gas + refund: `(cost, newRefundCounter)`.
    The legacy schedule depends only on `(current, new)` — there is
    no notion of the tx-entry "original" value before EIP-1283.
    EELS `ethereum/frontier/vm/instructions/storage.py` `sstore`. -/
def sstoreGas (refund : Nat) (current new_ : Evm.U256) : Nat × Nat :=
  ( if current = (0 : Evm.U256) ∧ new_ ≠ (0 : Evm.U256) then Gas.sSet
    else Gas.sReset,
    if current ≠ (0 : Evm.U256) ∧ new_ = (0 : Evm.U256) then
      refund + Gas.sClearRefund
    else refund )

/-- 0x55 SSTORE -/
def sstore : Handler := fun evm => do
  -- EIP-214 (Byzantium+): SSTORE is forbidden in a static context.
  if evm.message.isStatic then
    .error .writeInStaticContext
  let (key, value, s) ← Stack.pop2 evm.stack
  let addr := evm.message.currentTarget
  let current := evm.env.state.getStorage addr key
  let (cost, refundCounter) := sstoreGas evm.env.refundCounter current value
  let gasLeft ← Gas.charge evm.gasLeft cost
  let state := evm.env.state.setStorage addr key value
  return { evm with
    gasLeft := gasLeft, stack := s,
    env := { evm.env with state := state, refundCounter := refundCounter },
    pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
