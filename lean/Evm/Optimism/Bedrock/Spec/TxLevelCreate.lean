/-
  Evm.Optimism.Bedrock.Spec.TxLevelCreate — gas obligations for a
  tx-level (tx.to = none) CREATE in the OP user-tx pipeline.

  This file pins TWO impl invariants that bit us empirically:

  1. `IsCodeDepositCharged` — when the constructor RETURNs runtime
     code, the per-byte deposit (`Gas.codeDeposit = 200`) is paid
     from the sub-EVM's `gasLeft`. The Cancun trampoline `.createLike`
     branch charges this for opcode-level CREATE; the OP tx-level
     pipeline must do the same. Caught by tx 48 of Base 0x2c98e00,
     where omission left every tx-CREATE 200 * runtime_size short
     on receipt gas.

  2. `IsInitCodePreserved` — when a tx-level CREATE invokes
     `applyMessage`, the message's `code` (the init bytecode) must
     NOT be overwritten by `resolveDelegation`'s output. The
     about-to-be-created address has empty code in state, so a
     delegation lookup would return `(empty, false)`, and an
     unconditional `msg.code := lookup_result` clobbers the
     constructor with empty bytes. The fix is to only override
     msg.code when a delegation actually fires; preserved here
     as the spec contract.

  EELS reference:
    * Code deposit: `forks/frontier/vm/__init__.py::process_create_message`
      around the end-of-execution `if charge_gas(...)` block.
    * Init-code preservation: implicit in EELS — `process_create_message`
      sets `message.code = code` (the init code) and never calls
      anything resembling `resolveDelegation` on it. Our Prague impl
      added a delegation-aware applyMessage wrapper for CALL flows,
      and getting the conditional wrong leaked into CREATE.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Gas
import Evm.Prague.Spec.SetCodeStep

namespace Evm.Optimism.Bedrock.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm (Message)

/-! ## (1) Code deposit charging on success

    On a successful constructor RETURN that yields `output` bytes,
    the sub-frame's remaining gas must cover
    `Gas.codeDeposit * output.size` (= 200 * size).
    On insufficient gas, the entire CREATE is treated as failure
    (no code is deployed, sender gets the result-0 stack push). -/

/-- The deposit cost. EELS `GAS_CODE_DEPOSIT = 200`. -/
def codeDepositPerByte : Nat := Evm.Frontier.Vm.Gas.codeDeposit

/-- The deposit gas required to deploy `runtime` bytes of code. -/
def codeDepositCost (runtime : Evm.Bytes) : Nat :=
  codeDepositPerByte * runtime.size

/-- Successful CREATE charges the deposit and deploys the code. -/
def IsCodeDepositCharged
    (gasBefore gasAfter : Nat) (runtime : Evm.Bytes) : Prop :=
  let cost := codeDepositCost runtime
  gasBefore ≥ cost ∧ gasAfter = gasBefore - cost

/-- CREATE failure when the sub-frame can't afford the deposit:
    no code is deployed, gas is consumed entirely. -/
def IsCodeDepositInsufficient
    (gasBefore : Nat) (runtime : Evm.Bytes) : Prop :=
  gasBefore < codeDepositCost runtime

theorem codeDepositPerByte_eq : codeDepositPerByte = 200 := rfl

/-! ## (2) Init-code preservation through resolveDelegation

    When the tx-level CREATE path constructs the top-level message,
    `msg.code = tx.data` (the constructor bytecode). The applyMessage
    wrapper must NOT overwrite `msg.code` with the result of
    `resolveDelegation` against `msg.target` (the not-yet-created
    address). Specifically, `resolveDelegation` returns `(target.code,
    false)` for a non-delegation target, and a buggy "always set
    msg.code := resolved" would replace the constructor bytecode
    with empty bytes, deploying an empty contract.

    The condition: a CREATE message's code is preserved iff the
    target's code is NOT a delegation designator (the only case
    where overwriting is legitimate). -/

def IsInitCodePreserved
    (state : State) (msg msgOut : Message) : Prop :=
  match msg.target with
  | none => msgOut = msg
  | some t =>
    let acc := state.getAccount t
    if Evm.Prague.Spec.isDelegationDesignator acc.code then
      -- Genuine delegation; msg.code must be the delegated code.
      let d := Evm.Prague.Spec.parseDelegated acc.code
      msgOut.code = (state.getAccount d).code
    else
      -- No delegation; msg.code must be PRESERVED (not clobbered
      -- to acc.code, which would zero out a tx-CREATE's init bytes).
      msgOut.code = msg.code

end Evm.Optimism.Bedrock.Spec
