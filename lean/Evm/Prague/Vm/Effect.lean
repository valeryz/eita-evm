/-
  Evm.Prague.Vm.Effect — call-frame execution dispatcher.

  EELS reference: ethereum/forks/prague/vm/interpreter.py
  (`process_message_call` / `process_message`).

  This module is the boundary between the Prague `State` (extended with
  transient storage, created-accounts, warm/cold sets) and the
  byte-by-byte interpreter. Two responsibilities:

    1. Handle EIP-7702 delegation when CALLing into an EOA whose code
       is the designator `0xef0100 || delegated_address`. The semantics
       (EIP-7702 §"Behavior"): the EVM loads `delegated_address`'s code
       but runs it in the EOA's storage / balance context. Concretely
       — for the call frame:
           message.code           := getAccount(delegated).code
           message.currentTarget  := original_target  (= the EOA)
       Gas charged for the delegation lookup: one warm/cold access of
       `delegated` per the EIP-2929 rules.

    2. Delegate the actual interpreter loop to **Cancun's** effect
       interpreter, threaded over the `inner` Frontier state. Cancun
       transitively pulls in Shanghai (PUSH0, EIP-3860), Paris
       (PREVRANDAO), Berlin (EIP-2929 warm/cold), Istanbul (EIP-2200
       SSTORE, BLAKE2F), and Constantinople (SHL/SHR/SAR, CREATE2,
       EXTCODEHASH). Plus Cancun's own TLOAD/TSTORE/MCOPY/BLOBHASH/
       BLOBBASEFEE and EIP-6780 SELFDESTRUCT.

  Rebased on Cancun 2026-05-29 (was Byzantium-direct). Prague-
  specific opcode additions (EIP-2935 BLOCKHASH-from-history,
  EIP-7702 set-code) are handled here in `applyMessage` and the
  Prague Fork driver; the inner Cancun interpreter handles the rest.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Effect
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Cancun.Vm.Effect
import Evm.Prague.State
import Evm.Prague.Vm.PrecompiledContracts

namespace Evm.Prague.Vm.Effect

open Evm.Frontier.Vm (Message Environment Evm Exception)

/-- Resolve an EIP-7702 delegation, if `target`'s account has one.

    Returns `(code, isDelegated)`:
      * If `target.code` is a 23-byte `0xef0100 || addr` designator,
        returns the delegated address's code (read fresh from state)
        and `true`.
      * Otherwise returns `target`'s own code and `false`.

    EELS: `process_message` in
    `ethereum/forks/prague/vm/interpreter.py` resolves designators
    by reading the delegated address's code and substituting into
    `message.code` before launching the interpreter. -/
def resolveDelegation (state : Evm.Prague.State) (target : Evm.Address) :
    Evm.Bytes × Bool :=
  let acc := state.getAccount target
  match Evm.Prague.State.parseDelegation acc.code with
  | some delegated =>
    let delegatedAcc := state.getAccount delegated
    (delegatedAcc.code, true)
  | none =>
    (acc.code, false)

/-- Run one message call through the Prague effect interpreter.

    Implementation: rewrite the message's code in the presence of an
    EIP-7702 delegation, then route into the Byzantium interpreter
    over the wrapped Frontier state. The Prague-specific extensions
    (transient storage, created_accounts, warm/cold sets) are passed
    through unchanged — the Byzantium interpreter doesn't touch them,
    so legacy / access-list txs behave correctly, and set-code-tx
    execution sees its delegated code as if it were the EOA's
    in-line code (which is the EIP-7702 semantics). -/
def applyMessage (msg : Message) (env : Environment)
    (pstate : Evm.Prague.State)
    (precompileLookup : Evm.Address →
        Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
      Evm.Frontier.Vm.Call.precompiles 17) :
    Except Exception Evm × Evm.Prague.State :=
  -- (1) Delegation lookup using the Prague state (the `inner` env.state
  -- only tracks accounts/storage; delegation lives in `account.code`
  -- already, so both views agree). If a delegation is in effect,
  -- pre-warm the delegated address in `env.accessedAddresses` so a
  -- subsequent CALL to the same target sees it warm (op-geth's
  -- behaviour: the top-level apply warms the delegated target).
  let (resolved, env) :=
    match msg.target with
    | some t =>
      let (code, isDeleg) := resolveDelegation pstate t
      -- ONLY override msg.code when a delegation actually fires.
      -- Otherwise leave the caller-supplied code intact — critical
      -- for tx-level CREATE, where msg.target is the about-to-be-
      -- created address (empty code) and msg.code carries the init
      -- bytecode. Without this guard we'd overwrite the init code
      -- with empty and the constructor would run as a no-op.
      let msg' := if isDeleg then { msg with code := code } else msg
      let env' :=
        if isDeleg then
          match Evm.Prague.State.parseDelegation (pstate.getAccount t).code with
          | some delegated =>
            if env.accessedAddresses.contains delegated then env
            else { env with accessedAddresses := env.accessedAddresses ++ [delegated] }
          | none => env
        else env
      (msg', env')
    | none => (msg, env)
  -- (2) Threaded run through Cancun's effect. We use `env.state`
  -- (= Frontier.State) directly; Prague-only fields ride along.
  -- Cancun transitively gives us all post-Byzantium opcodes.
  let r := Evm.Cancun.Vm.Effect.applyMessageWith precompileLookup resolved env
  -- (3) Re-bundle the post-state. Whether the inner frame succeeded
  -- or failed, the Prague extensions remain — modulo a tx-end reset
  -- handled by the fork's processTransaction.
  let pstate' :=
    match r with
    | .ok subEvm => { pstate with inner := subEvm.env.state }
    | .error _   => pstate
  (r, pstate')

end Evm.Prague.Vm.Effect
