/-
  Evm.Homestead.Spec.CreateStep — EIP-2 (Homestead) CREATE delta.

  EELS reference: `ethereum/forks/homestead/vm/interpreter.py`
  `process_create_message`, specifically the post-init-code branch
  where the deployed-code deposit cost is charged:

      contract_code_gas = len(output) * 200
      try:
          charge_gas(evm, contract_code_gas)
      except ExceptionalHalt:
          # HOMESTEAD CHANGE (EIP-2): the entire CREATE reverts.
          restore_tx_state(...)
          push 0
          ...

  Frontier behaviour (now overridden): on insufficient deposit gas,
  Frontier left an *empty-coded* contract in place and the parent's
  CREATE pushed the new address. EIP-2 turns the same condition into
  a hard revert: state changes from the init-code roll back, the
  sender's nonce bump survives (it was applied pre-init by
  `create`), the parent's CREATE pushes 0, and the parent KEEPS the
  forwarded gas as if it had been fully consumed.

  This is mirrored in `Evm.Frontier.Vm.Create.resume` (`Rules.homestead`):
    * Frontier: failed deposit ⇒ keep account (no code), refund
      `subEvm.gasLeft` to parent.
    * Homestead: failed deposit ⇒ DON'T merge state, push 0, do NOT
      refund leftover sub-gas.

  Per the SPEC-METHODOLOGY: this is a *state-machine delta* that is
  best stated as a relation over the post-sub-frame merge step
  rather than the on-frame opcode step. The relation describes the
  parent-frame transition `parent → parent'` given the sub-frame's
  outcome (`subEvm`).
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.CallStep  -- shares the SubFrameSetup language

namespace Evm.Homestead.Spec

open Evm.Frontier (Account)
open Evm.Frontier.Vm

/-! ## Helper: the EIP-2 deposit-gas predicate

    `depositCost = Gas.codeDeposit * |subEvm.output|`. The EIP-2
    revert condition is `subEvm.gasLeft < depositCost` AND the
    sub-frame did NOT itself revert (a sub-frame REVERT is handled by
    `resumeCallRevert`; the "deposit-fail" path is reachable only on
    a successfully halted init-code run). -/

/-- The deposit gas EIP-2 charges for the bytes the init code
    produced. Plain integer multiplication of `Gas.codeDeposit = 200`
    and the deployed-code length. -/
def depositCost (output : Evm.Bytes) : Nat :=
  Gas.codeDeposit * output.size

/-! ## IsCreateDepositRevert — the new revert path

    Inputs:
      * `parent` — the frame that issued CREATE, at the moment the
        sub-frame returns (gas already pre-charged, sub-frame's
        halted output known).
      * `subEvm` — the successfully-halted (not reverted) init-code
        frame. Importantly, `subEvm.env.state` carries the
        sender-nonce bump applied at CREATE-yield time.
      * `sender` — the CREATE-issuing account (the contract running
        CREATE; equal to `parent.message.currentTarget`).
      * `senderAccNonce` — sender's nonce captured at yield time.
      * `gasLeft`, `mem`, `s`, `pc` — the parent-side artefacts the
        trampoline carries through the yield/resume cycle.

    Post-state (`parent'`): push 0, restore returnData, drop init-
    code state mutations from `subEvm.env` BUT keep the sender-nonce
    bump (mirror what EELS does). Forwarded gas is consumed.

    The nonce-bump-persistence is the load-bearing detail that was
    missing from this spec until 2026-05-30. It came from the
    stCreate2/Create2OOGafterInitCode_* corpus: even on deposit
    OOG, EELS keeps the sender's nonce one higher than at CREATE
    entry. Implementations MUST mirror this — otherwise the same
    sender can re-issue CREATE2 at the same derived address and
    silently overwrite the failed-deploy attempt.

    EELS clause: `forks/homestead/vm/interpreter.py` lines
    around `charge_gas(evm, contract_code_gas)` (post-EIP-2 wrap),
    and `vm/__init__.py` `incorporate_child_on_error`'s use as the
    rollback path. -/
def IsCreateDepositRevert (parent subEvm : Evm) (sender : Evm.Address)
                          (senderAccNonce : Nat)
                          (gasLeft : Nat) (mem : Memory)
                          (s : Stack) (pc : Nat) (parent' : Evm) : Prop :=
  ¬ subEvm.reverted ∧
  subEvm.halted ∧
  subEvm.gasLeft < depositCost subEvm.output ∧
  s.length < stackLimit ∧
  -- Surgically rebuild parent.env.state with ONLY the sender nonce
  -- bump merged from the sub-frame; everything else (account
  -- creation, init-code SSTOREs, etc.) is discarded.
  let senderAcc := parent.env.state.getAccount sender
  let stateAfterNonceBump :=
    parent.env.state.setAccount sender
      { senderAcc with nonce := senderAccNonce + 1 }
  parent' = { parent with
    env         := { parent.env with state := stateAfterNonceBump },
    gasLeft     := gasLeft,
    memory      := mem,
    stack       := (0 : Evm.U256) :: s,
    returnData  := Evm.Bytes.empty,
    pc          := pc + 1 }

/-! ## IsCreateDepositOk — the deposit-succeeds path

    Same shape as Frontier's success branch but with the EIP-2
    framing made explicit: deposit cost is paid, the sub-frame's
    output becomes the new contract's code, gas remaining after
    deposit is refunded. -/
def IsCreateDepositOk (parent subEvm : Evm) (newAddr : Evm.Address)
                      (gasLeft : Nat) (mem : Memory)
                      (s : Stack) (pc : Nat) (parent' : Evm) : Prop :=
  ¬ subEvm.reverted ∧
  subEvm.halted ∧
  subEvm.gasLeft ≥ depositCost subEvm.output ∧
  s.length < stackLimit ∧
  let depositedState :=
    subEvm.env.state.setAccount newAddr
      { (subEvm.env.state.getAccount newAddr) with code := subEvm.output }
  parent' = { parent with
    env         := { subEvm.env with state := depositedState },
    gasLeft     := gasLeft + (subEvm.gasLeft - depositCost subEvm.output),
    memory      := mem,
    stack       := (Evm.U256.ofNat newAddr.toNat) :: s,
    returnData  := Evm.Bytes.empty,
    pc          := pc + 1 }

/-! ## Notes

    - These two predicates together cover the "init code halted
      cleanly" branch of the CREATE post-merge. The other two
      branches (sub-frame REVERTed; sub-frame errored) are inherited
      unchanged from Frontier: EIP-2 only changes the deposit-fail
      path, not the init-code-revert or init-code-error paths.

    - The `subEvm.reverted = false` clause distinguishes this from
      EIP-140 REVERT. A reverted sub-frame returns to a different
      resume path (`resumeCallRevert`-shaped), not this one.

    - The implementation in `Evm.Frontier.Vm.Create.resume`
      collapses both `IsCreateDepositRevert` and `IsCreateDepositOk`
      into a single `if subEvm.gasLeft < depositCost then ...`
      branch. The spec splits them so refinement obligations are
      stated per-branch. -/

end Evm.Homestead.Spec
