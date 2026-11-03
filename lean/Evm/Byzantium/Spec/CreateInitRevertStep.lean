/-
  Evm.Byzantium.Spec.CreateInitRevertStep — REVERT inside CREATE / CREATE2
  init code.

  EELS reference: `forks/byzantium/vm/__init__.py::process_create_message`
  + `vm/instructions/system.py::revert` interaction. The condition is
  `child_evm.reverted` at the post-init-code dispatch site.

  Byzantium introduces EIP-140 REVERT. When REVERT fires INSIDE a
  CREATE/CREATE2 init code, the parent frame's resume path needs
  semantics that combine three distinct properties:

    * Don't deploy. The bytes the init code RETURNed (well, REVERTed)
      are NOT deposited as the new contract's code.
    * Refund unused gas. Unlike a hard CREATE error which consumes
      all forwarded gas, REVERT preserves `subEvm.gasLeft` and gives
      it back to the parent.
    * Preserve returndata. The parent's `RETURNDATASIZE` /
      `RETURNDATACOPY` see the REVERT payload (this is how Solidity
      reads `revert("reason")` messages).
    * Keep sender nonce bump. Per EIP-2 (revised), the nonce bump
      that the trampoline applied BEFORE running init code persists
      across the REVERT. Otherwise the same caller could re-issue
      CREATE/CREATE2 at the same derived address.
    * Discard init-code state mutations. SSTOREs / sub-calls /
      account creations performed inside the init code roll back.
      Only the sender's nonce bump survives.

  This spec was missing until 2026-05-30. Found via:
    stCreate2/RevertOpcodeCreate_*
    stCreate2/RevertOpcodeInCreateReturnsCreate2_*
    stCreate2/returndatacopy_following_revert_in_create_*

  Before the fix, our implementation treated REVERT as a normal CREATE
  success and either attempted to deposit the REVERT data as code or
  fell into the deposit-OOG branch — losing both the nonce bump and
  the returndata.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.CallStep  -- shares the SubFrameSetup language
import Evm.Homestead.Spec.CreateStep  -- depositCost, stackLimit

namespace Evm.Byzantium.Spec

open Evm.Frontier (Account)
open Evm.Frontier.Vm
open Evm.Homestead.Spec (depositCost)

/-- REVERT inside init code: refund unused gas, preserve returndata,
    keep sender nonce bump, drop init-code state mutations.

    Inputs mirror `Homestead.Spec.IsCreateDepositRevert` but with a
    `subEvm.reverted = true` precondition (vs the deposit-OOG path
    which assumes `subEvm.reverted = false ∧ subEvm.halted = true ∧
    gas < depositCost`).

    The `subEvm.output` field carries the REVERT payload (set by
    `Evm.Byzantium.Vm.Instructions.System.revert` from `mem[off,
    off+len)` before halting).

    Implementation reference: each post-Byzantium fork's trampoline
    `createLike` branch checks `subFinal.reverted` BEFORE the
    deposit-OOG check; otherwise the deposit branch fires on the
    revert payload bytes. -/
def IsCreateInitRevert (parent subEvm : Evm) (sender : Evm.Address)
                       (senderAccNonce : Nat)
                       (gasLeft : Nat) (mem : Memory)
                       (s : Stack) (pc : Nat) (parent' : Evm) : Prop :=
  subEvm.reverted ∧
  s.length < stackLimit ∧
  let senderAcc := parent.env.state.getAccount sender
  let stateAfterNonceBump :=
    parent.env.state.setAccount sender
      { senderAcc with nonce := senderAccNonce + 1 }
  parent' = { parent with
    env         := { parent.env with state := stateAfterNonceBump },
    gasLeft     := gasLeft + subEvm.gasLeft,     -- REFUND unused gas
    memory      := mem,
    stack       := (0 : Evm.U256) :: s,
    returnData  := subEvm.output,                -- PRESERVE REVERT data
    pc          := pc + 1 }

/-! ## Notes

    - Distinct from `Homestead.Spec.IsCreateDepositRevert`:
      * `reverted = true` (vs `false ∧ halted`)
      * Gas REFUNDED (vs CONSUMED)
      * `returnData = subEvm.output` (vs `Bytes.empty`)
      * Shared: nonce bump preserved; state mutations discarded.

    - Distinct from a hard CREATE error (sub-frame raised
      `OutOfGasError` etc.): a hard error consumes all forwarded gas
      AND nukes returndata. EELS keeps the nonce bump in both cases.

    - The relation does NOT depend on CREATE vs CREATE2 — both share
      the same post-init-code resume path. Constantinople's CREATE2
      reuses this predicate. -/

end Evm.Byzantium.Spec
