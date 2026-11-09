/-
  Evm.Optimism.Isthmus.Spec.Soundness — explicit obligations the
  Isthmus executable must satisfy. Anything still `sorry` is a
  KNOWN gap, surfaced loudly so the build emits a warning until
  closed.

  Reflects the no-silent-gaps rule: divergences are either fixed,
  made unrepresentable, or stated here as `sorry` lemmas. Do NOT
  leave a divergence only in a code comment.
-/

import Evm.Optimism.Isthmus.Fork
import Evm.Prague.State
import Evm.Prague.Vm.Effect

namespace Evm.Optimism.Isthmus.Spec.Soundness

open Evm.Frontier.Vm (Message Environment Evm Exception)

/-! ## Prague applyMessage adapter

    `Isthmus.Fork.isthmusApplyMessage` runs each message on a FRESH
    `Prague.State` whose `inner` is `env.state`, and discards the
    returned Prague state. That is sound because `Prague.Vm.Effect.
    applyMessage`'s `Evm` result reads its Prague state only through
    `inner` (`resolveDelegation` → `State.getAccount` = `inner.getAccount`):
    the scratch maps (`transientStorage`, `createdAccounts`,
    `accessedAddresses`, `accessedKeys`) never reach the result. -/

set_option backward.isDefEq.respectTransparency false in
/-- `applyMessage`'s result depends on the Prague state only through
    `inner`. -/
theorem pragueApplyMessage_depends_only_on_inner
    (msg : Message) (env : Environment) (p q : Evm.Prague.State)
    (lookup : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (h : p.inner = q.inner) :
    (Evm.Prague.Vm.Effect.applyMessage msg env p lookup).1
      = (Evm.Prague.Vm.Effect.applyMessage msg env q lookup).1 := by
  simp only [Evm.Prague.Vm.Effect.applyMessage, Evm.Prague.Vm.Effect.resolveDelegation,
    Evm.Prague.State.getAccount, h]

/-- **The per-message wrap is sound**: running a message on the fresh
    `{ inner := env.state }` the Isthmus adapter builds gives the same
    result as running it on ANY Prague state that agrees with the
    message's world (`p.inner = env.state`), whatever its scratch maps. -/
theorem pragueApplyMessage_adapter_sound_for_delegation
    (msg : Message) (env : Environment) (p : Evm.Prague.State)
    (lookup : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (h : p.inner = env.state) :
    (Evm.Prague.Vm.Effect.applyMessage msg env { inner := env.state } lookup).1
      = (Evm.Prague.Vm.Effect.applyMessage msg env p lookup).1 :=
  pragueApplyMessage_depends_only_on_inner msg env _ p lookup h.symm

/-! ## EIP-7702 authorization-list processing (TRUE GAP)

    Prague set-code (type-4) transactions carry an `authorization_list`
    that, at tx ENTRY, must:
      (a) recover each authorization's signer (ECDSA over the
          authorization tuple),
      (b) bump that signer's nonce,
      (c) write the EIP-7702 delegation prefix
          (`0xef0100 || delegated_address`) into the signer's
          `account.code`,
      (d) pre-warm the signer's address.

    Our `Bedrock.UserTxInputs` does NOT carry an authorization list —
    so the OP user-tx processor at Isthmus cannot apply these steps.
    Type-4 txs that DEPEND on a same-tx-installed delegation will see
    the original (delegation-less) code at `target.code` and either
    fail or succeed-wrongly.

    Closing this gap requires extending `UserTxInputs` with an
    optional `authList : List Authorization`, replicating EELS's
    `apply_authorizations` at tx entry, then running the rest of the
    tx through the existing adapter. -/
/-! DISCHARGED by construction, not by a theorem: the
    `Evm.Optimism.Bedrock.OpTx.userWithAuths` constructor takes the
    authorization list as an argument (a set-code tx cannot be built
    without it), `Isthmus.Fork.applyBlock`'s `go` hands it to
    `processUserTx (auths := auths)`, and the pre-Isthmus driver
    (`Bedrock.applyAll`) refuses the variant with an explicit error.
    `applyAll` is `private partial`, so the refusal cannot be stated as a
    theorem here. (Until 2026-11-02 a theorem `eip7702_auth_list_processed`
    "pinned" this; its statement — `∃ tx, tx = .userWithAuths u auths` —
    was true of any constructor and said nothing about the drivers.) -/

end Evm.Optimism.Isthmus.Spec.Soundness
