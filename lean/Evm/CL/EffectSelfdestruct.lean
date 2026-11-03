import Evm.CL.EffectIR

/-! # CL/EffectSelfdestruct — `cb-selfdestruct`, derived (docs/effect-layer-derivation.md §4)

The SELFDESTRUCT host callback as one `EffectIR` term for every fork — proved in
`Evm.CL.EffectSelfdestructProof` (`selfdestruct_refines`) against the fork handlers the IR
trampoline binds (`Terminator.handler` before Cancun, Cancun's
`doSelfdestruct` yield + `runYieldOf` from Cancun on), and its emitted CL
(`spec-selfdestruct-effect`, src/generated/host.lisp).

**What is the callback's part.** The native SELFDESTRUCT handler pops the beneficiary,
raises EIP-214's static-context violation (Byzantium+, before any gas — `StaticGuard`),
charges the fork's base cost (0 to Homestead, 5000 from Tangerine Whistle: `baseGas`),
calls the callback, charges what it returns, and halts the frame. The callback does
everything else: the EIP-161 touch, the EIP-2929 warm-up, the new-account decision, the
destroyed-set mark and its refund, the balance move, the pre-Spurious existence of the
beneficiary, and returns cold + new-account gas. A chain override (Arc's
`*chain-selfdestruct-hook*`, `Evm.Arc.Spec.NativeCoin.runSelfdestructCheck`) runs in the
hand-written wrapper before it and is outside this theorem. Deletion itself happens at tx
end (`spec-destroy-effect`, `Evm.CL.EffectEndTx`; EELS `process_transaction`) — not here, on any fork.

**Out-of-gas.** The spec charges before the effects; the native handler charges the
returned gas after them. When the charge fails the frame halts exceptionally and its
journal is unwound (every write the term makes is journaled), so the state is the spec's;
`selfdestruct_refines` states the gas side of both outcomes exactly. -/

namespace Evm.CL.EffectSelfdestruct

open Evm.CL.EffectIR
open Evm.Frontier.Vm (Environment Evm)

abbrev self : AExp := .var "self"
abbrev ben  : AExp := .var "beneficiary"
abbrev bal  : WExp := .var "bal"

/-- The new-account surcharge (25000), fork-staged: none before Tangerine Whistle (Frontier
    SELFDESTRUCT costs GAS_ZERO); an ABSENT beneficiary at Tangerine Whistle (`not
    account_exists`, emptiness alone does not trigger it); from Spurious Dragon (EIP-161)
    a dead beneficiary and a non-zero balance moving. Replaces HostEmit's
    `selfdestructNewAccount` predicates. -/
def newAccount : BExp :=
  .or (.and (.forkGe 3) (.and (.not (.forkGe 4)) (.not (.present ben))))
      (.and (.forkGe 4) (.and (.pos bal) (.dead ben)))

/-- The callback. Inputs `self` (the executing account) and `beneficiary`; returns the gas
    beyond the native base. -/
def term : Stmt :=
  .letW "bal" (.balance self) <|
  .seq (.fault ben) <|
  .seq (.touch ben) <|                                         -- EIP-161 (SD+)
  .warm (.forkGe 10) ben "cold" <|                             -- EIP-2929 (Berlin+)
  .letB "new-acct" newAccount <|
  -- accounts_to_delete: every first SELFDESTRUCT before Cancun; from Cancun (EIP-6780)
  -- only an account created in this tx. The first mark earns the refund (24000 before
  -- London, 0 after: EIP-3529).
  .seq (.ite (.and (.or (.not (.forkGe 16)) (.created self)) (.not (.destroyed self)))
          (.seq (.markDestroyed self)
                (.refund (.formula1 "spec-selfdestruct-refund" GasEmit.selfdestructRefund
                                    "fork-ord" .forkOrd)))
          .skip) <|
  -- Credit the beneficiary, then zero the originator: a self-beneficiary burns the
  -- balance — always before Cancun, from Cancun only when created in this tx (otherwise
  -- move_ether to itself keeps it).
  .seq (.ite (.and (.pos bal) (.or (.not (.addrEq self ben))
                                   (.or (.not (.forkGe 16)) (.created self))))
          (.seq (.ite (.not (.addrEq self ben)) (.credit ben bal) .skip)
            (.seq (.setBalance self .zero)
                  (.transferFact 3 self ben bal)))
          .skip) <|
  -- Before Spurious Dragon the credit brings the beneficiary into existence even at 0 wei.
  .seq (.ite (.and (.not (.forkGe 4)) (.not (.addrEq self ben))) (.markPresent ben) .skip) <|
  .charge (.add (.formula1 "spec-selfdestruct-cold-gas" GasEmit.selfdestructColdGas
                           "cold" (.ofBool (.var "cold")))
                (.ite (.var "new-acct") (.formula0 "spec-new-account-fee" GasEmit.newAccountFee)
                      (.lit 0)))

/-- The emitted CL. -/
def termCL : String := Stmt.toDefun "spec-selfdestruct-effect" ["self", "beneficiary"] term

end Evm.CL.EffectSelfdestruct
