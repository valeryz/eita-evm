import Evm.CL.EffectIR

/-! # CL/EffectCreate — `cb-create`, derived (docs/effect-layer-derivation.md §4.6)

The CREATE/CREATE2 host callback as one `EffectIR` term for every fork, proved in
`Evm.CL.EffectCreateProof` (`create_refines`) against every fork's CREATE — the one
definition `Evm.Frontier.Vm.Create.run` that each fork's `doCreate`/`doCreate2` and
`.createLike` arm are (`create_binding`) — and emitted as `spec-create-effect`.

**What is the callback's part.** The native CREATE/CREATE2 handler pops the value, the
init-code range (and CREATE2's salt), raises EIP-214's static violation (Byzantium+),
charges the memory expansion of the init-code range, copies the init code, and calls the
callback with the gas left (`gas`). The wrapper (`cb-create`) derives the address — from
the creator's nonce (CREATE) or from the salt and the init code's hash (CREATE2,
EIP-1014) — and the opcode's own charge (`base`, `spec-create-gas`: GAS_CREATE, EIP-3860's
word cost, CREATE2's hashing cost) and EIP-3860's cap (`oversize`,
`spec-create-initcode-oversize`). Everything else is the term, which returns the gas used,
the pushed word and the return data:

* the charge (`gas < base`: out of gas) and EIP-3860's cap (out of gas: one more gas than
  the frame holds);
* the fail-fast — depth limit, balance below the value, nonce 2^64 − 1 — charging only the
  base;
* EIP-2929's warm-up of the new address (Berlin+), the collision rule (code, nonce —
  EIP-684; EIP-7610 is not applied), the creator's nonce bump; these survive everything below;
* on collision, the forwarded gas is lost;
* the child's world: any storage wiped (EELS `destroy_storage`), created mark (EIP-6780),
  nonce 1 (EIP-161), existence, the value
  (Arc's chain rule may veto here; not Ethereum, outside the theorem);
* the child run (`runChild`, the seam: the native interpreter on the init code with the
  forwarded gas — EIP-150's 63/64 — inside the observed call frame);
* its end: an exceptional halt or a REVERT rolls the child back (a REVERT returns its gas
  and output); EIP-3541's 0xEF prefix, the code deposit (Frontier keeps the creation
  without code, later forks fail it) and EIP-170's size fail it; otherwise the code is
  deposited and the address pushed. -/

namespace Evm.CL.EffectCreate

open Evm.CL.EffectIR

abbrev self  : AExp := .var "self"
abbrev new   : AExp := .var "new"
abbrev value : WExp := .var "value"
abbrev gas   : GExp := .var "gas"
abbrev base  : GExp := .var "base"

/-- The gas the child gets (EIP-150 from Tangerine Whistle). -/
def fwd : GExp := .formulaF "spec-retain-63-64" GasEmit.retain63of64 "gas" (.sub gas base)

/-- The code deposit of the child's output. -/
def deposit : GExp := .formula1 "spec-code-deposit-gas" GasEmit.codeDepositGas "nbytes" (.childLen "r")

/-- The creation fails after the child ran: nothing of the child stays, the forwarded gas
    is gone, 0 is pushed. -/
def fail : Stmt := .seq (.rollback "snap") (.seq (.charge (.add base fwd)) (.ret .zero))

/-- The creation succeeds: deposit the code, charge the base, the gas the child used and
    the deposit, push the address. -/
def succeed : Stmt :=
  .seq (.depositCode new "r") <|
  .seq (.charge (.add base (.add (.sub fwd (.childGas "r")) deposit))) (.ret (.ofAddr new))

/-- The end of the child run `r`. -/
def finish : Stmt :=
  .ite (.childErr "r") fail <|
  .ite (.childRev "r")
    (.seq (.rollback "snap") <| .seq (.charge (.add base (.sub fwd (.childGas "r")))) <|
      .seq (.retData "r") (.ret .zero)) <|
  .ite (.and (.forkGe 11) (.childEF "r")) fail <|                       -- EIP-3541
  .iteG (.childGas "r") deposit
    (.ite (.forkGe 1) fail                                               -- EIP-2
      (.seq (.charge (.add base (.sub fwd (.childGas "r")))) (.ret (.ofAddr new)))) <|
  .ite (.forkGe 4)                                                       -- EIP-170
    (.iteG (.lit Evm.SpuriousDragon.Vm.Gas.maxCodeSize) (.childLen "r") fail succeed)
    succeed

/-- The value moves (a non-zero one): the creator's balance down, the new account's up, a
    transfer fact (at the child's depth). -/
def transfer : Stmt :=
  .ite (.pos value)
    (.seq (.setBalance self (.sub (.balance self) value)) <|
     .seq (.credit new value) (.transferFact 2 self new value true)) .skip

/-- The init frame, inside its observed call frame, and its end. -/
def runInit : Stmt := .frameRow self new value fwd base <| .runChild self new value fwd "r" finish

/-- No collision: the child's world (any storage wiped — EELS `destroy_storage` —, created
    mark — EIP-6780 —, nonce 1 — EIP-161 —, existence, the value; Arc's chain rule may veto
    here), then the init frame. -/
def proceed : Stmt :=
  .seq (.wipeStorage new) <|
  .seq (.markCreated new) <|
  .seq (.ite (.forkGe 4) (.bumpNonce new) .skip) <|
  .seq (.markPresent new) <|
  .ite (.and (.pos value) (.chainVeto self new value))
    (.seq (.rollback "snap") (.seq (.charge base) (.ret .zero))) <|
  .seq transfer runInit

/-- After the creator's nonce bump: everything from here may be rolled back to it. -/
def afterBump : Stmt :=
  .save "snap" <|
  .ite (.var "coll") (.seq (.charge (.add base fwd)) (.ret .zero)) proceed   -- collision

/-- Past the charge and the fail-fast: EIP-2929's warm-up (it stays whatever happens next),
    the collision test, the creator's nonce bump. -/
def afterFailFast : Stmt :=
  .warm (.forkGe 10) new "cold" <|
  .letB "coll" (.collides new) <|
  .seq (.bumpNonce self) afterBump

/-- The callback. Inputs: `self` (the creator), `new` (the address), `value`, `gas` (left
    after the memory charge), `base`, `deep` (depth limit reached), `oversize` (EIP-3860);
    returns the gas used, the pushed word, the return data. -/
def term : Stmt :=
  .seq (.fault self) <| .seq (.fault new) <|
  .iteG gas base (.seq (.charge base) (.ret .zero)) <|                   -- caller out of gas
  .ite (.var "oversize") (.seq (.charge (.add gas (.lit 1))) (.ret .zero)) <|
  .ite (.or (.var "deep") (.or (.wlt (.balance self) value) (.nonceMax self)))
    (.seq (.charge base) (.ret .zero)) <|                                -- fail-fast
  afterFailFast

def params : List String := ["self", "new", "value", "gas", "base", "deep", "oversize", "kind", "init-code"]

def termCL : String := Stmt.toDefunChild "spec-create-effect" params term

end Evm.CL.EffectCreate
