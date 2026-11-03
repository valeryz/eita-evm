import Evm.CL.EffectIR

/-! # CL/EffectTx — `apply-tx`, derived (docs/effect-layer-derivation.md §4.10)

A transaction's effect up to the end of its message, as one `EffectIR` term for every fork,
proved in `Evm.CL.EffectTxProof` against `Evm.Frontier.Vm.Tx` (every fork's
`processTransaction` is `Tx.run`) and emitted as `spec-tx-effect`. The settlement and the
end of tx after it are the derived terms of stage 2 (`EffectSettle`, `EffectEndTx`); the
wrapper (`run-evm-tx`) runs the four in the order `Tx.finish` does, and `apply_tx_refines`
is about that sequence.

**What is the wrapper's part.** The byte counts of the data and the access list's sizes
(the seam the emitted `spec-intrinsic-gas` / `spec-calldata-floor-gas` read), the effective
gas price (`spec-effective-gas-price` for type 2 and later), the creation's address
(`derive-create-address`, the seam = `computeContractAddress`), the blob hashes' version
byte, and after the term the gas used (`spec-tx-gas-used`), the settlement and the end of
tx. Everything else is the term:

* the validation (`Tx.invalid`, rule by rule in its order): a broken rule is a `reject`
  with the rule's number, nothing else happens;
* the upfront charge: the nonce, then the gas at the effective price, the blob fee (EIP-4844)
  and a chain's extra (OP's L1 fee; 0 on Ethereum);
* the accessed sets (EIP-2929/2930/3651);
* from Prague the authorization list (EIP-7702 `set_delegation`, one `forAuths` body) and
  the target's delegation;
* the snapshot, then inside the observed top call frame: a creation's collision rule, its
  world (storage wiped, created mark, nonce 1, existence, the value) and init frame and the
  code deposit; a call's world (existence before EIP-161, the value), the fork's precompile
  at the target or the frame, EIP-161's touch on success;
* a failure rolls back to the snapshot; the gas the message used is the term's charge.

An OP deposit (`checked` off) skips the validation. A system call is its own term
(`Evm.CL.EffectSystem`: no validation, no charge, the chain rule's warm-up) over the same
delegation and message (`delegS`, `messageS`). -/

namespace Evm.CL.EffectTx

open Evm.CL.EffectIR

abbrev sender   : AExp := .var "sender"
abbrev target   : AExp := .var "target"
abbrev coinbase : AExp := .var "coinbase"
abbrev dlg      : AExp := .var "deleg"
abbrev au       : AExp := .var "authority"
abbrev value    : WExp := .var "value"
abbrev gasLimit : GExp := .var "gas-limit"

/-- The message's gas: the limit less the intrinsic gas. -/
def gas : GExp := .sub gasLimit (.var "intrinsic")

/-- The tx type is `n`. -/
def isType (n : Nat) : BExp := .and (.ge "type" n) (.not (.ge "type" (n + 1)))

/-- EIP-4844 blob gas. -/
def blobGas : GExp := .mul (.lit 131072) (.var "blob-count")

/-- `check_transaction`'s `max_gas_fee` with the value (and a chain's extra). -/
def maxCost : GExp :=
  .add (.add (.ite (.ge "type" 2) (.mul gasLimit (.var "max-fee")) (.mul gasLimit (.var "gas-price")))
             (.ite (isType 3) (.mul blobGas (.var "max-fee-blob")) (.lit 0)))
       (.add (.ofWord value) (.var "extra"))

/-- The upfront charge: the gas at the effective price, the blob fee (Cancun), a chain's extra. -/
def upfront : GExp :=
  .add (.add (.mul gasLimit (.var "egp")) (.ite (.forkGe 16) (.mul blobGas (.var "blob-base-fee")) (.lit 0)))
       (.var "extra")

/-- `max(intrinsic, floor)`: what `validate_transaction` requires of the gas limit (the floor
    is 0 before Prague). -/
def required : GExp := .add (.var "intrinsic") (.sub (.var "floor") (.var "intrinsic"))

/-- A tx type the fork does not decode (EIP-2718: 1 Berlin, 2 London, 3 Cancun, 4 Prague). -/
def badType : BExp :=
  .or (.and (.ge "type" 1) (.not (.forkGe 10))) <|
  .or (.and (.ge "type" 2) (.not (.forkGe 11))) <|
  .or (.and (.ge "type" 3) (.not (.forkGe 16))) <|
  .or (.and (.ge "type" 4) (.not (.forkGe 17))) (.ge "type" 5)

/-- The rules, in `Tx.invalid`'s order (the comparisons bound by `compares`). -/
def rules : List BExp :=
  [ badType,
    .var "lt-gas",
    .and (.forkGe 15) (.and (.var "create") (.var "big-init")),
    .not (.var "nonce-ok"),
    .and (.forkGe 18) (.var "big-gas"),
    .and (.ge "type" 2) (.var "lt-prio"),
    .and (.ge "type" 2) (.var "lt-mf"),
    .and (.not (.ge "type" 2)) (.var "lt-gp"),
    .and (isType 3) (.not (.ge "blob-count" 1)),
    .and (isType 3) (.and (.forkGe 18) (.var "many-blobs")),
    .and (isType 3) (.not (.var "blob-version-ok")),
    .and (isType 3) (.var "lt-mfb"),
    .and (.or (isType 3) (isType 4)) (.var "create"),
    .and (isType 4) (.not (.ge "auth-count" 1)),
    .or (.var "n-lo") (.var "n-hi"),
    .var "poor",
    .and (.not (.codeEmpty sender)) (.not (.and (.var "prague") (.delegated sender))) ]

/-- The numeric comparisons the rules read, on the world before the tx. -/
def compares (k : Stmt) : Stmt :=
  .letLt "lt-gas" gasLimit required <|
  .letLt "big-init" (.lit 49152) (.var "data-len") <|
  .letLt "nonce-ok" (.var "tx-nonce") (.lit (2 ^ 64 - 1)) <|
  .letLt "big-gas" (.lit 16777216) gasLimit <|
  .letLt "lt-prio" (.var "max-fee") (.var "max-prio") <|
  .letLt "lt-mf" (.var "max-fee") (.var "base-fee") <|
  .letLt "lt-gp" (.var "gas-price") (.var "base-fee") <|
  .letLt "many-blobs" (.lit 6) (.var "blob-count") <|
  .letLt "lt-mfb" (.var "max-fee-blob") (.var "blob-base-fee") <|
  .letLt "n-lo" (.nonce sender) (.var "tx-nonce") <|
  .letLt "n-hi" (.var "tx-nonce") (.nonce sender) <|
  .letLt "poor" (.ofWord (.balance sender)) maxCost k

/-- Reject on the first of `ps` broken (numbered from `n`), else `k`. -/
def validateFrom (n : Nat) : List BExp → Stmt → Stmt
  | [], k => k
  | p :: ps, k => .ite (.and (.var "checked") p) (.reject n) (validateFrom (n + 1) ps k)

/-- Reject on the first rule broken (numbered from 1, `Tx.rules`' order), else `k`. -/
def validate (k : Stmt) : Stmt := validateFrom 1 rules k

/-- `secp256k1n`. -/
def secpN : Nat := Evm.Frontier.Vm.Tx.secp256k1n

/-- One authorization (`set_delegation`'s loop body, `Tx.authorize`): the chain id, the nonce
    bound, the signature's scalars, the authority — warmed —, its code (none or a designator),
    its nonce; then the refund when it exists, the designator, the nonce. -/
def authBody : Stmt :=
  .ite (.not (.or (.weq (.var "a-chain") (.var "chain-id")) (.weq (.var "a-chain") .zero))) .skip <|
  .iteG (.var "a-nonce") (.lit (2 ^ 64 - 1))
    (.ite (.and (.wlt (.var "a-yp") (.lit 2)) <| .and (.pos (.var "a-r")) <|
           .and (.wlt (.var "a-r") (.lit secpN)) <| .and (.pos (.var "a-s"))
                (.not (.wlt (.lit (secpN / 2)) (.var "a-s"))))
      (.recoverAuth "authority" .skip <|
        .warm (.lit true) au "acold" <|
        .seq (.fault au) <|
        .ite (.and (.not (.codeEmpty au)) (.not (.delegated au))) .skip <|
        .ite (.nonceIs au "a-nonce")
          (.seq (.ite (.present au) (.refund (.lit 12500)) .skip) <|
           .seq (.setDelegation au (.var "a-addr")) (.bumpNonce au))
          .skip)
      .skip)
    .skip

/-- The value moves (a non-zero one): the sender's balance down, the target's up, the tx-level
    transfer fact. -/
def transfer : Stmt :=
  .ite (.pos value)
    (.seq (.setBalance sender (.sub (.balance sender) value)) <|
     .seq (.credit target value) (.transferFact 0 sender target value)) .skip

/-- What the message used when its frame hands back `r`. -/
def used : GExp := .sub gas (.childGas "r")

/-- The code deposit of the init frame's output. -/
def deposit : GExp := .formula1 "spec-code-deposit-gas" GasEmit.codeDepositGas "nbytes" (.childLen "r")

/-- A failure that loses the whole gas: back to the snapshot. -/
def fail0 : Stmt := .seq (.rollback "snap") (.seq (.charge gas) (.ret .zero))

/-- A creation that succeeds: the code, the gas used with the deposit. -/
def succeed : Stmt :=
  .seq (.depositCode target "r") (.seq (.charge (.add used deposit)) (.ret (.lit 1)))

/-- `process_create_message`'s end (`Tx.createEnd`). -/
def createEnd : Stmt :=
  .ite (.childErr "r") fail0 <|
  .ite (.childRev "r") (.seq (.rollback "snap") (.seq (.charge used) (.ret .zero))) <|
  .ite (.and (.forkGe 11) (.childEF "r")) fail0 <|                       -- EIP-3541
  .iteG (.childGas "r") deposit
    (.ite (.forkGe 1) fail0 (.seq (.charge used) (.ret (.lit 1)))) <|      -- EIP-2
  .ite (.forkGe 4) (.iteG (.lit Evm.SpuriousDragon.Vm.Gas.maxCodeSize) (.childLen "r") fail0 succeed)
    succeed                                                               -- EIP-170

/-- A creating tx (`Tx.create`): the collision rule, (Arc's veto), the child's world, the init
    frame. -/
def createPath : Stmt :=
  .ite (.collides target) (.seq (.charge gas) (.ret .zero)) <|
  .chainTxVeto sender target value (.ret .zero) <|
  .seq (.wipeStorage target) <| .seq (.markCreated target) <|
  .seq (.ite (.forkGe 4) (.bumpNonce target) .skip) <| .seq (.markPresent target) <|
  .seq transfer <|
  .runTx gas "r" createEnd

/-- `process_message`'s end at the top (`Tx.call`'s match). -/
def callEnd : Stmt :=
  .ite (.childErr "r") fail0 <|
  .ite (.childRev "r") (.seq (.rollback "snap") (.seq (.charge used) (.ret .zero))) <|
  .seq (.ite (.and (.present target) (.dead target)) (.touch target) .skip) <|
  .seq (.charge used) (.ret (.lit 1))

/-- A call (`Tx.call` after the delegation): existence before EIP-161, (Arc's veto), the
    value, (a chain precompile — Arc —), the fork's precompile at the target unless EIP-7702
    disabled them, or the frame. -/
def callPath : Stmt :=
  .seq (.ite (.forkGe 4) .skip (.markPresent target)) <|
  .chainTxVeto sender target value (.seq (.rollback "snap") (.ret .zero)) <|
  .seq transfer <|
  .chainTxCall target gas "snap" <|
  .ite (.and (.not (.var "hasdeleg")) (.pre target))
    (.runPreTx target gas "r" callEnd)
    (.runTx gas "r" callEnd)

/-- The upfront charge: the nonce, then the balance. -/
def chargeS : Stmt := .seq (.bumpNonce sender) (.debit sender upfront)

/-- The accessed sets (Berlin+). -/
def warmS : Stmt := .warmTx (.forkGe 10) sender target coinbase

/-- From Prague, a call's authorization list. -/
def authsS : Stmt := .ite (.and (.var "prague") (.not (.var "create"))) (.forAuths authBody) .skip

/-- From Prague, a call's target's delegation: the delegate loaded and warmed. -/
def delegS (rest : Stmt) : Stmt :=
  .letDeleg "deleg" "hasdeleg" (.and (.var "prague") (.not (.var "create"))) target <|
  .seq (.ite (.var "hasdeleg") (.fault dlg) .skip) <|
  .warm (.var "hasdeleg") dlg "dcold" rest

/-- The message: the snapshot, then in the observed top frame the creation or the call. -/
def messageS : Stmt := .save "snap" <| .txRow gas (.ite (.var "create") createPath callPath)

/-- After the validation: the charge, the accessed sets, the authorizations, the delegation,
    the message. -/
def main : Stmt := .seq chargeS <| .seq warmS <| .seq authsS <| delegS messageS

/-- The tx's effect. Inputs: the addresses (`sender`, `target` — `tx.to` or the creation's
    address —, `coinbase`), the flags (`create`, `checked`, `prague` — EIP-7702 on
    —, `blob-version-ok`), the value, the numbers (`gas-limit`, `intrinsic`, `floor`, `egp`,
    `extra`, `type`, `tx-nonce`, the fee fields, `base-fee`, `blob-count`, `blob-base-fee`,
    `auth-count`, `data-len`), `chain-id`, the access list, the authorization list, the data,
    the block context (for the frame); returns the gas the message used, the success flag,
    the rejection. -/
def term : Stmt :=
  .seq (.fault sender) <| .seq (.fault target) <|
  compares (validate main)

def params : List String :=
  ["sender", "target", "coinbase", "create", "checked", "prague", "blob-version-ok",
   "value", "gas-limit", "intrinsic", "floor", "egp", "extra", "type", "tx-nonce", "max-fee",
   "max-prio", "gas-price", "base-fee", "blob-count", "max-fee-blob", "blob-base-fee",
   "auth-count", "data-len", "chain-id", "access-list", "auth-list", "data", "block-ctx"]

def termCL : String := Stmt.toDefunTx "spec-tx-effect" params term

end Evm.CL.EffectTx
