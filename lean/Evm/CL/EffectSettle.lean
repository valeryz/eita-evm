import Evm.CL.EffectIR

/-! # CL/EffectSettle — the tx fee settlement, derived (docs/effect-layer-derivation.md §7.1)

After the message runs and the refund cap / calldata floor fix `gas-used`
(`spec-tx-gas-used`), EELS `process_transaction` settles the fee:

1. the sender gets its unused gas back: `(gas-limit − gas-used) × effective gas price`;
2. the coinbase gets the priority fee: `gas-used × (effective gas price − base fee)` —
   the base fee (London+, EIP-1559) is burned by not being credited anywhere, as is the
   blob fee (Cancun+, EIP-4844), which was debited upfront with the gas and is no part of
   either credit;
3. from Spurious Dragon a zero fee neither creates an empty coinbase nor keeps one
   (`SpuriousDragon.payCoinbase`); before it the zero credit creates the account. The
   spec asks "exists and empty"; the term asks "dead" (absent or empty) — destroying an
   absent account changes nothing where only existing accounts carry storage (`WF`), and
   it is the predicate the end-of-tx sweep uses (`EffectEndTx`).

Both credits are DELTAS (`Stmt.delta`): they read nothing, so a parallel executor need
not validate them (`Evm.Parallel.Reads`). The only reads are the EIP-161 existence and
emptiness of the coinbase, and only when the fee is zero — logged and validated like any
read. `settle_refines` (`Evm.CL.EffectSettleProof`) proves the two terms in sequence equal
every fork's `settleFees`.

Emitted as two defuns (src/generated/host.lisp), called in this order by
`run-evm-tx`: `spec-gas-refund-effect` and `spec-coinbase-fee-effect` — the second is the
default `*chain-fee-hook*`; a chain hook (OP's fee vaults) replaces only it, Arc calls it
with a zero base fee (Arc does not burn). -/

namespace Evm.CL.EffectSettle

open Evm.CL.EffectIR

abbrev sender   : AExp := .var "sender"
abbrev coinbase : AExp := .var "coinbase"
abbrev gasLimit : WExp := .var "gas-limit"
abbrev gasUsed  : WExp := .var "gas-used"
abbrev egp      : WExp := .var "egp"
abbrev baseFee  : WExp := .var "base-fee"
abbrev fee      : WExp := .var "fee"

/-- The sender's refund of its unused gas. -/
def refundTerm : Stmt := .delta sender (.mul (.sub gasLimit gasUsed) egp)

/-- The coinbase's fee: a delta; when it is zero, the EIP-161 rule (Spurious Dragon+:
    destroy an existing empty coinbase) or the pre-Spurious creation of the coinbase. -/
def coinbaseTerm : Stmt :=
  .seq (.fault coinbase) <|
  .letW "fee" (.mul gasUsed (.sub egp baseFee)) <|
  .seq (.delta coinbase fee) <|
  .ite (.not (.pos fee))
    (.ite (.forkGe 4)
      (.ite (.dead coinbase) (.deleteAccount coinbase) .skip)
      (.markPresent coinbase))
    .skip

/-- The whole settlement: what `run-evm-tx` runs (the two defuns, in order). -/
def settle : Stmt := .seq refundTerm coinbaseTerm

def refundCL : String :=
  Stmt.toDefun "spec-gas-refund-effect" ["sender", "gas-limit", "gas-used", "egp"] refundTerm
def coinbaseCL : String :=
  Stmt.toDefun "spec-coinbase-fee-effect" ["coinbase", "gas-used", "egp", "base-fee"] coinbaseTerm

end Evm.CL.EffectSettle
