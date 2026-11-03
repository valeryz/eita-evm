import Evm.CL.EffectIR

/-! # CL/EffectEndTx — the end of a tx, derived (docs/effect-layer-derivation.md §7.2)

After the fee settlement, EELS `process_transaction` destroys the accounts_to_delete — on
every fork; before Cancun every first SELFDESTRUCT puts its account there, from Cancun
only an account created in the same tx (EIP-6780, decided by `spec-selfdestruct-effect`)
— and, from Spurious Dragon, the touched accounts left empty (EIP-161,
`destroy_touched_empty_accounts`). `endTx_refines` (`Evm.CL.EffectEndTxProof`) proves the
two terms in sequence equal every fork's `destroyAccounts` / `finishTx`, and that the
order a hash set is walked in does not matter (`destroy_perm`, `sweep_perm`).

Emitted as `spec-destroy-effect` and `spec-sweep-effect` (src/generated/host.lisp);
the tx drivers (`run-evm-tx`, the fixture runner, OP deposits) call both after the
settlement, the system calls the sweep only (EELS system txs destroy nothing). -/

namespace Evm.CL.EffectEndTx

open Evm.CL.EffectIR

abbrev acct : AExp := .var "a"

/-- EELS `for address in accounts_to_delete: destroy_account`. -/
def destroyTerm : Stmt := .forEach .destroyed "a" (.deleteAccount acct)

/-- EIP-161 (Spurious Dragon+): destroy every touched account that is dead. The spec's
    condition is "exists and empty"; destroying an absent account changes nothing in a
    state where only existing accounts carry storage (`endTx_refines`'s `hwf`), so the
    CL asks only emptiness — one predicate, no existence read. -/
def sweepTerm : Stmt :=
  .ite (.forkGe 4) (.forEach .touched "a" (.ite (.dead acct) (.deleteAccount acct) .skip)) .skip

/-- The end of a user tx: what `run-evm-tx` runs after the settlement. -/
def endTx : Stmt := .seq destroyTerm sweepTerm

def destroyCL : String := Stmt.toDefun "spec-destroy-effect" [] destroyTerm
def sweepCL : String := Stmt.toDefun "spec-sweep-effect" [] sweepTerm

end Evm.CL.EffectEndTx
