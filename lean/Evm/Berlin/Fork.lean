/-
  Evm.Berlin — typed-transaction envelope and access-list gas model.

  EELS reference: ethereum/forks/berlin/.
  Activation: block 12,244,000 (2021-04-15).

  Introduces relative to MuirGlacier (which is itself a no-op gas delta
  over Istanbul; everything below presupposes the Istanbul/Petersburg/
  Constantinople additions are present — but per the [delta-only-forks]
  rule those intermediate modules remain stubs and are inlined inside
  `Berlin.Vm.Effect.step1`'s dispatch table):

    * EIP-2565: cheaper modexp precompile (handled in the Berlin
      modexp precompile module — stubbed; not yet implemented).
    * EIP-2718: typed-transaction envelope. The `Transaction` type is
      now a sum over `legacy | accessList` (see `Berlin.Transactions`).
    * EIP-2929: warm/cold gas accounting for state-access opcodes
      (SLOAD, BALANCE, EXTCODE*, CALL family, SELFDESTRUCT beneficiary)
      and an additional cold surcharge on SSTORE. Tracking via two
      new transaction-scoped sets on `Environment`:
        `accessedAddresses`, `accessedStorageKeys`.
    * EIP-2930: optional access list in the type-1 transaction. Entries
      pay an intrinsic-gas surcharge but pre-warm the listed `(address,
      slot)` pairs so subsequent in-tx accesses get the warm price.

  This module ports the EELS Berlin `process_transaction` flow:

    EELS reference (per knowledge — fetch was blocked in this env):
    `forks/berlin/fork.py` `process_transaction`:
      1. validate (same as Istanbul; intrinsic gas includes access list)
      2. increment_nonce + charge upfront
      3. initialize `accessed_addresses` with sender, tx.to, precompiles
         (0x01..0x09) and (for type-1 txs) the access list
      4. initialize `accessed_storage_keys` from the access list
      5. process_message_call
      6. compute refund (cap = gas_used / 2 — London EIP-3529 changes
         this to /5; we keep /2 here)
      7. refund unused gas + pay miner
      8. destroy self-destructed accounts
      9. EIP-161 sweep of touched empties

  Block reward is 2 ETH per Constantinople EIP-1234 (which Berlin
  inherits). EELS Berlin: `BLOCK_REWARD = 2 * 10**18`, paid by
  `Evm.Frontier.Vm.Block.payRewards`.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Vm.Interpreter
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Berlin.Transactions
import Evm.Berlin.Vm.Gas
import Evm.Berlin.Vm.Effect

namespace Evm.Berlin

open Evm.Frontier (State Account Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Berlin (fork ordinal 10: EIP-2929's accessed sets,
    EIP-2930's access list), with Berlin's trampoline and precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 10
    (Evm.Frontier.Vm.Tx.blockEnv coinbase number difficulty gasLimit timestamp blockHashes)
    state sender (Evm.Frontier.Vm.Tx.ofBerlin tx)
    (Evm.Frontier.Vm.Tx.table 10) Vm.Effect.trampoline (fun _ => none)

private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    -- Recover sender. We only have the SpuriousDragon ecrecover wired
    -- up for legacy transactions; access-list transactions need their
    -- own EIP-2930 signing-hash construction (sign(keccak(0x01 ||
    -- rlp(chainId, nonce, gasPrice, gas, to, value, data, accessList)))).
    -- That signing flow is NOT implemented here yet; we forward legacy
    -- variants through the existing recoverSender and reject type-1
    -- with a clear error.
    let sender ← match tx with
      | .legacy legacy =>
        match Evm.SpuriousDragon.Utils.recoverSender legacy with
        | some s => .ok s
        | none   => .error "invalid signature"
      | .accessList _ =>
        .error "access-list tx sender recovery not yet implemented"
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              sender tx
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Berlin block driver. `Block.transactions` carries legacy-only
    `Evm.Frontier.Transaction` for now; each is wrapped as
    `Transaction.legacy` here. Use `applyBlockTyped` to handle
    typed (EIP-2930+) transactions. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let berlinTxs : List Transaction := block.transactions.map Transaction.legacy
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    berlinTxs 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 10 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

/-- Block driver for typed transactions. Each tuple is `(tx, sender)`;
    the sender comes from the harness (test JSON's `sender` field) for
    EIP-2930 type-1 txs since their signing-hash construction isn't
    in our `recoverSender` yet. -/
def applyBlockTyped
    (state         : State)
    (header        : Header)
    (ommers        : List Header)
    (txsWithSender : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address))
    (blockHashes   : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← Evm.Frontier.Vm.Tx.runAll 10
    (Evm.Frontier.Vm.Tx.blockEnv header.coinbase header.number header.difficulty header.gasLimit
      header.timestamp blockHashes)
    (Evm.Frontier.Vm.Tx.table 10) Vm.Effect.trampoline (fun _ => none) state txsWithSender 0 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 10 state header.coinbase header.number
    (ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Berlin
