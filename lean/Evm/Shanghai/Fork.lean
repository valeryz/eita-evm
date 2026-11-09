/-
  Evm.Shanghai.Fork — top-level state transition for Shanghai.

  EELS reference: ethereum/forks/shanghai/fork.py.
  Activation: timestamp 1,681,338,455 (2023-04-12).

  Deltas applied here relative to the predecessor (Paris, currently a
  stub — we layer directly on Byzantium-shaped transaction processing
  with Paris's two main deltas folded in: block reward = 0 and no
  ommer reward distribution):

    * EIP-3651 (warm COINBASE): the coinbase is seeded into the
      touched-set at the start of each transaction so that any opcode
      that "accesses" the coinbase finds it pre-touched. EELS
      reference: `forks/shanghai/fork.py` line 575
      (`access_list_addresses.add(block_env.coinbase)` inside
      `process_transaction`).

      Note: this repo does not yet implement EIP-2929 warm/cold
      accounting per access-list at the opcode level; the seeding
      here is the minimum spec-fidelity move (record the address in
      the touched-set so that downstream EIP-2929 logic — when added
      — will find it warm). It is not load-bearing for any test
      currently in the Replay harness, but matches the EELS source.

    * EIP-3860 (initcode size limit and metering): tx-CREATE adds a
      per-32-byte-word surcharge to intrinsic gas of `2 * ceil(len/32)`
      and rejects transactions whose initcode exceeds
      `2 * MAX_CODE_SIZE = 49152` bytes. EELS reference:
      `forks/shanghai/transactions.py` `validate_transaction`
      lines 297-335 and `calculate_intrinsic_cost`
      lines 338-382 (specifically lines 369-370:
      `create_cost = GasCosts.TX_CREATE + init_code_cost(ulen(tx.data))`).

    * EIP-4895 (beacon-chain withdrawals): after all transactions
      have been processed, `apply_body` walks the block's
      `withdrawals` list and credits each recipient's balance by
      `amount * 10^9` wei (the amount is denominated in gwei). EELS
      reference: `forks/shanghai/fork.py` `process_withdrawals`
      lines 646-665 (especially line 663:
      `create_ether(wd_state, wd.address, wd.amount * U256(10**9))`).

    * EIP-3855 (PUSH0): handled in `Vm/Effect.lean`'s `step1`.

  Paris deltas folded in here:

    * Block reward = 0 (EIP-3675). The post-merge `apply_body` in
      EELS does NOT credit a base block reward to the coinbase;
      the coinbase only receives the priority fees (priority-fee-
      per-gas × gas-used per tx) accumulated through
      `process_transaction`. We do the same.

    * No ommer (uncle) rewards. Post-merge `apply_body` ignores the
      `block.ommers` field (validated to be empty at the consensus
      layer; `EMPTY_OMMER_HASH` is hard-coded in the header check).

    * DIFFICULTY → PREVRANDAO (EIP-4399). The opcode keeps numeric
      value 0x44; the underlying state field
      `Environment.difficulty` is reinterpreted as the PREVRANDAO
      value extracted from `header.prev_randao`. This module
      populates `Environment.difficulty` from `header.prevRandao`
      (cast to `Nat`).

  Known gaps (each will be a separate delta module when implemented):
    * EIP-1559 fee market (London): we still use a flat
      `tx.gasPrice` rather than `effective_gas_price =
      min(max_fee, max_priority_fee + base_fee)`. Mainnet replay
      will require EIP-1559 to land first.
    * Typed transactions (Berlin/EIP-2718, London/EIP-1559): the
      `Block.transactions` field carries RLP-encoded bytes per EELS,
      but our Block is wired to Frontier's plain Transaction record
      for now. The intrinsic-gas surcharge below is computed on the
      tx data we receive, which is fine for legacy txs.
    * EIP-2929 access-list-aware warm/cold accounting (Berlin).
      Without it, the EIP-3651 seed here is structural only.
-/

import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Istanbul.Fork
import Evm.London.Fork
import Evm.Shanghai.Blocks
import Evm.Shanghai.Vm.Effect

namespace Evm.Shanghai

open Evm.Frontier (State Account Transaction)
open Evm.Frontier.Vm (Log)

/-! ## EIP-3860 intrinsic gas surcharge -/

/-- Per-word init-code surcharge on the tx-CREATE intrinsic gas.
    EELS `forks/shanghai/vm/gas.py` lines 347-364 (`init_code_cost`)
    and `forks/shanghai/transactions.py` line 370
    (`create_cost = GasCosts.TX_CREATE + init_code_cost(ulen(tx.data))`).
    Constant `CODE_INIT_PER_WORD = 2` at gas.py line 55. -/
def initCodeCost (initCodeLen : Nat) : Nat :=
  2 * ((initCodeLen + 31) / 32)

/-- EIP-3860 max initcode size: `2 * MAX_CODE_SIZE = 49152`. EELS
    `forks/shanghai/vm/interpreter.py` line 63
    (`MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE`). Used by
    `validate_transaction` (transactions.py line 332). -/
def maxInitCodeSize : Nat := 2 * Evm.SpuriousDragon.Vm.Gas.maxCodeSize

/-- The block environment of a Shanghai header. -/
def blockEnv (header : Header) (blockHashes : List Evm.Hash32) : Evm.Frontier.Vm.Environment :=
  Evm.Frontier.Vm.Tx.blockEnv header.coinbase header.number 0 header.gasLimit header.timestamp
    blockHashes header.baseFeePerGas header.prevRandao

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Shanghai (fork ordinal 15: EIP-3651's warm coinbase,
    EIP-3860's init-code cap and words), with Shanghai's trampoline and precompile table. -/
def processTransaction (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) : Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 15 (blockEnv header blockHashes) state sender tx
    (Evm.Frontier.Vm.Tx.table 15) Vm.Effect.trampoline (fun _ => none)

private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    let sender ← match Evm.SpuriousDragon.Utils.recoverSender tx with
      | some s => .ok s
      | none   => .error "invalid signature"
    let r ← processTransaction state header blockHashes sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-! ## EIP-4895 withdrawals -/

/-- The block's withdrawals as (address, gwei amount), what
    `Evm.Frontier.Vm.Block.processWithdrawals` (EELS `process_withdrawals`) credits. -/
def withdrawalPairs (wds : List Withdrawal) : List (Evm.Address × Nat) :=
  wds.map fun wd => (wd.address, wd.amount)

/-! ## Block transition -/

/-- Pre-Berlin / pre-typed-transaction simplification: this Block type
    carries plain `List Transaction`-equivalent data — actually carrying
    RLP-encoded bytes per EELS — but to keep `applyBlock` typed against
    the existing Frontier-shaped tx records, we expose a sibling entry
    that takes already-decoded transactions. -/
structure DecodedBlock where
  header       : Header
  transactions : List Transaction
  ommers       : List Header           := []
  withdrawals  : List Withdrawal       := []
  deriving Inhabited

/-- Top-level state transition for a Shanghai block.

    EELS `forks/shanghai/fork.py` `apply_body` lines 469-508:

        for i, tx in enumerate(map(decode_transaction, transactions)):
            process_transaction(block_env, block_output, tx, Uint(i))
        process_withdrawals(block_env, block_output, withdrawals)

    Block reward = 0 (Paris/EIP-3675); no ommer rewards distributed
    post-merge. Coinbase only receives priority fees, accumulated by
    `processTransaction` already. -/
def applyBlock
    (state       : State)
    (block       : DecodedBlock)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  -- 1. Process transactions (priority fees credited to coinbase
  --    inside `processTransaction`; no separate block reward).
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  -- 2. EIP-4895: credit each withdrawal's recipient. EELS
  --    `process_withdrawals` (fork.py lines 646-665).
  let state := Evm.Frontier.Vm.Block.processWithdrawals 15 state (withdrawalPairs block.withdrawals)
  return { state := state, gasUsed := gasUsed, logs := logs }

/-- Drive a Shanghai block whose transactions arrive typed and paired with senders:
    `Evm.Frontier.Vm.Tx.runAll` at Shanghai, then the EIP-4895 withdrawal credits; no block
    reward (Paris, EIP-3675). -/
def applyBlockTyped
    (state         : State)
    (header        : Header)
    (txsWithSender : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address))
    (withdrawals   : List Withdrawal)
    (blockHashes   : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← Evm.Frontier.Vm.Tx.runAll 15 (blockEnv header blockHashes)
    (Evm.Frontier.Vm.Tx.table 15) Vm.Effect.trampoline (fun _ => none) state txsWithSender 0 0 []
  let state := Evm.Frontier.Vm.Block.processWithdrawals 15 state (withdrawalPairs withdrawals)
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Shanghai
