/-
  Evm.Paris — The Merge (proof-of-stake transition).

  EELS reference: ethereum/forks/paris/. Activation on mainnet:
  block 15,537,393 / timestamp 1,663,224,162 / TTD 58_750_000_000_000_000_000_000
  (2022-09-15). For replay we key off block number (see Forks.lean).

  EIPs introduced relative to Gray Glacier:

    * EIP-3675 ("Upgrade consensus to proof-of-stake"). At the
      execution-layer level this is *almost entirely subtractive*:
        - Block reward = 0. Validators are paid on the consensus
          layer; the EL no longer credits the coinbase with a base
          block reward.
        - Ommers (uncles) are eliminated. `block.ommers` MUST be
          empty (`()` in EELS Python). EELS `forks/paris/fork.py`
          `state_transition` line 159: `if block.ommers != (): raise
          InvalidBlock`.
        - `header.difficulty` must equal `0`; `header.nonce` must be
          eight zero bytes; `header.ommers_hash` must equal
          `keccak256(rlp.encode([]))` (the empty-ommers hash). EELS
          `validate_header` lines 330–335.
        - `header.mix_digest` is renamed `prev_randao` and carries a
          beacon-chain random value (32 bytes).
        - No more uncle inclusion bonus, no more uncle-coinbase
          reward.

    * EIP-4399 (companion). The EVM opcode 0x44 (was DIFFICULTY) is
      renamed PREVRANDAO and pushes `block_env.prev_randao` instead
      of `block_env.difficulty`. Gas cost is unchanged (base = 2).
      Implemented in `Evm.Paris.Vm.Effect`.

  Block validity rules from EELS `validate_header`
  (`forks/paris/fork.py` lines 308–339) tighten beyond the EIP-3675
  list: `extra_data ≤ 32 bytes`, `gas_used ≤ gas_limit`, parent-hash
  chain check, monotone timestamp, sequential block number. The
  replay harness already filters / supplies well-formed blocks, so
  we enforce only the Merge-distinctive checks below (ommers empty,
  difficulty == 0, nonce all-zero, ommersHash == EMPTY_OMMER_HASH).

  Everything below the block-level — transaction processing, message
  calls, intrinsic gas, EIP-161 sweep, refund cap (still 1/2 here;
  drops to 1/5 at London proper / EIP-3529) — is identical to the
  Byzantium pipeline routed through London.
-/

import Evm.Frontier.Vm.Create
import Evm.London.Fork
import Evm.Byzantium.Fork
import Evm.Paris.Vm.Effect

namespace Evm.Paris

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log Message Environment Evm)

/-! ## EIP-3675 block-level constants -/

/-- Hash of `rlp.encode([])` — the canonical empty-ommers hash that a
    valid post-Merge header MUST carry. EELS `forks/paris/fork.py`
    line 71: `EMPTY_OMMER_HASH = keccak256(rlp.encode([]))`. The
    well-known value is `0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347`. -/
def EMPTY_OMMER_HASH : Evm.Hash32 :=
  -- The keccak of rlp([]) (i.e. of the single byte 0xc0).
  -- Pre-computed constant; matches `keccak256(0xc0)`.
  Evm.U256.ofNat 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Paris (fork ordinal 14), with Paris's trampoline (0x44 is
    PREVRANDAO, EIP-4399, read from the block environment) and precompile table. -/
def processTransaction
    (state         : State)
    (blockHashes   : List Evm.Hash32)
    (coinbase      : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (baseFeePerGas : Nat)
    (prevRandao    : Evm.Hash32)
    (sender        : Evm.Address)
    (tx            : Evm.Frontier.Vm.Tx.Tx) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 14
    (Evm.Frontier.Vm.Tx.blockEnv coinbase number difficulty gasLimit timestamp blockHashes
      baseFeePerGas prevRandao)
    state sender tx (Evm.Frontier.Vm.Tx.table 14) Vm.Effect.trampoline (fun _ => none)

private partial def processAll
    (state : State) (header : Header) (prevRandao : Evm.Hash32)
    (blockHashes : List Evm.Hash32) (txs : List Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    let sender ← match Evm.SpuriousDragon.Utils.recoverSender tx with
      | some s => .ok s
      | none   => .error "invalid signature"
    -- EIP-3675: header.difficulty is 0 post-Merge; we pass it through
    -- unchanged (the 0x44 opcode reads prevRandao, not difficulty).
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              header.baseFeePerGas prevRandao sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    processAll r.state header prevRandao blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-! ## Block transition

  EELS `forks/paris/fork.py` `state_transition` (lines 142–225).
  Compared to Byzantium / Gray Glacier:
    * No miner / uncle rewards at the end (deleted).
    * Ommers MUST be empty (validate, then ignore).
    * The `BlockEnvironment` carries `prev_randao` from the header. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  -- EIP-3675 ommer-elimination check. EELS `state_transition` line
  -- 159: `if block.ommers != (): raise InvalidBlock`. We mirror that
  -- here as an early-error in the applyBlock pipeline.
  if block.ommers.length ≠ 0 then
    .error "EIP-3675: post-Merge blocks must have empty ommers"
  -- EIP-3675 header-level checks. EELS `validate_header` lines 330–335.
  -- Mainnet replay only ever hands us valid headers, but the rules
  -- belong to the spec.
  if block.header.difficulty ≠ 0 then
    .error "EIP-3675: post-Merge header.difficulty must be 0"
  if block.header.ommersHash ≠ EMPTY_OMMER_HASH then
    .error "EIP-3675: post-Merge header.ommersHash must be EMPTY_OMMER_HASH"
  -- header.nonce is 8 bytes; check it's all zero.
  if block.header.nonce.toList.any (fun b => b ≠ (0 : UInt8)) then
    .error "EIP-3675: post-Merge header.nonce must be 0x0000000000000000"
  -- EIP-4399: the value formerly in mixDigest is now prev_randao.
  let prevRandao : Evm.Hash32 := block.header.mixDigest
  let (state, gasUsed, logs) ← processAll state block.header prevRandao
    blockHashes block.transactions 0 []
  -- NO block reward, NO uncle bonus, NO uncle-coinbase credit.
  -- EELS `state_transition` post-loop: it goes straight to
  -- root-checking; no `pay_rewards` call exists in
  -- `forks/paris/fork.py`. (Cf. `forks/byzantium/fork.py`
  -- `pay_rewards`, which Paris deletes entirely.)
  return { state := state, gasUsed := gasUsed, logs := logs }

/-- Drive a Paris block whose transactions arrive already-typed and
    paired with senders. Tx processing delegates to London (which
    already does EIP-1559 fee market + EIP-2929 + intrinsic surcharge);
    block-level we drop the block reward (EIP-3675) and validate
    `ommers = []`. PREVRANDAO is plumbed via header.mixDigest /
    header.difficulty per Paris's reinterpretation. -/
def applyBlockTyped
    (state         : State)
    (header        : Evm.Frontier.Header)
    (ommers        : List Evm.Frontier.Header)
    (txsWithSender : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address))
    (blockHashes   : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  -- EIP-3675: ommers MUST be empty.
  if ¬ ommers.isEmpty then
    .error "Paris block has ommers (forbidden post-merge)"
  -- Per-tx via London (typed, fee-market correct). Note that London's
  -- block reward / uncle bonus run only in London.applyBlockTyped —
  -- here we drive the tx loop directly so no reward is added.
  let rec go (st : State) (gasAcc : Nat) (logsAcc : List Log)
      (xs : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :
      Except String (State × Nat × List Log) :=
    match xs with
    | [] => .ok (st, gasAcc, logsAcc)
    | (tx, sender) :: xs' => do
      let r ← processTransaction st blockHashes header.coinbase
                header.number header.difficulty header.gasLimit header.timestamp
                header.baseFeePerGas header.mixDigest sender tx
      go r.state (gasAcc + r.gasUsed) (logsAcc ++ r.logs) xs'
  let (state, gasUsed, logs) ← go state 0 [] txsWithSender
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Paris
