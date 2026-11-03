/-
  Evm.Frontier.Vm.System — a system transaction for every fork, once.

  EELS master (fetched 2026-10-26): `forks/<fork>/fork.py`
  `process_unchecked_system_transaction` (cancun 546-611, prague 640-707, osaka 657-724) and
  `process_checked_system_transaction` (prague 581-637, osaka 598-654), and the system
  message's `vm/interpreter.py` `process_message_call` (prague 92-160: from Prague the
  target's delegation, 126-133). The same clauses at every fork, switched by the fork's
  ordinal `k`:

    * the tx environment (`TransactionEnvironment`): origin `SYSTEM_ADDRESS`, gas price the
      block's base fee, gas `SYSTEM_TRANSACTION_GAS` (30,000,000), the access list's
      addresses and keys EMPTY, no blob hashes, no authorizations; the message: caller
      `SYSTEM_ADDRESS`, value 0 (`should_transfer_value = False`), the whole gas, and
      `accessed_addresses = set()`, `accessed_storage_keys = set()` — nothing starts warm,
      not the precompiles, the caller or the target (EIP-2929's tx-start warm-up is
      `prepare_message`'s, which a system transaction does not run). No validation, no
      nonce, no intrinsic gas, no fee.
    * the message (`process_message_call`): from Prague the target's delegation (the
      delegate warmed, its code run, precompiles disabled), then `process_message` — the
      fork's precompile at the target or the code; a failure keeps the snapshot.
    * the end (`incorporate_tx_into_block`): the world after the message. The
      accounts_to_delete, the refund counter, the touched set and the logs of the message
      are dropped: a system transaction destroys nothing and sweeps nothing.
    * `process_checked_system_transaction` (EIP-7002, EIP-7251): a target without code, or a
      message that fails (an exceptional halt or a REVERT: `system_tx_output.error`),
      invalidates the block (`InvalidBlock`).

  The message is `Tx.call` on the system tx record (`sysTx`): the same `callTail` user txs
  run, with no authorizations (`set_delegation` runs only for a non-empty list). The
  derived effect (`Evm.CL.EffectSystem`) is proved against `message` in
  `Evm.CL.EffectSystemProof` for every fork, every frame run `runSub`, every precompile
  table and every rule.

  **The rule a chain follows** (`Rule`): the addresses warm at the start and the gas price
  GASPRICE reads. Ethereum is EELS (`eels`: none, the base fee). Arc follows arc-node
  (revm's `run_system_call`), which warms the target: `Evm.Arc.Spec.BlockSystem.systemRule`
  — one owner per chain, the term takes it as a parameter.

  Stated choices (as `Tx`): the success touch of an existing empty target (EIP-161) is kept
  after Paris, where EELS has no touched set; nothing reads it here (no sweep).
-/

import Evm.Frontier.Vm.Tx

namespace Evm.Frontier.Vm.System

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Tx (Tx Out ins)
open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-- EELS `SYSTEM_ADDRESS`, as a number (the emitted defun's constant) and an address. -/
def systemAddressNat : Nat := 0xfffffffffffffffffffffffffffffffffffffffe
def systemAddress : Evm.Address := Evm.Address.ofNat systemAddressNat

/-- EELS `SYSTEM_TRANSACTION_GAS`. -/
def systemGas : Nat := 30000000

/-- What a chain's system call starts with: the addresses warm (in insertion order) and the
    gas price the frame's GASPRICE reads. -/
structure Rule where
  seed     : List Evm.Address
  gasPrice : Nat

/-- EELS: nothing warm, GASPRICE the block's base fee. -/
def eels (benv : Environment) : Rule := { seed := [], gasPrice := benv.baseFeePerGas }

/-- The system message as a tx: no nonce, the whole gas, no value, the data. -/
def sysTx (target : Evm.Address) (data : Evm.Bytes) : Tx :=
  { nonce := 0, gas := systemGas, to := some target, value := 0, data := data }

/-- The environment the message starts in (EELS `TransactionEnvironment` and the `Message`'s
    sets): the block's, origin `SYSTEM_ADDRESS`, the rule's gas price and warm addresses,
    no warm slots, the empty per-tx sets; the originals of the storage are the world before;
    EIP-7702 delegation on from Prague. -/
def env0 (k : Nat) (benv : Environment) (st : State) (r : Rule) : Environment :=
  { benv with
    state := st, origin := systemAddress, gasPrice := Evm.U256.ofNat r.gasPrice,
    logs := [], selfDestructSet := [], refundCounter := 0, touched := [], originalState := st,
    accessedAddresses := r.seed.foldl ins [], accessedStorageKeys := [], storageOriginals := [],
    transientStorage := [], createdAccounts := [], blobVersionedHashes := [],
    pragueDelegation := decide (k ≥ 17) }

/-- The message (`process_message_call` on the system message): `Tx.call` with no
    authorizations — from Prague the target's delegation —, `callTail`. -/
def message (k : Nat) (benv : Environment) (st : State) (r : Rule) (target : Evm.Address)
    (data : Evm.Bytes) (pre : Environment → Evm.Address → Option Precompile)
    (runSub : Evm → Except Exception Evm) : Out :=
  Tx.call k (env0 k benv st r) systemAddress target (sysTx target data) systemGas pre runSub
    (fun _ => none)

/-- EELS `process_unchecked_system_transaction`: the world after the message, its success and
    output. -/
def unchecked (k : Nat) (benv : Environment) (st : State) (r : Rule) (target : Evm.Address)
    (data : Evm.Bytes) (pre : Environment → Evm.Address → Option Precompile)
    (runSub : Evm → Except Exception Evm) : State × Bool × Evm.Bytes :=
  let o := message k benv st r target data pre runSub
  (o.env.state, o.success, o.output)

/-- EELS `process_checked_system_transaction`: the block is invalid when the target has no
    code or the message fails; otherwise the world after it and its output. -/
def checked (k : Nat) (benv : Environment) (st : State) (r : Rule) (target : Evm.Address)
    (data : Evm.Bytes) (pre : Environment → Evm.Address → Option Precompile)
    (runSub : Evm → Except Exception Evm) : Except String (State × Evm.Bytes) :=
  if (st.getAccount target).code.size = 0 then .error "system contract has no code"
  else
    let o := message k benv st r target data pre runSub
    if o.success then .ok (o.env.state, o.output) else .error "system contract call failed"

end Evm.Frontier.Vm.System
