/-
  Evm.Frontier.Vm.Tx — a transaction for every fork, once.

  EELS `forks/<fork>/fork.py` `process_transaction` and `check_transaction`,
  `transactions.py` `validate_transaction` / `calculate_intrinsic_cost`, `utils/message.py`
  `prepare_message`, `vm/interpreter.py` `process_message_call` / `process_create_message`
  / `process_message`, and from Prague `vm/eoa_delegation.py` `set_delegation` — the same
  clauses at every fork, switched by the fork's ordinal `k` (`Evm.Fork.ord`; EELS master
  fetched 2026-10-26, line numbers from `forks/prague`):

    * validation (`validate_transaction`, `check_transaction`): the intrinsic gas and from
      Prague (EIP-7623) the calldata floor within the gas limit; EIP-3860's init-code cap
      (Shanghai); EIP-2681's nonce bound; EIP-7825's gas cap (Osaka); the fee fields
      (EIP-1559 from London: `max_fee ≥ max_priority`, `max_fee ≥ base_fee`; a legacy price
      at least the base fee); the blob fields (EIP-4844, Cancun: at least one blob, the KZG
      version byte, EIP-7594's six-blob cap from Osaka, `max_fee_per_blob_gas` at least the
      blob base fee); type 3 and 4 cannot create; type 4 carries authorizations; the nonce;
      the balance against `gas × max price + blob gas × max blob price + value`; EIP-3607
      (the sender has no code, or from Prague a delegation designator). The tx's chain id
      and signature are the driver's (the sender is an input).
    * the upfront charge (`process_transaction` 857-868): the nonce, then
      `gas × effective price + blob gas × blob base fee` (EIP-1559 London, EIP-4844 Cancun).
    * the accessed sets (EIP-2929 Berlin, EIP-2930, EIP-3651 Shanghai): the precompiles,
      the sender, the target (the address a creation derives), the coinbase, the access
      list — EELS sets; the lists here insert in that order, the replay's.
    * the message (`process_message_call`): a creation collides (EIP-684; no storage leg,
      EIP-7610 is not applied — `Create.collides`) or runs its init code in the world
      `Create.childState` builds, then the code deposit (EIP-2, EIP-170, EIP-3541 as
      `Create.resume`); a call runs, from Prague, the authorization list
      (`set_delegation`: the refund for an authority that exists, the designator, the
      nonce) and the target's delegation (the delegate warmed, its code run, precompiles
      disabled), then `process_message` (`touch_account` before EIP-161, the value, the
      fork's precompile at the target or the code — `Call.runChild`); a failure keeps the
      snapshot taken after the authorizations (a REVERT its gas); from EIP-161 a success
      touches the target when it is existing and empty.
    * the end (`process_transaction` 913-940): the refund cap (EIP-3529 London) and the
      EIP-7623 floor (`GasEmit.txGasUsed`), the settlement (`specSettle`: the sender's
      unused gas, the coinbase's priority fee — the base fee and the blob fee are burned
      by being credited nowhere), the accounts_to_delete and the EIP-161 sweep.

  The numbers are the emitted formulas' (`Evm.CL.GasEmit`: `intrinsicGas`,
  `calldataFloorGas`, `effectiveGasPrice`, `txGasUsed`), so each has one owner.

  The frame runs through `runSub` (the fork's trampoline) and a precompile through `pre`
  (the fork's table, read in the tx environment); the authority of an authorization comes
  from `recover` (EELS `recover_authority`: secp256k1 over the EIP-7702 message). The
  derived effect (`Evm.CL.EffectTx`) is proved against `message` and the end
  (`Evm.CL.EffectTxProof.apply_tx_refines`) for every fork, every `runSub`, every table
  and every `recover`.

  Stated choices (each unobservable on the chains we replay, or recorded as a gap):

    * Amsterdam's tx level (EELS: the state-gas reservoir, the block access list,
      `process_top_level`) is not in the Lean Amsterdam spec; it runs Osaka's.
    * From Spurious Dragon `process_message` also brings an absent target into existence
      (until the sweep); the spec does not (`Call.lean`'s choice, `sd_form_closes`).
    * The touch and the sweep are kept after Paris, where EELS dropped the touched set
      (EIP-7523: no empty account exists to sweep).
-/

import Evm.Frontier.Vm.Create
import Evm.Frontier.Vm.Call
import Evm.Frontier.Vm.Settle
import Evm.Frontier.Utils.Address
import Evm.Prague.State
import Evm.Prague.Transactions
import Evm.CL.GasEmit
import Evm.Frontier.Transactions
import Evm.Berlin.Transactions
import Evm.London.Transactions

namespace Evm.Frontier.Vm.Tx

open Evm.Frontier (State Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-- A transaction, every type (EIP-2718: 0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844,
    4 EIP-7702) in one record; a field a type lacks is its default. -/
structure Tx where
  type     : Nat := 0
  nonce    : Nat
  gas      : Nat
  /-- Type 0 and 1. -/
  gasPrice : Nat := 0
  /-- Type 2 and later. -/
  maxFee   : Nat := 0
  maxPrio  : Nat := 0
  /-- Type 3. -/
  maxFeePerBlobGas : Nat := 0
  to       : Option Evm.Address
  value    : Evm.U256
  data     : Evm.Bytes
  /-- Type 1 and later: (address, storage keys). -/
  accessList : List (Evm.Address × List Evm.U256) := []
  /-- Type 3. -/
  blobHashes : List Evm.Hash32 := []
  /-- Type 4. -/
  auths    : List Evm.Prague.Authorization := []
  deriving Inhabited

/-! ## The numbers -/

/-- Zero bytes of the calldata. -/
def zeroBytes (d : Evm.Bytes) : Nat := (List.range d.size).countP (fun i => d.get! i = 0)

/-- The emitted formulas' inputs for `tx` at fork `k` (`intrinsicGas`, `calldataFloorGas`). -/
def gasEnv (k : Nat) (tx : Tx) : Evm.CL.GasEmit.Env := fun y =>
  if y = "is-create" then (if tx.to.isNone then 1 else 0)
  else if y = "data-len" then tx.data.size
  else if y = "zero-bytes" then zeroBytes tx.data
  else if y = "nonzero-bytes" then tx.data.size - zeroBytes tx.data
  else if y = "al-addrs" then tx.accessList.length
  else if y = "al-keys" then (tx.accessList.map (·.2.length)).sum
  else if y = "fork-ord" then k
  else 0

/-- EELS `calculate_intrinsic_cost` (`regular`): `TX_BASE`, the calldata (4 per zero byte,
    68 per other — 16 from Istanbul, EIP-2028), `TX_CREATE` (Homestead, EIP-2) and the
    init-code words (Shanghai, EIP-3860), the access list (EIP-2930), and from Prague
    `PER_EMPTY_ACCOUNT_COST` per authorization (EIP-7702). -/
def intrinsic (k : Nat) (tx : Tx) : Nat :=
  Evm.CL.GasEmit.intrinsicGas.eval (gasEnv k tx) + (if k ≥ 17 then 25000 * tx.auths.length else 0)

/-- EIP-7623's calldata floor (Prague; 0 before). -/
def floor (k : Nat) (tx : Tx) : Nat := Evm.CL.GasEmit.calldataFloorGas.eval (gasEnv k tx)

/-- The effective gas price (`check_transaction`): EIP-1559's `min(max_fee, base_fee +
    max_priority)` for type 2 and later, the gas price otherwise. -/
def egp (baseFee : Nat) (tx : Tx) : Nat :=
  if tx.type ≥ 2 then
    Evm.CL.GasEmit.effectiveGasPrice.eval (fun y =>
      if y = "max-fee" then tx.maxFee else if y = "base-fee" then baseFee
      else if y = "max-prio" then tx.maxPrio else 0)
  else tx.gasPrice

/-- EIP-4844 `GAS_PER_BLOB` per blob. -/
def blobGas (tx : Tx) : Nat := 131072 * tx.blobHashes.length

/-- The highest tx type each fork decodes (EIP-2718 types arrive with Berlin, London,
    Cancun, Prague). -/
def maxType (k : Nat) : Nat :=
  if k ≥ 17 then 4 else if k ≥ 16 then 3 else if k ≥ 11 then 2 else if k ≥ 10 then 1 else 0

/-- The most the sender can be charged (`check_transaction`'s `max_gas_fee`). -/
def maxGasFee (tx : Tx) : Nat :=
  (if tx.type ≥ 2 then tx.gas * tx.maxFee else tx.gas * tx.gasPrice) +
    (if tx.type = 3 then blobGas tx * tx.maxFeePerBlobGas else 0)

/-- `secp256k1n`. -/
def secp256k1n : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- A blob versioned hash carries the KZG version byte (EIP-4844 `VERSIONED_HASH_VERSION_KZG`,
    0x01, its first byte). -/
def versionOk (h : Evm.Hash32) : Bool := h.toNat / 2 ^ 248 = 1

/-- A delegation designator (EIP-7702): `0xef0100 || address`. -/
def designator (a : Evm.Address) : Evm.Bytes :=
  Evm.Prague.State.delegationPrefix ++ Evm.Address.toBytesBE a

/-! ## Validation -/

/-- EELS `validate_transaction` then `check_transaction`, rule by rule in their order: each
    rule is `true` when the tx breaks it. `chainId` and the block gas left are the block's;
    the sender is the driver's. -/
def rules (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx) :
    List (Bool × String) :=
  let acc := st.getAccount sender
  [ (decide (tx.type > maxType k), "tx type"),
    (decide (max (intrinsic k tx) (floor k tx) > tx.gas), "intrinsic gas"),
    (decide (k ≥ 15 ∧ tx.to.isNone ∧ tx.data.size > Create.maxInitCodeSize), "init code size"),
    (decide (tx.nonce ≥ 2 ^ 64 - 1), "nonce overflow"),
    (decide (k ≥ 18 ∧ tx.gas > 16777216), "gas above TX_MAX_GAS_LIMIT"),
    (decide (tx.type ≥ 2 ∧ tx.maxFee < tx.maxPrio), "priority fee above max fee"),
    (decide (tx.type ≥ 2 ∧ tx.maxFee < benv.baseFeePerGas), "max fee below base fee"),
    (decide (tx.type < 2 ∧ tx.gasPrice < benv.baseFeePerGas), "gas price below base fee"),
    (decide (tx.type = 3 ∧ tx.blobHashes.length = 0), "no blobs"),
    (decide (tx.type = 3 ∧ k ≥ 18 ∧ tx.blobHashes.length > 6), "too many blobs"),
    (decide (tx.type = 3) && !tx.blobHashes.all versionOk,
      "blob versioned hash version"),
    (decide (tx.type = 3 ∧ tx.maxFeePerBlobGas < benv.blobBaseFee), "max blob fee below blob base fee"),
    (decide ((tx.type = 3 ∨ tx.type = 4) ∧ tx.to.isNone), "type cannot create"),
    (decide (tx.type = 4 ∧ tx.auths.length = 0), "empty authorization list"),
    (decide (acc.nonce ≠ tx.nonce), "nonce mismatch"),
    (decide (acc.balance.toNat < maxGasFee tx + tx.value.toNat), "insufficient balance"),
    (decide (acc.code.size ≠ 0 ∧
      ¬ (k ≥ 17 ∧ (Evm.Prague.State.parseDelegation acc.code).isSome)), "sender not an EOA") ]

/-- The first rule the tx breaks (`none`: it is valid). -/
def invalid (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx) :
    Option String :=
  ((rules k benv st sender tx).find? (·.1)).map (·.2)

/-- A valid tx breaks no rule: `invalid = none` makes every rule's flag `false` (the
    shared first step of every tx-validity refinement, `Evm.*.Spec.Refinement`). -/
theorem rules_false_of_valid {k : Nat} {benv : Environment} {st : State} {sender : Evm.Address}
    {tx : Tx} (h : invalid k benv st sender tx = none) :
    ∀ r ∈ rules k benv st sender tx, r.1 = false := by
  unfold invalid at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro r hr; simpa using h r hr

/-! ## The prologue -/

/-- Add `a` to an insertion-ordered set. -/
def ins (l : List Evm.Address) (a : Evm.Address) : List Evm.Address :=
  if l.contains a then l else l ++ [a]

/-- Add a slot to an insertion-ordered set. -/
def insSlot (l : List (Evm.Address × Evm.U256)) (p : Evm.Address × Evm.U256) :
    List (Evm.Address × Evm.U256) :=
  if l.contains p then l else l ++ [p]

/-- The addresses of the fork's precompiles (EIP-2929 warms them): 0x01–0x04, Byzantium
    0x05–0x08, Istanbul 0x09, Cancun 0x0a, Prague 0x0b–0x11, Osaka 0x100 — the keys of
    `Call.precompiles k`. -/
def precompileAddrs (k : Nat) : List Evm.Address :=
  let n := if k ≥ 17 then 17 else if k ≥ 16 then 10 else if k ≥ 8 then 9 else if k ≥ 5 then 8 else 4
  (List.range n).map (fun i => Evm.Address.ofNat (i + 1)) ++
    (if k ≥ 18 then [Evm.Address.ofNat 0x100] else [])

/-- The addresses the message starts warm with, in insertion order: the precompiles, the
    sender, the target, from Shanghai the coinbase (EIP-3651), the access list's. -/
def seedAddrs (k : Nat) (sender target coinbase : Evm.Address)
    (al : List (Evm.Address × List Evm.U256)) : List Evm.Address :=
  precompileAddrs k ++ [sender, target] ++ (if k ≥ 15 then [coinbase] else []) ++ al.map (·.1)

/-- The access list's slots, in order. -/
def seedSlots (al : List (Evm.Address × List Evm.U256)) : List (Evm.Address × Evm.U256) :=
  al.flatMap (fun e => e.2.map (fun s => (e.1, s)))

/-- The accessed addresses at the start of the message (Berlin+; empty before). -/
def accessedSeed (k : Nat) (sender target coinbase : Evm.Address) (tx : Tx) : List Evm.Address :=
  if k ≥ 10 then (seedAddrs k sender target coinbase tx.accessList).foldl ins [] else []

/-- The accessed storage keys at the start (Berlin+): the access list's. -/
def slotSeed (k : Nat) (tx : Tx) : List (Evm.Address × Evm.U256) :=
  if k ≥ 10 then (seedSlots tx.accessList).foldl insSlot [] else []

/-- The world after the upfront charge (`process_transaction` 857-868): the nonce, then
    the balance less the gas at the effective price and the blob fee (Cancun+). -/
def charged (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx) : State :=
  let a := st.getAccount sender
  let st := st.setAccount sender { a with nonce := a.nonce + 1 }
  let a := st.getAccount sender
  let fee := tx.gas * egp benv.baseFeePerGas tx + (if k ≥ 16 then blobGas tx * benv.blobBaseFee else 0)
  st.setAccount sender { a with balance := a.balance - Evm.U256.ofNat fee }

/-- The message's target: `tx.to`, or the address a creation derives from the sender's
    nonce before the charge. -/
def target (st : State) (sender : Evm.Address) (tx : Tx) : Evm.Address :=
  match tx.to with
  | some a => a
  | none => Evm.Frontier.Utils.computeContractAddress sender (st.getAccount sender).nonce

/-- The tx environment the message starts in (EELS `TransactionEnvironment` and
    `prepare_message`): the block's, with the tx's origin, price, accessed sets, blob
    hashes, the world after the charge and the empty per-tx sets; the originals of the
    storage are the world before the tx; EIP-7702 delegation is on from Prague. -/
def env0 (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx) : Environment :=
  { benv with
    state := charged k benv st sender tx, origin := sender,
    gasPrice := Evm.U256.ofNat (egp benv.baseFeePerGas tx),
    logs := [], selfDestructSet := [], refundCounter := 0, touched := [],
    originalState := st,
    accessedAddresses := accessedSeed k sender (target st sender tx) benv.coinbase tx,
    accessedStorageKeys := slotSeed k tx, storageOriginals := [],
    transientStorage := [], createdAccounts := [], blobVersionedHashes := tx.blobHashes,
    pragueDelegation := decide (k ≥ 17) }

/-! ## EIP-7702: the authorization list (`set_delegation`) -/

/-- One authorization (EELS `validate_authorization` and the loop body of
    `set_delegation`): the chain id (this chain's, or 0), the nonce bound, the signature's
    scalars (`recover_authority`'s checks), the authority (`recover`), warmed; its code
    empty or a designator; its nonce the authorization's; then the refund
    (`PER_EMPTY_ACCOUNT_COST − PER_AUTH_BASE_COST` when the authority exists), the code
    (the designator, or none for the zero address), the nonce. -/
def authorize (chainId : Evm.U256) (recover : Evm.Prague.Authorization → Option Evm.Address)
    (env : Environment) (a : Evm.Prague.Authorization) : Environment :=
  if ¬ (a.chainId = chainId ∨ a.chainId = 0) then env
  else if a.nonce.toNat ≥ 2 ^ 64 - 1 then env
  else if ¬ (a.yParity.toNat ≤ 1 ∧ 0 < a.r.toNat ∧ a.r.toNat < secp256k1n ∧ 0 < a.s.toNat ∧
             a.s.toNat ≤ secp256k1n / 2) then env
  else
  match recover a with
  | none => env
  | some au =>
    let env := Call.warm env au
    let acc := env.state.getAccount au
    if acc.code.size ≠ 0 ∧ (Evm.Prague.State.parseDelegation acc.code).isNone then env
    else if acc.nonce ≠ a.nonce.toNat then env
    else
    let r := if env.state.accountExists au then env.refundCounter + 12500 else env.refundCounter
    let st := env.state.setAccount au
      { acc with code := if a.address = 0 then Evm.Bytes.empty else designator a.address }
    let acc := st.getAccount au
    { env with refundCounter := r, state := st.setAccount au { acc with nonce := acc.nonce + 1 } }

/-! ## The message (`process_message_call`) -/

/-- What the message hands back: the tx environment after it (on failure the snapshot's:
    no logs, no accounts to delete, no touches, the authorizations' refund), the gas left,
    success. -/
structure Out where
  env     : Environment
  gasLeft : Nat
  success : Bool
  /-- The top frame's output (EELS `MessageCallOutput.return_data`; a system call's
      requests payload). -/
  output  : Evm.Bytes := Evm.Bytes.empty

/-- `process_create_message`'s end, on the init frame's result: an exceptional halt or a
    REVERT keeps nothing (a REVERT returns its gas); EIP-3541's prefix (London), the code
    deposit (a deposit the frame cannot pay drops the code at Frontier and fails the
    creation from Homestead, EIP-2), EIP-170's size (Spurious Dragon). -/
def createEnd (k : Nat) (snap : Environment) (newAddr : Evm.Address) (res : Except Exception Evm) : Out :=
  let fail (g : Nat) : Out := { env := snap, gasLeft := g, success := false }
  match res with
  | .error _ => fail 0
  | .ok sub =>
    if sub.reverted then fail sub.gasLeft
    else
    let code := sub.output
    let d := Gas.codeDeposit * code.size
    if k ≥ 11 ∧ 0 < code.size ∧ code.get! 0 = (0xEF : UInt8) then fail 0
    else if sub.gasLeft < d then
      if k ≥ 1 then fail 0 else { env := sub.env, gasLeft := sub.gasLeft, success := true }
    else if k ≥ 4 ∧ code.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize then fail 0
    else
      let acc := sub.env.state.getAccount newAddr
      { env := { sub.env with state := sub.env.state.setAccount newAddr { acc with code := code } },
        gasLeft := sub.gasLeft - d, success := true }

/-- The init message of a creating tx (its gas is `gas`). -/
def createMsg (sender newAddr : Evm.Address) (tx : Tx) (gas : Nat) : Message :=
  { caller := sender, target := none, currentTarget := newAddr, value := tx.value,
    data := Evm.Bytes.empty, code := tx.data, gas := gas, depth := 0 }

/-- A creating tx: the collision rule (all the gas is lost), else the init frame in the
    world `Create.childState` builds — the storage wiped, the nonce 1 (EIP-161),
    `touch_account`, the value — marked created (EIP-6780), and its end. -/
def create (k : Nat) (e : Environment) (sender newAddr : Evm.Address) (tx : Tx) (gas : Nat)
    (runSub : Evm → Except Exception Evm) : Out :=
  if Create.collides e.state newAddr then { env := e, gasLeft := 0, success := false }
  else
  let msg := createMsg sender newAddr tx gas
  let parent : Evm := { gasLeft := 0, message := msg, env := e }
  createEnd k e newAddr
    (runSub (Create.child parent msg (Create.childState (Create.Rules.ofOrd k) e.state sender newAddr tx.value)))

/-- The call message (its code and gas set by `call`). -/
def callMsg (sender to : Evm.Address) (tx : Tx) (code : Evm.Bytes) (gas : Nat) : Message :=
  { caller := sender, target := some to, currentTarget := to, value := tx.value,
    data := tx.data, code := code, gas := gas, depth := 0 }

/-- `process_message` at the top, after the delegation: from the snapshot `e2`,
    `touch_account` before EIP-161, the value, the fork's precompile at the target (unless
    the delegation `d` disabled them) or the code (`Call.runChild`); a failure keeps the
    snapshot (a REVERT its gas), a success the frame's environment, from EIP-161 with the
    target touched when it is existing and empty. -/
def callTail (k : Nat) (e2 : Environment) (sender to : Evm.Address) (tx : Tx) (gas : Nat)
    (d : Option Evm.Address) (pre : Environment → Evm.Address → Option Precompile)
    (runSub : Evm → Except Exception Evm) : Out :=
  let code := match d with
    | some a => (e2.state.getAccount a).code
    | none => (e2.state.getAccount to).code
  let st := if k ≥ 4 then e2.state else e2.state.touchAccount to
  let st := if tx.value = 0 then st else (st.subBalance sender tx.value).addBalance to tx.value
  let msg := callMsg sender to tx code gas
  let parent : Evm := { gasLeft := 0, message := msg, env := e2 }
  match Call.runChild pre parent msg (if d.isSome then none else some to) st runSub with
  | .error _ => { env := e2, gasLeft := 0, success := false }
  | .ok sub =>
    if sub.reverted then { env := e2, gasLeft := sub.gasLeft, success := false, output := sub.output }
    else
      let env := if k ≥ 4 ∧ sub.env.state.accountExists to ∧ (sub.env.state.getAccount to).isEmpty
                 then Call.touch sub.env to else sub.env
      { env := env, gasLeft := sub.gasLeft, success := true, output := sub.output }

/-- A call: from Prague the authorizations (`set_delegation`) and the target's delegation
    (EELS `process_message_call` 132-146: the delegate warmed, its code, precompiles off),
    then `callTail`. -/
def call (k : Nat) (e : Environment) (sender to : Evm.Address) (tx : Tx) (gas : Nat)
    (pre : Environment → Evm.Address → Option Precompile) (runSub : Evm → Except Exception Evm)
    (recover : Evm.Prague.Authorization → Option Evm.Address) : Out :=
  let e1 := if k ≥ 17 then tx.auths.foldl (authorize e.chainId recover) e else e
  let d := if k ≥ 17 then Evm.Prague.State.parseDelegation (e1.state.getAccount to).code else none
  let e2 := match d with | some a => Call.warm e1 a | none => e1
  callTail k e2 sender to tx gas d pre runSub

/-- The message of a valid tx: `prepare_message` and `process_message_call`. -/
def message (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Precompile) (runSub : Evm → Except Exception Evm)
    (recover : Evm.Prague.Authorization → Option Evm.Address) : Out :=
  let e := env0 k benv st sender tx
  let gas := tx.gas - intrinsic k tx
  match tx.to with
  | none => create k e sender (target st sender tx) tx gas runSub
  | some to => call k e sender to tx gas pre runSub recover

/-! ## The end (`process_transaction` 913-940) -/

/-- The gas the tx is charged: its gas less what the message left, the refund capped
    (half; a fifth from London, EIP-3529), at least the EIP-7623 floor (Prague). -/
def gasUsed (k : Nat) (tx : Tx) (o : Out) : Nat :=
  Evm.CL.GasEmit.txGasUsed.eval (fun y =>
    if y = "gas-used" then tx.gas - o.gasLeft
    else if y = "refund-counter" then o.env.refundCounter
    else gasEnv k tx y)

/-- The fork's fee settlement (`settleFees`; the coinbase rule from Spurious Dragon). -/
def settle (k : Nat) (s : State) (sender coinbase : Evm.Address) (refundWei minerWei : Nat) : State :=
  if 4 ≤ k then Evm.SpuriousDragon.settleFees s sender coinbase refundWei minerWei
  else Evm.Frontier.settleFees s sender coinbase refundWei minerWei

/-- The fork's end of tx (the accounts_to_delete; the EIP-161 sweep from Spurious Dragon). -/
def endTx (k : Nat) (s : State) (destroyed touched : List Evm.Address) : State :=
  if 4 ≤ k then Evm.SpuriousDragon.finishTx s destroyed touched
  else Evm.Frontier.destroyAccounts s destroyed

/-- After the message: the gas, the sender's unused gas back, the coinbase's priority fee,
    the end of tx. -/
def finish (k : Nat) (benv : Environment) (sender : Evm.Address) (tx : Tx) (o : Out) :
    Evm.Frontier.TxResult :=
  let gu := gasUsed k tx o
  let p := egp benv.baseFeePerGas tx
  let st := settle k o.env.state sender benv.coinbase ((tx.gas - gu) * p) (gu * (p - benv.baseFeePerGas))
  { state := endTx k st o.env.selfDestructSet o.env.touched, gasUsed := gu, logs := o.env.logs,
    success := o.success }

/-- One transaction at fork `k` in the block environment `benv`, from world `st`. -/
def run (k : Nat) (benv : Environment) (st : State) (sender : Evm.Address) (tx : Tx)
    (pre : Environment → Evm.Address → Option Precompile) (runSub : Evm → Except Exception Evm)
    (recover : Evm.Prague.Authorization → Option Evm.Address) :
    Except String Evm.Frontier.TxResult :=
  match invalid k benv st sender tx with
  | some why => .error why
  | none => .ok (finish k benv sender tx (message k benv st sender tx pre runSub recover))


/-- The block's transactions in order (EELS `apply_body`'s loop; the block gas limit is
    the driver's): the world after each, the gas, the logs. -/
def runAll (k : Nat) (benv : Environment)
    (pre : Environment → Evm.Address → Option Precompile) (runSub : Evm → Except Exception Evm)
    (recover : Evm.Prague.Authorization → Option Evm.Address) :
    State → List (Tx × Evm.Address) → Nat → List Log → Except String (State × Nat × List Log)
  | st, [], g, ls => .ok (st, g, ls)
  | st, (tx, s) :: rest, g, ls => do
    let r ← run k benv st s tx pre runSub recover
    runAll k benv pre runSub recover r.state rest (g + r.gasUsed) (ls ++ r.logs)

/-- A block environment from the header's fields (the state is the tx's, set by `env0`). -/
def blockEnv (coinbase : Evm.Address) (number difficulty gasLimit timestamp : Nat)
    (blockHashes : List Evm.Hash32) (baseFee : Nat := 0) (prevRandao : Evm.Hash32 := 0)
    (blobBaseFee excessBlobGas : Nat := 0) : Environment :=
  { origin := 0, gasPrice := 0, coinbase := coinbase, number := number, difficulty := difficulty,
    gasLimit := gasLimit, timestamp := timestamp, blockHashes := blockHashes, state := {},
    baseFeePerGas := baseFee, prevRandao := prevRandao, blobBaseFee := blobBaseFee,
    excessBlobGas := excessBlobGas }

/-- The fork's precompile table at the tx level (Ethereum: no OP-Stack flags). -/
def table (k : Nat) : Environment → Evm.Address → Option Precompile := fun _ a => Call.precompiles k a

/-! ## The forks' transactions as `Tx` -/

/-- A legacy transaction (every fork). -/
def ofLegacy (t : _root_.Evm.Frontier.Transaction) : Tx :=
  { nonce := t.nonce.toNat, gas := t.gas.toNat, gasPrice := t.gasPrice.toNat, to := t.to,
    value := t.value, data := t.data }

/-- A Berlin transaction (legacy, EIP-2930). -/
def ofBerlin : Evm.Berlin.Transaction → Tx
  | .legacy t => ofLegacy t
  | .accessList t =>
    { type := 1, nonce := t.nonce.toNat, gas := t.gas.toNat, gasPrice := t.gasPrice.toNat,
      to := t.to, value := t.value, data := t.data,
      accessList := t.accessList.map (fun e => (e.address, e.storageKeys)) }

/-- A London transaction (legacy, EIP-2930, EIP-1559). -/
def ofLondon : Evm.London.Transaction → Tx
  | .legacy t => ofLegacy t
  | .accessList t =>
    { type := 1, nonce := t.nonce.toNat, gas := t.gas.toNat, gasPrice := t.gasPrice.toNat,
      to := t.to, value := t.value, data := t.data,
      accessList := t.accessList.map (fun e => (e.account, e.slots)) }
  | .feeMarket t =>
    { type := 2, nonce := t.nonce.toNat, gas := t.gas.toNat, maxFee := t.maxFeePerGas.toNat,
      maxPrio := t.maxPriorityFeePerGas.toNat, to := t.to, value := t.value, data := t.data,
      accessList := t.accessList.map (fun e => (e.account, e.slots)) }

/-- A Prague transaction (every type). -/
def ofPrague : Evm.Prague.Transaction → Tx
  | .legacy n gp g to v d _ _ _ =>
    { nonce := n.toNat, gas := g.toNat, gasPrice := gp.toNat, to := to, value := v, data := d }
  | .accessList _ n gp g to v d al _ _ _ =>
    { type := 1, nonce := n.toNat, gas := g.toNat, gasPrice := gp.toNat, to := to, value := v,
      data := d, accessList := al.map (fun a => (a.account, a.slots)) }
  | .feeMarket _ n mp mf g to v d al _ _ _ =>
    { type := 2, nonce := n.toNat, gas := g.toNat, maxFee := mf.toNat, maxPrio := mp.toNat,
      to := to, value := v, data := d, accessList := al.map (fun a => (a.account, a.slots)) }
  | .blob _ n mp mf g to v d al mfb bh _ _ _ =>
    { type := 3, nonce := n.toNat, gas := g.toNat, maxFee := mf.toNat, maxPrio := mp.toNat,
      maxFeePerBlobGas := mfb.toNat, to := some to, value := v, data := d,
      accessList := al.map (fun a => (a.account, a.slots)), blobHashes := bh }
  | .setCode _ n mp mf g to v d al auths _ _ _ =>
    { type := 4, nonce := n.toNat, gas := g.toNat, maxFee := mf.toNat, maxPrio := mp.toNat,
      to := some to, value := v, data := d,
      accessList := al.map (fun a => (a.account, a.slots)), auths := auths }

end Evm.Frontier.Vm.Tx
