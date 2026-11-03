/-
  Replay — driver for `ethereum/tests` BlockchainTests against the
  Lean EVM. See lean/REPLAY.md for the design notes.

  Reads a JSON test file, parses each test in it into a Frontier-shaped
  state + block, calls `Evm.Frontier.applyBlock`, and compares the
  resulting accounts/storage to the expected `postState`.

  Currently scoped to Frontier-tagged tests; multi-fork dispatch arrives
  once Homestead+ have their own end-to-end harnesses.
-/

import Lean.Data.Json
import Evm.BaseTypes
import Evm.Frontier.Fork
import Evm.Frontier.StateRoot
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Constantinople.Fork
import Evm.Petersburg.Fork
import Evm.Istanbul.Fork
import Evm.Berlin.Fork
import Evm.London.Fork
import Evm.Paris.Fork
import Evm.Shanghai.Fork
import Evm.Cancun.Fork

open Lean (Json)

namespace Replay

/-! ## Hex parsing -/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def stripHex (s : String) : String :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then String.ofList (s.toList.drop 2) else s

private partial def hexBytesLoop : List Char → ByteArray → Option ByteArray
  | [],             acc => some acc
  | [_],            _   => none
  | h :: l :: rest, acc =>
    match hexDigit? h, hexDigit? l with
    | some hi, some lo => hexBytesLoop rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
    | _, _ => none

def hexToBytes (s : String) : Option ByteArray :=
  let s := stripHex s
  let s := if s.length % 2 = 1 then "0" ++ s else s
  hexBytesLoop s.toList ByteArray.empty

def hexToNat (s : String) : Nat := Id.run do
  let s := stripHex s
  let mut acc : Nat := 0
  for c in s.toList do
    match hexDigit? c with
    | some d => acc := acc * 16 + d
    | none   => return acc
  pure acc

def hexToU256 (s : String) : Evm.U256 := Evm.U256.ofNat (hexToNat s)

def hexToAddress (s : String) : Evm.Address := Evm.Address.ofNat (hexToNat s)

/-! ## JSON accessors -/

private def jStr (j : Json) : Except String String := j.getStr?

private def jObj (j : Json) (k : String) : Except String Json := j.getObjVal? k

def jObjEntries (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj entries => .ok (entries.toArray.toList.map (fun ⟨k, v⟩ => (k, v)))
  | _            => .error "expected an object"

private def jArr (j : Json) (k : String) : Except String (Array Json) := do
  let v ← j.getObjVal? k
  v.getArr?

private def jHexBytes (j : Json) (k : String) : Except String ByteArray := do
  let s ← jStr (← j.getObjVal? k)
  match hexToBytes s with
  | some b => .ok b
  | none   => .error s!"invalid hex string for field '{k}': {s}"

private def jHexNat (j : Json) (k : String) : Except String Nat := do
  let s ← jStr (← j.getObjVal? k)
  .ok (hexToNat s)

private def jHexU256 (j : Json) (k : String) : Except String Evm.U256 := do
  return Evm.U256.ofNat (← jHexNat j k)

private def jHexAddr (j : Json) (k : String) : Except String Evm.Address := do
  return Evm.Address.ofNat (← jHexNat j k)

/-! ## Test schema -/

structure TestAccount where
  balance : Evm.U256
  nonce   : Nat
  code    : Evm.Bytes
  storage : List (Evm.U256 × Evm.U256)
  deriving Inhabited

/-- Raw transaction with every field any fork might need. Built from
    the JSON; per-fork dispatch in `applyBlockFor` projects it to the
    fork's typed `Transaction` sum (Berlin.Transaction / London.Transaction
    / Cancun.Transaction). Frontier-only call sites keep using the
    derived `Frontier.Transaction` via `toFrontier`. -/
structure RawTransaction where
  /-- EIP-2718 type tag: 0 = legacy, 1 = EIP-2930, 2 = EIP-1559,
      3 = EIP-4844, 4 = EIP-7702. -/
  txType               : Nat := 0
  chainId              : Evm.U256 := 0
  nonce                : Evm.U256
  /-- Pre-computed effective gas price for type-2 (so legacy call sites
      see the right per-gas price); equals `tx.gasPrice` for legacy/
      type-1; equals `min(maxFee, baseFee + maxPriority)` for type-2. -/
  effectiveGasPrice    : Evm.U256
  maxFeePerGas         : Evm.U256 := 0
  maxPriorityFeePerGas : Evm.U256 := 0
  maxFeePerBlobGas     : Evm.U256 := 0
  gas                  : Evm.U256
  to                   : Option Evm.Address
  value                : Evm.U256
  data                 : Evm.Bytes
  /-- EIP-2930 access list (type-1+). Empty for legacy / type-0. -/
  accessList           : List Evm.Berlin.AccessListEntry := []
  /-- EIP-4844 blob versioned hashes (type-3). Empty otherwise. -/
  blobVersionedHashes  : List Evm.Hash32 := []
  v                    : Evm.U256
  r                    : Evm.U256
  s                    : Evm.U256
  /-- Sender, when the test JSON provides it explicitly. Typed
      (EIP-2930+) txs need this because their signing-hash
      construction isn't wired into our ecrecover yet. Legacy txs
      omit it and `recoverSender` is used instead. -/
  sender               : Option Evm.Address := none
  deriving Inhabited

/-- Project a `RawTransaction` to the Frontier-legacy shape used by
    pre-Berlin forks (and as the `.legacy` payload at later forks).
    The effective gas price stands in for `gasPrice` so type-2 txs
    look like legacy txs paying the EIP-1559 effective rate. -/
def RawTransaction.toFrontier (rt : RawTransaction) : Evm.Frontier.Transaction :=
  { nonce    := rt.nonce
    gasPrice := rt.effectiveGasPrice
    gas      := rt.gas
    to       := rt.to
    value    := rt.value
    data     := rt.data
    v        := rt.v
    r        := rt.r
    s        := rt.s }

/-- Project a `RawTransaction` to the one tx record every fork's tx level takes
    (`Evm.Frontier.Vm.Tx.Tx`): type, nonce, gas, the fee fields, target, value, data, access
    list, blob hashes. -/
def RawTransaction.toTx (rt : RawTransaction) : Evm.Frontier.Vm.Tx.Tx :=
  { type := rt.txType, nonce := rt.nonce.toNat, gas := rt.gas.toNat,
    gasPrice := rt.effectiveGasPrice.toNat,
    maxFee := rt.maxFeePerGas.toNat, maxPrio := rt.maxPriorityFeePerGas.toNat,
    maxFeePerBlobGas := rt.maxFeePerBlobGas.toNat, to := rt.to, value := rt.value,
    data := rt.data, accessList := rt.accessList.map (fun e => (e.address, e.storageKeys)),
    blobHashes := rt.blobVersionedHashes }

structure ParsedBlockEntry where
  block : Evm.Frontier.Block
  hash  : Evm.U256
  /-- Raw tx records (one per `block.transactions[i]`), retained
      so post-Berlin dispatch can route typed payloads. -/
  rawTxs : List RawTransaction := []
  /-- EIP-4895 (Shanghai+) — empty list at pre-Shanghai forks. -/
  withdrawals : List Evm.Shanghai.Withdrawal := []
  /-- EIP-4788 (Cancun+) — zero hash at pre-Cancun forks. -/
  parentBeaconBlockRoot : Evm.Hash32 := 0
  /-- EIP-4844 (Cancun+) — 0 at pre-Cancun forks. -/
  blobGasUsed : Nat := 0
  /-- EIP-4844 (Cancun+) — 0 at pre-Cancun forks. -/
  excessBlobGas : Nat := 0

inductive PostExpectation where
  | accounts (xs : List (Evm.Address × TestAccount))
  | rootHash (h : Evm.Bytes)
  deriving Inhabited

structure ParsedTest where
  name          : String
  network       : String
  pre           : List (Evm.Address × TestAccount)
  genesisHash   : Evm.U256
  /-- The canonical chain head — the hash whose state we compare to
      the expected `postState` / `postStateHash`. Tests that simulate
      chain re-orgs may list blocks from multiple chains in `blocks`;
      `lastBlockHash` picks the winner. -/
  lastBlockHash : Evm.U256
  blocks        : List ParsedBlockEntry
  postExp       : PostExpectation

private def parseStorage (j : Json) : Except String (List (Evm.U256 × Evm.U256)) := do
  let entries ← jObjEntries j
  entries.mapM fun (k, v) => do
    let s ← jStr v
    return (hexToU256 k, hexToU256 s)

private def parseAccount (j : Json) : Except String TestAccount := do
  return {
    balance := ← jHexU256 j "balance"
    nonce   := ← jHexNat j "nonce"
    code    := ← jHexBytes j "code"
    storage := ← parseStorage (← j.getObjVal? "storage")
  }

private def parseAccounts (j : Json) :
    Except String (List (Evm.Address × TestAccount)) := do
  let entries ← jObjEntries j
  entries.mapM fun (k, v) => do
    return (hexToAddress k, ← parseAccount v)

private def parseTo (j : Json) : Except String (Option Evm.Address) := do
  let s ← jStr (← j.getObjVal? "to")
  if s == "" ∨ s == "0x" then return none
  return some (hexToAddress s)

/-- Optional hex-Nat field with a default. -/
private def jHexNatOr (j : Json) (k : String) (d : Nat) : Nat :=
  match j.getObjVal? k with
  | .ok v => match v.getStr? with
             | .ok s => hexToNat s
             | .error _ => d
  | .error _ => d

/-- Parse a single access-list entry: `{address, storageKeys: [...]}`. -/
private def parseAccessEntry (j : Json) :
    Except String Evm.Berlin.AccessListEntry := do
  let address ← jHexAddr j "address"
  let keysJson ← j.getObjVal? "storageKeys"
  let keysArr ← keysJson.getArr?
  let keys ← keysArr.toList.mapM (fun k => do
    let s ← k.getStr?
    return Evm.U256.ofNat (hexToNat s))
  return { address := address, storageKeys := keys }

/-- Parse the access list (empty/absent → []). -/
private def parseAccessList (j : Json) :
    Except String (List Evm.Berlin.AccessListEntry) :=
  match j.getObjVal? "accessList" with
  | .ok arrJson =>
    match arrJson.getArr? with
    | .ok arr => arr.toList.mapM parseAccessEntry
    | .error _ => .ok []
  | .error _ => .ok []

/-- Parse the blob-versioned-hashes list (empty/absent → []). -/
private def parseBlobHashes (j : Json) : Except String (List Evm.Hash32) :=
  match j.getObjVal? "blobVersionedHashes" with
  | .ok arrJson =>
    match arrJson.getArr? with
    | .ok arr => arr.toList.mapM (fun k => do
      let s ← k.getStr?
      return (Evm.U256.ofNat (hexToNat s) : Evm.Hash32))
    | .error _ => .ok []
  | .error _ => .ok []

/-- Parse a single transaction into the unified `RawTransaction` form.
    EIP-2718 typed transactions are recognised by the `type` field; the
    effective gas price is pre-computed (so the Frontier-legacy
    projection sees the correct per-gas price for type-2).

    The `gas`/`gasLimit` and `v`/`yParity` field-name aliases come
    from differing test authors; both are accepted. -/
private def parseRawTransaction (baseFeePerGas : Nat) (j : Json) :
    Except String RawTransaction := do
  let gasField := j.getObjVal? "gasLimit"
                  |>.orElseLazy fun _ => j.getObjVal? "gas"
  let parityField := j.getObjVal? "v"
                     |>.orElseLazy fun _ => j.getObjVal? "yParity"
  let txType : Nat := jHexNatOr j "type" 0
  let chainId : Evm.U256 := Evm.U256.ofNat (jHexNatOr j "chainId" 0)
  let maxFeePerGas : Nat := jHexNatOr j "maxFeePerGas" 0
  let maxPriorityFeePerGas : Nat := jHexNatOr j "maxPriorityFeePerGas" 0
  let maxFeePerBlobGas : Nat := jHexNatOr j "maxFeePerBlobGas" 0
  let effectiveGasPrice : Nat ←
    match j.getObjVal? "gasPrice" with
    | .ok v =>
      match v.getStr? with
      | .ok s => .ok (hexToNat s)
      | .error _ => .error "non-string gasPrice"
    | .error _ =>
      if maxFeePerGas = 0 then
        .error "tx missing gasPrice and maxFeePerGas"
      else
        .ok (min maxFeePerGas (baseFeePerGas + maxPriorityFeePerGas))
  let accessList ← parseAccessList j
  let blobHashes ← parseBlobHashes j
  let sender : Option Evm.Address ←
    match j.getObjVal? "sender" with
    | .ok v => match v.getStr? with
               | .ok s => .ok (some (Evm.Address.ofNat (hexToNat s)))
               | .error _ => .ok none
    | .error _ => .ok none
  return {
    txType               := txType
    chainId              := chainId
    nonce                := ← jHexU256 j "nonce"
    effectiveGasPrice    := Evm.U256.ofNat effectiveGasPrice
    maxFeePerGas         := Evm.U256.ofNat maxFeePerGas
    maxPriorityFeePerGas := Evm.U256.ofNat maxPriorityFeePerGas
    maxFeePerBlobGas     := Evm.U256.ofNat maxFeePerBlobGas
    gas                  := Evm.U256.ofNat (hexToNat (← jStr (← gasField)))
    to                   := ← parseTo j
    value                := ← jHexU256 j "value"
    data                 := ← jHexBytes j "data"
    accessList           := accessList
    blobVersionedHashes  := blobHashes
    v                    := Evm.U256.ofNat (hexToNat (← jStr (← parityField)))
    r                    := ← jHexU256 j "r"
    s                    := ← jHexU256 j "s"
    sender               := sender
  }

/-- Back-compat alias: callers that want a Frontier-shaped tx (pre-Berlin
    dispatch path) get the legacy projection of the raw tx. -/
private def parseTransaction (baseFeePerGas : Nat) (j : Json) :
    Except String Evm.Frontier.Transaction := do
  return (← parseRawTransaction baseFeePerGas j).toFrontier

private def parseHeader (j : Json) : Except String Evm.Frontier.Header := do
  return {
    parentHash       := Evm.U256.ofNat (← jHexNat j "parentHash")
    -- JSON calls it `uncleHash`; spec field is `ommersHash`.
    ommersHash       := Evm.U256.ofNat (← jHexNat j "uncleHash")
    coinbase         := ← jHexAddr j "coinbase"
    stateRoot        := Evm.U256.ofNat (← jHexNat j "stateRoot")
    transactionsRoot := Evm.U256.ofNat (← jHexNat j "transactionsTrie")
    receiptRoot      := Evm.U256.ofNat (← jHexNat j "receiptTrie")
    bloom            := ← jHexBytes j "bloom"
    difficulty       := ← jHexNat j "difficulty"
    number           := ← jHexNat j "number"
    gasLimit         := ← jHexNat j "gasLimit"
    gasUsed          := ← jHexNat j "gasUsed"
    timestamp        := ← jHexNat j "timestamp"
    extraData        := ← jHexBytes j "extraData"
    mixDigest        := Evm.U256.ofNat (← jHexNat j "mixHash")
    nonce            := ← jHexBytes j "nonce"
    -- London+ adds baseFeePerGas to the header; default to 0 for
    -- pre-London JSON.
    baseFeePerGas    :=
      match j.getObjVal? "baseFeePerGas" with
      | .ok v => match v.getStr? with
                 | .ok s => hexToNat s
                 | .error _ => 0
      | .error _ => 0
  }

private def parseWithdrawal (j : Json) : Except String Evm.Shanghai.Withdrawal := do
  return {
    index          := ← jHexNat j "index"
    validatorIndex := ← jHexNat j "validatorIndex"
    address        := ← jHexAddr j "address"
    amount         := ← jHexNat j "amount"
  }

private def parseBlock (j : Json) : Except String ParsedBlockEntry := do
  let bhJson := (← j.getObjVal? "blockHeader")
  let header ← parseHeader bhJson
  let hash   := Evm.U256.ofNat (← jHexNat bhJson "hash")
  let txArr  ← jArr j "transactions"
  let rawTxs ← txArr.toList.mapM (parseRawTransaction header.baseFeePerGas)
  let txs    := rawTxs.map (·.toFrontier)
  let omArr  ← jArr j "uncleHeaders"
  let ommers ← omArr.toList.mapM parseHeader
  -- EIP-4895 withdrawals — present on Shanghai+ blocks, absent
  -- pre-Shanghai. Tolerate both.
  let withdrawals : List Evm.Shanghai.Withdrawal ←
    match j.getObjVal? "withdrawals" with
    | .ok wArr =>
      match wArr.getArr? with
      | .ok arr => arr.toList.mapM parseWithdrawal
      | .error _ => .ok []
    | .error _ => .ok []
  -- Cancun-only header fields (parentBeaconBlockRoot / blobGasUsed /
  -- excessBlobGas). Read them best-effort; default to zero.
  let pbbr : Evm.Hash32 ←
    match bhJson.getObjVal? "parentBeaconBlockRoot" with
    | .ok v => match v.getStr? with
               | .ok s => .ok (Evm.U256.ofNat (hexToNat s))
               | .error _ => .ok 0
    | .error _ => .ok 0
  let bgu : Nat ←
    match bhJson.getObjVal? "blobGasUsed" with
    | .ok v => match v.getStr? with
               | .ok s => .ok (hexToNat s)
               | .error _ => .ok 0
    | .error _ => .ok 0
  let ebg : Nat ←
    match bhJson.getObjVal? "excessBlobGas" with
    | .ok v => match v.getStr? with
               | .ok s => .ok (hexToNat s)
               | .error _ => .ok 0
    | .error _ => .ok 0
  return { block := { header := header, transactions := txs, ommers := ommers },
           hash := hash,
           rawTxs := rawTxs,
           withdrawals := withdrawals,
           parentBeaconBlockRoot := pbbr,
           blobGasUsed := bgu,
           excessBlobGas := ebg }

def parseTest (name : String) (j : Json) : Except String ParsedTest := do
  let network ← jStr (← j.getObjVal? "network")
  let pre     ← parseAccounts (← j.getObjVal? "pre")
  let postExp : PostExpectation ←
    match j.getObjVal? "postState" with
    | .ok psJson => .accounts <$> parseAccounts psJson
    | .error _ =>
      let hashStr ← jStr (← j.getObjVal? "postStateHash")
      match hexToBytes hashStr with
      | some b => .ok (.rootHash b)
      | none   => .error s!"invalid postStateHash: {hashStr}"
  let blkArr  ← jArr j "blocks"
  let blocks  ← blkArr.toList.mapM parseBlock
  let genHash := Evm.U256.ofNat
    (← jHexNat (← j.getObjVal? "genesisBlockHeader") "hash")
  let lastHash := Evm.U256.ofNat (← jHexNat j "lastblockhash")
  return { name := name, network := network, pre := pre,
           genesisHash := genHash, lastBlockHash := lastHash,
           blocks := blocks, postExp := postExp }

/-! ## Runner -/

private def buildState (accounts : List (Evm.Address × TestAccount)) :
    Evm.Frontier.State :=
  accounts.foldl (init := Evm.Frontier.State.empty) fun st (addr, a) =>
    let st := st.setAccount addr {
      nonce := a.nonce, balance := a.balance, code := a.code }
    a.storage.foldl (init := st) fun st (k, v) => st.setStorage addr k v

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 0x30) else Char.ofNat (n - 10 + 0x61)

private def addrHex (a : Evm.Address) : String :=
  let n := a.toNat
  let chrs := List.range 40 |>.map fun i =>
    hexChar ((n >>> ((39 - i) * 4)) &&& 0xf)
  "0x" ++ String.ofList chrs

structure Mismatch where
  field   : String
  address : Evm.Address
  slot    : Option Evm.U256
  expected: String
  got     : String

def fmtMismatch (m : Mismatch) : String :=
  let slotStr := match m.slot with
    | some s => s!" slot={s.toNat}"
    | none   => ""
  s!"  {m.field} mismatch at {addrHex m.address}{slotStr}\n" ++
  s!"    expected: {m.expected}\n" ++
  s!"    got:      {m.got}"

private def compareAccount (addr : Evm.Address) (expected : TestAccount)
    (actual : Evm.Frontier.Account)
    (storageAt : Evm.U256 → Evm.U256) : List Mismatch := Id.run do
  let mut ms : List Mismatch := []
  if actual.nonce ≠ expected.nonce then
    ms := ms ++ [{
      field := "nonce", address := addr, slot := none,
      expected := s!"{expected.nonce}", got := s!"{actual.nonce}" }]
  if actual.balance ≠ expected.balance then
    ms := ms ++ [{
      field := "balance", address := addr, slot := none,
      expected := s!"{expected.balance.toNat}", got := s!"{actual.balance.toNat}" }]
  if actual.code.size ≠ expected.code.size then
    ms := ms ++ [{
      field := "code-size", address := addr, slot := none,
      expected := s!"{expected.code.size}", got := s!"{actual.code.size}" }]
  for (slot, v) in expected.storage do
    let gotV := storageAt slot
    if gotV ≠ v then
      ms := ms ++ [{
        field := "storage", address := addr, slot := some slot,
        expected := s!"{v.toNat}", got := s!"{gotV.toNat}" }]
  pure ms

private def bytesHex (b : Evm.Bytes) : String := Id.run do
  let mut out := "0x"
  for i in [0:b.size] do
    let byte := b.get! i
    out := out ++ String.ofList
      [hexChar ((byte.toNat >>> 4) &&& 0xf), hexChar (byte.toNat &&& 0xf)]
  pure out

private def assocFind {α β} [DecidableEq α] (m : List (α × β)) (k : α) : Option β :=
  (m.find? (fun e => e.1 = k)).map Prod.snd

/-- Forks the harness currently dispatches to. Each name must match the
    test JSON's `network` field exactly. ConstantinopleFix is the name
    ethereum/tests uses for Petersburg (Constantinople-without-EIP-1283,
    the version that actually shipped to mainnet). -/
def supportedNetworks : List String :=
  ["Frontier", "Homestead", "EIP150", "EIP158", "Byzantium",
   "Constantinople", "ConstantinopleFix", "Istanbul",
   "Berlin", "London", "Paris", "Merge",
   "Shanghai", "Cancun"]

/-- Build a Shanghai header from a parsed Frontier-shaped header. The
    field rename (`mixDigest` → `prevRandao`) is a no-op at the byte
    level; `withdrawalsRoot` isn't validated by the harness, so we
    just default to zero. -/
private def shanghaiHeaderOf (h : Evm.Frontier.Header) : Evm.Shanghai.Header :=
  { parentHash       := h.parentHash
    ommersHash       := h.ommersHash
    coinbase         := h.coinbase
    stateRoot        := h.stateRoot
    transactionsRoot := h.transactionsRoot
    receiptRoot      := h.receiptRoot
    logsBloom        := h.bloom
    difficulty       := h.difficulty
    number           := h.number
    gasLimit         := h.gasLimit
    gasUsed          := h.gasUsed
    timestamp        := h.timestamp
    extraData        := h.extraData
    prevRandao       := h.mixDigest
    nonce            := h.nonce
    baseFeePerGas    := h.baseFeePerGas
    withdrawalsRoot  := 0 }

/-- Build a Cancun header from a parsed Frontier-shaped header plus
    the Cancun-specific fields parsed alongside. -/
private def cancunHeaderOf (h : Evm.Frontier.Header)
    (pbbr : Evm.Hash32) (blobGasUsed excessBlobGas : Nat) :
    Evm.Cancun.Header :=
  { parentHash            := h.parentHash
    ommersHash            := h.ommersHash
    coinbase              := h.coinbase
    stateRoot             := h.stateRoot
    transactionsRoot      := h.transactionsRoot
    receiptRoot           := h.receiptRoot
    bloom                 := h.bloom
    difficulty            := h.difficulty
    number                := h.number
    gasLimit              := h.gasLimit
    gasUsed               := h.gasUsed
    timestamp             := h.timestamp
    extraData             := h.extraData
    mixDigest             := h.mixDigest
    nonce                 := h.nonce
    baseFeePerGas         := Evm.U256.ofNat h.baseFeePerGas
    withdrawalsRoot       := 0
    blobGasUsed           := blobGasUsed
    excessBlobGas         := excessBlobGas
    parentBeaconBlockRoot := pbbr }

/-- Dispatch `applyBlock` by fork name. The test JSON uses
    `"EIP150"` for Tangerine Whistle, `"EIP158"` for Spurious Dragon,
    `"ConstantinopleFix"` for Petersburg, and `"Merge"` interchangeably
    with `"Paris"`. Shanghai+ takes a richer parsed entry so the
    withdrawal list / Cancun-specific header fields can be threaded
    into the fork-shaped Block. -/
private def applyBlockFor (network : String)
    (state : Evm.Frontier.State) (entry : ParsedBlockEntry)
    (hashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult :=
  let block := entry.block
  match network with
  | "Frontier"          => Evm.Frontier.applyBlock state block hashes
  | "Homestead"         => Evm.Homestead.applyBlock state block hashes
  | "EIP150"            => Evm.TangerineWhistle.applyBlock state block hashes
  | "EIP158"            => Evm.SpuriousDragon.applyBlock state block hashes
  | "Byzantium"         => Evm.Byzantium.applyBlock state block hashes
  | "Constantinople"    => Evm.Constantinople.applyBlock state block hashes
  | "ConstantinopleFix" => Evm.Petersburg.applyBlock state block hashes
  | "Istanbul"          => Evm.Istanbul.applyBlock state block hashes
  | "Berlin" =>
    -- Route typed (EIP-2930) txs through Berlin's typed driver so
    -- access-list intrinsic surcharge + EIP-2929 pre-warming kick in.
    -- Senders: prefer the harness-provided `sender`; fall back to
    -- ecrecover for legacy txs that don't carry one.
    let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
      entry.rawTxs.mapM fun rt => do
        let berlinTx := rt.toTx
        let sender ← match rt.sender with
          | some a => .ok a
          | none =>
            match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
            | some s => .ok s
            | none   => .error "Berlin: invalid signature, no sender field"
        return (berlinTx, sender)
    withSenders.bind fun txs =>
      Evm.Berlin.applyBlockTyped state block.header block.ommers txs hashes
  | "London" =>
    let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
      entry.rawTxs.mapM fun rt => do
        let londonTx := rt.toTx
        let sender ← match rt.sender with
          | some a => .ok a
          | none =>
            match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
            | some s => .ok s
            | none   => .error "London: invalid signature, no sender field"
        return (londonTx, sender)
    withSenders.bind fun txs =>
      Evm.London.applyBlockTyped state block.header block.ommers txs hashes
  -- ethereum/tests uses both "Paris" and the older "Merge" label for
  -- the EIP-3675 fork (Block reward = 0, ommers banned).
  | "Paris" =>
    let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
      entry.rawTxs.mapM fun rt => do
        let tx := rt.toTx
        let sender ← match rt.sender with
          | some a => .ok a
          | none =>
            match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
            | some s => .ok s
            | none   => .error "Paris: invalid signature, no sender field"
        return (tx, sender)
    withSenders.bind fun txs =>
      Evm.Paris.applyBlockTyped state block.header block.ommers txs hashes
  | "Merge" =>
    -- `Merge` is just an older label for Paris; reuse the same path.
    let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
      entry.rawTxs.mapM fun rt => do
        let tx := rt.toTx
        let sender ← match rt.sender with
          | some a => .ok a
          | none =>
            match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
            | some s => .ok s
            | none   => .error "Merge: invalid signature, no sender field"
        return (tx, sender)
    withSenders.bind fun txs =>
      Evm.Paris.applyBlockTyped state block.header block.ommers txs hashes
  | "Shanghai" =>
    -- Two paths: pure-legacy blocks go through Shanghai's own
    -- processTransaction (which has EIP-3860 init-code surcharge);
    -- blocks with any typed tx route through the London-delegating
    -- typed driver (loses EIP-3860 for typed CREATEs — rare).
    let allLegacy := entry.rawTxs.all (·.txType = 0)
    if allLegacy then
      let decoded : Evm.Shanghai.DecodedBlock :=
        { header       := shanghaiHeaderOf block.header
          transactions := block.transactions
          ommers       := block.ommers.map shanghaiHeaderOf
          withdrawals  := entry.withdrawals }
      Evm.Shanghai.applyBlock state decoded hashes
    else
      let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
        entry.rawTxs.mapM fun rt => do
          let tx := rt.toTx
          let sender ← match rt.sender with
            | some a => .ok a
            | none =>
              match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
              | some s => .ok s
              | none   => .error "Shanghai: invalid signature, no sender field"
          return (tx, sender)
      withSenders.bind fun txs =>
        Evm.Shanghai.applyBlockTyped state (shanghaiHeaderOf block.header)
          txs entry.withdrawals hashes
  | "Cancun" =>
    -- Dual-path like Shanghai: pure-legacy blocks via the existing
    -- Cancun.applyBlock; any typed tx → typed driver. Cancun's
    -- block-level adds the EIP-4788 beacon-root system call before
    -- per-tx processing.
    let allLegacy := entry.rawTxs.all (·.txType = 0)
    if allLegacy then
      let cancun : Evm.Cancun.Block :=
        { header := cancunHeaderOf block.header entry.parentBeaconBlockRoot
                     entry.blobGasUsed entry.excessBlobGas
          transactions := block.transactions
          ommers       := block.ommers
          withdrawals  := entry.withdrawals }
      Evm.Cancun.applyBlock state cancun hashes
    else
      let withSenders : Except String (List (Evm.Frontier.Vm.Tx.Tx × Evm.Address)) :=
        entry.rawTxs.mapM fun rt => do
          let tx := rt.toTx
          let sender ← match rt.sender with
            | some a => .ok a
            | none =>
              match Evm.SpuriousDragon.Utils.recoverSender rt.toFrontier with
              | some s => .ok s
              | none   => .error "Cancun: invalid signature, no sender field"
          return (tx, sender)
      let cancunHdr :=
        cancunHeaderOf block.header entry.parentBeaconBlockRoot
                       entry.blobGasUsed entry.excessBlobGas
      withSenders.bind fun txs =>
        Evm.Cancun.applyBlockTyped state cancunHdr txs entry.withdrawals hashes
  | n => .error s!"unsupported fork: {n}"

/-- Apply blocks in order, dispatched by `parentHash` rather than threaded
    linearly. This handles multi-chain tests: a block whose `parentHash`
    isn't the previous block's hash forks off an earlier state. The final
    state is whichever block hash `lastBlockHash` points to. -/
private def applyAll (test : ParsedTest) (preState : Evm.Frontier.State) :
    List (Evm.U256 × Evm.Frontier.State) × List (Evm.U256 × List Evm.U256) :=
  let init :
      List (Evm.U256 × Evm.Frontier.State) × List (Evm.U256 × List Evm.U256) :=
    ([(test.genesisHash, preState)], [(test.genesisHash, [])])
  test.blocks.foldl (init := init) fun (sm, hm) entry =>
    let parentHash := entry.block.header.parentHash
    match assocFind sm parentHash, assocFind hm parentHash with
    | some ps, some ph =>
      let thisHashes := ph ++ [parentHash]
      match applyBlockFor test.network ps entry thisHashes with
      | .ok r => (sm ++ [(entry.hash, r.state)], hm ++ [(entry.hash, thisHashes)])
      | .error _ => (sm, hm)
    | _, _ => (sm, hm)

def runTest (test : ParsedTest) : Except String (List Mismatch) := do
  let preState := buildState test.pre
  let (stateMap, _) := applyAll test preState
  let finalState := (assocFind stateMap test.lastBlockHash).getD Evm.Frontier.State.empty
  match test.postExp with
  | .accounts xs =>
    let mut allMismatches : List Mismatch := []
    for (addr, expected) in xs do
      let actual := finalState.getAccount addr
      let storageAt := fun slot => finalState.getStorage addr slot
      allMismatches := allMismatches ++ compareAccount addr expected actual storageAt
    return allMismatches
  | .rootHash expected =>
    let computed := Evm.Frontier.stateRootBytes finalState
    -- Compare byte-by-byte; ByteArray equality.
    let same := Id.run do
      if computed.size ≠ expected.size then pure false
      else
        let mut ok := true
        for i in [0:computed.size] do
          if computed.get! i ≠ expected.get! i then ok := false
        pure ok
    if same then return []
    else
      -- Dump accounts on mismatch so we can investigate. (Only does
      -- harm to debug-test output; passes don't dump.)
      let count := finalState.accounts.length
      let mut summary : String :=
        s!"  account count = {count}\n"
      for (addr, acc) in finalState.accounts.take 60 do
        summary := summary ++
          s!"    {addrHex addr}: nonce={acc.nonce} bal={acc.balance.toNat} code-size={acc.code.size}\n"
      let storageCount := finalState.storage.length
      summary := summary ++ s!"  storage entries: {storageCount}\n"
      for ((addr, slot), v) in finalState.storage.take 20 do
        summary := summary ++
          s!"    {addrHex addr} [{slot.toNat}] = {v.toNat}\n"
      return [{
        field := "stateRoot", address := 0, slot := none,
        expected := bytesHex expected,
        got := bytesHex computed ++ "\n" ++ summary }]

/-! ## CLI -/

def runFile (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let entries ← IO.ofExcept (jObjEntries json)
  let mut pass := 0
  let mut fail := 0
  let mut skip := 0
  for (name, body) in entries do
    match parseTest name body with
    | .error e =>
      IO.println s!"PARSE-ERROR  {name}: {e}"
      fail := fail + 1
    | .ok t =>
      if t.network ≠ "Frontier" then
        skip := skip + 1
      else
        match runTest t with
        | .error e =>
          IO.println s!"RUN-ERROR    {name}: {e}"
          fail := fail + 1
        | .ok [] =>
          IO.println s!"PASS         {name}"
          pass := pass + 1
        | .ok ms =>
          IO.println s!"FAIL         {name}"
          for m in ms do
            IO.println (fmtMismatch m)
          fail := fail + 1
  IO.println s!"---"
  IO.println s!"summary: pass={pass} fail={fail} skip-non-frontier={skip}"

end Replay

partial def collectJsonFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  let attrs ← path.metadata
  match attrs.type with
  | .file =>
    if path.extension = some "json" then return #[path] else return #[]
  | .dir =>
    let mut out : Array System.FilePath := #[]
    for entry in (← path.readDir) do
      out := out ++ (← collectJsonFiles entry.path)
    return out
  | _ => return #[]

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println "usage: replay <path-to-test.json | dir>"
  | path :: _ =>
    let files ← collectJsonFiles ⟨path⟩
    let mut totalPass := 0
    let mut totalFail := 0
    let mut totalSkip := 0
    for f in files do
      let contents ← IO.FS.readFile f
      let json ← IO.ofExcept (Lean.Json.parse contents)
      let entries ← IO.ofExcept (Replay.jObjEntries json)
      for (name, body) in entries do
        match Replay.parseTest name body with
        | .error e =>
          IO.println s!"PARSE-ERROR  {name}: {e}"
          totalFail := totalFail + 1
        | .ok t =>
          if ¬ Replay.supportedNetworks.contains t.network then
            totalSkip := totalSkip + 1
          else
            match Replay.runTest t with
            | .error e =>
              IO.println s!"RUN-ERROR    {name}: {e}"
              totalFail := totalFail + 1
            | .ok [] =>
              totalPass := totalPass + 1
            | .ok ms =>
              IO.println s!"FAIL         {name}"
              for m in ms.take 3 do
                IO.println (Replay.fmtMismatch m)
              if ms.length > 3 then
                IO.println s!"    ... and {ms.length - 3} more mismatches"
              totalFail := totalFail + 1
    IO.println "---"
    IO.println s!"summary: pass={totalPass} fail={totalFail} skip={totalSkip}"
