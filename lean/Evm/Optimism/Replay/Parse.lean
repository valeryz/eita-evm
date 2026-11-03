/-
  Evm.Optimism.Replay.Parse — JSON parser for Base-mainnet blocks
  (the shape returned by `eth_getBlockByNumber` against op-geth /
  reth-op).

  Covers:
    * `BaseHeader` — block header with the OP-specific fields
      (extraData carries Holocene+Isthmus EIP-1559 params; the
      `withdrawalsRoot` carries the L2ToL1MessagePasser storage root
      from Isthmus onward; the rest tracks the Ethereum header
      schema).
    * `parseDepositedTx` — extract a `Bedrock.DepositedTx` from one
      tx JSON object (where `type = "0x7e"`).

  Non-deposited user txs reuse the existing mainnet parser shape
  (see `Replay.RawTransaction`); they're wired in by the block
  driver, not here.
-/

import Lean.Data.Json
import Evm.BaseTypes
import Evm.Optimism.Bedrock.Transactions

namespace Evm.Optimism.Replay.Parse

open Lean (Json)

/-! ## Hex helpers (small dupe of `Replay.lean` — keeps this module
    decoupled from the mainnet replay file). -/

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def stripHex (s : String) : String :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then String.ofList (s.toList.drop 2) else s

def hexToNat (s : String) : Nat :=
  (stripHex s).foldl (init := 0) fun acc c => acc * 16 + (hexDigit? c).getD 0

private partial def hexBytesLoop : List Char → ByteArray → Option ByteArray
  | [],           acc => some acc
  | [_],          _   => none   -- odd length should be padded by caller
  | a :: b :: t,  acc => do
    let hi ← hexDigit? a
    let lo ← hexDigit? b
    hexBytesLoop t (acc.push (UInt8.ofNat (hi * 16 + lo)))

def hexToBytes (s : String) : Option ByteArray :=
  let s := stripHex s
  let s := if s.length % 2 = 1 then "0" ++ s else s
  hexBytesLoop s.toList ByteArray.empty

def hexToU256 (s : String) : Evm.U256 := Evm.U256.ofNat (hexToNat s)

def hexToAddress (s : String) : Evm.Address :=
  Evm.Address.ofNat (hexToNat s)

/-- A 32-byte hash field from JSON. Tolerant of short hexes (pads
    high). -/
def hexToHash32 (s : String) : Evm.Hash32 :=
  BitVec.ofNat 256 (hexToNat s)

/-! ## JSON accessors -/

private def jStr (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

private def jOptStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok v   => match v with
               | .null => .ok none
               | _ => .ok (some (v.getStr?.toOption.getD ""))
  | .error _ => .ok none

private def jHexNat (j : Json) (k : String) : Except String Nat := do
  return hexToNat (← jStr j k)

private def jHexU256 (j : Json) (k : String) : Except String Evm.U256 := do
  return Evm.U256.ofNat (← jHexNat j k)

private def jHexAddr (j : Json) (k : String) : Except String Evm.Address := do
  return Evm.Address.ofNat (← jHexNat j k)

private def jHexBytes (j : Json) (k : String) : Except String Evm.Bytes := do
  let s ← jStr j k
  match hexToBytes s with
  | some b => .ok b
  | none   => .error s!"invalid hex string for field '{k}': {s}"

private def jHexHash32 (j : Json) (k : String) : Except String Evm.Hash32 := do
  return hexToHash32 (← jStr j k)

/-! ## Base block header -/

/-- Header fields we read from a Base block JSON. Extends the
    Ethereum-mainnet header with two OP additions:
      * `extraData` carries per-block EIP-1559 params at Holocene+
        (9 bytes) plus operator-fee scalars at Isthmus+ (8 more).
      * `withdrawalsRoot` carries the L2ToL1MessagePasser storage
        root at Isthmus+ (was empty-trie root pre-Isthmus). -/
structure BaseHeader where
  parentHash       : Evm.Hash32
  coinbase         : Evm.Address       -- always SequencerFeeVault on OP
  stateRoot        : Evm.Hash32
  transactionsRoot : Evm.Hash32
  receiptsRoot     : Evm.Hash32
  withdrawalsRoot  : Option Evm.Hash32  -- absent pre-Canyon
  number           : Nat
  gasLimit         : Nat
  gasUsed          : Nat
  timestamp        : Nat
  baseFeePerGas    : Nat
  mixHash          : Evm.Hash32         -- prevRandao on PoS
  extraData        : Evm.Bytes
  blobGasUsed      : Option Nat         -- present from Ecotone
  excessBlobGas    : Option Nat         -- present from Ecotone
  deriving Repr

def parseHeader (j : Json) : Except String BaseHeader := do
  let withdrawalsRoot :=
    match jHexHash32 j "withdrawalsRoot" with
    | .ok h => some h
    | .error _ => none
  let blobGasUsed :=
    match jHexNat j "blobGasUsed" with
    | .ok n => some n
    | .error _ => none
  let excessBlobGas :=
    match jHexNat j "excessBlobGas" with
    | .ok n => some n
    | .error _ => none
  return {
    parentHash       := ← jHexHash32 j "parentHash"
    coinbase         := ← jHexAddr   j "miner"
    stateRoot        := ← jHexHash32 j "stateRoot"
    transactionsRoot := ← jHexHash32 j "transactionsRoot"
    receiptsRoot     := ← jHexHash32 j "receiptsRoot"
    withdrawalsRoot  := withdrawalsRoot
    number           := ← jHexNat    j "number"
    gasLimit         := ← jHexNat    j "gasLimit"
    gasUsed          := ← jHexNat    j "gasUsed"
    timestamp        := ← jHexNat    j "timestamp"
    baseFeePerGas    := ← jHexNat    j "baseFeePerGas"
    mixHash          := ← jHexHash32 j "mixHash"
    extraData        := ← jHexBytes  j "extraData"
    blobGasUsed      := blobGasUsed
    excessBlobGas    := excessBlobGas
  }

/-! ## Deposited tx -/

/-- Extract one deposited tx from a JSON tx object. Caller is
    responsible for filtering on `type = "0x7e"` first. -/
def parseDepositedTx (j : Json) : Except String Evm.Optimism.Bedrock.DepositedTx := do
  let to : Option Evm.Address :=
    match j.getObjVal? "to" with
    | .ok (Json.str s) => if s == "" then none else some (hexToAddress s)
    | .ok Json.null    => none
    | _                => none
  let mint : Evm.U256 :=
    match j.getObjVal? "mint" with
    | .ok (Json.str s) => hexToU256 s
    | _ => 0
  let sourceHash :=
    match jHexHash32 j "sourceHash" with
    | .ok h => h
    | .error _ => 0
  let isSystemTx :=
    match j.getObjVal? "isSystemTx" with
    | .ok (Json.bool b) => b
    | _ => false
  return {
    sourceHash := sourceHash
    from_      := ← jHexAddr   j "from"
    to         := to
    mint       := mint
    value      := ← jHexU256   j "value"
    gas        := ← jHexU256   j "gas"
    isSystemTx := isSystemTx
    data       := ← jHexBytes  j "input"
  }

/-- Is this tx the deposited (type 0x7E) variant? -/
def isDeposited (j : Json) : Bool :=
  match j.getObjVal? "type" with
  | .ok (Json.str s) => s == "0x7e" ∨ s == "0x7E"
  | _ => false

end Evm.Optimism.Replay.Parse
