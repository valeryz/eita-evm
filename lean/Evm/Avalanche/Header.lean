/-
  Evm.Avalanche.Header — Coreth header RLP layout (Etna → Fortuna → Granite → Helicon)
  and SAE consensus-header invariants.

  Source: avalanchego
    graft/coreth/plugin/evm/customtypes/gen_header_serializable_rlp.go  HeaderSerializable.EncodeRLP
    graft/coreth/plugin/evm/customtypes/header_ext.go                   HeaderExtra
    vms/saevm/saexec                                                    settledHeight & worst-case gasUsed
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Avalanche.Forks

namespace Evm.Avalanche.Header

/-- Coreth block header fields in exact `HeaderSerializable.EncodeRLP` consensus order
    (16 mandatory fields through `extDataHash`, followed by 14 optional trailing fields). -/
structure CorethHeader where
  -- Mandatory 16 fields (indices 0..15)
  parentHash          : Evm.Bytes
  uncleHash           : Evm.Bytes
  coinbase            : Evm.Bytes
  stateRoot           : Evm.Bytes
  txHash              : Evm.Bytes
  receiptHash         : Evm.Bytes
  bloom               : Evm.Bytes
  difficulty          : Nat
  number              : Nat
  gasLimit            : Nat
  gasUsed             : Nat
  timestamp           : Nat
  extraData           : Evm.Bytes
  mixDigest           : Evm.Bytes
  nonce               : Evm.Bytes
  extDataHash         : Evm.Bytes
  -- Optional trailing fields (indices 16..29); trailing `none`s are omitted, interior `none`s
  -- encode as empty byte string (RLP 0x80).
  baseFee             : Option Nat       := none
  extDataGasUsed      : Option Nat       := none
  blockGasCost        : Option Nat       := none
  blobGasUsed         : Option Nat       := none
  excessBlobGas       : Option Nat       := none
  parentBeaconRoot    : Option Evm.Bytes := none
  timeMilliseconds    : Option Nat       := none
  minDelayExcess      : Option Nat       := none
  targetExponent      : Option Nat       := none
  minPriceExponent    : Option Nat       := none
  settledHeight       : Option Nat       := none
  settledGasUnix      : Option Nat       := none
  settledGasNumerator : Option Nat       := none
  settledExcess       : Option Nat       := none

private def optNatItem (x : Option Nat) : Option Evm.Rlp.Item :=
  x.map (fun v => .bytes (Evm.Rlp.natToBytes v))

private def optBytesItem (x : Option Evm.Bytes) : Option Evm.Rlp.Item :=
  x.map .bytes

/-- Drop trailing `none` entries and encode any remaining interior `none` as empty bytes (`0x80`). -/
def trimOptionalItems (xs : List (Option Evm.Rlp.Item)) : List Evm.Rlp.Item :=
  let rec go : List (Option Evm.Rlp.Item) → List Evm.Rlp.Item
    | [] => []
    | none :: rest =>
      match go rest with
      | [] => []
      | tail => .bytes ByteArray.empty :: tail
    | some x :: rest => x :: go rest
  go xs

/-- Encode a `CorethHeader` into its consensus RLP list (`HeaderSerializable.EncodeRLP`). -/
def encodeCorethHeaderRlp (h : CorethHeader) : Evm.Rlp.Item :=
  let mandatory : List Evm.Rlp.Item :=
    [ .bytes h.parentHash
    , .bytes h.uncleHash
    , .bytes h.coinbase
    , .bytes h.stateRoot
    , .bytes h.txHash
    , .bytes h.receiptHash
    , .bytes h.bloom
    , .bytes (Evm.Rlp.natToBytes h.difficulty)
    , .bytes (Evm.Rlp.natToBytes h.number)
    , .bytes (Evm.Rlp.natToBytes h.gasLimit)
    , .bytes (Evm.Rlp.natToBytes h.gasUsed)
    , .bytes (Evm.Rlp.natToBytes h.timestamp)
    , .bytes h.extraData
    , .bytes h.mixDigest
    , .bytes h.nonce
    , .bytes h.extDataHash ]
  let optional : List (Option Evm.Rlp.Item) :=
    [ optNatItem h.baseFee
    , optNatItem h.extDataGasUsed
    , optNatItem h.blockGasCost
    , optNatItem h.blobGasUsed
    , optNatItem h.excessBlobGas
    , optBytesItem h.parentBeaconRoot
    , optNatItem h.timeMilliseconds
    , optNatItem h.minDelayExcess
    , optNatItem h.targetExponent
    , optNatItem h.minPriceExponent
    , optNatItem h.settledHeight
    , optNatItem h.settledGasUnix
    , optNatItem h.settledGasNumerator
    , optNatItem h.settledExcess ]
  .list (mandatory ++ trimOptionalItems optional)

/-- Number of RLP list items expected for a canonical header of each supported Avalanche fork. -/
def expectedFieldCount : AvaxFork → Nat
  | .preEtna => 19 -- ApricotPhase4..Durango: through blockGasCost
  | .etna    => 22 -- + blobGasUsed, excessBlobGas, parentBeaconRoot
  | .fortuna => 22 -- same header shape as Etna
  | .granite => 24 -- + timeMilliseconds, minDelayExcess
  | .helicon => 30 -- + targetExponent, minPriceExponent, settledHeight, settledGasUnix, settledGasNumerator, settledExcess

/-- Which executed block's state root a header commits to.
    Under synchronous execution (pre-Helicon), `stateRoot` commits to `number`.
    Under Helicon/SAE (`settledHeight = some s`), `stateRoot` commits to block `s ≤ number`. -/
def stateRootBlock (number : Nat) (settledHeight : Option Nat) : Option Nat :=
  match settledHeight with
  | none => some number
  | some s => if s ≤ number then some s else none

/-- Under Helicon/SAE, consensus header `gasUsed` is the worst-case bound:
    sum of tx gas limits plus atomic transaction gas. -/
def saeConsensusGasUsed (txGasLimits : List Nat) (atomicGas : Nat) : Nat :=
  txGasLimits.foldl (· + ·) 0 + atomicGas

theorem trimOptionalItems_all_none :
    ∀ n : Nat, trimOptionalItems (List.replicate n none) = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, trimOptionalItems] at ih ⊢
    simp [trimOptionalItems.go, ih]

theorem stateRootBlock_sync (number : Nat) :
    stateRootBlock number none = some number := rfl

theorem stateRootBlock_sae_le (number s : Nat) (h : s ≤ number) :
    stateRootBlock number (some s) = some s := by
  simp [stateRootBlock, h]

theorem stateRootBlock_sae_future_none (number s : Nat) (h : number < s) :
    stateRootBlock number (some s) = none := by
  have hnot : ¬ (s ≤ number) := by omega
  simp [stateRootBlock, hnot]

theorem stateRootBlock_le_number (number : Nat) (sh : Option Nat) (r : Nat)
    (h : stateRootBlock number sh = some r) : r ≤ number := by
  cases sh with
  | none =>
    simp [stateRootBlock] at h
    omega
  | some s =>
    simp only [stateRootBlock] at h
    split at h
    · injection h with h'; omega
    · cases h

theorem expectedFieldCount_monotone (a b : AvaxFork) (h : a.ord ≤ b.ord) :
    expectedFieldCount a ≤ expectedFieldCount b := by
  cases a <;> cases b <;> simp [AvaxFork.ord, expectedFieldCount] at h ⊢

end Evm.Avalanche.Header
