/-
  Evm.Berlin.Spec.TypedTx — EIP-2718 typed-transaction envelope.

  EELS reference: `forks/berlin/transactions.py` (the `decode_transaction`
  helper) and `forks/berlin/fork.py` (`process_transaction`'s entry
  point dispatches on the type byte).

  EIP-2718 generalizes the transaction encoding from "bare RLP" to a
  *tagged union*: the canonical encoding of a transaction is either

    * a legacy RLP-encoded transaction (the byte sequence begins with
      an RLP list-prefix byte, 0xc0..0xff), OR
    * `type_byte || payload`, where `type_byte ∈ {0x01, 0x02, 0x03, …}`
      is a single byte tag and `payload` is a fork-specific encoding
      of the typed body.

  At Berlin only one new type exists:

    * `0x01` — `AccessListTransaction` (EIP-2930): legacy fields plus
      `chain_id` and `access_list : [(Address, [U256])]`. The
      `access_list` pre-warms the listed addresses + storage keys at
      tx start (the EIP-2929 warm-set seed).

  Later forks add:

    * `0x02` — `FeeMarketTransaction` (London / EIP-1559): adds
      `max_fee_per_gas`, `max_priority_fee_per_gas`, drops the
      monolithic `gas_price`.
    * `0x03` — `BlobTransaction` (Cancun / EIP-4844): adds blob
      fields.
    * `0x04` — `SetCodeTransaction` (Prague / EIP-7702).

  ## Scope of this file

  Just the *envelope* relation: `IsTypedTxEnvelope bytes type body`
  asserts that a tx-encoded byte sequence is either legacy (no type
  byte) or splits into `(type_byte, payload)` with `type_byte` in
  {0x01}. The decoding of `payload` into a concrete typed-tx
  structure is the job of `Berlin/Transactions.lean` once that
  module materializes; we don't model the payload here.

  ## What's encoded vs glossed

  * Encoded: the 0x01 / "legacy" disjunction, with the legacy
    fall-through gate (`bytes[0] ≥ 0xc0`, the RLP list-prefix
    range).
  * Encoded: the type-byte cutoff `bytes[0] < 0x80` for typed-tx
    envelopes (the EIP-2718 reserved range). At Berlin specifically,
    only 0x01 is admitted; we expose `BerlinAdmittedTypes = {0x01}`
    as the predicate's parameter.
  * Glossed: the payload structure (delegated to the
    fork-transactions module). The relation is "the byte stream
    parses; what it parses to is a separate predicate".
  * Glossed: the EIP-2930 access-list seeding effect on
    `accessedAddresses` / `accessedStorageKeys`. That belongs to
    Berlin's `processTransaction`, not the envelope predicate.
-/

import Evm.BaseTypes

namespace Evm.Berlin.Spec

/-- The set of transaction-type bytes admitted at Berlin. EIP-2930
    introduces `0x01` (AccessListTransaction). Later forks extend
    this set without removing entries (the type-byte tag space is
    monotonic across forks). -/
def BerlinAdmittedTypes : List UInt8 := [0x01]

/-- Decision predicate: does `b` look like an RLP list-prefix? RLP
    encodes a list whose total payload size is < 56 bytes as a
    single prefix byte in `[0xc0, 0xf7]`; larger lists use
    `[0xf8, 0xff]`. Either way the first byte is ≥ 0xc0. EIP-2718
    relies on this disjointness with the typed-tx reserved type-byte
    range `[0x00, 0x7f]` to keep legacy decoding unambiguous. -/
def isLegacyTxFirstByte (b : UInt8) : Prop := b.toNat ≥ 0xc0

/-- Decision predicate: is `b` a reserved typed-tx type byte? EIP-2718
    reserves the entire `[0x00, 0x7f]` half-byte range for type bytes;
    `[0x80, 0xbf]` are RLP single-byte literals and `[0xc0, 0xff]`
    are RLP list prefixes (so neither can collide with a type byte). -/
def isTypedTxFirstByte (b : UInt8) : Prop := b.toNat < 0x80

/-! ## Envelope relation -/

/-- `IsLegacyTxEnvelope bytes` — the byte stream is a legacy RLP-
    encoded transaction. The legacy decoder consumes the entire
    stream. -/
def IsLegacyTxEnvelope (bytes : Evm.Bytes) : Prop :=
  ∃ b₀, bytes.size ≥ 1 ∧ bytes.get! 0 = b₀ ∧ isLegacyTxFirstByte b₀

/-- `IsTypedTxEnvelope bytes typeByte payload` — the byte stream
    decomposes as `typeByte :: payload` with `typeByte` in the
    admitted set for Berlin (just `[0x01]`). The payload is
    everything after the type byte. -/
def IsTypedTxEnvelope (bytes : Evm.Bytes) (typeByte : UInt8)
                      (payload : Evm.Bytes) : Prop :=
  bytes.size ≥ 1 ∧
  bytes.get! 0 = typeByte ∧
  isTypedTxFirstByte typeByte ∧
  typeByte ∈ BerlinAdmittedTypes ∧
  -- `payload` is the tail of `bytes` after the first byte; equality
  -- of byte-sliced sequences. The slice formula is `start = 1,
  -- length = bytes.size - 1`.
  payload = Evm.Bytes.sliceZeroPad bytes 1 (bytes.size - 1)

/-- The full Berlin transaction-encoding spec: a byte stream is a
    valid tx encoding iff it is either a legacy envelope OR a typed
    envelope. EELS `decode_transaction` raises on anything else. -/
def IsBerlinTxEncoding (bytes : Evm.Bytes) : Prop :=
  IsLegacyTxEnvelope bytes ∨
  ∃ tyB payload, IsTypedTxEnvelope bytes tyB payload

/-! ## Properties

    The legacy / typed disjunction is *exclusive* (RLP list prefixes
    and typed-tx type bytes occupy disjoint byte ranges), so a
    well-formed byte stream matches at most one of the two arms. -/

theorem legacy_typed_disjoint
    (bytes : Evm.Bytes) (tyB : UInt8) (payload : Evm.Bytes)
    (hL : IsLegacyTxEnvelope bytes)
    (hT : IsTypedTxEnvelope bytes tyB payload) :
    False := by
  obtain ⟨b₀, _, hEqL, hLeg⟩ := hL
  obtain ⟨_, hEqT, hTyped, _, _⟩ := hT
  -- `b₀ = bytes.get! 0 = tyB`; `b₀.toNat ≥ 0xc0` and
  -- `tyB.toNat < 0x80` together yield 0xc0 ≤ tyB.toNat < 0x80,
  -- contradiction.
  have hb : b₀ = tyB := hEqL.symm.trans hEqT
  rw [hb] at hLeg
  -- isLegacyTxFirstByte tyB ↔ tyB.toNat ≥ 0xc0
  -- isTypedTxFirstByte  tyB ↔ tyB.toNat < 0x80
  -- 0xc0 = 192, 0x80 = 128, so 192 ≤ tyB.toNat < 128 is impossible.
  unfold isLegacyTxFirstByte at hLeg
  unfold isTypedTxFirstByte at hTyped
  omega

end Evm.Berlin.Spec
