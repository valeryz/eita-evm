/-
  Evm.Paris.Spec.BlockHeaderInvariants — EIP-3675 header invariants.

  EELS reference: `forks/paris/fork.py` `validate_header` (lines
  ~330-335 across recent EELS revisions). Post-Merge headers MUST
  satisfy:

    * `header.difficulty == 0`
      The PoW difficulty target is gone; consensus is supplied by
      the beacon chain. The execution-layer header still carries
      the field for layout compatibility but its value is fixed.
    * `header.nonce == b"\x00\x00\x00\x00\x00\x00\x00\x00"`
      An 8-byte zero. Same compatibility reason.
    * `header.ommers_hash == keccak256(rlp([]))`
      Ommers are eliminated; the field's value is fixed at the
      keccak of the empty RLP list (constant `EMPTY_OMMER_HASH`,
      value `0x1dcc4de8…d49347`).
    * `len(block.ommers) == 0`
      Block-body level invariant (not strictly a header field, but
      validated together).

  ## What's encoded vs glossed

  * Encoded: each of the four invariants as a named predicate over
    a header. We don't reach into the header structure — we accept
    abstract operands for each field, since the `Header` type lives
    in `Frontier/ForkTypes.lean` and we don't want a heavy import.
  * Encoded: the `EMPTY_OMMER_HASH` constant (the actual 32-byte
    value, copied from `Paris/Fork.lean`).
  * Glossed: the `extra_data ≤ 32 bytes` rule. That's a pre-Merge
    invariant inherited from earlier forks; not EIP-3675-specific.
  * Glossed: the parent-hash, monotone timestamp, sequential
    block number checks. Also inherited / non-Merge-distinctive.
  * Glossed: post-Merge `base_fee_per_gas` validity (that's
    London's `IsCalculatedBaseFee`, composed separately).
-/

import Evm.BaseTypes

namespace Evm.Paris.Spec

/-- `keccak256(rlp([]))` — the canonical empty-ommers hash. Value
    copied from `Paris/Fork.lean` `EMPTY_OMMER_HASH`. -/
def EMPTY_OMMER_HASH : Evm.Hash32 :=
  Evm.U256.ofNat 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

/-- EIP-3675: post-Merge header difficulty must be zero. -/
def IsParisDifficultyValid (difficulty : Nat) : Prop :=
  difficulty = 0

/-- EIP-3675: post-Merge header nonce must be eight zero bytes.
    Parametrized over a byte sequence; the caller checks the
    sequence has length 8 separately (it's a header-shape
    invariant). -/
def IsParisNonceValid (nonce : ByteArray) : Prop :=
  nonce.size = 8 ∧ ∀ i, i < 8 → nonce.get! i = (0 : UInt8)

/-- EIP-3675: post-Merge `ommersHash` must equal
    `keccak256(rlp([]))`. -/
def IsParisOmmersHashValid (ommersHash : Evm.Hash32) : Prop :=
  ommersHash = EMPTY_OMMER_HASH

/-- EIP-3675: post-Merge block body's `ommers` list must be empty. -/
def IsParisOmmersBodyValid {α : Type} (ommers : List α) : Prop :=
  ommers = []

/-! ## Combined invariant -/

/-- Conjunction of the four Paris header invariants. A header passes
    iff every component predicate holds. -/
def IsParisHeaderInvariants
    (difficulty : Nat) (nonce : ByteArray) (ommersHash : Evm.Hash32)
    {α : Type} (ommers : List α) : Prop :=
  IsParisDifficultyValid difficulty ∧
  IsParisNonceValid nonce ∧
  IsParisOmmersHashValid ommersHash ∧
  IsParisOmmersBodyValid ommers

/-! ## Properties -/

/-- Each invariant is decidable in isolation. The `IsParisNonceValid`
    one needs a finite quantifier; the rest are equational. -/
instance : Decidable (IsParisDifficultyValid d) := by
  unfold IsParisDifficultyValid; exact inferInstance

instance : Decidable (IsParisOmmersHashValid h) := by
  unfold IsParisOmmersHashValid; exact inferInstance

instance {α : Type} {ommers : List α} [DecidableEq (List α)] :
    Decidable (IsParisOmmersBodyValid ommers) := by
  unfold IsParisOmmersBodyValid; exact inferInstance

end Evm.Paris.Spec
