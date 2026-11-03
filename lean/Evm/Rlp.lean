/-
  Evm.Rlp — Recursive Length Prefix encoding.

  EELS reference: ethereum/rlp.py. Follows the Yellow Paper Appendix B.

  We model RLP as an inductive type and provide an encoder over `ByteArray`.
  A complete decoder is TODO; the current `decode` handles only the short
  (single-byte length prefix) forms.
-/

import Evm.BaseTypes

namespace Evm.Rlp

/-- Minimal big-endian byte encoding of a non-negative integer, as
    required by RLP for unsigned ints. `0` encodes to the empty byte
    string. -/
def natToBytes (n : Nat) : Bytes := Id.run do
  if n = 0 then return Bytes.empty
  let mut out : List UInt8 := []
  let mut x := n
  while x > 0 do
    out := UInt8.ofNat (x % 256) :: out
    x := x / 256
  pure (ByteArray.mk out.toArray)

/-- RLP-encodable term: either a flat byte string or a list of subterms. -/
inductive Item where
  | bytes (b : Bytes)
  | list  (xs : List Item)
  deriving Inhabited

/-- Encode an unsigned big-endian length prefix using the given offset
    (0x80 for strings, 0xc0 for lists). -/
private def encodeLength (len : Nat) (offset : UInt8) : Bytes := Id.run do
  if len < 56 then
    pure (ByteArray.mk #[offset + UInt8.ofNat len])
  else
    let mut payload : ByteArray := ByteArray.empty
    let mut n := len
    while n > 0 do
      payload := ByteArray.mk #[UInt8.ofNat (n % 256)] ++ payload
      n := n / 256
    pure (ByteArray.mk #[offset + 55 + UInt8.ofNat payload.size] ++ payload)

/-- Encode an `Item` to its RLP byte string. -/
partial def encode : Item → Bytes
  | .bytes b =>
      if b.size = 1 ∧ b.get! 0 < 0x80 then
        b
      else
        encodeLength b.size 0x80 ++ b
  | .list xs =>
      let payload := xs.foldl (fun acc x => acc ++ encode x) ByteArray.empty
      encodeLength payload.size 0xc0 ++ payload

/-- Decode the RLP item starting at `b[start]`. Returns the item and the
    number of bytes consumed. Long-form (length-of-length) headers are not
    yet handled. -/
partial def decodeAt (b : Bytes) (start : Nat) : Option (Item × Nat) :=
  if start ≥ b.size then none
  else
    let prefixByte := (b.get! start).toNat
    if prefixByte < 0x80 then
      some (.bytes (ByteArray.mk #[b.get! start]), 1)
    else if prefixByte < 0xb8 then
      let len := prefixByte - 0x80
      if start + 1 + len > b.size then none
      else some (.bytes (b.extract (start + 1) (start + 1 + len)), 1 + len)
    else if prefixByte < 0xc0 then
      none  -- TODO: long-form bytes
    else if prefixByte < 0xf8 then
      let len := prefixByte - 0xc0
      decodeListPayload b (start + 1) len
    else
      none  -- TODO: long-form list
where
  decodeListPayload (b : Bytes) (off len : Nat) : Option (Item × Nat) := Id.run do
    if off + len > b.size then return none
    let mut items : List Item := []
    let mut cur := off
    let stop := off + len
    while cur < stop do
      match decodeAt b cur with
      | none => return none
      | some (it, n) =>
        items := items ++ [it]
        cur := cur + n
    return some (.list items, 1 + len)

/-- Convenience: decode starting at offset 0. -/
def decode (b : Bytes) : Option Item :=
  (decodeAt b 0).map Prod.fst

end Evm.Rlp
