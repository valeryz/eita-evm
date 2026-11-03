/-
  Evm.BaseTypes — fixed-width numeric and byte-sequence types.

  Mirrors ethereum/execution-specs/src/ethereum/base_types.py. We use Lean's
  built-in `BitVec n` so that arithmetic wraps modulo 2^n by construction.

  Conventions: all multi-byte encodings are big-endian, matching EVM.
-/

namespace Evm

/-- Unsigned 8-bit integer. -/
abbrev U8   : Type := BitVec 8

/-- Unsigned 64-bit integer (used for gas, block number, nonce, ...). -/
abbrev U64  : Type := BitVec 64

/-- Unsigned 256-bit integer (the native EVM word). -/
abbrev U256 : Type := BitVec 256

/-- Ethereum account address (20 bytes, big-endian). -/
abbrev Address : Type := BitVec 160

/-- 32-byte hash (Keccak-256, block hashes, storage keys, ...). -/
abbrev Hash32 : Type := BitVec 256

/-- Arbitrary byte string. We use `ByteArray` for efficient in-place
    construction; treat it as immutable at the spec level. -/
abbrev Bytes : Type := ByteArray

instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray<size={b.size}>"

namespace Bytes

/-- Empty byte string. -/
def empty : Bytes := ByteArray.empty

/-- Concatenation. -/
def append (a b : Bytes) : Bytes := a ++ b

/-- Length. -/
def length (b : Bytes) : Nat := b.size

private def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n (0 : UInt8))

/-- Left-pad with zero bytes to reach `n` bytes. If `b` is already at least
    `n` bytes, return it unchanged. -/
def padLeft (b : Bytes) (n : Nat) : Bytes :=
  if b.size ≥ n then b else zeros (n - b.size) ++ b

/-- Right-pad with zero bytes to reach `n` bytes. -/
def padRight (b : Bytes) (n : Nat) : Bytes :=
  if b.size ≥ n then b else b ++ zeros (n - b.size)

/-- Take a slice `[start, start+len)`. If the source is shorter, the result
    is zero-padded on the right (EVM-style memory / calldata read). -/
def sliceZeroPad (b : Bytes) (start len : Nat) : Bytes := Id.run do
  let mut out : ByteArray := ByteArray.empty
  for i in [0:len] do
    let idx := start + i
    out := out.push (if idx < b.size then b.get! idx else 0)
  pure out

end Bytes

namespace U256

/-- Build a `U256` from a `Nat` (mod 2^256). -/
def ofNat (n : Nat) : U256 := BitVec.ofNat 256 n

/-- Extract the underlying `Nat` representative in `[0, 2^256)`. -/
def toNat (x : U256) : Nat := BitVec.toNat x

/-- Decode a big-endian byte sequence as `U256`. Bytes longer than 32 are
    truncated to the low-order 32 bytes (matches the wrap semantics). -/
def ofBytesBE (b : Bytes) : U256 := Id.run do
  let mut acc : Nat := 0
  for i in [0:b.size] do
    acc := acc * 256 + (b.get! i).toNat
  pure (BitVec.ofNat 256 acc)

/-- Encode as 32 big-endian bytes. -/
def toBytesBE (x : U256) : Bytes := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let n := BitVec.toNat x
  for i in [0:32] do
    let shift := (31 - i) * 8
    out := out.push (UInt8.ofNat ((n >>> shift) &&& 0xff))
  pure out

end U256

namespace Address

/-- Build an address from a `Nat`. -/
def ofNat (n : Nat) : Address := BitVec.ofNat 160 n

/-- Decode a 20-byte big-endian sequence as an `Address`. Input length is
    not checked here; callers should validate. -/
def ofBytesBE (b : Bytes) : Address := Id.run do
  let mut acc : Nat := 0
  for i in [0:b.size] do
    acc := acc * 256 + (b.get! i).toNat
  pure (BitVec.ofNat 160 acc)

/-- Encode as 20 big-endian bytes. -/
def toBytesBE (a : Address) : Bytes := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let n := BitVec.toNat a
  for i in [0:20] do
    let shift := (19 - i) * 8
    out := out.push (UInt8.ofNat ((n >>> shift) &&& 0xff))
  pure out

end Address

end Evm
