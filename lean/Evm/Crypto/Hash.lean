/-
  Evm.Crypto.Hash — Keccak-256.

  EELS reference: ethereum/crypto/hash.py.

  Bound via Lean's `@[extern]` FFI to a small C implementation in
  `c/keccak.c`. Ethereum's Keccak-256 uses the pre-FIPS-202 padding byte
  `0x01` (not `0x06` as in SHA3-256). The hash output is interpreted as a
  big-endian 256-bit integer when pushed onto the EVM stack.
-/

import Evm.BaseTypes

namespace Evm.Crypto

/-- Raw FFI entry: 32-byte Keccak-256 of `input` as a `ByteArray`. -/
@[extern "lean_keccak256"]
opaque keccak256Bytes (input : @& ByteArray) : ByteArray

/-- Keccak-256 of `input`, returned as a 256-bit big-endian word. -/
def keccak256 (input : Bytes) : Hash32 :=
  Evm.U256.ofBytesBE (keccak256Bytes input)

/-- The hash of the empty string. Useful as a sanity check on the FFI
    plumbing: must equal
    `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`. -/
def emptyKeccak : Hash32 := keccak256 Bytes.empty

end Evm.Crypto
