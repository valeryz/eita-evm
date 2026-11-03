/-
  Evm.Crypto.Bn254 — EIP-196 / EIP-197 alt_bn128 (BN254) precompiles
  via FFI to libmcl.

  EELS reference:
    `ethereum/crypto/alt_bn128.py` (and the corresponding precompile
    handlers under `forks/byzantium/vm/precompiled_contracts/`).

  The three operations EVM precompiles use:

    bn254Add input64       — G1 point addition
    bn254Mul input96       — G1 scalar multiplication
    bn254Pairing input192k — multi-pairing check (returns 0x...01 if
                              ∏ e(G1_i, G2_i) == 1 in GT, else 0x...00)

  All inputs are zero-padded on the right if shorter than the expected
  length. All outputs are fixed-size big-endian.

  Bound via Lean's `@[extern]` FFI to `c/bn254.cpp`, which links
  against libmcl (Homebrew: `brew install mcl`).
-/

import Evm.BaseTypes

namespace Evm.Crypto

/-- 0x06 alt_bn128 ADD: input 128 bytes (G1 || G1), output 64 bytes (G1).
    Returns all-zero on invalid input (EELS raises OOG; our caller in
    Byzantium's PrecompiledContracts.Bn256 should treat all-zero
    output from invalid input as failure). -/
@[extern "lean_bn254_add"]
opaque bn254Add (input : @& ByteArray) : ByteArray

/-- 0x07 alt_bn128 MUL: input 96 bytes (G1 || scalar), output 64 bytes (G1). -/
@[extern "lean_bn254_mul"]
opaque bn254Mul (input : @& ByteArray) : ByteArray

/-- 0x08 alt_bn128 PAIRING_CHECK: input 192k bytes (k tuples of
    (G1, G2)), output 32 bytes (0x...01 = identity pairing, else 0x...00).
    Empty input (k=0) returns true. -/
@[extern "lean_bn254_pairing"]
opaque bn254Pairing (input : @& ByteArray) : ByteArray

end Evm.Crypto
