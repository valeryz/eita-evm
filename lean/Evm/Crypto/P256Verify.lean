/-
  Evm.Crypto.P256Verify — the secp256r1 (NIST P-256) signature-verification precompile
  at 0x100: EIP-7951 (Osaka, 6900 gas) and RIP-7212 (OP Fjord..Isthmus, 3450 gas), one
  wrapper with the gas a parameter.

  EELS reference: `forks/osaka/vm/precompiled_contracts/p256verify.py::p256verify` 31-90,
  with the curve constants and `is_on_curve_secp256r1` from
  `ethereum/crypto/elliptic_curve.py` 79-90 and 134-169.

  `p256VerifyWithOracle verify` is EELS's wrapper (gas, the 160-byte length, the bounds on
  r, s, qx, qy, the infinity and curve-equation checks, the 32-byte output) over an oracle
  `verify` — EELS's own black box `secp256r1_verify(r, s, x, y, msg_hash)` (93-131, which
  calls the `cryptography` package). The replay instantiates it with `isValidP256Signature`,
  OpenSSL libcrypto's `ECDSA_do_verify` via `lean/c/p256verify.c` — the same function the
  production precompile calls. What `verify` is assumed to compute (ECDSA verification over
  Mathlib's Weierstrass curve) is `Evm.Crypto.Contracts.P256VerifyContract`.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm

namespace Evm.Crypto

/-! ## Curve constants (EELS `elliptic_curve.py` 79-90) -/

/-- `SECP256R1N`, the group order. -/
def p256N : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
/-- `SECP256R1P`, the field modulus. -/
def p256P : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
/-- `SECP256R1A` (= p − 3). -/
def p256A : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC
/-- `SECP256R1B`. -/
def p256B : Nat := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B

/-- The base point G (SEC 2 §2.4.2; not in EELS, which delegates to `cryptography`). -/
def p256Gx : Nat := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
def p256Gy : Nat := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

/-- `is_on_curve_secp256r1` (134-169): y² ≡ x³ + a·x + b (mod p). -/
def p256OnCurve (x y : Nat) : Bool :=
  y * y % p256P == (x * x * x % p256P + p256A * x % p256P + p256B) % p256P

/-! ## The oracle -/

/-- `secp256r1_verify(r, s, x, y, msg_hash)` as a predicate (EELS raises
    `InvalidSignatureError` where this is `false`): arguments `msgHash r s qx qy`. -/
abbrev P256Verifier := Nat → Nat → Nat → Nat → Nat → Bool

/-- Raw FFI: the 160-byte input `msgHash ‖ r ‖ s ‖ qx ‖ qy` → `1` (valid) / `0`. Bound to
    `lean/c/p256verify.c`'s `lean_p256_verify` (OpenSSL libcrypto `ECDSA_do_verify`). -/
@[extern "lean_p256_verify"]
opaque verifyRaw (input : @& ByteArray) : UInt8

/-- TRUST BOUNDARY: secp256r1 ECDSA verification as computed by OpenSSL libcrypto. -/
def isValidP256Signature : P256Verifier := fun msgHash r s qx qy =>
  let be (n : Nat) := Evm.U256.toBytesBE (Evm.U256.ofNat n)
  verifyRaw (be msgHash ++ be r ++ be s ++ be qx ++ be qy) = 1

/-! ## The wrapper -/

/-- The 32 big-endian bytes at `off` (`U256.from_be_bytes(buffer_read(data, off, 32))`). -/
def p256Word (input : Evm.Bytes) (off : Nat) : Nat :=
  (Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad input off 32)).toNat

/-- EELS 46-88: the input passes every check and `verify` accepts. -/
def p256Accepts (verify : P256Verifier) (input : Evm.Bytes) : Bool :=
  let z := p256Word input 0
  let r := p256Word input 32
  let s := p256Word input 64
  let qx := p256Word input 96
  let qy := p256Word input 128
  input.size == 160 &&
  -- 63-66: 0 < r < n and 0 < s < n
  decide (0 < r ∧ r < p256N ∧ 0 < s ∧ s < p256N) &&
  -- 71-74: qx < p and qy < p
  decide (qx < p256P ∧ qy < p256P) &&
  -- 77-78: not the point at infinity (0, 0)
  !(qx == 0 && qy == 0) &&
  -- 82-83: on the curve
  p256OnCurve qx qy &&
  -- 85-88
  verify z r s qx qy

/-- The 32-byte success output `left_pad_zero_bytes(b"\x01", 32)` (EELS 90). -/
def p256SuccessOutput : Evm.Bytes := Evm.U256.toBytesBE (Evm.U256.ofNat 1)

/-- EELS `p256verify` 41-90 over the oracle `verify`, with the gas `gasCost` (EIP-7951
    6900; RIP-7212 3450): charge (44, an out-of-gas exceptional halt), then the 32-byte one
    when every check passes, else empty output. -/
def p256VerifyWithOracle (verify : P256Verifier) (gasCost : Nat) (input : Evm.Bytes)
    (gasLeft : Nat) : Except Evm.Frontier.Vm.Exception (Evm.Bytes × Nat) :=
  if gasLeft < gasCost then .error Evm.Frontier.Vm.Exception.outOfGas
  else if p256Accepts verify input then .ok (p256SuccessOutput, gasLeft - gasCost)
  else .ok (Evm.Bytes.empty, gasLeft - gasCost)

/-- The precompile the replay runs: over OpenSSL. -/
def p256VerifyWith (gasCost : Nat) :
    Evm.Bytes → Nat → Except Evm.Frontier.Vm.Exception (Evm.Bytes × Nat) :=
  p256VerifyWithOracle isValidP256Signature gasCost

end Evm.Crypto
