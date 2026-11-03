/-
  Evm.Crypto.P256Verify — RIP-7212 secp256r1 signature verification.

  Used by OP-stack Fjord+ to implement the P256VERIFY precompile at
  0x100. Lives in `Evm/Crypto/` (not `Evm/Optimism/`) so the Cancun
  trampoline can call it without circular imports.

  Current state: `isValidP256Signature` is `opaque` with a `false`
  default body — the SAFE default (rejects all signatures rather
  than accepting some wrongly). The opaque is the named trust
  boundary; a future PR replaces the body with one of:
    (a) FFI to OpenSSL's `EC_KEY_verify` against NIST P-256;
    (b) FFI to libsecp256r1 / mbedtls;
    (c) pure-Lean P-256 verifier (slow but axiom-free).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm

namespace Evm.Crypto

/-- Raw FFI: takes the 160-byte RIP-7212 input
    (`msgHash || r || s || qx || qy`) and returns `1` (valid) or
    `0` (invalid). Bound to `c/p256verify.c`, which links against
    OpenSSL libcrypto. -/
@[extern "lean_p256_verify"]
opaque verifyRaw (input : @& ByteArray) : UInt8

/-- Convert a `U256` to its 32-byte big-endian representation. -/
private def u256ToBytesBE (x : Evm.U256) : ByteArray := Id.run do
  let n := x.toNat
  let mut buf : ByteArray := ByteArray.empty
  let mut i := 32
  while i > 0 do
    i := i - 1
    let b := (n >>> (i * 8)) &&& 0xff
    buf := buf.push (UInt8.ofNat b)
  return buf

/-- TRUST BOUNDARY: secp256r1 signature verification. Returns `true`
    iff `(r, s)` is a valid ECDSA-P256 signature on `msgHash` under
    the public key `(qx, qy)`.

    Implemented via FFI to OpenSSL's `ECDSA_do_verify`. The trust
    boundary is now narrow: it sits at the FFI / OpenSSL boundary
    rather than inside Lean. (Replacing OpenSSL with a pure-Lean
    P-256 verifier would make the chain axiom-free.) -/
def isValidP256Signature
    (msgHash r s qx qy : Evm.U256) : Bool :=
  let buf :=
    u256ToBytesBE msgHash ++ u256ToBytesBE r ++ u256ToBytesBE s
                ++ u256ToBytesBE qx ++ u256ToBytesBE qy
  verifyRaw buf = 1

/-- Read 32 big-endian bytes from `input` starting at offset `off`.
    Bytes past the end of input are treated as zero. -/
private def readU256BE (input : Evm.Bytes) (off : Nat) : Evm.U256 :=
  let acc : Nat := Id.run do
    let mut a : Nat := 0
    for k in [0:32] do
      let b := if off + k < input.size then input.get! (off + k) else (0 : UInt8)
      a := a * 256 + b.toNat
    return a
  Evm.U256.ofNat acc

/-- The canonical 32-byte big-endian `1` returned on successful verify. -/
private def trueReturn : Evm.Bytes := Id.run do
  let mut buf : ByteArray := ByteArray.empty
  for _ in [0:31] do
    buf := buf.push 0
  buf := buf.push 1
  return buf

/-- RIP-7212 P256VERIFY precompile. Signature follows the same shape
    as `Evm.Frontier.Vm.PrecompiledContracts.Precompile`:
        `Bytes → Nat → Except Exception (Bytes × Nat)`.

    ABI:
        input (160 bytes): msgHash || r || s || qx || qy (32 each)
        output:            32-byte 0x...01 on valid signature
                           empty on invalid input / verify-fail
        gas:               GASCOST, constant per fork — the OP fork's
                           `Evm.Optimism.Fjord.Spec.p256VerifyGas`
                           (RIP-7212 3450 until Azul, then 6900). -/
def p256VerifyWith (gasCost : Nat) : Evm.Bytes → Nat → Except Evm.Frontier.Vm.Exception (Evm.Bytes × Nat) :=
  fun input gasLeft =>
    if gasLeft < gasCost then
      .error Evm.Frontier.Vm.Exception.outOfGas
    else if input.size ≠ 160 then
      .ok (Evm.Bytes.empty, gasLeft - gasCost)
    else
      let msgHash := readU256BE input 0
      let r       := readU256BE input 32
      let s       := readU256BE input 64
      let qx      := readU256BE input 96
      let qy      := readU256BE input 128
      if isValidP256Signature msgHash r s qx qy then
        .ok (trueReturn, gasLeft - gasCost)
      else
        .ok (Evm.Bytes.empty, gasLeft - gasCost)

end Evm.Crypto
