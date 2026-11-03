/-
  Evm.Byzantium.Vm.PrecompiledContracts.Bn256 — EIP-196/197 alt_bn128
  precompiles at addresses 0x06, 0x07, 0x08.

  EELS reference: `forks/byzantium/vm/precompiled_contracts/{
    alt_bn128_add, alt_bn128_mul, alt_bn128_pairing_check }.py`.

  Status: gas accounting + input-length checks are correct (so
  contracts get OOG'd properly when underfunded and don't silently
  succeed). The actual curve math is stubbed: ADD and MUL return
  the all-zero point (point at infinity in compressed BE form),
  PAIRING returns "valid pairing = false" (the canonical 32-byte
  zero word). Refining the stubs to real BN254 math requires FFI
  to the `c/bn254_shim.cpp` already in the repo — TODO.

  Gas constants (Byzantium / pre-Istanbul):
    BN256ADD       = 500
    BN256MUL       = 40_000
    BN256PAIRING   = 100_000 + 80_000 * #pairs    (where #pairs = input.size / 192)
  Istanbul EIP-1108 re-prices these to 150 / 6000 / 45000 + 34000·n.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Crypto.Bn254

namespace Evm.Byzantium.Vm.PrecompiledContracts

open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-- Pad `bs` on the RIGHT to length `n` with zero bytes (helper for
    fixed-size output blobs). -/
private def padRight (bs : Evm.Bytes) (n : Nat) : Evm.Bytes := Id.run do
  let mut out := bs
  while out.size < n do
    out := out.push 0
  pure out

/-- A 64-byte all-zero blob, used as the "point at infinity" output
    from ADD / MUL stubs. -/
private def zeroPoint : Evm.Bytes := padRight ByteArray.empty 64

/-- A 32-byte zero word, returned by PAIRING when verification fails
    (or in our stub case, always). -/
private def falseWord : Evm.Bytes := padRight ByteArray.empty 32

/-! ## 0x06 alt_bn128_add (EIP-196)

    Input: 128 bytes = two G1 points (x, y) each 32+32 BE; short input
    zero-padded on the right. Output: 64 bytes = (x, y) sum. -/
def bn256Add : Precompile := fun input gasLeft => do
  let cost : Nat := 500
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Add input
  -- FFI convention: zero-length output ⇒ invalid input. EELS raises
  -- OutOfGasError, consuming all forwarded gas.
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

/-! ## 0x07 alt_bn128_mul (EIP-196)

    Input: 96 bytes = G1 point (x, y, 32+32) followed by scalar
    (32 BE); short input zero-padded. Output: 64 bytes = scaled point. -/
def bn256Mul : Precompile := fun input gasLeft => do
  let cost : Nat := 40000
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Mul input
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

/-! ## 0x08 alt_bn128_pairing_check (EIP-197)

    Input: 192 * k bytes, k ≥ 0. Each 192-byte block is one (G1, G2)
    pair (G1 = 64 BE, G2 = 128 BE). Output: 32-byte word = 1 if the
    product of all pairings equals identity in Fp12, else 0.

    Gas: 100_000 + 80_000 * k (EIP-197). Berlin/EIP-1108 re-prices
    these constants; that delta lives in
    `Evm.Istanbul.Vm.PrecompiledContracts`. -/
def bn256Pairing : Precompile := fun input gasLeft => do
  if input.size % 192 ≠ 0 then .error .outOfGas
  let k := input.size / 192
  let cost := 100000 + 80000 * k
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Pairing input
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

end Evm.Byzantium.Vm.PrecompiledContracts
