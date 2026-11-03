/-
  Evm.Istanbul.Vm.PrecompiledContracts.Bn256 — EIP-1108 alt_bn128
  re-pricing at Istanbul.

  EELS reference:
  `forks/istanbul/vm/precompiled_contracts/{alt_bn128_add,
   alt_bn128_mul, alt_bn128_pairing_check}.py`.

  Gas constants vs Byzantium:
    ECADD       500   →   150
    ECMUL       40_000 →   6_000
    ECPAIRING   100_000 + 80_000·k → 45_000 + 34_000·k

  The actual curve math is identical to Byzantium's — we reuse the
  `Evm.Crypto.Bn254` FFI bindings, which return zero-bytes when
  `mclBn_init` reports a failure (see `c/bn254.cpp`). At that point
  the precompile's only effect is the gas charge, which we make sure
  matches EELS even when the math is stubbed.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Crypto.Bn254

namespace Evm.Istanbul.Vm.PrecompiledContracts

open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-- 0x06 alt_bn128_add — EIP-1108: 150 gas (was 500). -/
def bn256Add : Precompile := fun input gasLeft => do
  let cost : Nat := 150
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Add input
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

/-- 0x07 alt_bn128_mul — EIP-1108: 6000 gas (was 40000). -/
def bn256Mul : Precompile := fun input gasLeft => do
  let cost : Nat := 6000
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Mul input
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

/-- 0x08 alt_bn128_pairing_check — EIP-1108: 45000 + 34000·k
    (was 100000 + 80000·k). -/
def bn256Pairing : Precompile := fun input gasLeft => do
  if input.size % 192 ≠ 0 then .error .outOfGas
  let k := input.size / 192
  let cost := 45000 + 34000 * k
  if gasLeft < cost then .error .outOfGas
  let out := Evm.Crypto.bn254Pairing input
  if out.size = 0 then .error .outOfGas
  return (out, gasLeft - cost)

end Evm.Istanbul.Vm.PrecompiledContracts
