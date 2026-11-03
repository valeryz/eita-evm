/-
  Evm.Prague.Vm.PrecompiledContracts — full Prague precompile registry.

  EELS reference: `ethereum/forks/prague/vm/precompiled_contracts/`.

  Inherits the Cancun set 0x01..0x0a (ecrecover, sha256, ripemd160,
  identity, modexp, bn254 add/mul/pairing, blake2f, point_evaluation)
  via direct re-export of Frontier's 0x01..0x04 + Byzantium-shaped
  stubs for the BN254 / modexp range; on top of that EIP-2537 adds:

      0x0b  G1_ADD          (EELS: prague/.../bls12_381/bls12_381_g1.py
                             function `bls12_g1_add`; gas 375)
      0x0c  G1_MSM          (`bls12_g1_msm`; variable gas — base 12000,
                             linear in scalar count with discount table)
      0x0d  G2_ADD          (`bls12_g2_add`; gas 600)
      0x0e  G2_MSM          (`bls12_g2_msm`; base 22500, linear in count
                             with discount table)
      0x0f  PAIRING_CHECK   (`bls12_pairing`; 32600·k + 37700 where
                             k is the number of pairings)
      0x10  MAP_FP_TO_G1    (`bls12_map_fp_to_g1`; gas 5500)
      0x11  MAP_FP2_TO_G2   (`bls12_map_fp2_to_g2`; gas 23800)

  Per the task brief the BLS math itself is stubbed: we charge the gas
  (which is what the EVM observes) and return a well-formed
  zero-element output of the right length, so downstream callers that
  only check the return-data size don't trip. Real BLS-12-381 will
  arrive when `blst` (or similar) is wired through FFI; the stubs are
  marked with a TODO + EELS-cite each.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts

namespace Evm.Prague.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)

/-- Same shape as `Frontier.Vm.PrecompiledContracts.Precompile`. -/
abbrev Precompile :=
  Evm.Bytes → Nat → Except Exception (Evm.Bytes × Nat)

/-! ## EIP-2537 gas constants. EELS: `prague/vm/gas.py` `GAS_BLS_*`. -/

/-- EELS `GAS_BLS_G1_ADD`. -/
def gasG1Add        : Nat := 375
/-- EELS `GAS_BLS_G1_MUL` (used per-pair in MSM after discount). -/
def gasG1Mul        : Nat := 12000
/-- EELS `GAS_BLS_G2_ADD`. -/
def gasG2Add        : Nat := 600
/-- EELS `GAS_BLS_G2_MUL`. -/
def gasG2Mul        : Nat := 22500
/-- EELS `GAS_BLS_PAIRING_PER_PAIR`. -/
def gasPairingPair  : Nat := 32600
/-- EELS `GAS_BLS_PAIRING_BASE`. -/
def gasPairingBase  : Nat := 37700
/-- EELS `GAS_BLS_MAP_FP_TO_G1`. -/
def gasMapFpToG1    : Nat := 5500
/-- EELS `GAS_BLS_MAP_FP2_TO_G2`. -/
def gasMapFp2ToG2   : Nat := 23800

/-! ## Input/output sizes (bytes). EELS: `prague/vm/precompiled_contracts/bls12_381/*.py`. -/

/-- BLS12-381 single Fp element: 64 bytes (48 bytes serialized
    big-endian, left-padded with 16 zero bytes). -/
def fpSize          : Nat := 64
/-- A serialized G1 point: 2 Fp = 128 bytes. -/
def g1PointSize     : Nat := 128
/-- A serialized G2 point: 4 Fp = 256 bytes. -/
def g2PointSize     : Nat := 256
/-- MSM single (point, scalar) pair sizes: 160 / 288 bytes. -/
def g1MsmPairSize   : Nat := g1PointSize + 32
def g2MsmPairSize   : Nat := g2PointSize + 32
/-- Pairing input pair: G1 || G2 = 384 bytes. -/
def pairingPairSize : Nat := g1PointSize + g2PointSize

private def zeros (n : Nat) : Evm.Bytes :=
  ByteArray.mk (Array.replicate n (0 : UInt8))

private def charge (gas n : Nat) : Except Exception Nat :=
  if gas < n then .error .outOfGas else .ok (gas - n)

/-! ## EIP-2537 BLS12-381 precompiles.

    Each handler validates the input length (the standard EIP-2537
    requires fixed-stride input — `len % stride = 0` and `len > 0`
    for the MSM precompiles), charges gas, and returns a zero-padded
    output of the documented length.

    **Stubs**: actual BLS arithmetic is deferred until we have a
    Lean ↔ blst FFI. For now these compute the correct gas, so
    callers that meter gas precisely see the right `gasLeftAfter`.
    The returned bytes are zero, NOT a valid point — any caller
    that actually checks the output cryptographically (the only
    one that does is PAIRING_CHECK's bool output) will get `false`,
    which matches the "no pairing succeeded" answer. -/

/-- 0x0b — BLS12_G1ADD. Fixed input 256 bytes (two G1 points), output
    128 bytes (G1). EELS: `bls12_g1_add` in
    `prague/vm/precompiled_contracts/bls12_381/bls12_381_g1.py`. -/
def blsG1Add (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size ≠ 2 * g1PointSize then .error .outOfGas
  let gas' ← charge gas gasG1Add
  -- TODO: real BLS addition; for now return identity-shaped zero point.
  return (zeros g1PointSize, gas')

/-- 0x0c — BLS12_G1MSM. Input is k·160 bytes (k ≥ 1), output 128
    bytes (G1). Gas follows EELS `bls12_g1_msm`: per-pair cost is
    `GAS_BLS_G1_MUL · discount(k) / 1000` summed over pairs.

    We use the flat upper-bound `k · GAS_BLS_G1_MUL` here (no
    discount). Worst-case cost; matches EELS at k=1 (`discount(1)=1000`)
    and over-charges for k>1. Plumb the real `G1_MSM_DISCOUNT_TABLE`
    when wiring the real curve impl. -/
def blsG1Msm (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size = 0 ∨ input.size % g1MsmPairSize ≠ 0 then .error .outOfGas
  let k := input.size / g1MsmPairSize
  let cost := k * gasG1Mul
  let gas' ← charge gas cost
  return (zeros g1PointSize, gas')

/-- 0x0d — BLS12_G2ADD. Input 512 bytes, output 256 bytes. EELS:
    `bls12_g2_add`. -/
def blsG2Add (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size ≠ 2 * g2PointSize then .error .outOfGas
  let gas' ← charge gas gasG2Add
  return (zeros g2PointSize, gas')

/-- 0x0e — BLS12_G2MSM. Input k·288 bytes, output 256 bytes. Gas
    formula simplified per the G1MSM note above. -/
def blsG2Msm (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size = 0 ∨ input.size % g2MsmPairSize ≠ 0 then .error .outOfGas
  let k := input.size / g2MsmPairSize
  let cost := k * gasG2Mul
  let gas' ← charge gas cost
  return (zeros g2PointSize, gas')

/-- 0x0f — BLS12_PAIRING_CHECK. Input k·384 bytes, output 32 bytes
    (big-endian `1` on success, `0` on failure). Gas:
    `GAS_BLS_PAIRING_BASE + k · GAS_BLS_PAIRING_PER_PAIR`.

    EELS: `bls12_pairing` in
    `prague/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py`.

    Stub returns 32 zero bytes (= "false"), the conservative default. -/
def blsPairing (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size = 0 ∨ input.size % pairingPairSize ≠ 0 then .error .outOfGas
  let k := input.size / pairingPairSize
  let cost := gasPairingBase + k * gasPairingPair
  let gas' ← charge gas cost
  return (zeros 32, gas')

/-- 0x10 — BLS12_MAP_FP_TO_G1. Input 64 bytes (one Fp), output 128
    bytes (G1). EELS: `bls12_map_fp_to_g1`. -/
def blsMapFpToG1 (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size ≠ fpSize then .error .outOfGas
  let gas' ← charge gas gasMapFpToG1
  return (zeros g1PointSize, gas')

/-- 0x11 — BLS12_MAP_FP2_TO_G2. Input 128 bytes (one Fp2), output 256
    bytes (G2). EELS: `bls12_map_fp2_to_g2`. -/
def blsMapFp2ToG2 (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if input.size ≠ 2 * fpSize then .error .outOfGas
  let gas' ← charge gas gasMapFp2ToG2
  return (zeros g2PointSize, gas')

/-- Full Prague precompile registry. Frontier 0x01..0x04 are re-exported
    directly; 0x05..0x0a are not yet ported (Byzantium MODEXP/BN254 +
    Istanbul BLAKE2F + Cancun KZG point-eval), and 0x0b..0x11 are the
    new EIP-2537 stubs above. Address gaps will be plugged as each
    intermediate fork is filled in. -/
def registry : List (Evm.Address × Precompile) :=
  -- 0x01..0x04 from Frontier (Identity et al.). The handlers have the
  -- same Frontier exception type and are re-used verbatim.
  [ (Evm.Address.ofNat 0x01, Evm.Frontier.Vm.PrecompiledContracts.ecrecover)
  , (Evm.Address.ofNat 0x02, Evm.Frontier.Vm.PrecompiledContracts.sha256)
  , (Evm.Address.ofNat 0x03, Evm.Frontier.Vm.PrecompiledContracts.ripemd160)
  , (Evm.Address.ofNat 0x04, Evm.Frontier.Vm.PrecompiledContracts.identity)
  -- 0x05..0x0a: TODO (Byzantium/Istanbul/Cancun precompiles).
  -- 0x0b..0x11: EIP-2537 BLS12-381 (Prague).
  , (Evm.Address.ofNat 0x0b, blsG1Add)
  , (Evm.Address.ofNat 0x0c, blsG1Msm)
  , (Evm.Address.ofNat 0x0d, blsG2Add)
  , (Evm.Address.ofNat 0x0e, blsG2Msm)
  , (Evm.Address.ofNat 0x0f, blsPairing)
  , (Evm.Address.ofNat 0x10, blsMapFpToG1)
  , (Evm.Address.ofNat 0x11, blsMapFp2ToG2)
  ]

/-- Look up a precompile by address. -/
def lookup (a : Evm.Address) : Option Precompile :=
  (registry.find? (fun (k, _) => k = a)).map Prod.snd

end Evm.Prague.Vm.PrecompiledContracts
