/-
  Evm.Prague.Spec.Bls12381Step — EIP-2537 BLS12-381 precompiles.

  EELS reference: `forks/prague/vm/precompiled_contracts/bls12_381/`
  (`bls12_381_g1.py`, `bls12_381_g2.py`, `bls12_381_pairing.py`, and the decoders in
  `__init__.py`), gas constants in `forks/prague/vm/gas.py` (`GAS_BLS_*`).

      0x0b  G1_ADD           — 2·G1 → G1                   (375 gas)
      0x0c  G1_MSM           — k·(G1,scalar) → G1          (discounted, see below)
      0x0d  G2_ADD           — 2·G2 → G2                   (600 gas)
      0x0e  G2_MSM           — k·(G2,scalar) → G2          (discounted)
      0x0f  PAIRING_CHECK    — k·(G1,G2) → {0,1}           (32600·k + 37700)
      0x10  MAP_FP_TO_G1     — Fp → G1                     (5500 gas)
      0x11  MAP_FP2_TO_G2    — Fp² → G2                    (23800 gas)

  Each relation is parametric in the crypto oracle `o : Evm.Crypto.Bls12381.Oracle` (group
  law, scalar multiplication, subgroup test, map-to-curve, pairing check — what EELS takes
  from py_ecc). Lengths, field-element ranges, infinity, the curve equation, where the
  subgroup test applies, gas and the output encoding are stated here, via the EELS
  decoders transcribed in `Evm.Crypto.Bls12381`. Every failure (`InvalidParameter`,
  `OutOfGasError`) is an exceptional halt, which consumes the frame's gas; the
  `Is*Failure` relations list them. No axioms: what the oracle computes is a documented
  assumption, `Evm.Crypto.Contracts`.
-/

import Evm.BaseTypes
import Evm.CL.GasEmit
import Evm.Crypto.Bls12381

namespace Evm.Prague.Spec

open Evm.Crypto.Bls12381

/-! ## Gas constants. EELS: `forks/prague/vm/gas.py`. -/

def gasG1Add        : Nat := 375
def gasG1Mul        : Nat := 12000
def gasG2Add        : Nat := 600
def gasG2Mul        : Nat := 22500
def gasPairingBase  : Nat := 37700
def gasPairingPair  : Nat := 32600
def gasMapFpToG1    : Nat := 5500
def gasMapFp2ToG2   : Nat := 23800

/-! ## I/O sizes (bytes) -/

/-- An Fp element: 64 bytes (48-byte big-endian, zero-padded left). -/
def fpSize          : Nat := 64
/-- An Fp² element: 2 · Fp = 128 bytes. -/
def fp2Size         : Nat := 2 * fpSize
/-- A serialised G1 point: 2 · Fp = 128 bytes. -/
def g1PointSize     : Nat := 2 * fpSize
/-- A serialised G2 point: 2 · Fp² = 256 bytes. -/
def g2PointSize     : Nat := 2 * fp2Size
/-- An MSM (point, scalar) pair: G1 + 32 = 160 / G2 + 32 = 288. -/
def g1MsmPairSize   : Nat := g1PointSize + 32
def g2MsmPairSize   : Nat := g2PointSize + 32
/-- A pairing pair (G1 || G2) = 384 bytes. -/
def pairingPairSize : Nat := g1PointSize + g2PointSize

/-! ## Gas formulas -/

/-- G1_MSM gas: `k · GAS_BLS_G1_MUL · discount(k) / 1000` (floor), EELS
    `bls12_381_g1.py::bls12_g1_msm` 93-100 with `G1_K_DISCOUNT` (k = 1..128, then
    `G1_MAX_DISCOUNT`). The table and the formula are the emitted ones
    (`Evm.CL.GasEmit.msmGas`, `blsG1MsmDiscounts`) — one owner. -/
def g1MsmGas (k : Nat) : Nat :=
  Evm.CL.GasEmit.msmGas gasG1Mul Evm.CL.GasEmit.blsG1MsmDiscounts
    Evm.CL.GasEmit.blsG1MsmMaxDiscount k

/-- G2_MSM gas: the same with `GAS_BLS_G2_MUL` and `G2_K_DISCOUNT`
    (`bls12_381_g2.py::bls12_g2_msm` 94-101). -/
def g2MsmGas (k : Nat) : Nat :=
  Evm.CL.GasEmit.msmGas gasG2Mul Evm.CL.GasEmit.blsG2MsmDiscounts
    Evm.CL.GasEmit.blsG2MsmMaxDiscount k

/-- PAIRING_CHECK gas: `32600 · k + 37700` (EELS `bls12_pairing` 44-46). -/
def pairingGas (k : Nat) : Nat := gasPairingBase + k * gasPairingPair

/-! ## The relations -/

/-- G1_ADD success (EELS `bls12_g1_add` 53-66): 256 bytes (54-55), the gas (58), two G1
    points decoded without the subgroup check (61-62), output their sum (64-66). -/
def IsG1AddSuccess (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  input.size = 2 * g1PointSize ∧ gas ≥ gasG1Add ∧
  ∃ a b, g1Decode input 0 = some a ∧ g1Decode input g1PointSize = some b ∧
    output = g1Encode (o.g1Add a b) ∧ gas' = gas - gasG1Add

def IsG1AddFailure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ 2 * g1PointSize ∨ gas < gasG1Add ∨
  g1Decode input 0 = none ∨ g1Decode input g1PointSize = none

/-- G2_ADD success (EELS `bls12_381_g2.py::bls12_g2_add` 54-67). -/
def IsG2AddSuccess (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  input.size = 2 * g2PointSize ∧ gas ≥ gasG2Add ∧
  ∃ a b, g2Decode input 0 = some a ∧ g2Decode input g2PointSize = some b ∧
    output = g2Encode (o.g2Add a b) ∧ gas' = gas - gasG2Add

def IsG2AddFailure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ 2 * g2PointSize ∨ gas < gasG2Add ∨
  g2Decode input 0 = none ∨ g2Decode input g2PointSize = none

/-- G1_MSM success (EELS `bls12_g1_msm` 88-115): k ≥ 1 whole pairs (89-90), the
    discounted gas (93-100), every pair a subgroup point and a scalar (103-107,
    `decode_g1_scalar_pair`), output `Σ mᵢ·Pᵢ` folded as EELS does (108-115). -/
def IsG1MsmSuccess (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  let k := input.size / g1MsmPairSize
  input.size ≠ 0 ∧ input.size % g1MsmPairSize = 0 ∧ gas ≥ g1MsmGas k ∧
  ∃ ps, g1MsmPairs o input k = some ps ∧
    output = g1Encode (g1MsmSum o ps) ∧ gas' = gas - g1MsmGas k

def IsG1MsmFailure (o : Oracle) (input : Evm.Bytes) (gas : Nat) : Prop :=
  let k := input.size / g1MsmPairSize
  input.size = 0 ∨ input.size % g1MsmPairSize ≠ 0 ∨ gas < g1MsmGas k ∨
  g1MsmPairs o input k = none

/-- G2_MSM success (EELS `bls12_381_g2.py::bls12_g2_msm` 89-116). -/
def IsG2MsmSuccess (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  let k := input.size / g2MsmPairSize
  input.size ≠ 0 ∧ input.size % g2MsmPairSize = 0 ∧ gas ≥ g2MsmGas k ∧
  ∃ ps, g2MsmPairs o input k = some ps ∧
    output = g2Encode (g2MsmSum o ps) ∧ gas' = gas - g2MsmGas k

def IsG2MsmFailure (o : Oracle) (input : Evm.Bytes) (gas : Nat) : Prop :=
  let k := input.size / g2MsmPairSize
  input.size = 0 ∨ input.size % g2MsmPairSize ≠ 0 ∨ gas < g2MsmGas k ∨
  g2MsmPairs o input k = none

/-- PAIRING_CHECK success (EELS `bls12_pairing` 39-69): k ≥ 1 whole pairs (40-41), the gas
    (44-46), every pair a G1 and a G2 point each subgroup-checked (50-62), output the
    32-byte 1 iff the pairing product is one (64-69). -/
def IsPairingCheckSuccess (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  let k := input.size / pairingPairSize
  input.size ≠ 0 ∧ input.size % pairingPairSize = 0 ∧ gas ≥ pairingGas k ∧
  ∃ ps, pairingPairs o input k = some ps ∧
    output = pairingOutput (o.pairingCheck ps) ∧ gas' = gas - pairingGas k

def IsPairingCheckFailure (o : Oracle) (input : Evm.Bytes) (gas : Nat) : Prop :=
  let k := input.size / pairingPairSize
  input.size = 0 ∨ input.size % pairingPairSize ≠ 0 ∨ gas < pairingGas k ∨
  pairingPairs o input k = none

/-- MAP_FP_TO_G1 success (EELS `bls12_map_fp_to_g1` 133-146): 64 bytes, the gas, a field
    element < p (141-143), output `clear_cofactor(map_to_curve(u))`. -/
def IsMapFpToG1Success (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  input.size = fpSize ∧ gas ≥ gasMapFpToG1 ∧
  ∃ u, fpDecode input 0 = some u ∧ output = g1Encode (o.mapFpToG1 u) ∧
    gas' = gas - gasMapFpToG1

def IsMapFpToG1Failure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ fpSize ∨ gas < gasMapFpToG1 ∨ fpDecode input 0 = none

/-- MAP_FP2_TO_G2 success (EELS `bls12_381_g2.py::bls12_map_fp2_to_g2` 134-147). -/
def IsMapFp2ToG2Success (o : Oracle) (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  input.size = fp2Size ∧ gas ≥ gasMapFp2ToG2 ∧
  ∃ u, fp2Decode input 0 = some u ∧ output = g2Encode (o.mapFp2ToG2 u) ∧
    gas' = gas - gasMapFp2ToG2

def IsMapFp2ToG2Failure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ fp2Size ∨ gas < gasMapFp2ToG2 ∨ fp2Decode input 0 = none

end Evm.Prague.Spec
