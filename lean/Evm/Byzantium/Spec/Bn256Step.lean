/-
  Evm.Byzantium.Spec.Bn256Step — EIP-196 / EIP-197 alt_bn128 precompile
  invariants.

  EELS reference:
    `forks/byzantium/vm/precompiled_contracts/alt_bn128_add.py`
    `forks/byzantium/vm/precompiled_contracts/alt_bn128_mul.py`
    `forks/byzantium/vm/precompiled_contracts/alt_bn128_pairing_check.py`

  Implementation: `Evm.Byzantium.Vm.PrecompiledContracts.Bn256` ⇒ FFI
  to `lean/c/bn254.cpp` ⇒ libmcl.

  ## What this file pins down

  EVM spec lawyers tend to focus on the curve arithmetic, but the
  *failure semantics* are equally load-bearing — and were the source
  of multiple bugs found via the `stZeroKnowledge` / `stZeroKnowledge2`
  corpus during 2026-05-30:

    1. **Invalid input ⇒ OutOfGasError** (not "success with zeros").
       EELS raises `OutOfGasError` when a G1 / G2 point is off-curve
       or in the wrong subgroup. The CALL frame consumes its entire
       forwarded gas. Returning "success with zero point" silently
       admits invalid points — every contract that branches on the
       precompile's success bit reaches a divergent state.

    2. **Coordinate range check.** A 32-byte big-endian field element
       MUST satisfy `0 ≤ x < p` where
       `p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`
       (the BN254 base field modulus). EELS's `Fq.from_bytes` rejects
       `x >= p`. A naive `set_big_endian_mod` (e.g. mcl's
       `mclBnFp_setBigEndianMod`) silently reduces and accepts —
       which makes the `ecpairing_perturb_g2_by_field_modulus` tests
       see the precompile succeed where EELS rejects.

    3. **Empty pairing input ⇒ true.** Per EIP-197: with zero pairs
       the product over the empty set equals the identity in GT, so
       output is the 32-byte word `0x...01`. Not zero.

    4. **Pairing input length** MUST be a multiple of 192 (one
       `(G1, G2)` pair per block). Otherwise OOG.

  ## Gas

    bn256_add      : 500
    bn256_mul      : 40_000
    bn256_pairing  : 100_000 + 80_000 · k        (k = input.size / 192)

  Istanbul EIP-1108 re-prices these to 150 / 6000 / 45000 + 34000·k;
  that delta is in `Evm.Istanbul.Vm.PrecompiledContracts.Bn256`.

  ## Stub mode

  The implementation has a runtime fallback: if `mclBn_init` reports
  a build mismatch (rc != 0), all three precompiles return zero bytes
  WITHOUT calling mcl. That's a property of the binding, not the EVM
  semantics — it's wrong-but-non-crashing behaviour the implementation
  takes when curve math is unavailable. The spec describes the
  intended (mcl-available) semantics; a separate "stub mode"
  predicate could be added if/when we want to prove the fallback is
  also safe.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions

namespace Evm.Byzantium.Spec

/-- BN254 base-field modulus. EIP-197 / EIP-196. -/
def bn254FieldModulus : Nat :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

/-- A 32-byte big-endian blob, interpreted as a Nat. -/
def beBytesToNat (b : Evm.Bytes) (off : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [0:32] do
    let byte := if off + i < b.size then b.get! (off + i) else (0 : UInt8)
    acc := acc * 256 + byte.toNat
  pure acc

/-- A G1 coord is in range iff its 32-byte BE value is < `p`. -/
def G1CoordInRange (input : Evm.Bytes) (off : Nat) : Prop :=
  beBytesToNat input off < bn254FieldModulus

/-- All four G1 + G2 coordinates of one (G1, G2) pair are in range. -/
def PairCoordsInRange (input : Evm.Bytes) (blockOff : Nat) : Prop :=
  G1CoordInRange input blockOff           ∧  -- G1.x
  G1CoordInRange input (blockOff + 32)    ∧  -- G1.y
  G1CoordInRange input (blockOff + 64)    ∧  -- G2.x.im
  G1CoordInRange input (blockOff + 96)    ∧  -- G2.x.re
  G1CoordInRange input (blockOff + 128)   ∧  -- G2.y.im
  G1CoordInRange input (blockOff + 160)      -- G2.y.re

/-- Predicate that the input bytes represent points "on the curve."
    Left abstract — refined by the FFI implementation against
    libmcl's `mclBnG{1,2}_isValid` and the curve / twist equations
    `y² = x³ + 3` (G1) and `y² = x³ + 3/(9+i)` (G2). -/
opaque OnCurve : Evm.Bytes → Nat → Prop

/-! ## Failure modes — all three precompiles share these -/

/-- The input violates the precompile's structural invariants. -/
def Bn256InvalidInput (input : Evm.Bytes) (off len : Nat) : Prop :=
  -- Either a coord is out of field range, OR the point is off-curve.
  (∃ i, off + i * 32 < off + len ∧ ¬ G1CoordInRange input (off + i * 32))
  ∨ ¬ OnCurve input off

/-! ## ECADD (0x06) -/

/-- ECADD: input 128 bytes = (G1 || G1); output 64 bytes (sum, BE). -/
def IsBn256AddOk (input : Evm.Bytes) (gasLeft : Nat)
                 (output : Evm.Bytes) (gasLeft' : Nat) : Prop :=
  gasLeft ≥ 500 ∧
  PairCoordsInRange input 0 ∧   -- well, both halves' x/y
  OnCurve input 0 ∧
  OnCurve input 64 ∧
  output.size = 64 ∧
  gasLeft' = gasLeft - 500

/-- ECADD failure: invalid input OR insufficient gas. -/
def IsBn256AddFail (input : Evm.Bytes) (gasLeft : Nat) : Prop :=
  gasLeft < 500
  ∨ ¬ PairCoordsInRange input 0
  ∨ ¬ OnCurve input 0
  ∨ ¬ OnCurve input 64

/-! ## ECMUL (0x07) -/

/-- ECMUL: 96 bytes = (G1 point 64 || scalar 32); output 64 bytes. -/
def IsBn256MulOk (input : Evm.Bytes) (gasLeft : Nat)
                 (output : Evm.Bytes) (gasLeft' : Nat) : Prop :=
  gasLeft ≥ 40000 ∧
  G1CoordInRange input 0 ∧
  G1CoordInRange input 32 ∧
  OnCurve input 0 ∧
  -- Scalar is reduced mod the curve order (mcl's
  -- `mclBnFr_setBigEndianMod`); no range check needed.
  output.size = 64 ∧
  gasLeft' = gasLeft - 40000

def IsBn256MulFail (input : Evm.Bytes) (gasLeft : Nat) : Prop :=
  gasLeft < 40000
  ∨ ¬ G1CoordInRange input 0
  ∨ ¬ G1CoordInRange input 32
  ∨ ¬ OnCurve input 0

/-! ## ECPAIRING (0x08) -/

/-- ECPAIRING gas cost: `100000 + 80000 * k` where k = input.size/192. -/
def Bn256PairingGas (inputSize : Nat) : Nat :=
  100000 + 80000 * (inputSize / 192)

/-- Empty input (k=0) is a special case: the product over the empty
    set equals identity in GT, so output is `1` in the low byte. -/
def IsBn256PairingEmpty (gasLeft : Nat)
                        (output : Evm.Bytes) (gasLeft' : Nat) : Prop :=
  gasLeft ≥ 100000 ∧
  output.size = 32 ∧
  output.get! 31 = 1 ∧
  (∀ i < 31, output.get! i = 0) ∧
  gasLeft' = gasLeft - 100000

/-- Multi-pair pairing-check success. Output is `0x...01` iff the
    product of pairings equals identity in GT, else `0x...00`. -/
def IsBn256PairingOk (input : Evm.Bytes) (gasLeft : Nat)
                     (output : Evm.Bytes) (gasLeft' : Nat) : Prop :=
  input.size % 192 = 0 ∧
  input.size > 0 ∧
  let k := input.size / 192
  gasLeft ≥ Bn256PairingGas input.size ∧
  -- Every (G1, G2) pair has in-range coords and lies on the curve.
  (∀ i < k, PairCoordsInRange input (i * 192)) ∧
  (∀ i < k, OnCurve input (i * 192)) ∧
  output.size = 32 ∧
  gasLeft' = gasLeft - Bn256PairingGas input.size

/-- ECPAIRING failure: bad input size, OOG, coord out of range, or
    off-curve point. -/
def IsBn256PairingFail (input : Evm.Bytes) (gasLeft : Nat) : Prop :=
  input.size % 192 ≠ 0
  ∨ gasLeft < Bn256PairingGas input.size
  ∨ (let k := input.size / 192
     ∃ i, i < k ∧ ¬ PairCoordsInRange input (i * 192))
  ∨ (let k := input.size / 192
     ∃ i, i < k ∧ ¬ OnCurve input (i * 192))

end Evm.Byzantium.Spec
