/-
  Evm.Crypto.Bls12381 — BLS12-381 for the EIP-2537 precompiles (0x0b..0x11): the
  curve constants, the EIP-2537 encodings, the on-curve checks, and the crypto ORACLE.

  The precompile wrappers (`Evm.Prague.Vm.PrecompiledContracts.bls*With`) and their
  relations (`Evm.Prague.Spec.Bls12381Step`) are parametric in an `Oracle`: the group law,
  scalar multiplication, the subgroup test, the two map-to-curve functions and the
  pairing-product check. Everything else — lengths, the field-element range check, the
  point-at-infinity encoding, the curve equation, where the subgroup test is applied, gas,
  and the output encoding — is written here and in the wrapper, from EELS
  `forks/prague/vm/precompiled_contracts/bls12_381/__init__.py`.

  `native` is the oracle the replay runs: each operation calls `lean/c/bls12381.cpp`'s
  `lean_bls_oracle_*` entries, i.e. blst (vendor/blst, pinned v0.3.17) — the same library
  and the same blst calls as the production precompiles in that file. What the oracle is
  assumed to compute, in Mathlib terms, is `Evm.Crypto.Contracts`; `cryptoTests` checks
  those contracts on random inputs against `native`.
-/

import Evm.BaseTypes
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp

namespace Evm.Crypto.Bls12381

open Evm.Byzantium.Vm.PrecompiledContracts (readBytesAsNat natToBytesBE)

/-- The base-field modulus p (py_ecc `FQ.field_modulus`). -/
def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The order r of G1 and G2 (py_ecc `curve_order`). -/
def r : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- An element `c0 + c1·u` of Fp2 = Fp[u]/(u² + 1) (py_ecc `FQ2((c0, c1))`). -/
abbrev Fp2 := Nat × Nat
/-- An affine G1 point (x, y) over Fp; (0, 0) is the point at infinity (EIP-2537 encoding,
    EELS `_bytes_to_g1_cached` 327-329). -/
abbrev G1 := Nat × Nat
/-- An affine G2 point (x, y) over Fp2; ((0,0), (0,0)) is the point at infinity. -/
abbrev G2 := Fp2 × Fp2

def g1Zero : G1 := (0, 0)
def g2Zero : G2 := ((0, 0), (0, 0))

/-! ## Field arithmetic (only what the curve equation needs) -/

def fp2Add (a b : Fp2) : Fp2 := ((a.1 + b.1) % p, (a.2 + b.2) % p)
/-- (a0 + a1 u)(b0 + b1 u) = (a0 b0 − a1 b1) + (a0 b1 + a1 b0) u, as u² = −1. -/
def fp2Mul (a b : Fp2) : Fp2 :=
  ((a.1 * b.1 % p + (p - a.2 * b.2 % p)) % p, (a.1 * b.2 + a.2 * b.1) % p)

/-- G1: y² = x³ + 4 (py_ecc `b = FQ(4)`); infinity is on the curve (py_ecc `is_on_curve`
    returns true for z = 0). EELS `_bytes_to_g1_cached` 332-333. -/
def g1OnCurve (P : G1) : Bool :=
  P == g1Zero || P.2 * P.2 % p == (P.1 * P.1 % p * P.1 + 4) % p

/-- G2: y² = x³ + 4(1 + u) (py_ecc `b2 = FQ2([4, 4])`). EELS `_bytes_to_g2_cached` 514-515. -/
def g2OnCurve (Q : G2) : Bool :=
  Q == g2Zero || fp2Mul Q.2 Q.2 == fp2Add (fp2Mul Q.1 (fp2Mul Q.1 Q.1)) (4, 4)

/-! ## The oracle -/

/-- The cryptographic operations the EIP-2537 wrappers delegate. Inputs are what the
    wrappers have validated (field elements < p, points on their curves; subgroup points
    for `*Mul` and `pairingCheck`); scalars are < 2²⁵⁶. -/
structure Oracle where
  /-- G1 point addition (py_ecc `add`, EELS `bls12_g1_add` 64). -/
  g1Add : G1 → G1 → G1
  /-- G1 scalar multiplication (py_ecc `multiply`, EELS `bls12_g1_msm` 108). -/
  g1Mul : G1 → Nat → G1
  /-- G1 subgroup test, EELS's `is_inf(multiply(point, curve_order))` (`__init__.py` 335). -/
  g1InSubgroup : G1 → Bool
  g2Add : G2 → G2 → G2
  g2Mul : G2 → Nat → G2
  g2InSubgroup : G2 → Bool
  /-- `clear_cofactor_G1(map_to_curve_G1(u))` (EELS `bls12_map_fp_to_g1` 145). -/
  mapFpToG1 : Nat → G1
  /-- `clear_cofactor_G2(map_to_curve_G2(u))` (EELS `bls12_381_g2.py::bls12_map_fp2_to_g2` 146). -/
  mapFp2ToG2 : Fp2 → G2
  /-- Whether `∏ e(Pᵢ, Qᵢ) = 1` in GT (EELS `bls12_pairing` 49-66). -/
  pairingCheck : List (G1 × G2) → Bool

/-! ## EIP-2537 encodings (EELS `bls12_381/__init__.py`) -/

/-- `bytes_to_fq` (426-454): the 64-byte big-endian integer at `off`, which must be < p. -/
def fpDecode (b : Evm.Bytes) (off : Nat) : Option Nat :=
  let c := readBytesAsNat b off 64
  if c < p then some c else none

/-- `bytes_to_fq2` (457-487): c0 then c1. -/
def fp2Decode (b : Evm.Bytes) (off : Nat) : Option Fp2 :=
  match fpDecode b off, fpDecode b (off + 64) with
  | some c0, some c1 => some (c0, c1)
  | _, _ => none

/-- `bytes_to_g1` without the subgroup check (`_bytes_to_g1_cached` 309-338): x, y field
    elements, (0, 0) the infinity, on the curve. -/
def g1Decode (b : Evm.Bytes) (off : Nat) : Option G1 :=
  match fpDecode b off, fpDecode b (off + 64) with
  | some x, some y => if g1OnCurve (x, y) then some (x, y) else none
  | _, _ => none

/-- `bytes_to_g2` without the subgroup check (`_bytes_to_g2_cached` 495-520). -/
def g2Decode (b : Evm.Bytes) (off : Nat) : Option G2 :=
  match fp2Decode b off, fp2Decode b (off + 128) with
  | some x, some y => if g2OnCurve (x, y) then some (x, y) else none
  | _, _ => none

/-- `bytes_to_g1(…, subgroup_check=True)` (335-336). -/
def g1DecodeSub (o : Oracle) (b : Evm.Bytes) (off : Nat) : Option G1 :=
  match g1Decode b off with
  | some P => if o.g1InSubgroup P then some P else none
  | none => none

/-- `bytes_to_g2(…, subgroup_check=True)` (517-518). -/
def g2DecodeSub (o : Oracle) (b : Evm.Bytes) (off : Nat) : Option G2 :=
  match g2Decode b off with
  | some Q => if o.g2InSubgroup Q then some Q else none
  | none => none

def fpEncode (x : Nat) : Evm.Bytes := natToBytesBE x 64
/-- `g1_to_bytes` (372-391): normalised x ‖ y, 64 bytes each (infinity = zeros). -/
def g1Encode (P : G1) : Evm.Bytes := fpEncode P.1 ++ fpEncode P.2
def fp2Encode (x : Fp2) : Evm.Bytes := fpEncode x.1 ++ fpEncode x.2
/-- `g2_to_bytes` (573-591, `fq2_to_bytes` 554-570): x.c0 ‖ x.c1 ‖ y.c0 ‖ y.c1. -/
def g2Encode (Q : G2) : Evm.Bytes := fp2Encode Q.1 ++ fp2Encode Q.2

/-- A 32-byte big-endian scalar (`decode_g1_scalar_pair` 421). -/
def scalarDecode (b : Evm.Bytes) (off : Nat) : Nat := readBytesAsNat b off 32

/-- PAIRING_CHECK's 32-byte output (EELS `bls12_381_pairing.py` 66-69:
    `b"\\x00" * 31 + b"\\x01"` or `b"\\x00" * 32`). -/
def pairingOutput (ok : Bool) : Evm.Bytes := natToBytesBE (if ok then 1 else 0) 32

/-! ## MSM and pairing inputs -/

/-- `decode_g1_scalar_pair` over each of the `k` 160-byte pairs (EELS `bls12_g1_msm`
    103-107): subgroup-checked point, scalar. `none` if any pair is invalid. -/
def g1MsmPairs (o : Oracle) (b : Evm.Bytes) (k : Nat) : Option (List (G1 × Nat)) :=
  (List.range k).mapM fun i =>
    (g1DecodeSub o b (160 * i)).map fun P => (P, scalarDecode b (160 * i + 128))

/-- `decode_g2_scalar_pair` (594-622) over each of the `k` 288-byte pairs (EELS
    `bls12_381_g2.py::bls12_g2_msm` 104-108). -/
def g2MsmPairs (o : Oracle) (b : Evm.Bytes) (k : Nat) : Option (List (G2 × Nat)) :=
  (List.range k).mapM fun i =>
    (g2DecodeSub o b (288 * i)).map fun Q => (Q, scalarDecode b (288 * i + 256))

/-- EELS `bls12_g1_msm` 103-113: `result = multiply(p₀, m₀)`, then
    `result = add(result, multiply(pᵢ, mᵢ))`. -/
def g1MsmSum (o : Oracle) : List (G1 × Nat) → G1
  | [] => g1Zero
  | (P, m) :: rest => rest.foldl (fun acc (Q, n) => o.g1Add acc (o.g1Mul Q n)) (o.g1Mul P m)

/-- EELS `bls12_381_g2.py::bls12_g2_msm` 104-116. -/
def g2MsmSum (o : Oracle) : List (G2 × Nat) → G2
  | [] => g2Zero
  | (P, m) :: rest => rest.foldl (fun acc (Q, n) => o.g2Add acc (o.g2Mul Q n)) (o.g2Mul P m)

/-- EELS `bls12_pairing` 50-62: each 384-byte pair is a G1 point and a G2 point, both
    decoded and subgroup-checked. -/
def pairingPairs (o : Oracle) (b : Evm.Bytes) (k : Nat) : Option (List (G1 × G2)) :=
  (List.range k).mapM fun i =>
    match g1DecodeSub o b (384 * i), g2DecodeSub o b (384 * i + 128) with
    | some P, some Q => some (P, Q)
    | _, _ => none

/-! ## The native oracle: blst through `lean/c/bls12381.cpp`

    Each extern takes and returns EIP-2537 encodings; a malformed argument (never passed:
    the wrappers validate first) yields the infinity encoding. -/

@[extern "lean_bls_oracle_g1_add"] opaque g1AddRaw (a b : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_g1_mul"] opaque g1MulRaw (a s : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_g1_in_g1"] opaque g1InG1Raw (a : @& ByteArray) : UInt8
@[extern "lean_bls_oracle_g2_add"] opaque g2AddRaw (a b : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_g2_mul"] opaque g2MulRaw (a s : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_g2_in_g2"] opaque g2InG2Raw (a : @& ByteArray) : UInt8
@[extern "lean_bls_oracle_map_fp_to_g1"] opaque mapFpToG1Raw (u : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_map_fp2_to_g2"] opaque mapFp2ToG2Raw (u : @& ByteArray) : ByteArray
@[extern "lean_bls_oracle_pairing_check"] opaque pairingCheckRaw (pairs : @& ByteArray) : UInt8

def g1OfBytes (b : Evm.Bytes) : G1 := (readBytesAsNat b 0 64, readBytesAsNat b 64 64)
def g2OfBytes (b : Evm.Bytes) : G2 :=
  ((readBytesAsNat b 0 64, readBytesAsNat b 64 64),
   (readBytesAsNat b 128 64, readBytesAsNat b 192 64))

/-- TRUST BOUNDARY: BLS12-381 as computed by blst v0.3.17 (vendor/blst), via
    `lean/c/bls12381.cpp`. -/
def native : Oracle where
  g1Add a b := g1OfBytes (g1AddRaw (g1Encode a) (g1Encode b))
  g1Mul a n := g1OfBytes (g1MulRaw (g1Encode a) (natToBytesBE n 32))
  g1InSubgroup a := g1InG1Raw (g1Encode a) == 1
  g2Add a b := g2OfBytes (g2AddRaw (g2Encode a) (g2Encode b))
  g2Mul a n := g2OfBytes (g2MulRaw (g2Encode a) (natToBytesBE n 32))
  g2InSubgroup a := g2InG2Raw (g2Encode a) == 1
  mapFpToG1 u := g1OfBytes (mapFpToG1Raw (fpEncode u))
  mapFp2ToG2 u := g2OfBytes (mapFp2ToG2Raw (fp2Encode u))
  pairingCheck ps :=
    pairingCheckRaw (ps.foldl (fun acc (P, Q) => acc ++ g1Encode P ++ g2Encode Q) ByteArray.empty) == 1

end Evm.Crypto.Bls12381
