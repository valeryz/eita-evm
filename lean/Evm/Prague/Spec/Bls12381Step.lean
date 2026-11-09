/-
  Evm.Prague.Spec.Bls12381Step — EIP-2537 BLS12-381 precompiles.

  EELS reference: `forks/prague/vm/precompiled_contracts/bls12_381/`
  (one file per precompile: `bls12_381_g1.py`, `bls12_381_g2.py`,
  `bls12_381_pairing.py`, `bls12_381_map.py`), with gas constants in
  `forks/prague/vm/gas.py` (`GAS_BLS_*`).

  Seven new precompiles at addresses 0x0b..0x11:

      0x0b  G1_ADD           — 2·G1 → G1                   (375 gas)
      0x0c  G1_MSM           — k·(G1,scalar) → G1          (variable)
      0x0d  G2_ADD           — 2·G2 → G2                   (600 gas)
      0x0e  G2_MSM           — k·(G2,scalar) → G2          (variable)
      0x0f  PAIRING_CHECK    — k·(G1,G2) → {0,1}           (32600·k + 37700)
      0x10  MAP_FP_TO_G1     — Fp → G1                     (5500 gas)
      0x11  MAP_FP2_TO_G2    — Fp² → G2                    (23800 gas)

  Per the task brief: we spec input-size predicates and gas formulas
  (i.e. what the EVM observes) but axiomatise the cryptographic
  semantics. The serialised-point encodings are 64 / 128 / 256 bytes
  for Fp / G1 / G2.

  Inheritance: introduced at Prague; no later fork repricing yet.
-/

import Evm.BaseTypes
import Evm.CL.GasEmit

namespace Evm.Prague.Spec

/-! ## Gas constants. EELS: `forks/prague/vm/gas.py`. -/

def gasG1Add        : Nat := 375
def gasG1Mul        : Nat := 12000
def gasG2Add        : Nat := 600
def gasG2Mul        : Nat := 22500
def gasPairingBase  : Nat := 37700
def gasPairingPair  : Nat := 32600
def gasMapFpToG1    : Nat := 5500
def gasMapFp2ToG2   : Nat := 23800

/-! ## I/O sizes (bytes). EELS:
    `forks/prague/vm/precompiled_contracts/bls12_381/*.py`. -/

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

/-! ## Axiomatised crypto predicates

    Per the task brief, we don't try to spec the BLS math here.
    These opaque predicates carry the *correctness* obligation; a
    future bring-up replaces them with concrete checks against a
    verified BLS library (e.g. `blst`). -/

axiom IsValidG1Point  : Evm.Bytes → Prop
axiom IsValidG2Point  : Evm.Bytes → Prop
axiom IsValidFpElem   : Evm.Bytes → Prop
axiom IsValidFp2Elem  : Evm.Bytes → Prop

/-- The pairing product is 1_GT (a successful pairing check). Input is
    a list of (G1, G2) pairs serialised consecutively in `input`. -/
axiom IsValidBlsPairing : Evm.Bytes → Prop

/-! ## Input-size predicates

    Each precompile has a fixed-stride input. The dispatcher rejects
    any input not matching the stride with an `OutOfGas` exception
    (EELS pattern: `if not is_valid_length(input): raise OutOfGasError`). -/

def IsG1AddInputValid       (input : Evm.Bytes) : Prop :=
  input.size = 2 * g1PointSize

def IsG2AddInputValid       (input : Evm.Bytes) : Prop :=
  input.size = 2 * g2PointSize

def IsG1MsmInputValid       (input : Evm.Bytes) : Prop :=
  0 < input.size ∧ input.size % g1MsmPairSize = 0

def IsG2MsmInputValid       (input : Evm.Bytes) : Prop :=
  0 < input.size ∧ input.size % g2MsmPairSize = 0

def IsPairingInputValid     (input : Evm.Bytes) : Prop :=
  0 < input.size ∧ input.size % pairingPairSize = 0

def IsMapFpToG1InputValid   (input : Evm.Bytes) : Prop :=
  input.size = fpSize

def IsMapFp2ToG2InputValid  (input : Evm.Bytes) : Prop :=
  input.size = fp2Size

/-! ## Gas formulas -/

/-- G1_MSM gas: `k · GAS_BLS_G1_MUL · discount(k) / 1000` (floor), EELS
    `forks/prague/vm/precompiled_contracts/bls12_381/bls12_381_g1.py::bls12_g1_msm`
    with `G1_MSM_DISCOUNT_TABLE` (k = 1..128, constant beyond). The table and the
    formula are the emitted ones (`Evm.CL.GasEmit.msmGas`, `blsG1MsmDiscounts`) — one
    owner. (2026-11-09: this used to be the undiscounted `k · GAS_BLS_G1_MUL`.) -/
def g1MsmGas (k : Nat) : Nat :=
  Evm.CL.GasEmit.msmGas gasG1Mul Evm.CL.GasEmit.blsG1MsmDiscounts
    Evm.CL.GasEmit.blsG1MsmMaxDiscount k

/-- G2_MSM gas: the same with `GAS_BLS_G2_MUL` and `G2_MSM_DISCOUNT_TABLE`
    (`bls12_381_g2.py::bls12_g2_msm`). -/
def g2MsmGas (k : Nat) : Nat :=
  Evm.CL.GasEmit.msmGas gasG2Mul Evm.CL.GasEmit.blsG2MsmDiscounts
    Evm.CL.GasEmit.blsG2MsmMaxDiscount k

/-- PAIRING_CHECK gas: `BASE + k · PER_PAIR`. EELS:
    `forks/prague/vm/gas.py::GAS_BLS_PAIRING_BASE` (37700) plus
    `GAS_BLS_PAIRING_PER_PAIR` (32600). -/
def pairingGas (k : Nat) : Nat := gasPairingBase + k * gasPairingPair

/-! ## Output-size invariants -/

/-- G1_ADD, G1_MSM, MAP_FP_TO_G1 all produce a 128-byte G1 point. -/
def isG1Output (out : Evm.Bytes) : Prop := out.size = g1PointSize

/-- G2_ADD, G2_MSM, MAP_FP2_TO_G2 all produce a 256-byte G2 point. -/
def isG2Output (out : Evm.Bytes) : Prop := out.size = g2PointSize

/-- PAIRING_CHECK produces 32 bytes: big-endian `1` on success,
    `0` on failure. -/
def isPairingOutput (out : Evm.Bytes) : Prop := out.size = 32

/-! ## Per-precompile success predicates

    Each `IsXxxSuccess input gas output gas'` says: the precompile
    accepted the input, charged the right gas, and produced a
    well-formed output. Crypto correctness is delegated to the
    axiomatised predicates above. -/

def IsG1AddSuccess (input : Evm.Bytes) (gas : Nat)
                    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsG1AddInputValid input ∧
  gas ≥ gasG1Add ∧
  isG1Output output ∧
  gas' = gas - gasG1Add

def IsG2AddSuccess (input : Evm.Bytes) (gas : Nat)
                    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsG2AddInputValid input ∧
  gas ≥ gasG2Add ∧
  isG2Output output ∧
  gas' = gas - gasG2Add

def IsG1MsmSuccess (input : Evm.Bytes) (gas : Nat)
                    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsG1MsmInputValid input ∧
  let k := input.size / g1MsmPairSize
  gas ≥ g1MsmGas k ∧
  isG1Output output ∧
  gas' = gas - g1MsmGas k

def IsG2MsmSuccess (input : Evm.Bytes) (gas : Nat)
                    (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsG2MsmInputValid input ∧
  let k := input.size / g2MsmPairSize
  gas ≥ g2MsmGas k ∧
  isG2Output output ∧
  gas' = gas - g2MsmGas k

def IsPairingCheckSuccess (input : Evm.Bytes) (gas : Nat)
                           (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsPairingInputValid input ∧
  let k := input.size / pairingPairSize
  gas ≥ pairingGas k ∧
  isPairingOutput output ∧
  gas' = gas - pairingGas k ∧
  -- Output encodes the pairing-check result: 1 ↔ pairing valid.
  (IsValidBlsPairing input → output = Evm.U256.toBytesBE 1) ∧
  (¬ IsValidBlsPairing input → output = Evm.U256.toBytesBE 0)

def IsMapFpToG1Success (input : Evm.Bytes) (gas : Nat)
                        (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsMapFpToG1InputValid input ∧
  gas ≥ gasMapFpToG1 ∧
  isG1Output output ∧
  gas' = gas - gasMapFpToG1

def IsMapFp2ToG2Success (input : Evm.Bytes) (gas : Nat)
                         (output : Evm.Bytes) (gas' : Nat) : Prop :=
  IsMapFp2ToG2InputValid input ∧
  gas ≥ gasMapFp2ToG2 ∧
  isG2Output output ∧
  gas' = gas - gasMapFp2ToG2

end Evm.Prague.Spec
