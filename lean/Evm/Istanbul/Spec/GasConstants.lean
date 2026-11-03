/-
  Evm.Istanbul.Spec.GasConstants — EIP-1884 re-pricing constants.

  EELS reference: `forks/istanbul/vm/gas.py` class `GasCosts`
  (lines 40 / 116 / 160 for SLOAD / EXTCODEHASH / BALANCE
  respectively). EIP-1884 was the controversial "trie-touching ops are
  underpriced" reprice — it tripled or quadrupled three opcodes whose
  cost no longer reflected the I/O work they entailed.

  This file is the *spec-level* statement of those constants; the
  matching *implementation-level* definitions live in
  `Evm.Istanbul.Vm.Gas`. Both sources agree (and a one-liner
  refinement check could eventually be added — `simp` should close it).

  EIP-1884 also added SELFBALANCE at 5 gas (FAST_STEP), but that's a
  new opcode rather than a reprice, so its constant lives with the
  step relation (`Evm/Istanbul/Spec/SelfbalanceStep.lean`).
-/

namespace Evm.Istanbul.Spec

/-- EIP-1884: SLOAD 200 → 800. -/
def gSload : Nat := 800

/-- EIP-1884: BALANCE 400 → 700. -/
def gBalance : Nat := 700

/-- EIP-1884: EXTCODEHASH 400 → 700. -/
def gExtCodeHash : Nat := 700

/-! ## EIP-1108 — alt_bn128 reprice

    These override Byzantium's bn256 gas formula at Istanbul. The
    underlying curve math doesn't change — only the gas charge.

    EELS reference: `forks/istanbul/vm/precompiled_contracts/{alt_bn
    128_add, alt_bn128_mul, alt_bn128_pairing_check}.py`. Spec source
    is `Evm.Byzantium.Spec.Bn256Step`; the matching implementation
    lives in `Evm.Istanbul.Vm.PrecompiledContracts.Bn256`. -/

/-- EIP-1108: bn256 ECADD 500 → 150. -/
def gBn256Add : Nat := 150

/-- EIP-1108: bn256 ECMUL 40000 → 6000. -/
def gBn256Mul : Nat := 6000

/-- EIP-1108: bn256 ECPAIRING fixed-cost 100000 → 45000. -/
def gBn256PairingBase : Nat := 45000

/-- EIP-1108: bn256 ECPAIRING per-pair 80000 → 34000. -/
def gBn256PairingPerPair : Nat := 34000

end Evm.Istanbul.Spec
