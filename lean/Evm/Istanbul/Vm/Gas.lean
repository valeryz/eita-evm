/-
  Evm.Istanbul.Vm.Gas — EIP-1108, EIP-1884, EIP-2028, EIP-2200 re-pricing.

  EELS reference: `forks/istanbul/vm/gas.py` (class `GasCosts`). Every
  constant below is the Istanbul value, cited line-by-line against
  EELS' `GasCosts`. Pre-Istanbul values are still available in the
  TangerineWhistle / Frontier gas modules and remain in use for ops
  whose price didn't change at Istanbul.

  Activation: block 9,069,000 (2019-12-08). Constants listed in the
  order they appear in `GasCosts`.
-/

namespace Evm.Istanbul.Vm.Gas

/-- EIP-1884: SLOAD 200 → 800. EELS `GasCosts.SLOAD` (line 40 of
    `forks/istanbul/vm/gas.py`). -/
def sLoad : Nat := 800

/-- EIP-1884: BALANCE 400 → 700. EELS `GasCosts.OPCODE_BALANCE`
    (line 160). -/
def balance : Nat := 700

/-- EIP-1884: EXTCODEHASH 400 → 700. EELS
    `GasCosts.OPCODE_EXTCODEHASH` (line 116). The opcode itself was
    introduced at Constantinople (EIP-1052). -/
def extCodeHash : Nat := 700

/-- EIP-1884: new opcode SELFBALANCE (0x47) priced at FAST_STEP (5).
    EELS `forks/istanbul/vm/instructions/environment.py` `self_balance`
    charges `GasCosts.FAST_STEP` (= 5, line 57). -/
def selfBalance : Nat := 5

/-- EIP-1344: new opcode CHAINID (0x46) priced at BASE (2). EELS
    `GasCosts.OPCODE_CHAINID` (line 135 = BASE = 2). -/
def chainId : Nat := 2

/-- EIP-2028: non-zero calldata byte 68 → 16. EELS
    `GasCosts.TX_DATA_PER_NON_ZERO` (line 81). The zero-byte cost
    (4) is unchanged. -/
def txDataNonZero : Nat := 16

/-- EIP-2028 zero-byte calldata cost (unchanged from Frontier). EELS
    `GasCosts.TX_DATA_PER_ZERO` (line 80). -/
def txDataZero : Nat := 4

/-! ### EIP-2200 net SSTORE metering

  The three constants below are the post-Istanbul SSTORE schedule;
  refund handling is encoded directly in `Vm/Instructions/Storage.lean`
  (this fork's `sstore`). All values from EELS `GasCosts`:
    `STORAGE_SET` = 20000 (line 43), unchanged.
    `COLD_STORAGE_WRITE` = 5000 (line 44), unchanged.
    `REFUND_STORAGE_CLEAR` = 15000 (line 60), unchanged.
  The no-op / dirty-slot price is `SLOAD` = 800. -/

/-- EIP-2200: SSTORE on a clean slot, 0 → non-zero. EELS
    `GasCosts.STORAGE_SET`. -/
def sstoreSet : Nat := 20000

/-- EIP-2200: SSTORE on a clean slot, non-zero → other. EELS
    `GasCosts.COLD_STORAGE_WRITE`. (Frontier called this
    `sReset`; Istanbul keeps the same value.) -/
def sstoreReset : Nat := 5000

/-- EIP-2200: refund for clearing a non-zero slot to zero (issued the
    first time per tx, can be reversed on a subsequent write).
    EELS `GasCosts.REFUND_STORAGE_CLEAR`. -/
def sstoreClearRefund : Nat := 15000

/-- EIP-2200 trip-wire: SSTORE reverts with `OutOfGas` if gas remaining
    before the cost charge is `≤ CALL_STIPEND` (2300). This is the
    EIP-1706 reentrancy guard folded into EIP-2200 — it prevents
    contracts whose only gas is the 2300-stipend forwarded by CALL with
    value from issuing a SSTORE.

    EELS reference: `forks/istanbul/vm/instructions/storage.py` lines
    66-67 (`if evm.gas_left <= GasCosts.CALL_STIPEND: raise OutOfGasError`). -/
def sstoreSentryGas : Nat := 2300

/-! ### EIP-1108 alt_bn128 re-pricing

  Repriced from Byzantium. The precompiles themselves remain stubs in
  this codebase; the constants are here for fidelity / future use. -/

/-- EIP-1108: ALT_BN128_ADD 500 → 150. EELS `GasCosts.PRECOMPILE_ECADD`. -/
def altBn128Add : Nat := 150

/-- EIP-1108: ALT_BN128_MUL 40000 → 6000. EELS
    `GasCosts.PRECOMPILE_ECMUL`. -/
def altBn128Mul : Nat := 6000

/-- EIP-1108: ALT_BN128_PAIRING base 100000 → 45000. EELS
    `GasCosts.PRECOMPILE_ECPAIRING_BASE`. -/
def altBn128PairingBase : Nat := 45000

/-- EIP-1108: ALT_BN128_PAIRING per-point 80000 → 34000. EELS
    `GasCosts.PRECOMPILE_ECPAIRING_PER_POINT`. -/
def altBn128PairingPerPoint : Nat := 34000

/-- EIP-152: BLAKE2F per-round cost = 1 gas. EELS
    `GasCosts.PRECOMPILE_BLAKE2F_PER_ROUND` (line 71). -/
def blake2fPerRound : Nat := 1

end Evm.Istanbul.Vm.Gas
