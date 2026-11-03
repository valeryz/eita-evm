/-
  Evm.London.Vm.Gas — gas-table deltas at London.

  EELS reference: `forks/london/vm/gas.py` (the `GasCosts` Final-class).

  London inherits the Berlin warm/cold split (EIP-2929: WARM_ACCESS=100,
  COLD_ACCOUNT_ACCESS=2600, COLD_STORAGE_ACCESS=2100). London then
  applies EIP-3529 deltas on top:

    * `REFUND_STORAGE_CLEAR`: 15000 (Frontier) → 4800 (London).
    * `SELFDESTRUCT_REFUND`: 24000 (Frontier) → removed (no refund).
    * Max-refund ratio: `gasUsed/2` (pre-London) → `gasUsed/5` (London).

  EELS lines:
    * `forks/london/vm/gas.py` line 62 — `REFUND_STORAGE_CLEAR = 4800`.
    * `forks/london/fork.py`     line 819 — `tx_gas_used_before_refund //
                                              Uint(5)` (the 1/5 cap).
    * SELFDESTRUCT refund removal: `forks/london/vm/instructions/system.py`
      `selfdestruct` (lines 470-532) — no `refund_counter` mutation.
-/

namespace Evm.London.Vm.Gas

/-- EIP-3529: SSTORE clear refund drops 15000 → 4800. -/
def sStoreClearRefund : Nat := 4800

/-- EIP-3529: the SELFDESTRUCT refund is removed entirely. Kept as a
    named constant so the dispatch table reads symmetrically with
    older forks. -/
def selfDestructRefund : Nat := 0

/-- EIP-3529: cap denominator for refund. Returns `gasUsed / 5` where
    pre-London returned `gasUsed / 2`. EELS:
    `forks/london/fork.py` line 819 (`Uint(5)`). -/
def refundCap (gasUsed : Nat) : Nat := gasUsed / 5

/-- EIP-2929 warm/cold constants (Berlin baseline inherited by London).
    EELS: `forks/london/vm/gas.py` lines 40-42. -/
def warmAccess         : Nat := 100
def coldAccountAccess  : Nat := 2600
def coldStorageAccess  : Nat := 2100

end Evm.London.Vm.Gas
