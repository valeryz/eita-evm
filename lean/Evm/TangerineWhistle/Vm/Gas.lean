/-
  Evm.TangerineWhistle.Vm.Gas — EIP-150 gas re-pricing.

  EELS reference: `forks/tangerine_whistle/vm/gas.py` class `GasCosts`
  (lines 40+). All values below are direct from EELS' delta from
  Homestead, traceable to EIP-150:

    * SLOAD             50  →  200    (EIP-150 #1)
    * BALANCE           20  →  400    (EIP-150 #1)
    * EXTERNAL_BASE     20  →  700    (EIP-150 #1, covers
                                       EXTCODESIZE/EXTCODECOPY)
    * CALL_BASE         40  →  700    (EIP-150 #1)
    * SELFDESTRUCT       0  → 5000    (EIP-150 #2)
    * SELFDESTRUCT_NEW_ACCOUNT — new constant 25000 charged when
      beneficiary doesn't exist (EIP-150 #4, NEW_ACCOUNT).

  Also new at this fork: the "all-but-one-64th" / 63/64 gas-
  forwarding rule for CALL family (EIP-150 #5). That's structural
  rather than a constant — see `Vm/Effect.lean`'s CALL gas math.

  All these are responses to the 2016 Shanghai DoS attack — opcodes
  that pull lots of state on each step got expensive enough to be
  uneconomical in attack scenarios.

  Per `lean/REPLAY.md`, ValidBlocks pass 185/185 and GeneralStateTests
  pass 1014/1015 (one outlier is a known 10KB compiled-Solidity edge
  case — see REPLAY.md). So this module's constants + the 63/64 rule
  in Effect.lean are well-validated.

  KEVM cross-check pending — see [[feedback-eels-is-the-spec]].
-/

namespace Evm.TangerineWhistle.Vm.Gas

/-- BALANCE: 20 → 400. -/
def balance : Nat := 400

/-- SLOAD: 50 → 200. -/
def sLoad : Nat := 200

/-- CALL family (CALL / CALLCODE / DELEGATECALL) base: 40 → 700. -/
def call : Nat := 700

/-- EXTCODESIZE / EXTCODECOPY base: 20 → 700. (Per-byte cost stays at
    `GAS_COPY` = 3.) -/
def extCode : Nat := 700

/-- SELFDESTRUCT base: 0 → 5000. -/
def selfDestruct : Nat := 5000

end Evm.TangerineWhistle.Vm.Gas
