/-
  Evm.TangerineWhistle.Spec.GasConstants — EIP-150 gas re-pricing.

  EELS reference: `ethereum/forks/tangerine_whistle/vm/gas.py`
  class `GasCosts` (lines ~40-80). All values below are direct from
  EELS' delta from Homestead, traceable to EIP-150.

  These are the spec-level constants the relations in the rest of
  this fork (and downstream) refer to by name. The corresponding
  implementation lives in `Evm.TangerineWhistle.Vm.Gas`; this file
  re-exports them under the `Spec` namespace so spec relations
  don't reach into `Vm.Gas`.

  Per the SPEC-METHODOLOGY: this is a "GasConstants" delta — not a
  per-opcode step relation, but a table of base costs that
  per-opcode relations elsewhere will consume.

  EIP-150 (re-pricing for the 2016 Shanghai DoS attack):

    | Opcode          | Frontier/Hmstd | TW     |
    |-----------------|----------------|--------|
    | SLOAD     0x54  |    50          |   200  |
    | BALANCE   0x31  |    20          |   400  |
    | CALL fam.       |    40          |   700  |
    | EXTCODESIZE 0x3b|    20          |   700  |
    | EXTCODECOPY 0x3c|    20          |   700  |
    | SELFDESTRUCT    |     0          |  5000  |
    | NEW_ACCOUNT add |     -          | 25000  |  (SELFDESTRUCT
    |                                              beneficiary dead;
    |                                              EIP-150 #4)

  Not changed at this fork (clarifications):
    * EXTCODEHASH (0x3f) — doesn't exist yet; introduced at
      Constantinople (EIP-1052). No constant here.
    * The 25000 NEW_ACCOUNT cost for CALL when transferring to a
      non-existent account was already 25000 since Frontier (lives
      in `Evm.Frontier.Vm.Gas.newAccount`). EIP-150's #4 ADDS the
      same per-call surcharge to SELFDESTRUCT, which is the
      `selfDestructNewAccount` below.

  Also new at this fork: the "all-but-one-64th" / 63/64 gas-
  forwarding rule for CALL family (EIP-150 #5). That's structural,
  not a constant; see `Evm.Frontier.Vm.Call` (`Rules.eip150`).
-/

import Evm.TangerineWhistle.Vm.Gas

namespace Evm.TangerineWhistle.Spec.Gas

/-- BALANCE (0x31): 20 → 400. EIP-150 #1. -/
def balance : Nat := Evm.TangerineWhistle.Vm.Gas.balance

/-- SLOAD (0x54): 50 → 200. EIP-150 #1. -/
def sLoad : Nat := Evm.TangerineWhistle.Vm.Gas.sLoad

/-- CALL family base (CALL / CALLCODE / DELEGATECALL): 40 → 700.
    EIP-150 #1. The per-call surcharges (`Gas.callValue`,
    `Gas.newAccount`) are unchanged from Frontier and still added on
    top of this base. -/
def call : Nat := Evm.TangerineWhistle.Vm.Gas.call

/-- EXTCODESIZE / EXTCODECOPY base: 20 → 700. EIP-150 #1.
    Per-byte copy cost (`Gas.copy` = 3) is unchanged. -/
def extCode : Nat := Evm.TangerineWhistle.Vm.Gas.extCode

/-- SELFDESTRUCT base: 0 → 5000. EIP-150 #2. -/
def selfDestruct : Nat := Evm.TangerineWhistle.Vm.Gas.selfDestruct

/-- EIP-150 #4: additional NEW_ACCOUNT cost when SELFDESTRUCT's
    beneficiary doesn't already exist. Same numeric value as the
    long-standing CALL NEW_ACCOUNT (`Frontier.Vm.Gas.newAccount` =
    25000); EIP-150 reuses that constant for SELFDESTRUCT. -/
def selfDestructNewAccount : Nat := 25000

/-! ## Note on EIP-150 #5 (63/64 forward rule)

    The forwarded-gas cap is structural, not a constant:
        forward = min(gasArg, available - available / 64)
    See `Evm.TangerineWhistle.Vm.Effect.capForward` and `Evm.Frontier.Vm.Call.plan`
    (proved against the derived cb-call in `Evm.CL.EffectCallProof`). -/

end Evm.TangerineWhistle.Spec.Gas
