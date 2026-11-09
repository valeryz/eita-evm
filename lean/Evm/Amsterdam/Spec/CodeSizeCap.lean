/-
  Evm.Amsterdam.Spec.CodeSizeCap — EIP-7954: increase max contract size.

  EELS reference: `forks/amsterdam/vm/interpreter.py` line 65:

      MAX_CODE_SIZE = 0x8000

  Compare to EIP-170 / Spurious Dragon:
    `Evm.SpuriousDragon.Vm.Gas.maxCodeSize = 0x6000 = 24576`.

  The cap is enforced on `CREATE` / `CREATE2` deployment: a deploy whose
  returned init-code output exceeds the cap is rejected with
  `OutOfGasError`. EELS: `forks/amsterdam/vm/interpreter.py` line ~110:

      if len(contract_code) > MAX_CODE_SIZE:
          evm = Evm(... AddressCollision ...)   # actually OutOfGas-ish

  Per the SPEC-METHODOLOGY: this is a cross-cutting constant change
  affecting the CREATE/CREATE2 deployment relation. The relation
  itself is the Cancun `IsCreateStep` (or its EIP-3860 Shanghai form)
  with the cap parameter overridden. We expose the constant here.
-/

namespace Evm.Amsterdam.Spec

/-- EELS `forks/amsterdam/vm/interpreter.py` 80 (execution-specs 636b5f1):
    `MAX_CODE_SIZE = 0x10000`. Pre-Amsterdam forks use `0x6000` (EIP-170, Spurious
    Dragon). Corrected 2026-11-09 from an earlier draft's `0x8000`. -/
def maxCodeSize : Nat := 0x10000

/-- Validity predicate on a deployed contract's bytecode length under
    Amsterdam rules. The CREATE / CREATE2 spec uses this in the
    deploy-success branch in lieu of the older EIP-170 / Spurious
    Dragon cap. -/
def IsValidDeployedCodeSize (codeLen : Nat) : Prop :=
  codeLen ≤ maxCodeSize

end Evm.Amsterdam.Spec
