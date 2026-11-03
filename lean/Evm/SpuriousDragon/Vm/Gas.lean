/-
  Evm.SpuriousDragon.Vm.Gas — EIP-160 gas re-pricing.

  EELS reference: ethereum/spurious_dragon/vm/gas.py.

  Only one constant actually changes at SD compared to Tangerine Whistle:
  the per-byte cost of `EXP`. Everything else is unchanged from TW.
-/

namespace Evm.SpuriousDragon.Vm.Gas

/-- EXP per-byte cost: 10 → 50 (EIP-160). Base cost (`GAS_EXP` = 10)
    is unchanged. -/
def expByte : Nat := 50

/-- Maximum allowed deployed-contract code size (EIP-170). -/
def maxCodeSize : Nat := 24576

end Evm.SpuriousDragon.Vm.Gas
