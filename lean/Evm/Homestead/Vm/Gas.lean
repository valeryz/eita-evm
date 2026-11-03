/-
  Evm.Homestead.Vm.Gas — Homestead-specific gas constants.

  Only the constants that change at Homestead live here; everything else
  is referenced from `Evm.Frontier.Vm.Gas`.

  EIP-2 (Homestead): contract-creation transactions cost an extra 32000
  gas (`G_txcreate`) on top of the base `G_transaction`.
-/

namespace Evm.Homestead.Vm.Gas

/-- Extra intrinsic gas for contract-creation transactions. Frontier:
    `0`. Homestead: `32000` (EIP-2). -/
def txCreate : Nat := 32000

end Evm.Homestead.Vm.Gas
