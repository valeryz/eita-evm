/-
  Evm.Frontier.Vm.PrecompiledContracts.Identity — 0x04 (datacopy).

  EELS reference: ethereum/frontier/vm/precompiled_contracts/identity.py.
  Returns the input unchanged. Gas: `15 + 3·⌈len/32⌉`.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm.PrecompiledContracts

/-- Identity precompile: output = input, cost depends on input length. -/
def identity (input : Evm.Bytes) (gas : Nat) : Except Exception (Evm.Bytes × Nat) :=
  let cost := 15 + 3 * ((input.size + 31) / 32)
  if gas < cost then .error .outOfGas
  else return (input, gas - cost)

end Evm.Frontier.Vm.PrecompiledContracts
