/-
  Evm.Frontier.Vm.PrecompiledContracts.Sha256 — 0x02 SHA256.

  EELS reference: ethereum/frontier/vm/precompiled_contracts/sha256.py.
  Output: SHA-256 of the input. Gas: `60 + 12·⌈len/32⌉`.
-/

import Evm.BaseTypes
import Evm.Crypto.Sha256
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm.PrecompiledContracts

def sha256 (input : Evm.Bytes) (gas : Nat) : Except Exception (Evm.Bytes × Nat) :=
  let cost := 60 + 12 * ((input.size + 31) / 32)
  if gas < cost then .error .outOfGas
  else return (Evm.Crypto.sha256 input, gas - cost)

end Evm.Frontier.Vm.PrecompiledContracts
