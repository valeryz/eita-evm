/-
  Evm.Frontier.Vm.PrecompiledContracts.EcRecover — 0x01 ECRECOVER.

  EELS reference:
  ethereum/frontier/vm/precompiled_contracts/ecrecover.py.

  Input: `hash ‖ v ‖ r ‖ s` (128 bytes, EVM-padded). Output: 32-byte
  zero-padded recovered address, or empty bytes on invalid signature.
  Gas: 3000 (constant).

  Implementation forwards to `Evm.Crypto.ecrecoverRaw`, which wraps
  libsecp256k1 in C. Inputs shorter than 128 bytes are right-zero-padded
  to 128 first, matching the EVM ABI convention for precompiles.
-/

import Evm.BaseTypes
import Evm.Crypto.EcRecover
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm.PrecompiledContracts

def ecrecover (input : Evm.Bytes) (gas : Nat) : Except Exception (Evm.Bytes × Nat) :=
  let cost := 3000
  if gas < cost then .error .outOfGas
  else
    let padded := Evm.Bytes.padRight input 128
    return (Evm.Crypto.ecrecoverRaw padded, gas - cost)

end Evm.Frontier.Vm.PrecompiledContracts
