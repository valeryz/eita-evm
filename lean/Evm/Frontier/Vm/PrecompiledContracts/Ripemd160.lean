/-
  Evm.Frontier.Vm.PrecompiledContracts.Ripemd160 — 0x03 RIPEMD160.

  EELS reference:
  ethereum/frontier/vm/precompiled_contracts/ripemd160.py.

  Output: 20-byte RIPEMD-160 of the input, left-zero-padded to 32 bytes
  (the EVM convention). Gas: `600 + 120·⌈len/32⌉`.
-/

import Evm.BaseTypes
import Evm.Crypto.Ripemd160
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm.PrecompiledContracts

def ripemd160 (input : Evm.Bytes) (gas : Nat) : Except Exception (Evm.Bytes × Nat) :=
  let cost := 600 + 120 * ((input.size + 31) / 32)
  if gas < cost then .error .outOfGas
  else
    let h := Evm.Crypto.ripemd160 input
    -- Left-zero-pad the 20-byte digest to 32 bytes.
    return (Evm.Bytes.padLeft h 32, gas - cost)

end Evm.Frontier.Vm.PrecompiledContracts
