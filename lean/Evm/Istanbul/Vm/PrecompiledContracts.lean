/-
  Evm.Istanbul.Vm.PrecompiledContracts — registry extended with
  BLAKE2F (EIP-152) at 0x09.

  EELS reference:
  `forks/istanbul/vm/precompiled_contracts/mapping.py` (registry) and
  `forks/istanbul/vm/precompiled_contracts/__init__.py` (addresses).

  Istanbul precompile table (`mapping.py`):
    0x01 ECRECOVER   — from Frontier
    0x02 SHA256      — from Frontier
    0x03 RIPEMD160   — from Frontier
    0x04 IDENTITY    — from Frontier
    0x05 MODEXP      — from Byzantium (EIP-198)
    0x06 ECADD       — from Byzantium (EIP-196), re-priced (EIP-1108)
    0x07 ECMUL       — from Byzantium (EIP-196), re-priced (EIP-1108)
    0x08 ECPAIRING   — from Byzantium (EIP-197), re-priced (EIP-1108)
    0x09 BLAKE2F     — Istanbul, EIP-152

  This codebase wires 0x01..0x04 through `Evm.Frontier.Vm.Precompiled
  Contracts.registry`, then 0x05..0x08 through `Evm.Byzantium.Vm.
  PrecompiledContracts.registry`, then appends BLAKE2F at 0x09. The
  bn256 entries here still use Byzantium-era gas pricing rather than
  EIP-1108's reduced schedule (150 / 6000 / 45000+34000·n vs
  500 / 40000 / 100000+80000·n) — that's a known gas-overcharge for
  bn256 CALLs at Istanbul, tracked separately. The address mapping
  itself is correct now.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Byzantium.Vm.PrecompiledContracts
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp
import Evm.Istanbul.Vm.PrecompiledContracts.Blake2f
import Evm.Istanbul.Vm.PrecompiledContracts.Bn256

namespace Evm.Istanbul.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)

/-- Same shape as `Evm.Frontier.Vm.PrecompiledContracts.Precompile`. -/
abbrev Precompile := Evm.Frontier.Vm.PrecompiledContracts.Precompile

/-- Istanbul precompile table. EIP-1108 re-prices the bn256 trio
    (0x06/0x07/0x08), so we override them here rather than inheriting
    Byzantium's entries. MODEXP at 0x05 inherits unchanged. -/
def registry : List (Evm.Address × Precompile) :=
  Evm.Frontier.Vm.PrecompiledContracts.registry ++
    [ (Evm.Address.ofNat 0x05, Evm.Byzantium.Vm.PrecompiledContracts.modexp)
    , (Evm.Address.ofNat 0x06, Evm.Istanbul.Vm.PrecompiledContracts.bn256Add)
    , (Evm.Address.ofNat 0x07, Evm.Istanbul.Vm.PrecompiledContracts.bn256Mul)
    , (Evm.Address.ofNat 0x08, Evm.Istanbul.Vm.PrecompiledContracts.bn256Pairing)
    , (Evm.Address.ofNat 0x09, Evm.Istanbul.Vm.PrecompiledContracts.blake2f)
    ]

/-- Address → handler. -/
def lookup (addr : Evm.Address) : Option Precompile :=
  (registry.find? (fun (a, _) => a = addr)).map Prod.snd

end Evm.Istanbul.Vm.PrecompiledContracts
