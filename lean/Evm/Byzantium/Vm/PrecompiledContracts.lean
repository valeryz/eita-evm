/-
  Evm.Byzantium.Vm.PrecompiledContracts — registry of Byzantium
  precompiles.

  EELS reference: `forks/byzantium/vm/precompiled_contracts/
  __init__.py`. Extends Frontier's 0x01..0x04 with:

    0x05 MODEXP        — modular exponentiation (EIP-198)
    0x06 BN256ADD      — alt_bn128 G1 point addition (EIP-196)
    0x07 BN256MUL      — alt_bn128 G1 scalar multiplication (EIP-196)
    0x08 BN256PAIRING  — alt_bn128 pairing check (EIP-197)

  Implementation status (see the per-file headers):
    * Modexp.lean  — real pure-Lean impl, EIP-198 gas formula.
    * Bn256.lean   — gas + input-length checks correct; curve math
                     stubbed (returns identity / false). Real BN254
                     math via FFI to c/bn254_shim.cpp is a TODO.

  Each precompile follows the `Precompile` signature
  `Bytes → Nat → Except Exception (Bytes × Nat)` introduced in
  Frontier's PrecompiledContracts module.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp
import Evm.Byzantium.Vm.PrecompiledContracts.Bn256

namespace Evm.Byzantium.Vm.PrecompiledContracts

open Evm.Frontier.Vm.PrecompiledContracts (registry) in
/-- Byzantium precompile registry: Frontier's four plus four new ones.

    Lookups go through `lookup` below, which checks this table.
    Note: `Evm.Byzantium.Vm.Effect`'s trampoline currently calls
    `Evm.Frontier.Vm.PrecompiledContracts.lookup` (Frontier registry),
    so the Byzantium-only precompiles don't fire even when this file
    is imported. Fixing that dispatch is task #122.B (out of scope
    here; that one-line change happens in the slim-Effect refactor). -/
def registry : List (Evm.Address × Evm.Frontier.Vm.PrecompiledContracts.Precompile) :=
  Evm.Frontier.Vm.PrecompiledContracts.registry ++
  [ (Evm.Address.ofNat 0x05, modexp)
  , (Evm.Address.ofNat 0x06, bn256Add)
  , (Evm.Address.ofNat 0x07, bn256Mul)
  , (Evm.Address.ofNat 0x08, bn256Pairing)
  ]

/-- Look up the precompile at `addr` in the Byzantium registry. -/
def lookup (addr : Evm.Address) :
    Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  (registry.find? (fun (a, _) => a = addr)).map Prod.snd

end Evm.Byzantium.Vm.PrecompiledContracts
