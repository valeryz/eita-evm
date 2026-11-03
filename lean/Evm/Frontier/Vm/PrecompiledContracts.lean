/-
  Evm.Frontier.Vm.PrecompiledContracts — registry of Frontier precompiles.

  EELS reference:
  ethereum/frontier/vm/precompiled_contracts/__init__.py.

  Frontier ships with four precompiles, at fixed addresses 0x01..0x04:
    0x01 ECRECOVER       — secp256k1 signature recovery (stub)
    0x02 SHA256           — SHA-256 hash (stub)
    0x03 RIPEMD160       — RIPEMD-160 hash, left-zero-padded (stub)
    0x04 IDENTITY        — datacopy (real)

  Byzantium adds MODEXP / BN256ADD / BN256MUL / BN256PAIRING; Istanbul
  adds BLAKE2F; Cancun adds POINT_EVALUATION; Prague adds BLS-12-381
  precompiles.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts.EcRecover
import Evm.Frontier.Vm.PrecompiledContracts.Sha256
import Evm.Frontier.Vm.PrecompiledContracts.Ripemd160
import Evm.Frontier.Vm.PrecompiledContracts.Identity

namespace Evm.Frontier.Vm.PrecompiledContracts

/-- A precompile is a pure function from input bytes and an available gas
    budget to either (output, gasLeftAfter) or an exception. -/
abbrev Precompile :=
  Evm.Bytes → Nat → Except Evm.Frontier.Vm.Exception (Evm.Bytes × Nat)

/-- Address → handler table, in fork-order. -/
def registry : List (Evm.Address × Precompile) :=
  [ (Evm.Address.ofNat 0x01, ecrecover)
  , (Evm.Address.ofNat 0x02, sha256)
  , (Evm.Address.ofNat 0x03, ripemd160)
  , (Evm.Address.ofNat 0x04, identity)
  ]

/-- Look up the precompile at `addr`, if any. -/
def lookup (addr : Evm.Address) : Option Precompile :=
  (registry.find? (fun (a, _) => a = addr)).map Prod.snd

end Evm.Frontier.Vm.PrecompiledContracts
