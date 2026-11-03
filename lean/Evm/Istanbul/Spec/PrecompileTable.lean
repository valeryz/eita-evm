/-
  Evm.Istanbul.Spec.PrecompileTable — Istanbul precompile-set delta.

  EELS reference: `forks/istanbul/vm/precompiled_contracts/__init__.py`
  `PRE_COMPILED_CONTRACTS` mapping.

  Istanbul appends `0x09 BLAKE2F` (EIP-152) to Byzantium's eight
  precompiles. All previously-present addresses remain.

  ## The shipped-buggy registry pattern

  Until 2026-05-30 our `Evm.Istanbul.Vm.PrecompiledContracts.registry`
  was defined as
      `Evm.Frontier.Vm.PrecompiledContracts.registry ++ [(0x09, blake2f)]`
  — accidentally dropping Byzantium's 0x05..0x08. Implementations
  that consult `Istanbul.lookup` (e.g. Berlin / London / Paris /
  Shanghai now do) silently lost MODEXP and bn256 at those forks.

  The spec invariant below catches this kind of regression: the
  Istanbul table MUST contain everything Byzantium had, plus 0x09.
  An implementation that fails to inherit Byzantium's rows violates
  the invariant.
-/

import Evm.BaseTypes
import Evm.Byzantium.Spec.PrecompileTable
import Evm.Istanbul.Vm.PrecompiledContracts

namespace Evm.Istanbul.Spec

/-- Istanbul precompile set: Byzantium's eight plus BLAKE2F. -/
def precompileAddresses : List Evm.Address :=
  Evm.Byzantium.Spec.precompileAddresses ++ [Evm.Address.ofNat 0x09]

def IsPrecompile (addr : Evm.Address) : Prop :=
  addr ∈ precompileAddresses

/-- Istanbul's table strictly extends Byzantium's. An implementation
    that ships a registry missing Byzantium's rows is unsound. -/
theorem extends_byzantium :
    ∀ addr, Evm.Byzantium.Spec.IsPrecompile addr → IsPrecompile addr := by
  intro addr h
  exact List.mem_append_left _ h

/-- **The executable registry is the spec table**, address for address and in
    order. `extends_byzantium` alone is about the spec list, which is
    Byzantium's by construction; this is the statement that catches the
    shipped regression above — a `registry` built on Frontier's four rows only
    has five addresses and fails here. -/
theorem registry_is_spec_table :
    Evm.Istanbul.Vm.PrecompiledContracts.registry.map Prod.fst = precompileAddresses := by
  rfl

end Evm.Istanbul.Spec
