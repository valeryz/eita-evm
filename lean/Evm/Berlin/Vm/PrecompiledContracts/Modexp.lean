/-
  Evm.Berlin.Vm.PrecompiledContracts.Modexp — EIP-2565 modexp
  reprice.

  EELS reference: `forks/berlin/vm/precompiled_contracts/modexp.py`.

  Berlin keeps the same modexp operation as Byzantium (same input
  layout, same output) but re-prices via EIP-2565. The change is
  ~10-100× cheaper for typical RSA-sized inputs, because the old
  Byzantium piecewise formula (`x^2`, `x^2/4 + 96x - 3072`,
  `x^2/16 + 480x - 199680`) is replaced with a single
  `ceil(max(Blen, Mlen) / 8)^2`, and the divisor moves from 20 to 3.

  Formula:
      multiplication_complexity = ceil(max(Blen, Mlen) / 8)^2
      iteration_count            = max(1, adjusted_exp_length)
      gas = max(200, multiplication_complexity * iteration_count / 3)

  `adjusted_exp_length` is unchanged from EIP-198 Byzantium.

  The MOD-EXP COMPUTATION (the actual `B^E mod M`) is identical to
  Byzantium's — we re-export it. Only the gas formula differs.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp

namespace Evm.Berlin.Vm.PrecompiledContracts

open Evm.Frontier.Vm.PrecompiledContracts (Precompile)
open Evm.Frontier.Vm (Exception)
open Evm.Byzantium.Vm.PrecompiledContracts (adjustedExpLength)

/-- EIP-2565 multiplication complexity: `ceil(max(B, M) / 8)^2`. -/
def multComplexity2565 (baseLen modLen : Nat) : Nat :=
  let words := (max baseLen modLen + 7) / 8
  words * words

/-- EIP-2565 floor / divisor. -/
def gasFloor2565    : Nat := 200
def gasDivisor2565  : Nat := 3

/-- 0x05 MODEXP — Berlin (EIP-2565) gas. The exec body is identical
    to Byzantium; only the gas charge changes. -/
def modexp : Precompile := fun input gasLeft => do
  let baseLen := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 0 32
  let expLen  := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 32 32
  let modLen  := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 64 32
  let expOff   := 96 + baseLen
  let adj      := adjustedExpLength input expOff expLen
  let iter     := max 1 adj
  let mult     := multComplexity2565 baseLen modLen
  let cost     := max gasFloor2565 (mult * iter / gasDivisor2565)
  if gasLeft < cost then
    .error Exception.outOfGas
  else
    -- Re-use Byzantium's modexp body for the actual computation.
    -- It re-charges its own gas (Byzantium formula) — which would
    -- be wrong here — so we DON'T call it directly. Instead we
    -- inline the body. Eventually we should refactor the Byzantium
    -- body into an exec-only helper; for now, duplicate.
    let base    := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 96 baseLen
    let exp_    := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input expOff expLen
    let modN    := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input (expOff + expLen) modLen
    let result  := if modN = 0 then 0
                   else Evm.Byzantium.Vm.PrecompiledContracts.powMod base exp_ modN
    let output  := Evm.Byzantium.Vm.PrecompiledContracts.natToBytesBE result modLen
    .ok (output, gasLeft - cost)

end Evm.Berlin.Vm.PrecompiledContracts
