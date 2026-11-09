/-
  Evm.Istanbul.Vm.PrecompiledContracts.Blake2f — 0x09 BLAKE2F
  compression function precompile (EIP-152).

  EELS reference: `forks/istanbul/vm/precompiled_contracts/blake2f.py`
  function `blake2f` (21-42).

  ## Input layout (EIP-152, 213 bytes)
      [  0:  4) rounds : uint32 big-endian
      [  4: 68) h      : 8 × uint64 little-endian
      [ 68:196) m      : 16 × uint64 little-endian
      [196:212) t      : 2 × uint64 little-endian
      [212:213) f      : uint8 (0 or 1)

  ## Gas
  `rounds * PRECOMPILE_BLAKE2F_PER_ROUND` (= rounds * 1, `forks/istanbul/vm/gas.py`).

  ## Failures (EELS 32-40), each an exceptional halt
    * `len(data) != 213` → `InvalidParameter`
    * insufficient gas   → `OutOfGasError` (via `charge_gas`)
    * `f ∉ {0, 1}`       → `InvalidParameter`

  ## Output
  64 bytes: `Evm.Crypto.Blake2f.ofInput`, RFC 7693's F in pure Lean.
  The relation is `Evm.Istanbul.Spec.IsBlake2fStep`; `blake2f_sound` proves this refines it.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Istanbul.Vm.Gas
import Evm.Crypto.Blake2f

namespace Evm.Istanbul.Vm.PrecompiledContracts

open Evm.Frontier.Vm

/-- 0x09 BLAKE2F. Mirrors EELS `blake2f`. -/
def blake2f (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  -- EELS 32-33: length must be exactly 213 bytes.
  if input.size ≠ 213 then .error .outOfGas
  else
    -- EELS 38: charge `PRECOMPILE_BLAKE2F_PER_ROUND * rounds`.
    let cost := Evm.Istanbul.Vm.Gas.blake2fPerRound * Evm.Crypto.Blake2f.rounds input
    if gas < cost then .error .outOfGas
    -- EELS 39-40: `f` must be 0 or 1.
    else if Evm.Crypto.Blake2f.flag input ≠ 0 ∧ Evm.Crypto.Blake2f.flag input ≠ 1 then
      .error .outOfGas
    -- EELS 42: `blake2b.compress(rounds, h, m, t_0, t_1, f)`.
    else .ok (Evm.Crypto.Blake2f.ofInput input, gas - cost)

end Evm.Istanbul.Vm.PrecompiledContracts
