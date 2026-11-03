/-
  Evm.Istanbul.Vm.PrecompiledContracts.Blake2f — 0x09 BLAKE2F
  compression function precompile (EIP-152).

  EELS reference: `forks/istanbul/vm/precompiled_contracts/blake2f.py`
  function `blake2f` (line 21).

  ## Input layout (EIP-152, 213 bytes, big-endian fields)
      [  0:  4) rounds : uint32       — number of compression rounds
      [  4: 68) h      : 8 × uint64   — state vector
      [ 68:196) m      : 16 × uint64  — message block
      [196:212) t      : 2 × uint64   — offset counter
      [212:213) f      : uint8        — final-block flag (0 or 1)

  ## Gas
  `rounds * G_BLAKE2_PER_ROUND` (= rounds * 1) — `GasCosts.PRECOMPILE_
  BLAKE2F_PER_ROUND` from `forks/istanbul/vm/gas.py` line 71.

  ## Failures (EELS lines 32-40)
    * `len(data) != 213` → `InvalidParameter`
    * insufficient gas → `OutOfGasError` (via `charge_gas`)
    * `f ∉ {0, 1}` → `InvalidParameter`

  ## Output
  64 bytes: the post-compression state `h`.

  ## What this module actually does today
  Validates input shape + `f` flag, charges gas, returns 64 bytes of
  zero. The Blake2b compression itself is NOT implemented yet — this
  is a behavioural stub on par with Frontier's `sha256`/`ecrecover`
  prior to their C bindings landing. Any test that exercises the
  precompile semantically (i.e. expects the canonical Blake2b output)
  will fail; tests that only exercise the gas / error path pass.

  TODO: bind to a `c/blake2b.c` implementation the way `c/keccak.c`
  was bound (`Crypto/Hash.lean`). Until then the precompile is at
  least correctly gas-priced and correctly errors on malformed input.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Istanbul.Vm.Gas

namespace Evm.Istanbul.Vm.PrecompiledContracts

open Evm.Frontier.Vm

/-- Decode a 4-byte big-endian unsigned int from `input` at offset 0. -/
private def beU32 (input : Evm.Bytes) : Nat :=
  let b0 := input.get! 0
  let b1 := input.get! 1
  let b2 := input.get! 2
  let b3 := input.get! 3
  (b0.toNat <<< 24) ||| (b1.toNat <<< 16) ||| (b2.toNat <<< 8) ||| b3.toNat

/-- 0x09 BLAKE2F. Mirrors EELS `blake2f`. -/
def blake2f (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  -- EELS line 32-33: length must be exactly 213 bytes.
  if input.size ≠ 213 then .error .outOfGas
  else
    let rounds := beU32 input
    -- EELS line 38: charge `PRECOMPILE_BLAKE2F_PER_ROUND * rounds`.
    let cost := Evm.Istanbul.Vm.Gas.blake2fPerRound * rounds
    if gas < cost then .error .outOfGas
    else
      -- EELS line 39-40: `f` (last byte) must be 0 or 1.
      let f := input.get! 212
      if f.toNat ≠ 0 ∧ f.toNat ≠ 1 then .error .outOfGas
      else
        -- Stub output: 64 bytes of zero. Real Blake2b compression
        -- pending C binding. See module docstring.
        let zeroOutput : Evm.Bytes :=
          ByteArray.mk (Array.replicate 64 (0 : UInt8))
        .ok (zeroOutput, gas - cost)

end Evm.Istanbul.Vm.PrecompiledContracts
