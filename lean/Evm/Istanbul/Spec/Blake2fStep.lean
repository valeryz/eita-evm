/-
  Evm.Istanbul.Spec.Blake2fStep — EIP-152 BLAKE2F precompile (0x09).

  EELS reference: `forks/istanbul/vm/precompiled_contracts/blake2f.py`
  function `blake2f` (21-42), over `ethereum/crypto/blake2.py`
  (`get_blake2_parameters` 133-150, `compress` 194-247).

  ## Input layout (EIP-152, 213 bytes)
      [  0:  4) rounds : uint32 big-endian
      [  4: 68) h      : 8 × uint64 little-endian
      [ 68:196) m      : 16 × uint64 little-endian
      [196:212) t      : 2 × uint64 little-endian
      [212:213) f      : uint8

  ## Output
  64 bytes: the post-compression state `h`, RFC 7693 §3.2's F
  (`Evm.Crypto.Blake2f.compress`, pure Lean — no oracle).

  ## Gas
  `rounds * PRECOMPILE_BLAKE2F_PER_ROUND` = `rounds * 1` (EELS 38).

  ## Failures (each an exceptional halt, consuming the frame's gas)
    * `len(data) != 213` (32-33)
    * `gas < rounds * 1` (38, `charge_gas`)
    * `f ∉ {0, 1}`       (39-40)
-/

import Evm.BaseTypes
import Evm.Istanbul.Vm.Gas
import Evm.Crypto.Blake2f

namespace Evm.Istanbul.Spec

/-- EELS 38: the gas charged for `input`. -/
def blake2fCost (input : Evm.Bytes) : Nat :=
  Evm.Istanbul.Vm.Gas.blake2fPerRound * Evm.Crypto.Blake2f.rounds input

/-- 0x09 BLAKE2F success (EELS `blake2f` 31-42): the input is 213 bytes, `f` is 0 or 1,
    the rounds' gas is there, the output is F over the decoded parameters. -/
def IsBlake2fStep
    (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gasLeft : Nat) : Prop :=
  input.size = 213 ∧
  (Evm.Crypto.Blake2f.flag input = 0 ∨ Evm.Crypto.Blake2f.flag input = 1) ∧
  gas ≥ blake2fCost input ∧
  output = Evm.Crypto.Blake2f.ofInput input ∧
  gasLeft = gas - blake2fCost input

/-- 0x09 BLAKE2F failure: a wrong length, too little gas, or a bad flag. -/
def IsBlake2fFailure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ 213 ∨ gas < blake2fCost input ∨
  (Evm.Crypto.Blake2f.flag input ≠ 0 ∧ Evm.Crypto.Blake2f.flag input ≠ 1)

end Evm.Istanbul.Spec
