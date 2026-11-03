/-
  Evm.Istanbul.Spec.Blake2fStep — EIP-152 BLAKE2F precompile (0x09).

  EELS reference: `forks/istanbul/vm/precompiled_contracts/blake2f.py`
  function `blake2f` (line 21). Matching implementation in this
  repo: `Evm.Istanbul.Vm.PrecompiledContracts.Blake2f`.

  ## Input layout (EIP-152, 213 bytes, big-endian fields)
      [  0:  4) rounds : uint32       — number of compression rounds
      [  4: 68) h      : 8 × uint64   — state vector
      [ 68:196) m      : 16 × uint64  — message block
      [196:212) t      : 2 × uint64   — offset counter
      [212:213) f      : uint8        — final-block flag (0 or 1)

  ## Output
  64 bytes: the post-compression state `h`.

  ## Gas
  `rounds * GAS_BLAKE2_PER_ROUND` = `rounds * 1`. EELS
  `GasCosts.PRECOMPILE_BLAKE2F_PER_ROUND` (gas.py line 71).

  ## Failures (lifted out of the relation)
    * `len(data) != 213`               → InvalidParameter
    * `gas < rounds * 1`               → OutOfGasError
    * `f ∉ {0, 1}`                     → InvalidParameter

  The relation below describes ONLY the success path: it takes the
  input bytes, the available gas, and predicates over the output
  bytes and the gas-left-after. Failure paths are not part of the
  relation (matching how other precompile specs are stated).

  ## Open obligation
  The Blake2b compression itself is not yet bound in this repo (the
  implementation stub returns 64 bytes of zeros and only the gas /
  error path is testable). The relation here uses a *symbolic* hook
  `blake2bCompress` (declared opaque) so the spec captures the
  output's structural dependencies without committing to a concrete
  function. When the C binding lands, `blake2bCompress` gets a
  definition; refinement at that point should be trivial. -/

import Evm.BaseTypes
import Evm.Istanbul.Vm.Gas

namespace Evm.Istanbul.Spec

/-- Symbolic Blake2b compression function over a 213-byte input.
    Returns the canonical 64-byte output. The actual algorithm will
    be supplied via a C FFI binding analogous to `keccak256Bytes`;
    until then the spec treats it as a black box.

    EELS reference: the function `spec_blake2_compress_f` invoked
    inside `blake2f` in `forks/istanbul/vm/precompiled_contracts/
    blake2f.py`. -/
opaque blake2bCompress (input : Evm.Bytes) : Evm.Bytes

/-- Decode a 4-byte big-endian uint32 starting at offset 0 of `b`.
    EELS uses `int.from_bytes(data[:4], "big")`. -/
private def beU32 (b : Evm.Bytes) : Nat :=
  let b0 := b.get! 0
  let b1 := b.get! 1
  let b2 := b.get! 2
  let b3 := b.get! 3
  (b0.toNat <<< 24) ||| (b1.toNat <<< 16) ||| (b2.toNat <<< 8) ||| b3.toNat

/-- 0x09 BLAKE2F (Istanbul precompile, EIP-152).

    `IsBlake2fStep input gas output gasLeft` holds iff:
      * the input is exactly 213 bytes
      * the final byte `f` is 0 or 1
      * `gas ≥ rounds * 1` (where `rounds` is the first 4 bytes
        of the input, big-endian)
      * `output = blake2bCompress input`
      * `gasLeft = gas - rounds * 1`
    -/
def IsBlake2fStep
    (input : Evm.Bytes) (gas : Nat)
    (output : Evm.Bytes) (gasLeft : Nat) : Prop :=
  input.size = 213 ∧
  ((input.get! 212).toNat = 0 ∨ (input.get! 212).toNat = 1) ∧
  let rounds := beU32 input
  let cost   := rounds * Evm.Istanbul.Vm.Gas.blake2fPerRound
  gas ≥ cost ∧
  output = blake2bCompress input ∧
  gasLeft = gas - cost

end Evm.Istanbul.Spec
