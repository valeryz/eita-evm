/-
  Evm.Osaka.Vm.PrecompiledContracts — Osaka delta on Prague's
  precompile registry.

  EELS reference: `forks/osaka/vm/precompiled_contracts/`.

  Three changes from Prague:

    * EIP-7951 (`p256verify.py`): adds a new precompile at address
      `0x100` that verifies a SECP256R1 signature. Input is 160 bytes
      `(msg_hash, r, s, qx, qy)`; output is 32 bytes (left-padded
      `0x01` on success, empty on failure). Gas: 6900 (flat).
      EELS: `forks/osaka/vm/precompiled_contracts/p256verify.py`;
      address constant `P256VERIFY_ADDRESS = hex_to_address("0x100")`
      in `forks/osaka/vm/precompiled_contracts/__init__.py`.

    * EIP-7823 (`modexp.py` lines 32-41): rejects MODEXP inputs whose
      base, exponent, or modulus length exceeds 1024 bytes with an
      `ExceptionalHalt`. Encoded here as the precompile returning
      `.error .outOfGas` for those inputs (which has the same effect
      at the EVM call boundary — the call returns failure).

    * EIP-7883 (`modexp.py` lines 95-175): MODEXP gas formula changes
      (`max(500, cost)` floor instead of `max(200, cost) / 3`,
      `complexity = 16` for `max_length ≤ 32` else `2 * words²`, etc.).
      Since the Prague spec doesn't yet implement MODEXP itself (it's
      currently stubbed out of the precompile registry — see
      `Prague/Vm/PrecompiledContracts.lean` line 187 "TODO"), Osaka
      inherits the same stub status; the Osaka-distinctive formulas
      are documented here so that when MODEXP is implemented for
      Prague, the Osaka delta is a single-file edit. -/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Prague.Vm.PrecompiledContracts
import Evm.Berlin.Vm.PrecompiledContracts.Modexp
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp

namespace Evm.Osaka.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)

abbrev Precompile := Evm.Prague.Vm.PrecompiledContracts.Precompile

/-! ## EIP-7951 P256VERIFY -/

/-- Address of the P256VERIFY precompile. EELS:
    `forks/osaka/vm/precompiled_contracts/__init__.py` line 56. -/
def p256verifyAddress : Evm.Address := Evm.Address.ofNat 0x100

/-- Gas cost of the P256VERIFY precompile. EELS:
    `forks/osaka/vm/gas.py::PRECOMPILE_P256VERIFY = Uint(6900)`. -/
def gasP256Verify : Nat := 6900

/-- EIP-7951 P256VERIFY precompile.

    EELS `forks/osaka/vm/precompiled_contracts/p256verify.py`
    `p256verify(evm)`:

      data := evm.message.data
      charge_gas(evm, PRECOMPILE_P256VERIFY)
      if len(data) != 160: return                  -- empty output
      (msg_hash, r, s, qx, qy) := slice(data, ...)
      if r out-of-range, s out-of-range,
         qx ≥ p, qy ≥ p, (qx, qy) = (0, 0),
         not on curve, or signature invalid: return
      evm.output := left_pad_zero_bytes(b"\\x01", 32)

    For the spec layer we faithfully reproduce the gas charge and the
    output shape; the cryptographic SECP256R1 verification is stubbed
    (returns the failure case = empty output) because Lean has no
    SECP256R1 FFI yet. EVM observers see the right gas cost; tx-side
    correctness on the success path requires a real impl. Marked
    TODO with the EELS function name so the substitution is one
    edit. -/
def p256verify (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) := do
  if gas < gasP256Verify then .error .outOfGas
  let gas' := gas - gasP256Verify
  -- Per EELS: malformed input length returns gas-consumed + empty output.
  if input.size ≠ 160 then
    return (Evm.Bytes.empty, gas')
  -- KNOWN GAP (stated as `p256verify_stub_rejects` below): no SECP256R1
  -- verification in Lean yet — every signature is rejected (empty output).
  -- EELS reference: `ethereum.crypto.elliptic_curve.secp256r1_verify`. The
  -- host (Lisp/C) implements the real check; this Lean table entry does not.
  return (Evm.Bytes.empty, gas')

/-- The visible form of the P256VERIFY gap: the Lean precompile never verifies — every
    successful run returns empty output, valid signature or not (EELS returns
    `left_pad_zero_bytes(b"\x01", 32)` for a valid one). So
    `Evm.Osaka.Spec.Refinement.p256Verify_sound_shape` stays open: proving the spec
    against this stub would certify the stub. -/
theorem p256verify_stub_rejects (input : Evm.Bytes) (gas : Nat) (out : Evm.Bytes × Nat) :
    p256verify input gas = .ok out → out.1 = Evm.Bytes.empty := by
  unfold p256verify
  by_cases hg : gas < gasP256Verify
  · simp [hg, bind, Except.bind]
  · by_cases hs : input.size ≠ 160
    · simp [hg, hs, bind, Except.bind, pure, Except.pure]
      intro h; rw [← h]
    · simp [hg, hs, bind, Except.bind, pure, Except.pure]
      intro h; rw [← h]

/-! ## EIP-7883 / EIP-7823 MODEXP (documented; not yet wired)

    EELS `forks/osaka/vm/precompiled_contracts/modexp.py`:

      MAX_OPERAND_LEN = 1024                                  -- EIP-7823
      if base_length > 1024 or exp_length > 1024
         or modulus_length > 1024: raise ExceptionalHalt
      ...
      complexity = 16
      if max_length > 32:
          complexity = 2 * words ** 2                         -- EIP-7883
      ...
      length_part = 16 * (exp_length - 32)                    -- EIP-7883
      ...
      return max(500, cost)                                   -- EIP-7883

    The pre-Osaka formula divided the cost by `GQUADDIVISOR = 3` and
    floored at 200; Osaka multiplies (effectively raising gas ~3x) and
    floors at 500. -/

def maxModexpOperandLen : Nat := 1024
def osakaModexpFloor    : Nat := 500
def osakaExpLengthMul   : Nat := 16
def osakaQuadBase       : Nat := 16

/-! ### EIP-7883 implementation

    Spec deltas from Berlin's EIP-2565 (`Evm.Berlin.Vm.PrecompiledContracts.modexp`):

      * `multComplexity x ≤ 32` returns 16 (Berlin computes
        `ceil(32/8)^2 = 16` too); `x > 32` returns
        `2 * berlinComplexity(x)` — i.e. doubled.
      * `iterationCount` extension term for `expLen > 32` uses
        multiplier 16 (Berlin: 8).
      * Cost is `mult * iter` directly — Berlin divides by 3.
      * Minimum gas is 500 (Berlin: 200).

    The exec body (the actual `B^E mod M` computation) is the
    same as Byzantium / Berlin — reused via the Byzantium helpers
    `readBytesAsNat` / `powMod` / `natToBytesBE`. Only the gas
    formula and the input-length cap (EIP-7823) differ. -/

private partial def bitLengthOsaka : Nat → Nat
  | 0 => 0
  | n => 1 + bitLengthOsaka (n / 2)

def multComplexity7883 (baseLen modLen : Nat) : Nat :=
  let x := max baseLen modLen
  if x ≤ 32 then osakaQuadBase
  else 2 * Evm.Berlin.Vm.PrecompiledContracts.multComplexity2565 baseLen modLen

def adjustedExpLength7883 (input : Evm.Bytes) (eOff eLen : Nat) : Nat :=
  if eLen ≤ 32 then
    let e := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input eOff eLen
    if e = 0 then 0 else bitLengthOsaka e - 1
  else
    let head := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input eOff 32
    let bl := if head = 0 then 0 else bitLengthOsaka head - 1
    osakaExpLengthMul * (eLen - 32) + bl

/-- 0x05 MODEXP — EIP-7883 (Osaka) gas. The exec body is the same
    as Berlin's `modexp`; only the gas formula differs. EIP-7823's
    input-length cap (≤ 1024 bytes per operand) is also enforced
    here, returning OOG on overflow. -/
def modexp7883 : Precompile := fun input gasLeft => do
  let baseLen := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 0 32
  let expLen  := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 32 32
  let modLen  := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 64 32
  -- EIP-7823: reject any operand longer than 1024 bytes.
  if baseLen > maxModexpOperandLen ∨ expLen > maxModexpOperandLen
     ∨ modLen > maxModexpOperandLen then
    .error Exception.outOfGas
  else
    let expOff := 96 + baseLen
    let adj    := adjustedExpLength7883 input expOff expLen
    let iter   := max 1 adj
    let mult   := multComplexity7883 baseLen modLen
    let cost   := max osakaModexpFloor (mult * iter)
    if gasLeft < cost then
      .error Exception.outOfGas
    else
      let base   := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input 96 baseLen
      let exp_   := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input expOff expLen
      let modN   := Evm.Byzantium.Vm.PrecompiledContracts.readBytesAsNat input (expOff + expLen) modLen
      let result := if modN = 0 then 0
                    else Evm.Byzantium.Vm.PrecompiledContracts.powMod base exp_ modN
      let output := Evm.Byzantium.Vm.PrecompiledContracts.natToBytesBE result modLen
      .ok (output, gasLeft - cost)

/-! ## Registry

    Inherits Prague's registry verbatim and appends the P256VERIFY
    entry at address 0x100. -/

/-- Prague's existing entries plus 0x100 → P256VERIFY. EELS:
    `forks/osaka/vm/precompiled_contracts/mapping.py` line 77 adds
    `P256VERIFY_ADDRESS: p256verify` to the previous-fork mapping. -/
def registry : List (Evm.Address × Precompile) :=
  Evm.Prague.Vm.PrecompiledContracts.registry ++
    [ (p256verifyAddress, p256verify) ]

def lookup (a : Evm.Address) : Option Precompile :=
  (registry.find? (fun (k, _) => k = a)).map Prod.snd

end Evm.Osaka.Vm.PrecompiledContracts
