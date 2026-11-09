/-
  Evm.Osaka.Vm.PrecompiledContracts — Osaka delta on Prague's
  precompile registry.

  EELS reference: `forks/osaka/vm/precompiled_contracts/`.

  Three changes from Prague:

    * EIP-7951 (`p256verify.py`): adds a new precompile at address
      `0x100` that verifies a SECP256R1 signature. Input is 160 bytes
      `(msg_hash, r, s, qx, qy)`; output is 32 bytes (left-padded
      `0x01` on success, empty on failure). Gas: 6900 (flat). The table entry
      is `Evm.Frontier.Vm.Call.osakaTable`.
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
      Implemented below as `modexp7883`. -/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Crypto.P256Verify
import Evm.Berlin.Vm.PrecompiledContracts.Modexp
import Evm.Byzantium.Vm.PrecompiledContracts.Modexp

namespace Evm.Osaka.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)

abbrev Precompile :=
  Evm.Bytes → Nat → Except Exception (Evm.Bytes × Nat)

/-! ## EIP-7951 P256VERIFY -/

/-- Address of the P256VERIFY precompile. EELS:
    `forks/osaka/vm/precompiled_contracts/__init__.py` line 56. -/
def p256verifyAddress : Evm.Address := Evm.Address.ofNat 0x100

/-- Gas cost of the P256VERIFY precompile. EELS:
    `forks/osaka/vm/gas.py::PRECOMPILE_P256VERIFY = Uint(6900)`. -/
def gasP256Verify : Nat := 6900

/-- EIP-7951 P256VERIFY precompile: EELS `forks/osaka/vm/precompiled_contracts/
    p256verify.py::p256verify` 31-90, the one wrapper `Evm.Crypto.p256VerifyWithOracle`
    (shared with OP's RIP-7212) over OpenSSL's verifier, at 6900 gas. The relation is
    `Evm.Osaka.Spec.IsP256VerifyStep`. -/
def p256verify : Precompile := Evm.Crypto.p256VerifyWith gasP256Verify

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

end Evm.Osaka.Vm.PrecompiledContracts
