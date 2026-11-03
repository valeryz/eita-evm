/-
  Evm.Optimism.Fjord.Spec.P256Verify — RIP-7212 secp256r1 verify
  precompile.

  Source: ethereum/RIPs `RIPS/rip-7212.md`; optimism-specs
  `specs/protocol/fjord/predeploys.md` (P256Verify section).

  RIP-7212 ports the secp256r1 (a.k.a. P-256, NIST P-256) signature
  verification routine into a precompile at address 0x100, for use
  by account-abstraction wallets that store passkey-derived public
  keys. The precompile is OP-stack-specific at Fjord; it lands on
  Ethereum L1 in a later upgrade (currently scheduled for the
  post-Prague timeframe under the "RIP" namespace).

  ABI:
    input  (160 bytes): keccak-message-hash || r || s || qx || qy
                        (32 bytes each)
    output  (32 bytes): 0x...01 if (r,s) verifies under (qx,qy);
                        empty bytes if invalid input or verify fails
    gas:    3450 at Fjord..Isthmus (RIP-7212, op-geth `params.P256VerifyGas`
            pre-Osaka), 6900 from Azul (Base's Osaka analog: EIP-7951,
            EELS `PRECOMPILE_P256VERIFY`). Constant per fork; charged
            before verify, no refund on fail. MEASURED, not recited: the
            canonical callTracer charges 3450 at Base 33554432 tx 203,
            37748736 tx 86 and 45088768 tx 236 (Isthmus), and 6900 at
            Base 0x2c98000 tx 28 (Azul).

  Note the empty-bytes return for failure (not the usual 32-byte 0)
  — match the Ethereum-standard "precompile returns empty on logic-
  level fail, but gas is still consumed".
-/

import Evm.BaseTypes
import Evm.Optimism.Forks
import Evm.Osaka.Vm.PrecompiledContracts

namespace Evm.Optimism.Fjord.Spec

def p256VerifyAddress : Evm.Address := Evm.Address.ofNat 0x0100
def p256VerifyInputLen : Nat := 160

/-- RIP-7212's constant, the deployed op-geth `P256VerifyGas` before Osaka. -/
def rip7212Gas : Nat := 3450

/-- The precompile is available iff `f ≥ Fjord`. Bedrock..Ecotone
    treat 0x100 as a normal (empty, code=0) account; a CALL to it
    succeeds with zero output and no gas consumption beyond the call
    itself. -/
def hasP256Verify (f : Evm.Optimism.OpFork) : Bool := f.atLeast .fjord

theorem p256_iff_fjord (f : Evm.Optimism.OpFork) :
    hasP256Verify f = true ↔ f.atLeast .fjord := by
  unfold hasP256Verify; rfl

/-- P256VERIFY's gas at OP fork `f`: RIP-7212's 3450 until Azul, then
    Osaka's EIP-7951 constant (6900). Regression: the Lisp replay once
    treated 0x100 as an empty account at Fjord..Isthmus, so passkey
    wallets fell back to an in-EVM verifier (MODEXP) and their
    ERC-4337 validation ran out of gas (Base 33554432 tx 203). -/
def p256VerifyGas (f : Evm.Optimism.OpFork) : Nat :=
  if f.atLeast .azul then Evm.Osaka.Vm.PrecompiledContracts.gasP256Verify else rip7212Gas

/-- The env's 0x100 routing at OP fork `f` (`Environment.opP256VerifyGas`). -/
def p256VerifyGasAt (f : Evm.Optimism.OpFork) : Option Nat :=
  if hasP256Verify f then some (p256VerifyGas f) else none

theorem p256VerifyGas_pre_azul : p256VerifyGas .isthmus = 3450 ∧ p256VerifyGas .fjord = 3450 :=
  ⟨rfl, rfl⟩
theorem p256VerifyGas_azul : p256VerifyGas .azul = 6900 := by decide

end Evm.Optimism.Fjord.Spec
