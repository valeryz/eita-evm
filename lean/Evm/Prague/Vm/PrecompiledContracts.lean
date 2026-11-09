/-
  Evm.Prague.Vm.PrecompiledContracts — full Prague precompile registry.

  EELS reference: `ethereum/forks/prague/vm/precompiled_contracts/`.

  Prague's table is Cancun's (`Evm.Frontier.Vm.Call.pragueTable`) plus EIP-2537:

      0x0b  G1_ADD          (`bls12_381_g1.py::bls12_g1_add`; gas 375)
      0x0c  G1_MSM          (`bls12_g1_msm`; k · 12000 · discount(k) / 1000)
      0x0d  G2_ADD          (`bls12_381_g2.py::bls12_g2_add`; gas 600)
      0x0e  G2_MSM          (`bls12_g2_msm`; k · 22500 · discount(k) / 1000)
      0x0f  PAIRING_CHECK   (`bls12_381_pairing.py::bls12_pairing`; 32600·k + 37700)
      0x10  MAP_FP_TO_G1    (`bls12_map_fp_to_g1`; gas 5500)
      0x11  MAP_FP2_TO_G2   (`bls12_map_fp2_to_g2`; gas 23800)

  Each `bls*With o` is EELS's wrapper over a crypto oracle `o : Evm.Crypto.Bls12381.Oracle`
  (lengths, field-element range checks, the curve equation, subgroup checks where EELS
  applies them, gas, output encoding); the registry instantiates `o` with
  `Evm.Crypto.Bls12381.native` (blst). Every failure is an exceptional halt
  (`InvalidParameter` / `OutOfGasError`), consuming the frame's gas. The relations are
  `Evm.Prague.Spec.Bls12381Step`; `Evm.Prague.Spec.Refinement.*_sound` prove these refine
  them for every oracle.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Crypto.Bls12381
import Evm.CL.GasEmit

namespace Evm.Prague.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)
open Evm.Crypto.Bls12381

/-- Same shape as `Frontier.Vm.PrecompiledContracts.Precompile`. -/
abbrev Precompile :=
  Evm.Bytes → Nat → Except Exception (Evm.Bytes × Nat)

/-! ## EIP-2537 gas constants. EELS: `prague/vm/gas.py` `GAS_BLS_*`. -/

/-- EELS `GAS_BLS_G1_ADD`. -/
def gasG1Add        : Nat := 375
/-- EELS `GAS_BLS_G2_ADD`. -/
def gasG2Add        : Nat := 600
/-- EELS `GAS_BLS_PAIRING_PER_PAIR`. -/
def gasPairingPair  : Nat := 32600
/-- EELS `GAS_BLS_PAIRING_BASE`. -/
def gasPairingBase  : Nat := 37700
/-- EELS `GAS_BLS_MAP_FP_TO_G1`. -/
def gasMapFpToG1    : Nat := 5500
/-- EELS `GAS_BLS_MAP_FP2_TO_G2`. -/
def gasMapFp2ToG2   : Nat := 23800

/-! ## EIP-2537 BLS12-381 precompiles -/

/-- 0x0b — BLS12_G1ADD (EELS `bls12_g1_add` 53-66): 256 bytes, two G1 points on the
    curve (no subgroup check), output their sum. -/
def blsG1AddWith (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size ≠ 256 then .error .outOfGas
  else if gas < gasG1Add then .error .outOfGas
  else match g1Decode input 0, g1Decode input 128 with
    | some a, some b => .ok (g1Encode (o.g1Add a b), gas - gasG1Add)
    | _, _ => .error .outOfGas

/-- 0x0c — BLS12_G1MSM (EELS `bls12_g1_msm` 88-115): k ≥ 1 pairs of 160 bytes, the
    discounted gas (the emitted `Evm.CL.GasEmit.blsG1MsmGas`), subgroup-checked points,
    output Σ mᵢ·Pᵢ. -/
def blsG1MsmWith (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size = 0 ∨ input.size % 160 ≠ 0 then .error .outOfGas
  else if gas < Evm.CL.GasEmit.blsG1MsmGas input.size then .error .outOfGas
  else match g1MsmPairs o input (input.size / 160) with
    | some ps => .ok (g1Encode (g1MsmSum o ps), gas - Evm.CL.GasEmit.blsG1MsmGas input.size)
    | none => .error .outOfGas

/-- 0x0d — BLS12_G2ADD (EELS `bls12_381_g2.py::bls12_g2_add` 54-67). -/
def blsG2AddWith (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size ≠ 512 then .error .outOfGas
  else if gas < gasG2Add then .error .outOfGas
  else match g2Decode input 0, g2Decode input 256 with
    | some a, some b => .ok (g2Encode (o.g2Add a b), gas - gasG2Add)
    | _, _ => .error .outOfGas

/-- 0x0e — BLS12_G2MSM (EELS `bls12_381_g2.py::bls12_g2_msm` 89-116). -/
def blsG2MsmWith (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size = 0 ∨ input.size % 288 ≠ 0 then .error .outOfGas
  else if gas < Evm.CL.GasEmit.blsG2MsmGas input.size then .error .outOfGas
  else match g2MsmPairs o input (input.size / 288) with
    | some ps => .ok (g2Encode (g2MsmSum o ps), gas - Evm.CL.GasEmit.blsG2MsmGas input.size)
    | none => .error .outOfGas

/-- 0x0f — BLS12_PAIRING_CHECK (EELS `bls12_381_pairing.py::bls12_pairing` 39-69): k ≥ 1
    pairs of 384 bytes, gas `37700 + 32600·k`, both points subgroup-checked, output 1 iff
    the pairing product is 1. -/
def blsPairingWith (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size = 0 ∨ input.size % 384 ≠ 0 then .error .outOfGas
  else if gas < gasPairingBase + input.size / 384 * gasPairingPair then .error .outOfGas
  else match pairingPairs o input (input.size / 384) with
    | some ps => .ok (pairingOutput (o.pairingCheck ps),
        gas - (gasPairingBase + input.size / 384 * gasPairingPair))
    | none => .error .outOfGas

/-- 0x10 — BLS12_MAP_FP_TO_G1 (EELS `bls12_map_fp_to_g1` 133-146): one field element. -/
def blsMapFpToG1With (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size ≠ 64 then .error .outOfGas
  else if gas < gasMapFpToG1 then .error .outOfGas
  else match fpDecode input 0 with
    | some u => .ok (g1Encode (o.mapFpToG1 u), gas - gasMapFpToG1)
    | none => .error .outOfGas

/-- 0x11 — BLS12_MAP_FP2_TO_G2 (EELS `bls12_381_g2.py::bls12_map_fp2_to_g2` 134-147). -/
def blsMapFp2ToG2With (o : Oracle) (input : Evm.Bytes) (gas : Nat) :
    Except Exception (Evm.Bytes × Nat) :=
  if input.size ≠ 128 then .error .outOfGas
  else if gas < gasMapFp2ToG2 then .error .outOfGas
  else match fp2Decode input 0 with
    | some u => .ok (g2Encode (o.mapFp2ToG2 u), gas - gasMapFp2ToG2)
    | none => .error .outOfGas

/-- EIP-2537's entries, over blst (`Evm.Crypto.Bls12381.native`). 0x01..0x0a are
    Cancun's, served first by `Evm.Frontier.Vm.Call.pragueTable`. -/
def registry : List (Evm.Address × Precompile) :=
  [ (Evm.Address.ofNat 0x0b, blsG1AddWith native)
  , (Evm.Address.ofNat 0x0c, blsG1MsmWith native)
  , (Evm.Address.ofNat 0x0d, blsG2AddWith native)
  , (Evm.Address.ofNat 0x0e, blsG2MsmWith native)
  , (Evm.Address.ofNat 0x0f, blsPairingWith native)
  , (Evm.Address.ofNat 0x10, blsMapFpToG1With native)
  , (Evm.Address.ofNat 0x11, blsMapFp2ToG2With native)
  ]

/-- Look up a precompile by address. -/
def lookup (a : Evm.Address) : Option Precompile :=
  (registry.find? (fun (k, _) => k = a)).map Prod.snd

end Evm.Prague.Vm.PrecompiledContracts
