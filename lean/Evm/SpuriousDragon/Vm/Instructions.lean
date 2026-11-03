/-
  Evm.SpuriousDragon.Vm.Instructions — non-recursive EIP-160 delta.

  Only EXP changes (per-byte cost 10 → 50). All other non-recursive
  opcode handlers are inherited from TW (BALANCE/SLOAD/EXTCODE*) or
  Frontier (everything else).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.SpuriousDragon.Vm.Gas

namespace Evm.SpuriousDragon.Vm.Instructions

open Evm.Frontier.Vm

private partial def powMod (base e modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else
    let rec go (b e acc : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => acc
      | fuel+1 =>
        if e = 0 then acc
        else
          let acc' := if e % 2 = 1 then (acc * b) % modulus else acc
          go ((b * b) % modulus) (e / 2) acc' fuel
    go (base % modulus) e (1 % modulus) 257

private def expByteSize (e : Nat) : Nat :=
  if e = 0 then 0 else Nat.log2 e / 8 + 1

/-- 0x0a EXP — per-byte cost 50 (was 10 at Frontier). Base 10 stays. -/
def exp : Evm.Frontier.Vm.Instructions.Handler := fun evm => do
  let (base, e, s) ← Stack.pop2 evm.stack
  let cost := Gas.exp + Evm.SpuriousDragon.Vm.Gas.expByte * expByteSize e.toNat
  let gasLeft ← Gas.charge evm.gasLeft cost
  let result := Evm.U256.ofNat (powMod base.toNat e.toNat (1 <<< 256))
  let s ← Stack.push s result
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.SpuriousDragon.Vm.Instructions
