/-
  Evm.Frontier.Vm.Instructions.Keccak — opcode 0x20 SHA3 (Keccak-256).

  EELS reference: ethereum/frontier/vm/instructions/keccak.py.

  Gas: `30 + 6 · ⌈len/32⌉` plus the standard memory-expansion cost.
  Hashes are produced by `Evm.Crypto.keccak256`, which is currently a
  zero stub — anything that depends on the hash being correct is
  unverified until that is implemented for real.
-/

import Evm.BaseTypes
import Evm.Crypto.Hash
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory

namespace Evm.Frontier.Vm.Instructions

open Evm.Frontier.Vm

/-- 0x20 SHA3 — Keccak-256 of `memory[offset, offset+len)`. -/
def keccak256 : Handler := fun evm => do
  let (offset, len, s) ← Stack.pop2 evm.stack
  let off  := offset.toNat
  let lenN := len.toNat
  let words := (lenN + 31) / 32
  let baseCost := Gas.keccak256 + Gas.keccak256Word * words
  let gasLeft ← Gas.charge evm.gasLeft baseCost
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory off lenN
  let hash : Evm.Hash32 := Evm.Crypto.keccak256 (Memory.read mem off lenN)
  let s ← Stack.push s hash
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

end Evm.Frontier.Vm.Instructions
