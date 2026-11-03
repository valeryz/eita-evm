/-
  Evm.Cancun.Vm.Instructions — handlers for the opcodes Cancun adds.

  EELS references (all in `forks/cancun/vm/instructions/`):
    - `storage.py:tload, tstore`     — EIP-1153 (0x5c / 0x5d)
    - `memory.py:mcopy`              — EIP-5656 (0x5e)
    - `environment.py:blob_hash`     — EIP-4844 (0x49)
    - `block.py:blob_base_fee`       — EIP-7516 (0x4a)

  All five handlers are "pure" in the trampoline sense — they touch
  only the current frame's stack/memory/gas and (for transient
  storage) the tx-scope env. They never spawn a sub-frame, so they
  don't need to yield to the trampoline; the dispatcher in
  `Cancun.Vm.Effect` can route them through `liftPure`.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Cancun.State
import Evm.Cancun.Vm.Gas

namespace Evm.Cancun.Vm.Instructions

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-! ## EIP-1153: TLOAD / TSTORE

    EELS `forks/cancun/vm/instructions/storage.py:tload, tstore`. -/

/-- 0x5c TLOAD — push transient-storage[currentTarget][slot]. -/
def tload : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Cancun.Vm.Gas.tLoad
  let (slot, s) ← Stack.pop evm.stack
  let v := Evm.Cancun.State.getTransient evm.env evm.message.currentTarget slot
  let s ← Stack.push s v
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-- 0x5d TSTORE — write to transient storage. Static-context check
    (EELS calls `system.write_in_static_check` from the handler).
    EELS `forks/cancun/vm/instructions/storage.py:tstore`. -/
def tstore : Handler := fun evm => do
  if evm.message.isStatic then
    .error .writeInStaticContext
  let gasLeft ← Gas.charge evm.gasLeft Evm.Cancun.Vm.Gas.tStore
  let (slot, value, s) ← Stack.pop2 evm.stack
  let envAfter :=
    Evm.Cancun.State.setTransient evm.env evm.message.currentTarget slot value
  return { evm with gasLeft := gasLeft, env := envAfter, stack := s, pc := evm.pc + 1 }

/-! ## EIP-5656: MCOPY -/

/-- 0x5e MCOPY — copy `len` bytes from `memory[srcOff]` to `memory[dstOff]`.
    Static gas: `GAS_VERY_LOW (3)`. Dynamic gas: `3 · ⌈len/32⌉` + memory
    expansion over `max(dstOff+len, srcOff+len)`. Source and destination
    may overlap; EELS uses an intermediate buffer (`forks/cancun/vm/
    instructions/memory.py:mcopy` lines ~50-80). -/
def mcopy : Handler := fun evm => do
  let (destOff, srcOff, len, s) ← Stack.pop3 evm.stack
  let destOffN := destOff.toNat
  let srcOffN  := srcOff.toNat
  let lenN     := len.toNat
  -- Charge base before any dynamic cost.
  let gasLeft ← Gas.charge evm.gasLeft Evm.Cancun.Vm.Gas.mcopyBase
  -- Memory expansion: enough to cover both source-read and dest-write
  -- ranges. EELS extends to `max(dstOff+len, srcOff+len)` then bills
  -- the resulting expansion delta. We piggy-back on `chargeMemory`
  -- which both charges and extends.
  let highEnd := Nat.max (destOffN + lenN) (srcOffN + lenN)
  let (gasLeft, mem) ← chargeMemory gasLeft evm.memory 0 highEnd
  -- Per-word copy cost (3 · ⌈len/32⌉).
  let words := (lenN + 31) / 32
  let gasLeft ← Gas.charge gasLeft (Evm.Cancun.Vm.Gas.mcopyWord * words)
  -- Read first (overlap-safe), then write.
  let src := Memory.read mem srcOffN lenN
  let mem := Memory.write mem destOffN src
  return { evm with gasLeft := gasLeft, memory := mem, stack := s, pc := evm.pc + 1 }

/-! ## EIP-4844: BLOBHASH -/

/-- 0x49 BLOBHASH — push `tx.blobVersionedHashes[index]` or 0 if
    out of bounds. EELS `forks/cancun/vm/instructions/environment.py:
    blob_hash`. The hashes live tx-scope, on the env. -/
def blobhash : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Cancun.Vm.Gas.blobHash
  let (idx, s) ← Stack.pop evm.stack
  let idxN := idx.toNat
  let v : Evm.Hash32 :=
    if idxN < evm.env.blobVersionedHashes.length then
      evm.env.blobVersionedHashes[idxN]!
    else
      0
  let s ← Stack.push s v
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

/-! ## EIP-7516: BLOBBASEFEE -/

/-- 0x4a BLOBBASEFEE — push the current block's blob base fee (set
    on the env from header.excess_blob_gas at block entry). EELS
    `forks/cancun/vm/instructions/block.py:blob_base_fee`. -/
def blobbasefee : Handler := fun evm => do
  let gasLeft ← Gas.charge evm.gasLeft Evm.Cancun.Vm.Gas.blobBaseFee
  let s ← Stack.push evm.stack evm.env.blobBaseFee
  return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

end Evm.Cancun.Vm.Instructions
