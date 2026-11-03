/-
  Evm.Cancun.Spec.McopyStep — EIP-5656 MCOPY (0x5e).

  EELS reference: `forks/cancun/vm/instructions/memory.py` `mcopy`.

  MCOPY copies `len` bytes within memory from `srcOff` to `destOff`.
  The copy is overlap-safe (semantically, "as if" the source bytes
  are read in full before any destination byte is written).

  Gas cost:
    `total = veryLow + 3 · ceil(len / 32) + memoryExpansion(...)`
  where the memory-expansion size is `max(destOff + len, srcOff + len)`.
  The `3 · ceil(len / 32)` is the standard per-word copy cost (same
  rate as CALLDATACOPY, CODECOPY).

  Inheritance: applies unchanged at Prague.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Spec.MemStep   -- memExpansionGas / memAfterExpand helpers

namespace Evm.Cancun.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (memAfterExpand)

/-- The per-32-byte-word copy rate. Same constant as CALLDATACOPY /
    CODECOPY: 3 gas per word.

    EELS `forks/frontier/vm/gas.py` `GAS_COPY = 3`. -/
def gasCopyWord : Nat := 3

/-- Gas for the memory expansion needed to cover BOTH a read window
    `[srcOff, srcOff + len)` and a write window `[destOff, destOff + len)`.
    This is just `memExpansionGas` over the larger of the two end
    offsets. -/
def mcopyExpansionGas (mem : Memory) (destOff srcOff len : Nat) : Nat :=
  if len = 0 then 0
  else
    let hi := max (destOff + len) (srcOff + len)
    Gas.memoryExpansionCost (Memory.words mem) ((hi + 31) / 32)

/-- Memory expansion: extend to cover both windows. -/
def mcopyExpand (mem : Memory) (destOff srcOff len : Nat) : Memory :=
  if len = 0 then mem
  else
    let hi := max (destOff + len) (srcOff + len)
    Memory.extend mem hi

/-! ## MCOPY (0x5e)

    Pops three values (destOff, srcOff, len), charges
    `veryLow + 3 · ceil(len / 32) + memExpansion`, expands memory to
    cover the union of the two windows, then copies `len` bytes from
    `srcOff` to `destOff`. -/

def IsMcopyStep (evm evm' : Evm) : Prop :=
  ∃ destOff srcOff len rest,
    evm.stack = destOff :: srcOff :: len :: rest ∧
    let dN := destOff.toNat
    let sN := srcOff.toNat
    let lN := len.toNat
    let words := (lN + 31) / 32
    let totalGas := Gas.veryLow + gasCopyWord * words +
                    mcopyExpansionGas evm.memory dN sN lN
    evm.gasLeft ≥ totalGas ∧
    -- Read FROM the expanded memory (the source window is conceptually
    -- read after expansion, so reads past pre-expansion bounds yield
    -- zeros — matches EELS `memory_read_bytes`). The copy itself is
    -- conceptually atomic; we model it as one `Memory.write` of the
    -- pre-read bytes, which is overlap-safe by construction.
    let memExp := mcopyExpand evm.memory dN sN lN
    let bytes := Memory.read memExp sN lN
    evm' = { evm with
      stack   := rest,
      memory  := Memory.write memExp dN bytes,
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## Notes

    * The overlap-safety property is encoded by reading the source
      bytes FROM the expanded memory into an immutable `Evm.Bytes`
      first, then writing the destination. An implementation that
      iterates byte-by-byte with forward indexing would violate this
      for `destOff > srcOff ∧ destOff < srcOff + len`; the spec
      catches that.

    * `len = 0` is well-defined: zero memory expansion, zero copy
      gas, zero bytes moved. The spec covers this through
      `mcopyExpansionGas (..., 0) = 0` and `Memory.read mem _ 0 = empty`,
      `Memory.write mem _ empty = mem`. -/

end Evm.Cancun.Spec
