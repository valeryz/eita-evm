/-
  Evm.Frontier.Spec.MemStep — MLOAD / MSTORE / MSTORE8 specs.

  Memory ops are like the pure-stack ops except that:
    1. Gas cost is dynamic (depends on memory expansion).
    2. Memory contents change (MSTORE / MSTORE8).

  The spec captures both: gas formula is named (referring to the
  spec-level `Gas.memoryExpansionCost`), and the post-state memory
  is described by the equation `evm'.memory = ...` rather than
  abstracted away. -/

import Evm.Crypto.Hash
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Memory   -- chargeMemory + Memory.* helpers

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-! ## Memory-expansion gas formula

    The spec-level cost of growing memory from `oldWords` 32-byte
    words to `newWords` words. Wraps `Gas.memoryExpansionCost`
    which already implements the formula. -/

def memExpansionGas (mem : Memory) (off size : Nat) : Nat :=
  if size = 0 then 0
  else Gas.memoryExpansionCost (Memory.words mem) ((off + size + 31) / 32)

/-- The expanded memory after growing to cover `[off, off + size)`. -/
def memAfterExpand (mem : Memory) (off size : Nat) : Memory :=
  if size = 0 then mem else Memory.extend mem (off + size)

/-! ## MLOAD (0x51)

    Pop offset, charge `veryLow + memExpansion(off, 32)`, expand
    memory if needed, push the 32-byte word at `off`. -/

def IsMloadStep (evm evm' : Evm) : Prop :=
  ∃ offset rest,
    evm.stack = offset :: rest ∧
    rest.length < stackLimit ∧
    let off := offset.toNat
    let totalGas := Gas.veryLow + memExpansionGas evm.memory off 32
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory off 32
    let v := Evm.U256.ofBytesBE (Memory.read mem' off 32)
    evm' = { evm with
      stack   := v :: rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## MSTORE (0x52)

    Pop offset and value, charge `veryLow + memExpansion(off, 32)`,
    expand memory, write `value` as 32 big-endian bytes at `off`. -/

def IsMstoreStep (evm evm' : Evm) : Prop :=
  ∃ offset value rest,
    evm.stack = offset :: value :: rest ∧
    let off := offset.toNat
    let totalGas := Gas.veryLow + memExpansionGas evm.memory off 32
    evm.gasLeft ≥ totalGas ∧
    let mem' := Memory.write (memAfterExpand evm.memory off 32) off
                  (Evm.U256.toBytesBE value)
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## MSTORE8 (0x53)

    Pop offset and value, charge `veryLow + memExpansion(off, 1)`,
    expand memory, write the low byte of `value` at `off`. -/

def IsMstore8Step (evm evm' : Evm) : Prop :=
  ∃ offset value rest,
    evm.stack = offset :: value :: rest ∧
    let off := offset.toNat
    let totalGas := Gas.veryLow + memExpansionGas evm.memory off 1
    evm.gasLeft ≥ totalGas ∧
    let mem' := Memory.writeByte (memAfterExpand evm.memory off 1) off
                  (UInt8.ofNat (value.toNat &&& 0xff))
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## KECCAK256 (0x20)

    Pop offset and length, charge `30 + 6·⌈len/32⌉ + memExpansion`,
    expand memory, push the Keccak-256 of `memory[off, off+len)`. -/

def IsKeccak256Step (evm evm' : Evm) : Prop :=
  ∃ offset len rest,
    evm.stack = offset :: len :: rest ∧
    rest.length < stackLimit ∧
    let off  := offset.toNat
    let lenN := len.toNat
    let totalGas := Gas.keccak256 + Gas.keccak256Word * ((lenN + 31) / 32)
                      + memExpansionGas evm.memory off lenN
    evm.gasLeft ≥ totalGas ∧
    let mem' := memAfterExpand evm.memory off lenN
    let v : Evm.Hash32 := Evm.Crypto.keccak256 (Memory.read mem' off lenN)
    evm' = { evm with
      stack   := v :: rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## CALLDATACOPY (0x37) / CODECOPY (0x39)

    Pop dest, src-offset, length; charge `veryLow + 3·⌈len/32⌉ +
    memExpansion(dest, len)`; expand memory; write the zero-padded
    slice of the source buffer (calldata / code) at `dest`. -/

def IsCalldatacopyStep (evm evm' : Evm) : Prop :=
  ∃ dest off len rest,
    evm.stack = dest :: off :: len :: rest ∧
    let destN := dest.toNat
    let lenN  := len.toNat
    let totalGas := Gas.veryLow + Gas.copy * ((lenN + 31) / 32)
                      + memExpansionGas evm.memory destN lenN
    evm.gasLeft ≥ totalGas ∧
    let mem' := Memory.write (memAfterExpand evm.memory destN lenN) destN
                  (Evm.Bytes.sliceZeroPad evm.message.data off.toNat lenN)
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

def IsCodecopyStep (evm evm' : Evm) : Prop :=
  ∃ dest off len rest,
    evm.stack = dest :: off :: len :: rest ∧
    let destN := dest.toNat
    let lenN  := len.toNat
    let totalGas := Gas.veryLow + Gas.copy * ((lenN + 31) / 32)
                      + memExpansionGas evm.memory destN lenN
    evm.gasLeft ≥ totalGas ∧
    let mem' := Memory.write (memAfterExpand evm.memory destN lenN) destN
                  (Evm.Bytes.sliceZeroPad evm.message.code off.toNat lenN)
    evm' = { evm with
      stack   := rest,
      memory  := mem',
      gasLeft := evm.gasLeft - totalGas,
      pc      := evm.pc + 1 }

/-! ## Notes

    - `memExpansionGas` and `memAfterExpand` are spec-level
      definitions. They reference the implementation's `Memory.words`
      and `Memory.extend`, but those are PURE FUNCTIONS — they
      describe the math, not the algorithm. An implementation can
      represent memory as a `ByteArray`, sparse map, or rope, as long
      as it satisfies the resulting equations.

    - The spec is *strict* about gas: the post-state's `gasLeft` is
      pinned to `evm.gasLeft - totalGas` exactly. An implementation
      that under- or over-charges by even one wei fails the spec.

    - The spec is *strict* about memory contents: the post-state
      memory equals exactly `Memory.write ... (Evm.U256.toBytesBE
      value)`. An implementation that uses little-endian encoding,
      or fails to expand memory before writing, fails the spec. -/

end Evm.Frontier.Spec
