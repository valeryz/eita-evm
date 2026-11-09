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

/-! ## `chargeMemory`'s success form (shared by every memory-touching refinement proof;
    moved here from `Evm.IR.Soundness` so the fork Spec layers can use it). -/
open Evm.Frontier.Vm.Instructions (chargeMemory)

@[simp] theorem memoryExpansionCost_self (a : Nat) :
    Gas.memoryExpansionCost a a = 0 := by
  simp [Gas.memoryExpansionCost]

theorem memoryExpansionCost_max (a b : Nat) :
    Gas.memoryExpansionCost a (max a b) = Gas.memoryExpansionCost a b := by
  unfold Gas.memoryExpansionCost
  rcases Nat.le_total b a with h | h
  · simp [h]
  · rw [Nat.max_eq_right h]

theorem words_extend (m : Memory) (n : Nat) :
    Memory.words (Memory.extend m n)
      = max (Memory.words m) ((n + 31) / 32) := by
  simp only [Memory.extend, Memory.words]
  split
  · next h => omega
  · next h =>
    simp only [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate]
    omega

theorem charge_ok {g n g' : Nat} (h : Gas.charge g n = .ok g') :
    n ≤ g ∧ g' = g - n := by
  unfold Gas.charge at h
  by_cases hlt : g < n
  · rw [ite_eq_left hlt] at h; exact absurd h (by simp)
  · rw [ite_eq_right hlt] at h
    injection h with h
    exact ⟨Nat.not_lt.mp hlt, h.symm⟩

/-- Success characterization of `chargeMemory`: the charged cost is
    the expansion to `max oldWords rangeWords` (0 when the range is
    empty or already covered), and the returned memory's word count
    is exactly that max. -/
theorem chargeMemory_ok {g : Nat} {m : Memory} {off size : Nat}
    {g' : Nat} {m' : Memory}
    (h : chargeMemory g m off size = .ok (g', m')) :
    Gas.memoryExpansionCost (Memory.words m)
      (if size = 0 then Memory.words m
       else max (Memory.words m) ((off + size + 31) / 32)) ≤ g ∧
    g' = g - Gas.memoryExpansionCost (Memory.words m)
      (if size = 0 then Memory.words m
       else max (Memory.words m) ((off + size + 31) / 32)) ∧
    Memory.words m'
      = (if size = 0 then Memory.words m
         else max (Memory.words m) ((off + size + 31) / 32)) ∧
    m' = (if size = 0 then m else Memory.extend m (off + size)) := by
  by_cases hsz : size = 0
  · subst hsz
    simp only [chargeMemory] at h
    simp only [ite_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp [Gas.memoryExpansionCost]
  · simp only [chargeMemory, hsz, reduceIte, bind, Except.bind, pure,
      Except.pure] at h
    split at h
    · simp at h
    · next g1 hch =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      have hc := charge_ok hch
      simp only [hsz, reduceIte]
      rw [memoryExpansionCost_max]
      exact ⟨hc.1, hc.2, words_extend m (off + size), trivial⟩

/-- `chargeMemory` success in the spec's vocabulary: the cost is
    `memExpansionGas` and the resulting memory is `memAfterExpand`.
    Wraps `chargeMemory_ok`, folding away its `max`-form via
    `memoryExpansionCost_max`. -/
theorem chargeMemory_spec {g : Nat} {m : Memory} {off size g' : Nat}
    {m' : Memory}
    (h : chargeMemory g m off size = .ok (g', m')) :
    memExpansionGas m off size ≤ g ∧
    g' = g - memExpansionGas m off size ∧
    m' = memAfterExpand m off size := by
  obtain ⟨hle, hg, _, hm⟩ := chargeMemory_ok h
  by_cases hsz : size = 0
  · subst hsz
    simp only [reduceIte, memoryExpansionCost_self] at hg hm
    simp only [memExpansionGas,
               memAfterExpand, reduceIte]
    exact ⟨Nat.zero_le _, by omega, hm⟩
  · simp only [ite_eq_right hsz] at hle hg hm
    rw [memoryExpansionCost_max] at hle hg
    simp only [memExpansionGas,
               memAfterExpand, ite_eq_right hsz]
    exact ⟨hle, hg, hm⟩

/-- Two successive charges (memory expansion `m`, then `c`) are one charge of `c + m`.
    A pure-`Nat` statement so callers can use it on `Gas.Gas`-typed hypotheses, which
    `omega` does not see through. -/
theorem charge2_nat {a m c : Nat} (h1 : m ≤ a) (h2 : c ≤ a - m) :
    c + m ≤ a ∧ a - m - c = a - (c + m) := by omega

/-- Three successive charges (`b`, then memory `m`, then `c`) are one charge of
    `b + c + m`; pure `Nat`, like `charge2_nat`. -/
theorem charge3_nat {a b m c : Nat} (h0 : b ≤ a) (h1 : m ≤ a - b) (h2 : c ≤ a - b - m) :
    b + c + m ≤ a ∧ a - b - m - c = a - (b + c + m) := by omega

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
