/-
  Evm.CL.Boundary — the frame boundary: caching EvmState into registers on
  entry, flushing it back on exit, and the ABI save/restore around it.

  Stage 1 of #238, and the last high-stakes raw asm. `_eita_run_one` (and the
  JIT's `_eita_run_chunk`) caches pc/gas/sp/stack-base/code-base into x20-x26
  and the top two stack words into x6-x13; `_eita_sync_and_ret` writes them
  back. Every handler runs between those two, so a bug here is not one opcode
  wrong — it is every frame wrong, and #272 was already one slot off in this
  exact arithmetic.

  Three things have to hold, and none of them was written down:

   1. **Round trip.** Entry-then-exit with no handler in between must leave the
      EvmState as it was, except for the pre-incremented pc. That is what says
      the load address and the store address are the same function of `sp` — an
      off-by-one in either direction is the #272 shape.
   2. **Matching guards.** Entry loads TOS only when `sp ≥ 1` and NOS only when
      `sp ≥ 2`; exit must store under exactly the same thresholds. Store with a
      weaker guard and an uninitialised register lands in a live slot; store
      with a stronger one and a computed value is dropped.
   3. **ABI pairing.** Every callee-saved register pushed at entry is popped
      from the same offset at exit, and the frame size matches. Get that wrong
      and the corruption is in the CALLER, where no EVM-level test looks.

  (1) and (2) are proved below over a model of the boundary. (3) is a property
  of the emitted text, so it is checked against the text.
-/

import Evm.CL.ARM64

namespace Evm.CL.Boundary

abbrev U256 := Evm.CL.AsmCore.U256

/-- What the boundary reads and writes in `EvmState`. -/
structure Frame where
  pc    : Nat
  gas   : Nat
  sp    : Nat
  stack : Nat → U256

/-- The cached registers a handler runs with. -/
structure Regs where
  pc    : Nat
  gas   : Nat
  sp    : Nat
  tos   : U256
  nos   : U256
  stack : Nat → U256

/-- `_eita_run_one`'s prologue: cache the fields, load TOS/NOS under their
    guards, pre-increment pc past the opcode. -/
def entry (junk : U256) (f : Frame) : Regs :=
  { pc    := f.pc + 1
    gas   := f.gas
    sp    := f.sp
    tos   := if 1 ≤ f.sp then f.stack (f.sp - 1) else junk
    nos   := if 2 ≤ f.sp then f.stack (f.sp - 2) else junk
    stack := f.stack }

/-- `_eita_sync_and_ret`: store pc/gas/sp, then TOS and NOS under the same
    guards, in that order. -/
def exit (r : Regs) : Frame :=
  let s1 : Nat → U256 :=
    if 1 ≤ r.sp then (fun i => if i = r.sp - 1 then r.tos else r.stack i) else r.stack
  let s2 : Nat → U256 :=
    if 2 ≤ r.sp then (fun i => if i = r.sp - 2 then r.nos else s1 i) else s1
  { pc := r.pc, gas := r.gas, sp := r.sp, stack := s2 }

/-! ## (1) and (2): the round trip -/

/-- **The boundary is transparent.** With no handler in between, the stack comes
    back byte for byte — which is the statement that the load and store
    addresses agree, under matching guards, for every `sp` including 0 and 1. -/
theorem roundTrip_stack (junk : U256) (f : Frame) (i : Nat) :
    (exit (entry junk f)).stack i = f.stack i := by
  unfold exit entry
  by_cases h2 : 2 ≤ f.sp
  · have h1 : 1 ≤ f.sp := by omega
    have hne : f.sp - 1 ≠ f.sp - 2 := by omega
    simp only [h1, h2, ite_true]
    by_cases hi2 : i = f.sp - 2
    · simp [hi2]
    · by_cases hi1 : i = f.sp - 1
      · simp [hi1, hne]
      · simp [hi1, hi2]
  · by_cases h1 : 1 ≤ f.sp
    · simp only [h1, h2, ite_true, ite_false]
      by_cases hi1 : i = f.sp - 1
      · simp [hi1]
      · simp [hi1]
    · simp [h1, h2]

/-- The scalars come back as they went in, with pc pre-incremented past the
    opcode — the other half of the round trip. -/
theorem roundTrip_scalars (junk : U256) (f : Frame) :
    (exit (entry junk f)).pc = f.pc + 1 ∧
    (exit (entry junk f)).gas = f.gas ∧
    (exit (entry junk f)).sp = f.sp := by
  unfold exit entry
  exact ⟨rfl, rfl, rfl⟩

/-- An empty stack is not touched: with `sp = 0` neither store fires, so the
    uninitialised TOS/NOS registers cannot reach memory. This is the guard that
    matters — `sp - 1` on an empty stack is 0 in ℕ (and wraps on the machine),
    so an unguarded store would hit slot 0 or run off the arena. -/
theorem empty_stack_untouched (junk : U256) (f : Frame) (_h : f.sp = 0) (i : Nat) :
    (exit (entry junk f)).stack i = f.stack i := roundTrip_stack junk f i

/-! ## The off-by-one, as a counterexample

`_eita_sync_and_ret` computes the TOS slot as `sp-1`, matching the entry load.
A version that stored at `sp-2` — the #272 shape, one slot below the live top —
breaks the round trip, so the agreement is load-bearing in the proof. -/

def exitOffByOne (r : Regs) : Frame :=
  { pc := r.pc, gas := r.gas, sp := r.sp
    stack := if 1 ≤ r.sp then (fun i => if i = r.sp - 2 then r.tos else r.stack i)
             else r.stack }

theorem offByOne_store_corrupts :
    ∃ (junk : U256) (f : Frame),
      (exitOffByOne (entry junk f)).stack (f.sp - 2) ≠ f.stack (f.sp - 2) := by
  refine ⟨{ l0 := 0, l1 := 0, l2 := 0, l3 := 0 },
          { pc := 0, gas := 0, sp := 2
            stack := fun i => if i = 0 then { l0 := 7, l1 := 0, l2 := 0, l3 := 0 }
                              else { l0 := 9, l1 := 0, l2 := 0, l3 := 0 } }, ?_⟩
  simp [exitOffByOne, entry]

/-- And an UNGUARDED store on an empty stack writes the uninitialised register
    into slot 0 — the other half of (2). -/
def exitUnguarded (r : Regs) : Frame :=
  { pc := r.pc, gas := r.gas, sp := r.sp
    stack := fun i => if i = r.sp - 1 then r.tos else r.stack i }

theorem unguarded_store_writes_junk :
    ∃ (junk : U256) (f : Frame),
      f.sp = 0 ∧ (exitUnguarded (entry junk f)).stack 0 ≠ f.stack 0 := by
  refine ⟨{ l0 := 123, l1 := 0, l2 := 0, l3 := 0 },
          { pc := 0, gas := 0, sp := 0,
            stack := fun _ => { l0 := 0, l1 := 0, l2 := 0, l3 := 0 } }, rfl, ?_⟩
  simp [exitUnguarded, entry]

/-! ## (3) ABI pairing, checked against the emitted text

Every `stp` into the frame at entry must have a matching `ldp` from the same
offset at exit. Rather than restate the registers here (which would check a
transcription, not the emitter), pull the operand text out of both strings and
compare. -/

/-- The two ends spell the same frame slot differently — the push is
    pre-indexed (`[sp, #-96]!`) and the pop post-indexed (`[sp], #96`) — so
    normalise both to one form before comparing. -/
def normalizeFrame (t : String) : String :=
  ((t.replace "[sp, #-96]!" "[sp, #0]").replace "[sp], #96" "[sp, #0]").replace "  " " "

/-- Operand text of every `stp`/`ldp` line that addresses the frame, in order.
    (No `String.trim`: in this toolchain it is deprecated and returns a
    `String.Slice`, which does not compose with `String.replace`.) -/
def framePairs (mnem : String) (body : String) : List String :=
  (body.splitOn "\n").filterMap fun line =>
    if (line.splitOn mnem).length == 2 && (line.splitOn "[sp").length == 2 then
      some (normalizeFrame ((line.splitOn mnem).getLast!))
    else none

def saves : List String := framePairs "stp" ARM64.trampolineCode
def restores : List String := framePairs "ldp" ARM64.syncAndRetCode

/-- Six pairs saved: x29/x30 plus x19-x28. -/
theorem six_pairs_saved : saves.length = 6 := by native_decide

/-- **Everything saved is restored** — same registers, same offsets. The lists
    are reversed relative to each other (exit unwinds), so compare as sets. -/
theorem every_save_is_restored :
    saves.all (fun s => restores.contains s) = true := by native_decide

/-- …and nothing is restored that was not saved, so the frame layout is a
    bijection and no slot is read uninitialised. -/
theorem every_restore_was_saved :
    restores.all (fun r => saves.contains r) = true := by native_decide

theorem same_pair_count : saves.length = restores.length := by native_decide

/-- The frame is 96 bytes at both ends: the pre-indexed push and the
    post-indexed pop must agree or the caller's stack pointer is left wrong. -/
theorem frame_size_matches :
    (ARM64.trampolineCode.splitOn "[sp, #-96]!").length = 2 ∧
    (ARM64.syncAndRetCode.splitOn "[sp], #96").length = 2 := by native_decide

end Evm.CL.Boundary
