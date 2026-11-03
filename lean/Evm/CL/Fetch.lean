/-
  Evm.CL.Fetch — `_eita_next`: fetch, pre-increment, dispatch.

  Stage 1 of #238. `DispatchTable` checked the table; this is the loop that
  indexes it:

      ldrb w14, [x26, x21]          ; code[pc]
      add  x21, x21, #1             ; pc++  — BEFORE the handler runs
      ldr  x14, [x25, x14, lsl #3]  ; table[op]
      br   x14

  Two things follow from that pre-increment, and both are relied on elsewhere
  without ever being stated:

   * A handler sees `pc` already past its own opcode, which is why
     `AsmCore.pushImm` reads its immediate starting at `pc` and not `pc+1`.
     Get the order wrong in either place and every PUSH reads one byte early.
   * A fetch past the end of the code reads the host buffer's zero padding, so
     it decodes as STOP — the implicit halt EELS gives a frame that runs off
     the end. That only holds while the padding outlasts the longest possible
     overshoot, which is what `slack_suffices` below pins.

  The loop also has an opt-in tracing path that makes a real call, and ARM64's
  AAPCS64 does NOT preserve x6-x13 across one — those are exactly the registers
  holding the cached TOS/NOS. They are saved and restored around the `blr`;
  since tracing is off in production, a missing save would corrupt the stack
  only for whoever is debugging, which is the worst time to find out.
-/

import Evm.CL.ARM64
import Evm.CL.Boundary

namespace Evm.CL.Fetch

/-- The fetch step: the opcode byte, and the pc the handler starts with. Past
    the end of `codeSize` the host buffer is zero-padded, so the byte is 0. -/
def fetch (code : Nat → Nat) (codeSize pc : Nat) : Nat × Nat :=
  ((if pc < codeSize then code pc else 0), pc + 1)

/-- Byte 0x00 is STOP. -/
def stopOpcode : Nat := 0x00

/-- **Running off the end of the code halts.** The fetch reads zero, which is
    STOP — EELS's implicit halt, obtained from the buffer's padding rather than
    a bounds check in the hot path. -/
theorem fetch_past_end_is_stop (code : Nat → Nat) (codeSize pc : Nat)
    (h : ¬ pc < codeSize) : (fetch code codeSize pc).1 = stopOpcode := by
  simp [fetch, stopOpcode, h]

/-- **The handler starts one past its own opcode.** -/
theorem fetch_pre_increments (code : Nat → Nat) (codeSize pc : Nat) :
    (fetch code codeSize pc).2 = pc + 1 := rfl

/-- …which is exactly what `pushImm` assumes: a PUSH-n handler entered at
    `pc+1` reads its immediate from `pc+1 .. pc+n`, i.e. the n bytes AFTER the
    opcode at `pc`. Stated as the composition, so the two cannot drift apart. -/
theorem push_immediate_follows_the_opcode
    (code : Nat → Nat) (codeSize pc n : Nat) (a : Evm.CL.AsmCore.U256) :
    Evm.CL.AsmCore.pushAccum code codeSize (fetch code codeSize pc).2 n a
      = Evm.CL.AsmCore.pushAccum code codeSize (pc + 1) n a := by
  rfl

/-! ## The zero padding has to outlast the overshoot

The host allocates the code buffer with 64 bytes of zeroed slack. A frame can
only run past `codeSize` by one opcode plus its immediate, and the widest is
PUSH32: one opcode byte plus 32 immediate bytes. So the furthest a fetch can
land past the end is 33 bytes, and a fetch there must still read padding — not
whatever follows the allocation. -/

/-- The widest single step: PUSH32 advances pc by 1 (opcode) + 32 (immediate). -/
def maxStep : Nat := 33

/-- The slack the host allocates after the code. -/
def codeSlack : Nat := 64

theorem slack_suffices : maxStep ≤ codeSlack := by decide

/-- The margin is 31 bytes — comfortable, but NOT room for a second overshoot
    (2 × 33 = 66 > 64, which I first claimed and `decide` refuted). So the
    invariant that makes this sound is "at most one step past the end", not "the
    slack is huge". -/
theorem slack_margin : codeSlack - maxStep = 31 := by decide
theorem slack_is_not_two_steps : ¬ (2 * maxStep ≤ codeSlack) := by decide

/-! ## The tracing path preserves the cached registers

AAPCS64 gives x6-x13 to the callee, and those hold TOS/NOS. The `blr` is
wrapped in saves; this checks the emitted text rather than restating the list,
so adding a cached register without saving it here fails the build. -/

def traceSaves : List String := Boundary.framePairs "stp" ARM64.nextCode
def traceRestores : List String := Boundary.framePairs "ldp" ARM64.nextCode

/-- Five pairs: x29/x30 for the call frame, and x6-x13 — the whole TOS/NOS
    cache. -/
theorem five_pairs_saved : traceSaves.length = 5 := by native_decide

theorem every_trace_save_is_restored :
    traceSaves.all (fun s => traceRestores.contains s) = true := by native_decide

theorem every_trace_restore_was_saved :
    traceRestores.all (fun r => traceSaves.contains r) = true := by native_decide

/-- **Every register of the TOS/NOS cache is in the save set.** This is the one
    that matters: x6-x13 are caller-saved, so a cached register missing here is
    silently clobbered by the trace callback — and only when tracing is on. -/
theorem tos_and_nos_are_saved :
    ["x6, x7", "x8, x9", "x10, x11", "x12, x13"].all
      (fun r => traceSaves.any (fun s => (s.splitOn r).length == 2)) = true := by
  native_decide

/-- The callee-saved registers are NOT in the trace save set — saving them
    would be dead work, since the callee is obliged to preserve them. -/
theorem callee_saved_not_in_trace_set :
    ["x19, x20", "x21, x22", "x23, x24", "x25, x26", "x27, x28"].all
      (fun r => traceSaves.all (fun s => (s.splitOn r).length != 2)) = true := by
  native_decide

end Evm.CL.Fetch
