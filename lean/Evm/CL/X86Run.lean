/-
  Evm.CL.X86Run — the x86-64 frame: `eita_run_chunk`'s prologue and the
  `sync_and_ret` epilogue, derived from the role map.

  Stage 4 of #238. ARM64's `JIT.runChunkItems` caches the EvmState into the
  register file on entry and `_eita_sync_and_ret` writes it back on exit
  (`Evm/CL/ARM64.lean`). The x86-64 frame does the same job through
  `Target.x86_64`'s roles:

      state   x20 → rbx      pc        x21 → rbp      gas   x22 → r15
      sp      x23 → r13      stackBase x24 → r12      x26's slot → r14
      TOS     x6-x9 → r8-r11            NOS x10-x13 → (dropped, stage 0)

  Two differences from the ARM64 frame, both decided earlier and now visible as
  instructions rather than prose:

   * **sp is a BYTE offset on x86-64.** The state stores depth in words; the
     prologue loads it and shifts left by 5, the epilogue shifts right by 5
     before storing. Every stack access is then `[r12 + r13 - k]` at scale 1,
     which is what the SIB rule (stage 2f) demands — `sp_is_a_byte_offset`
     checks both conversions are present.
   * **No NOS block.** The prologue loads one cached word, the epilogue stores
     one. The memory read is the specification; the register cache is the
     refinement; one fewer cache is one fewer thing to keep coherent (#272 was
     exactly a NOS under-read).

  The dispatch pointer ARM64 keeps in x25 is reached RIP-relatively on x86-64
  (`jmp [table + rax*8]`), so there is no register for it here.

  Execution: `X86RunVectors` runs prologue + body + epilogue under Rosetta
  against a state in the harness array — the round trip of
  `Boundary.roundTrip_stack`, on hardware.
-/

import Evm.CL.X86Asm

namespace Evm.CL.X86Run

open Evm.CL.X86Encode Evm.CL.X86Items

/-- EvmState slots the frame caches, as the ARM64 frame loads them
    (`runChunkItems`: ldr x21,[x0,#0] … ldr x26,[x0,#64]). -/
def pcOff : Int := 0
def gasOff : Int := 8
def depthOff : Int := 16
def stackBaseOff : Int := 32
def x26SlotOff : Int := 64

/-- Where the frame saves its post-prologue `rsp`. ARM64 keeps this in x28 so
    the fault stubs can unwind from any depth; x86-64 has no callee-saved
    register left (stage 0's budget is exact), so it lives in the state — one
    store per run, one load per fault. The value 72 is a slot the test harness
    provides; tying it to the C `EvmState` layout is part of the arena packaging. -/
def frameSpOff : Int := 72

/-- The production slot: `EvmState.frame_sp` (offset 544, `c/evm_state.h`),
    added for this frame. The harness keeps 72 because its state buffer is 512
    bytes; the two frames differ in this one displacement
    (`prologueBodyAt`). -/
def frameSpProd : Int := 544

/-- SysV callee-saved registers the frame uses, in push order. -/
def calleeSaved : List XReg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The prologue, minus the final jump: cache the state, load TOS if the stack
    is non-empty. `rdi` is the state pointer (SysV arg 0). -/
def prologueBodyAt (fsp : Int) : List XItem :=
  (calleeSaved.map (fun r => XItem.I (.push r))) ++
  [ .I (.movRR .rbx .rdi),
    .I (.movRM .rbp { base := .rbx, disp := pcOff }),
    .I (.movRM .r15 { base := .rbx, disp := gasOff }),
    .I (.movRM .r13 { base := .rbx, disp := depthOff }),
    .I (.shiftRI .shl .r13 5),                          -- depth → byte offset
    .I (.movRM .r12 { base := .rbx, disp := stackBaseOff }),
    .I (.movRM .r14 { base := .rbx, disp := x26SlotOff }),
    .I (.movMR { base := .rbx, disp := fsp } .rsp),  -- x28's job, in memory
    .I (.aluRI .cmp .r13 0), .Jcc .e "Lrc0",            -- depth = 0: nothing cached
    .I (.movRM .r8  { base := .r12, index := some .r13, disp := -32 }),
    .I (.movRM .r9  { base := .r12, index := some .r13, disp := -24 }),
    .I (.movRM .r10 { base := .r12, index := some .r13, disp := -16 }),
    .I (.movRM .r11 { base := .r12, index := some .r13, disp := -8 }),
    .L "Lrc0" ]

/-- The harness instantiation (slot 72). -/
def prologueBody : List XItem := prologueBodyAt frameSpOff

/-- `eita_run_chunk(state, chunk_fn)`: the prologue, then enter the chunk
    (`rsi`, SysV arg 1). The chunk exits through `syncAndRet`. -/
def runChunk : List XItem := prologueBody ++ [.I (.jmpReg .rsi)]

/-- `sync_and_ret`: write pc/gas/depth back, store TOS if the stack is
    non-empty, restore, return. Leaves the depth in rax as a convenience the
    tests read. -/
def syncAndRet : List XItem :=
  [ .I (.movMR { base := .rbx, disp := pcOff } .rbp),
    .I (.movMR { base := .rbx, disp := gasOff } .r15),
    .I (.movRR .rax .r13), .I (.shiftRI .shr .rax 5),   -- byte offset → depth
    .I (.movMR { base := .rbx, disp := depthOff } .rax),
    .I (.aluRI .cmp .r13 0), .Jcc .e "Lsr0",
    .I (.movMR { base := .r12, index := some .r13, disp := -32 } .r8),
    .I (.movMR { base := .r12, index := some .r13, disp := -24 } .r9),
    .I (.movMR { base := .r12, index := some .r13, disp := -16 } .r10),
    .I (.movMR { base := .r12, index := some .r13, disp := -8 } .r11),
    .L "Lsr0" ] ++
  (calleeSaved.reverse.map (fun r => XItem.I (.pop r))) ++
  [ .I .ret ]

/-! ## Structural checks -/

/-- The prologue reads exactly the state slots the ARM64 frame reads. -/
def loadedSlots : List Int :=
  prologueBody.filterMap (fun it => match it with
    | .I (.movRM _ m) => if m.base == .rbx then some m.disp else none
    | _ => none)

theorem loads_the_arm64_slots : loadedSlots = [0, 8, 16, 32, 64] := by native_decide

/-- The epilogue writes back exactly the three the ARM64 epilogue writes
    (`str x21/x22/x23`), and nothing else into the state. -/
def storedSlots : List Int :=
  syncAndRet.filterMap (fun it => match it with
    | .I (.movMR m _) => if m.base == .rbx then some m.disp else none
    | _ => none)

theorem stores_the_arm64_slots : storedSlots = [0, 8, 16] := by native_decide

/-- Both ends of the byte-offset representation are present: `shl r13, 5` on
    entry and `shr rax, 5` (of r13's copy) before the depth store on exit. -/
theorem sp_is_a_byte_offset :
    prologueBody.any (fun it => match it with | .I (.shiftRI .shl .r13 5) => true | _ => false) = true ∧
    syncAndRet.any (fun it => match it with | .I (.shiftRI .shr .rax 5) => true | _ => false) = true := by
  native_decide

/-- The frame records its own stack pointer, which is what lets a fault stub
    reached from a called handler unwind to the epilogue. -/
theorem prologue_saves_frame_sp :
    prologueBody.any (fun it => match it with
      | .I (.movMR m .rsp) => m.base == .rbx && m.disp == frameSpOff
      | _ => false) = true := by
  native_decide

/-- Pushes and pops are mirror images. -/
theorem callee_saved_balanced :
    (prologueBody.filterMap (fun it => match it with | .I (.push r) => some r | _ => none))
      = (syncAndRet.filterMap (fun it => match it with | .I (.pop r) => some r | _ => none)).reverse := by
  native_decide

/-- The TOS word is the four limbs at `[sp - 32, sp)`, loaded and stored at the
    same four offsets — and no NOS access exists in either direction. -/
theorem tos_offsets_match :
    (prologueBody.filterMap (fun it => match it with
      | .I (.movRM _ m) => if m.base == .r12 then some m.disp else none | _ => none))
      = [-32, -24, -16, -8] ∧
    (syncAndRet.filterMap (fun it => match it with
      | .I (.movMR m _) => if m.base == .r12 then some m.disp else none | _ => none))
      = [-32, -24, -16, -8] := by
  native_decide

/-- Every stack address uses scale 1 — the byte-offset sp makes that possible. -/
theorem stack_addresses_encodable :
    (prologueBody ++ syncAndRet).all (fun it => match it with
      | .I (.movRM _ m) | .I (.movMR m _) => m.ok
      | _ => true) = true := by native_decide

end Evm.CL.X86Run
