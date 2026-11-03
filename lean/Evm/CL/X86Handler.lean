/-
  Evm.CL.X86Handler — a whole handler through the x86-64 pipeline.

  Stage 4 of #238. `OpInstrs.Op.instrs?` gives MLOAD and MSTORE an `AInstr`
  body text-identical to the ARM64 one. Lowering that body for x86-64 needs
  one more thing the per-instruction lowering cannot see: the stage-4d
  decision that `sp` is a BYTE offset on x86-64. In the ARM64 body `x23` counts
  words, so

      sub  x23, x23, #2                 two words popped
      cmp  x23, #2                      at least two words
      sub  x14, x23, #1 ; add x14, x24, x14, lsl #5     &stack[sp-1]

  mean 64 bytes, 64 bytes, and `r12 + r13 - 32` on x86-64 — and `reloadNos`'s
  loads into x10-x13 mean nothing at all, because x86-64 keeps no NOS cache
  (the memory below TOS is authoritative; the NOS reads are memory operands).
  Lowering those instructions literally would pop two bytes, compare against
  2 bytes, address the wrong word, and write the NOS "cache" into rax.

  `spScale` is that representation change as a program transformation over
  `AInstr`: immediates on x23 scale by 32, the stack-address idiom becomes a
  plain add, and NOS-destination instructions vanish. Everything else passes
  through untouched (`spScale_touches_only_sp_and_nos`). It is applied at the
  handler level, between `Op.instrs?` and `x86Items`, so the per-instruction
  lowering stays faithful and the refinement decision lives in one place.

  `mstoreX86` wraps the result in the stage-4d frame with `_eita_oog` and
  `_eita_stack_underflow` bound to local stubs, and `X86RunVectors` runs it
  under Rosetta against a state, a stack and a memory in the harness array —
  five cases: a plain store, a store that expands memory, an underflow, an
  out-of-range offset and an out-of-gas.
-/

import Evm.CL.OpInstrs
import Evm.CL.X86Run

namespace Evm.CL.X86Handler

open Evm.CL.AsmCore Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Asm Evm.CL.OpInstrs

/-- A handler body for x86-64: each op's x86-64 program (`Op.instrsX86?`). -/
def x86Body (p : Prog) : List AInstr := p.flatMap (fun o => (Op.instrsX86? o).getD [])

/-- Every covered handler's x86-64 program, for the items battery. -/
def x86Bodies : List (List AInstr) := Evm.CL.OpInstrs.covered.map x86Body

/-- `X86Items.lowerings_align`, over the handler bodies too: the text and byte
    lowerings expand every handler instruction into the same number of x86
    instructions, which is what lets `verify-x86-items.sh` pair them. -/
theorem handler_lowerings_align :
    x86Bodies.all (fun p => p.all (fun i =>
      (Evm.CL.X86Items.insns (Evm.CL.X86Items.x86Items i)).length ==
        (Evm.CL.X86Items.textInsnLines i).length)) = true := by
  native_decide


/-- Does an instruction involve sp, the stack-address idiom, or a NOS
    destination? Those are the only ones `spScale` may change. -/
def touched : AInstr → Bool
  | .subImm d a _ | .addImm d a _ => d == .x23 || a == .x23 || isNos d
  | .cmpImm a _ => a == .x23
  | .addLsl5 _ b _ => b == .x24
  | i => match dest? i with | some d => isNos d | none => false

/-- **`spScale` is the identity off its three targets** — checked over every
    instruction of the covered handlers. -/
theorem spScale_touches_only_sp_and_nos :
    handlerBodies.all (fun p => p.all (fun i => touched i || (spScale i == [i]))) = true := by
  native_decide

/-- After scaling, no instruction in a covered handler writes a NOS register —
    so the x86 lowering's `dst` is never asked about one. -/
theorem x86_bodies_write_no_nos :
    covered.all (fun p => (x86Body p).all (fun i =>
      match dest? i with | some d => !isNos d | none => true)) = true := by
  native_decide

/-- What scaling did to MSTORE: two instructions gone (the NOS reload's two
    `ldp`s), and the sp arithmetic in bytes. -/
theorem mstore_scaled_size : (x86Body (mstoreBody 3)).length = 57 - 2 := by native_decide

theorem mstore_pops_64_bytes :
    (x86Body (mstoreBody 3)).contains (.subImm .x23 .x23 64) = true ∧
    (x86Body (mstoreBody 3)).contains (.cmpImm .x23 64) = true := by native_decide

/-! ## The handler, framed -/

/-- The gas values the fault stubs leave behind, so a run says which path it
    took. -/
def oogGas : Nat := 7777
def underflowGas : Nat := 8888
def overflowGas : Nat := 9999
def invalidJumpGas : Nat := 6666
def staticGas : Nat := 5555

def faultSyms : List (String × String) :=
  [("_eita_oog", "Loog"), ("_eita_stack_underflow", "Lunder"), ("_eita_stack_overflow", "Lover"),
   ("_eita_invalid_jump", "Linval"), ("_eita_static_violation", "Lstatic"),
   -- terminators EXIT by jumping here (with the handler's return address still
   -- pushed), so `Lsync` restores rsp first, like the fault stubs
   ("_eita_sync_and_ret", "Lsync")]

/-- The helper symbols a body calls, in first-use order. -/
def helperSyms (body : List AInstr) : List String :=
  (body.filterMap (fun i => match i with | .blSym s => some s | _ => none)).eraseDups

/-- One 8-byte slot per helper, labelled as the `CallRip` expects; the loader
    fills them (abs64). Appended after the code, like the dispatch table. -/
def symTable (body : List AInstr) : List XItem :=
  (helperSyms body).flatMap (fun s => [XItem.L s!"Lsym_{s}", .QuadSym s])

/-- The frame CALLS the handler, as the dispatcher will: the handler's
    `brCont` is a `ret` back to the frame, which then falls into the epilogue.
    The fault stubs first restore `rsp` from the frame's saved copy — they are
    reached from inside the call, with a return address still pushed — then
    rejoin the epilogue, so the state is written back on every path.

    The first version inlined the body; its `ret` then popped a saved register
    as a return address and the success path crashed while every fault path
    passed. The design the crash enforced is the real one. -/
def framed (p : Prog) : List XItem :=
  let frameSp : Mem := { base := .rbx, disp := Evm.CL.X86Run.frameSpOff }
  let body := x86Body p
  Evm.CL.X86Run.prologueBody ++
  [.Call "Lbody", .L "Lsync", .I (.movRM .rsp frameSp)] ++ Evm.CL.X86Run.syncAndRet ++
  [.L "Loog",   .I (.movRM .rsp frameSp), .I (.movRI .r15 (Int.ofNat oogGas)),       .Jmp "Lsync",
   .L "Lunder", .I (.movRM .rsp frameSp), .I (.movRI .r15 (Int.ofNat underflowGas)), .Jmp "Lsync",
   .L "Lover",  .I (.movRM .rsp frameSp), .I (.movRI .r15 (Int.ofNat overflowGas)),  .Jmp "Lsync",
   .L "Linval", .I (.movRM .rsp frameSp), .I (.movRI .r15 (Int.ofNat invalidJumpGas)), .Jmp "Lsync",
   .L "Lstatic", .I (.movRM .rsp frameSp), .I (.movRI .r15 (Int.ofNat staticGas)),   .Jmp "Lsync",
   .L "Lbody"] ++ progItems body ++ symTable body

def mstoreX86 : List XItem := framed (mstoreBody 3)
def mloadX86  : List XItem := framed (mloadBody 3)
def addX86    : List XItem := framed (arithBody .add 3)
def subX86    : List XItem := framed (arithBody .sub 3)
def andX86    : List XItem := framed (bitwiseBody .and 3)
def orX86     : List XItem := framed (bitwiseBody .orr 3)
def xorX86    : List XItem := framed (bitwiseBody .eor 3)
def notX86    : List XItem := framed (notBody 3)
def eqX86     : List XItem := framed (eqBody 3)
def iszeroX86 : List XItem := framed (iszeroBody 3)
def ltX86     : List XItem := framed (cmpBody false .lo 3)
def gtX86     : List XItem := framed (cmpBody true .lo 3)
def sltX86    : List XItem := framed (cmpBody false .lt 3)
def sgtX86    : List XItem := framed (cmpBody true .lt 3)
def popX86    : List XItem := framed (popBody 2)
def push0X86  : List XItem := framed (pushBody 0 2)
def push1X86  : List XItem := framed (pushBody 1 3)
def push2X86  : List XItem := framed (pushBody 2 3)
def push8X86  : List XItem := framed (pushBody 8 3)
def push9X86  : List XItem := framed (pushBody 9 3)
def push32X86 : List XItem := framed (pushBody 32 3)
def dup1X86   : List XItem := framed (dupBody 1 3)
def dup2X86   : List XItem := framed (dupBody 2 3)
def swap1X86  : List XItem := framed (swapBody 1 3)
def swap2X86  : List XItem := framed (swapBody 2 3)
def mulX86    : List XItem := framed (binComputeBody "_eita_helper_mul" 5)
def divX86    : List XItem := framed (binComputeBody "_eita_helper_div" 5)
def sdivX86   : List XItem := framed (binComputeBody "_eita_helper_sdiv" 5)
def modX86    : List XItem := framed (binComputeBody "_eita_helper_mod" 5)
def smodX86   : List XItem := framed (binComputeBody "_eita_helper_smod" 5)
def shlX86    : List XItem := framed (binComputeBody "_eita_helper_shl" 3)
def shrX86    : List XItem := framed (binComputeBody "_eita_helper_shr" 3)
def sarX86    : List XItem := framed (binComputeBody "_eita_helper_sar" 3)
def byteX86   : List XItem := framed (binComputeBody "_eita_helper_byte" 3)
def sextX86   : List XItem := framed (binComputeBody "_eita_helper_signextend" 5)
def addmodX86 : List XItem := framed (ternaryComputeBody "_eita_helper_addmod" 8)
def mulmodX86 : List XItem := framed (ternaryComputeBody "_eita_helper_mulmod" 8)
def pcX86     : List XItem := framed (pcBody 2)
def gasX86    : List XItem := framed (gasBody 2)
def envU64X86 : List XItem := framed (envU64Body 8 2)
def envU256X86 : List XItem := framed (envU256Body 320 2)
def sloadX86  : List XItem := framed sloadBody
def stopX86   : List XItem := framed stopBody
def jumpdestX86 : List XItem := framed (jumpdestBody 1)
def invalidX86 : List XItem := framed invalidBody
def returnX86 : List XItem := framed returnBody
def revertX86 : List XItem := framed revertBody
def jumpX86   : List XItem := framed (jumpBody 8)
def jumpiX86  : List XItem := framed (jumpiBody 10)
def blobhashX86 : List XItem := framed (blobhashBody 3)
def blobbasefeeX86 : List XItem := framed (envU256Body 568 2)
def mstore8X86 : List XItem := framed (mstore8Body 3)
def keccakX86 : List XItem := framed (keccak256Body 30)
def copyX86   : List XItem := framed (copyBody "_eita_helper_calldatacopy" 3)
def mcopyX86  : List XItem := framed (mcopyBody "_eita_helper_mcopy" 3)
def clzX86    : List XItem := framed (clzBody 5)
def msizeX86  : List XItem := framed (msizeBody 2)
def tloadX86  : List XItem := framed tloadBody
def expX86    : List XItem := framed (expBody 10 50)
def sstoreX86 : List XItem := framed (sstoreBody 2300)
def tstoreX86 : List XItem := framed tstoreBody
def selfdestructX86 : List XItem := framed (selfdestructBody 5000)
def extcodecopyX86 : List XItem := framed extcodecopyBody
def log0X86   : List XItem := framed (logBody 0 375)
def log4X86   : List XItem := framed (logBody 4 1875)
def createX86 : List XItem := framed createBody
def create2X86 : List XItem := framed create2Body
def callX86   : List XItem := framed (callFamilyBody "call" 0 0 true)
def staticcallX86 : List XItem := framed (callFamilyBody "staticcall" 3 1 false)

/-- Every helper call in every covered body sits at rsp ≡ 0 (mod 16), so the
    callee sees the SysV-required ≡ 8. -/
theorem helper_calls_are_aligned :
    covered.all (fun p => helperCallsAligned (x86Body p)) = true := by native_decide

/-- Every instruction of every framed handler has an x86 lowering, and the
    only relocations left for a loader are the helper table's abs64 slots —
    no branch displacement ever escapes the image. -/
theorem framed_handlers_lower :
    [mstoreX86, mloadX86, addX86, subX86, andX86, orX86, xorX86, notX86,
     eqX86, iszeroX86, ltX86, gtX86, sltX86, sgtX86,
     popX86, push0X86, push1X86, push2X86, push8X86, push9X86, push32X86,
     dup1X86, dup2X86, swap1X86, swap2X86,
     mulX86, divX86, sdivX86, modX86, smodX86, shlX86, shrX86, sarX86, byteX86, sextX86,
     addmodX86, mulmodX86, pcX86, gasX86, envU64X86, envU256X86, sloadX86,
     stopX86, jumpdestX86, invalidX86, returnX86, revertX86, jumpX86, jumpiX86, mstore8X86,
     blobhashX86, blobbasefeeX86,
     keccakX86, copyX86, mcopyX86, clzX86, msizeX86, tloadX86, expX86,
     sstoreX86, tstoreX86, selfdestructX86, extcodecopyX86,
     log0X86, log4X86, createX86, create2X86, callX86, staticcallX86].all (fun its =>
      its.all (fun it => !isUnlowered it) &&
      (assembleWith faultSyms its).2.all (fun r => r.kind == .abs64)) = true := by
  native_decide


/-! ## Register aliasing is safe (stage 5, the first x86-64 Linux divergence)

The x86-64 register map gives several `Reg`s one home: x1/x15 → rdx,
x2/x17 → rsi, x3/x4/x16 → rdi. That is sound only while no two of them are
live at once. The CALL family's gas load (`ldp x15, x16 ; ldp x0, x1`) broke
it — limb 3 landed on limb 0 — and nothing said so until a sub-frame on x86-64 Linux
started with gas 0. This check is conservative (mention ranges, not exact
liveness): for every x86-64 body, no two registers with the same home have
overlapping mention ranges. -/

/-- Registers that share an x86-64 home. -/
def aliasPairs : List (Reg × Reg) :=
  [(.x1, .x15), (.x2, .x17), (.x3, .x4), (.x3, .x16), (.x4, .x16)]

/-- The pairs whose mention ranges overlap in a body. -/
def aliasOverlaps (p : List AInstr) : List (Reg × Reg) :=
  aliasPairs.filter (fun (a, b) =>
    match Evm.CL.Pressure.liveRange p a, Evm.CL.Pressure.liveRange p b with
    | some (a0, a1), some (b0, b1) => a0 ≤ b1 && b0 ≤ a1
    | _, _ => false)

-- **No two aliased registers are mentioned in overlapping ranges**, in any
-- covered x86-64 body (`no_alias_overlap`, enabled once the overlaps are fixed).

end Evm.CL.X86Handler
