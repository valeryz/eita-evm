/-
  Evm.CL.ARM64.RunProgram — emit `_eita_execute_program`, the native binding
  of the chunk-dispatch trampoline `IR.executeProgram` (Execute.lean).

  The Lisp replay's `run-jit-frame` hand-mirrored the dispatch loop;
  this emits it once, case-for-case against the spec:

    executeProgram 0 _ _            = .error .outOfGas      → return 2
    | prog.lookup evm.pc = none     = .error .invalidJumpDest → return 1
    | execute ch evm; halted        = .ok evm'              → return 0
    | otherwise                     = loop on evm'

  The host maps the nonzero returns: 1 (manifest miss) is a compiler
  coverage gap — logged, frame finished on the interp tier, never
  silent; 2 (fuel) is the spec's `.outOfGas` convention for the
  transition bound (the host passes gas_left+1, which dominates the
  chunk-transition count since every transition charges ≥ 1 gas).

  C ABI (AAPCS64):

    uint64_t eita_execute_program(EvmState *state,          // x0
                              const uint64_t *entries,  // x1: manifest
                              void (*run_chunk)(EvmState*, void*), // x2
                              uint64_t fuel);           // x3

  `entries` is the DISPATCH TABLE the host loader builds from the
  program's `(pc, fn)` manifest (`_eita_jit_entries`, JIT.lean): a length
  `n`, then `n` u64 words indexed by pc — `fn` where a chunk starts, 0
  where none does (`RunProgramDenote.build`). The lookup is one bounds
  check and one load. (It was a linear scan of the pairs: ~400 entries for
  a median near-tip contract, ~1,800 for an 18.8 KB one, paid at EVERY
  chunk transition — it made the JIT tier 2x slower than the interpreter
  on mainnet 24,538,111.) The chunk runner is passed in because
  `_eita_run_chunk` is a per-program symbol (RTLD_LOCAL) while this loop
  lives once in libeita.
-/

import Evm.CL.Frame

namespace Evm.CL.ARM64.RunProgram

def codeSpec : String :=
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  ".global _eita_execute_program\n" ++
  ".p2align 2\n" ++
  "_eita_execute_program:\n" ++
  "    stp   x29, x30, [sp, #-48]!\n" ++
  "    mov   x29, sp\n" ++
  "    stp   x19, x20, [sp, #16]\n" ++
  "    stp   x21, x22, [sp, #32]\n" ++
  "    mov   x19, x0\n" ++                       -- state
  "    mov   x20, x1\n" ++                       -- manifest
  "    mov   x21, x2\n" ++                       -- run_chunk
  "    mov   x22, x3\n" ++                       -- fuel
  "Lrp_loop:\n" ++
  -- `if evm'.halted then .ok evm'` (also covers an already-halted entry)
  "    ldrb  w9, [x19, #128]\n" ++
  "    cbnz  w9, Lrp_halted\n" ++
  -- `executeProgram 0 _ _ = .error .outOfGas`
  "    cbz   x22, Lrp_fuel\n" ++
  "    sub   x22, x22, #1\n" ++
  -- `prog.lookup evm.pc` — one load from the pc-indexed table (0 = no entry)
  "    ldr   x9, [x19, #0]\n" ++                 -- pc
  "    ldr   x10, [x20]\n" ++                    -- table length
  "    cmp   x9, x10\n" ++
  "    b.hs  Lrp_miss\n" ++                      -- pc past the table
  "    add   x11, x20, #8\n" ++                  -- fn[0]
  "    ldr   x1, [x11, x9, lsl #3]\n" ++         -- fn[pc]
  "    cbz   x1, Lrp_miss\n" ++                  -- no chunk starts at pc
  -- `execute ch evm` via the per-program chunk runner
  "    mov   x0, x19\n" ++
  "    blr   x21\n" ++
  "    b     Lrp_loop\n" ++
  "Lrp_halted:\n" ++
  "    mov   x0, #0\n" ++
  "    b     Lrp_ret\n" ++
  -- `| none => .error .invalidJumpDest`
  "Lrp_miss:\n" ++
  "    mov   x0, #1\n" ++
  "    b     Lrp_ret\n" ++
  "Lrp_fuel:\n" ++
  "    mov   x0, #2\n" ++
  "Lrp_ret:\n" ++
  "    ldp   x21, x22, [sp, #32]\n" ++
  "    ldp   x19, x20, [sp, #16]\n" ++
  "    ldp   x29, x30, [sp], #48\n" ++
  "    ret\n"

/-! ## As instructions (stage 4t) -/

open Evm.CL.AsmCore Evm.CL.Frame in
def instrs : List AInstr :=
  [.textSection] ++ header "_eita_execute_program" ++
  [ .stpPreSp .x29 .x30 48, .movFromSp .x29, .stpSp .x19 .x20 16, .stpSp .x21 .x22 32,
    .movReg .x19 .x0, .movReg .x20 .x1, .movReg .x21 .x2, .movReg .x22 .x3,
    .label "Lrp_loop",
    .ldrbOff .x9 .x19 128, .cbnzWLbl .x9 "Lrp_halted", .cbzLbl .x22 "Lrp_fuel", .subImm .x22 .x22 1,
    .ldrOff .x9 .x19 0, .ldrBase .x10 .x20, .cmpReg .x9 .x10, .bcLbl .hs "Lrp_miss",
    .addImm .x11 .x20 8, .ldrLsl3 .x1 .x11 .x9, .cbzLbl .x1 "Lrp_miss",
    .movReg .x0 .x19, .blr .x21, .bLbl "Lrp_loop",
    .label "Lrp_halted", .movImm .x0 0, .bLbl "Lrp_ret",
    .label "Lrp_miss", .movImm .x0 1, .bLbl "Lrp_ret",
    .label "Lrp_fuel", .movImm .x0 2,
    .label "Lrp_ret", .ldpSp .x21 .x22 32, .ldpSp .x19 .x20 16, .ldpPostSp .x29 .x30 48, .ret ]

def code : String := Evm.CL.Frame.text instrs

theorem code_derived : code = codeSpec := by native_decide

end Evm.CL.ARM64.RunProgram
