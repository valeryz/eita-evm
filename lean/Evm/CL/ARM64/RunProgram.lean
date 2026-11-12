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

end Evm.CL.ARM64.RunProgram
