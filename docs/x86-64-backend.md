# The x86-64 backend

Eita runs on x86-64 as well as ARM64, on the threaded interpreter. Both backends are emitted
from the same Lean instruction layer, so a block replayed on
the two machines is a cross-check that neither backend alone gives. Every x86-64 artifact is
printed from Lean; nothing in it is hand-written assembly.

## 1. What is shared, what is per target

**ISA-neutral, shared unchanged:**

- The IR and gas layer. Every handler's static cost comes from `IR.Op.metadata`, never from the
  asm; the SSTORE/CALL gas plans, `MemExpandSpec`, the host-seam decisions emitted to
  `host.lisp`, and the chunk/pre-charge structure are independent of the target.
- `AsmCore.Mach`, the abstract machine the handler correctness theorems are stated over. It has
  no registers and no flags: stack slots, memory, gas, state fields. Those theorems hold for any
  target.
- The instruction layer `AsmCore.AInstr`: structured instructions with a denotation, which each
  target lowers. The program registry (`Interp.handlerProgs`) is the source of both targets'
  interpreter files.

**Per target:**

| | ARM64 | x86-64 |
|---|---|---|
| lowering | `AInstr` → AArch64 text and words (`AsmEncode`) | `Lowering.emitX86` (text), `X86Items.x86Items` → `X86Encode.encode` (bytes) |
| encoding | fixed 4-byte words | variable length (ModRM/SIB/REX); branch relaxation (`Relax.lean`) chooses rel8/rel32 |
| interpreter file | `c/handlers.S` | `c/handlers-x86-elf.S` (`lake exe emitX86Interp elf`) |
| host gas routines | `ARM64.CallGas`, `ARM64.SstoreGas` | `X86CallGas`, `X86SstoreGas` |
| JIT chunks (Lean model) | `ARM64.JIT.emitChunkGen` over `ChunkOut` | the same algorithm, x86-64 instance (`X86JIT.lean`) |

The x86-64 Linux build also links `csu_shim`, which supplies `__libc_csu_init`/`__libc_csu_fini`
for the Lean toolchain's old-style `Scrt1.o` against glibc ≥ 2.34. The baseline is
**x86-64-v3** (`-march=x86-64-v3`): BMI2 `shlx/shrx/sarx` keep a variable shift count out of
`cl`, `mulx` avoids the implicit `rdx`, and the handlers use `lzcnt`.

## 2. Registers (`lean/Evm/CL/Target.lean`)

ARM64 commits 16 registers to named jobs — TOS limbs ×4, NOS limbs ×4, and eight singletons
(state, pc, gas, sp, stackBase, dispatch, codeBase, cont) — plus 4 scratch, so 20 of its 31.
x86-64 has 16 general-purpose registers, one of which is `rsp`. Two singletons are not needed:

- `cont` — ARM64 threads through `br x27` because `adr`+`br` is that ISA's computed return.
  x86-64 has `call`/`ret` with a return-stack-buffer predictor: subroutine threading uses the
  hardware stack and needs no register.
- `dispatch` — ARM64 keeps the 256-entry table base in x25. x86-64 reaches it RIP-relatively:
  `jmp *table(,%rax,8)`.

That leaves exactly enough for the TOS cache with 5 scratch registers:

```
r8-r11  TOS limbs 0..3        rbx  EvmState*     r12  stack base
rax,rcx,rdx,rsi,rdi  scratch  rbp  pc            r13  sp (byte offset, 32·sp)
rsp     hardware stack (threading)               r14  code base
                                                 r15  gas
```

10 named + 5 scratch + `rsp` = 16. **There is no NOS cache.** The second stack item is a memory
operand, `[r12 + r13 - 64 + 8l]` for limb l; no gadget writes a NOS register, and x86 arithmetic
takes a memory operand, so a NOS read is an addressing mode. r13 holds sp as a byte offset
because the SIB scale is 1/2/4/8. With no NOS cache the memory read is the specification and the
register cache the refinement; on x86-64 there is nothing to keep in step below the TOS.

Five scratch registers cover every gadget without a spill. The measured scratch pressure peaks at
five (`Pressure.lean`), and the temporary map is forced: the interference graph is K₆ minus one
edge, so x4 and x16 share `rdi`. The shared homes (x1/x15, x2/x17, x3/x4/x16) are aliasing hazards
for callback-argument staging; `X86Alias.no_alias_hazards` checks every emitted body by exact
liveness.

## 3. The interpreter and the host gas routines

`lake exe emitX86Interp elf` prints the whole x86-64 threaded interpreter: the `X86Run` frame with
a run loop that calls handlers (terminators `jmp` to `sync_and_ret`, which unwinds through
`EvmState.frame_sp`), every registry handler through `Op.instrsX86?` and the x86-64 lowering, the
per-fork address tables and `set_fork`.

The host-facing gas routines (`X86CallGas`, `X86SstoreGas`) are the same plans as `AInstr`
programs over the registers whose x86-64 homes are the SysV argument registers; the six SSTORE
predicates are packed into one register as bits. They are proved under `AsmSem`
(`X86CallGasSem`, `X86SstoreGasSem`: program → plan → spec, as on ARM64) and byte-exact against
clang. `libeita.so` links natively on x86-64 Linux with every `eita_*` symbol the replay loads.

## 4. The JIT chunks (`lean/Evm/CL/X86JIT.lean`)

The chunk JIT's runtime is not part of this repository for now (see the README: on real replays
it does not yet beat the threaded interpreter); its Lean model, described here, and its proofs
are. The chunk algorithm is one definition with two instances; the ARM64 output is byte-identical to
its single-target form.

- `ChunkOut.callSym` — an op site (enter a flat handler, continue at the label after) is
  distinct from `tailSym` (a terminator). ARM64 prints both as `b sym`; x86-64 prints
  `call [rip + Lsym_sym]` and, for a terminator, adds `jmp Lx_sync`.
- `FlushTarget` — the region flush (`emitRegionFlushT`) is one algorithm over a record of target
  choices: the right-operand quad of a binary core (NOS registers on ARM64; the temporaries
  x15/x17/x16/x0 — rdx/rsi/rdi/rax — on x86-64, keeping rcx for the address scratch that `sbcsZr`
  also needs), immediates, scratch-slot addressing, frame open/close (`32·n + 8` on x86-64 so
  helper call sites sit at rsp ≡ 0 mod 16), fault jumps, helper argument registers and call form,
  base-register stores, and the cache reload (TOS only on x86-64).

A chunk is made of the instruction forms the handlers' lowering already produces (`spScale`, then
`x86Items`). Every external reference is an abs64 slot (`QuadSym`, relocation kind 5, eight bytes
the loader writes); the fault symbols and `_eita_sync_and_ret` are reached through
per-chunk trampolines (`lea rax, [rip + Lsym_x]; jmp [rax]`, rax dead on every such path), so a
mapped image needs no `rel32` reach into `libeita.so`. A gas gadget is `sub r15, n; jb Lx_oog` —
`GInstr.denote`'s `n ≤ gas` as the carry flag. `_eita_execute_program` is an `XItem` frame unit in
`X86Interp`; the image's chunk runner is `X86Run`'s prologue plus `jmp rsi`.

**Size budget.** Chunks overlap (each runs through interior JUMPDESTs to its terminator), so a
contract with many JUMPDESTs can expand to hundreds of millions of chunk ops. Over 4,000,000 chunk
ops (`maxProgramOps`) the emitter refuses the program.

## 5. The x86-64 semantics (`X86Sem.lean`, `X86FlagProv.lean`, `X86SemCtrl.lean`, `X86Xfer.lean`)

`X86Sem` gives the lowering's instruction subset its own machine — registers, CF/ZF/SF/OF as the
SDM defines them for `add`/`sub`/`adc`/`sbb`/logic, byte memory, local-label fragments with fault
exits (`xrun`), SysV helper calls as an oracle — and states the **lowering simulation**:
`x86Items i` run on it tracks `AsmRun.step i`, under a relation indexed by

- the **live set** (x1/x15, x2/x17, x3/x4/x16 share a home; NOS x10-x13 is the word at
  `[r12 + r13 - (64 - 8l)]`), the semantic counterpart of `X86Alias.no_alias_hazards`, and
- the **flag provenance**: after a `sub`-type instruction every lowered condition agrees (x86
  CF = borrow = ARM ¬C); after an `add`-type one, or a `tst`, only `eq`/`ne`/`lt` do — ARM's `lo`
  is the carry CLEAR, which x86's `jb` is not. `adc`/`bcsOog` need `add` provenance,
  `sbb`/`bloOog`/`bhiOog` need `sub`, and the x86 `add`/`sub`/logic/shift/`imul`/`lzcnt`/`shld`
  clobber flags their ARM originals leave alone. Shifts and `imul` leave the flags opaque
  (`clobXF`), so nothing downstream can depend on them.

Proved (no `sorry`): the relation through register writes, stores and rsp moves; every data
instruction form the lowering produces (the two-operand expansion `twoOp`, the three-way `cmov`
expansion, the carry chains `adcs`/`sbcs`/`sbcsZr` per polarity, compares, shifts, `mulReg`,
`addLsl` as `lea`, `csel`/`cset`, `rev`, `mvn`, moves, loads and stores, the sp adjustments); and
the x86-64 gas gadgets directly on the x86 machine (`charge_x86`, `handBack_x86`, `retake_x86`:
`sub r15, n ; jb Lx_oog` is `GInstr.denote`, exiting to the OOG trampoline iff it halts).

`X86FlagProv.no_flag_provenance_hazards` is the static side of the same fact: a forward dataflow
over every handler body, gas routine and corpus chunk piece, checking each flag consumer against
every provenance that can reach it.

**Control** (`X86SemCtrl.sim_run`): for a fragment with an annotation — the live set and
provenance code may assume at each local label — `Ok` threads the live set and provenance down
the fall-through path, checking every branch against its target's annotation, and `LabelsOk` says
every local branch target is defined. Under `Ok`, `LabelsOk` and the relation at entry,
`AsmRun.run` of the fragment and `xrun` of its lowering both fall off the end, or both `ret`, with
the exit annotation related. It covers helper calls (`blSym` against `call [rip + Lsym_h]`, under
the x86 argument convention: x3, x2, x1, x14 in the SysV homes rdi, rsi, rdx, rcx; the fourth only
for `addmod`/`mulmod`) and far exits (`bTramp`/`bcTramp` against `jmp`/`jcc Lx_<sym>`). Dead code
after a trampoline exit is marked by the unhomed `x5`, which makes the relation unsatisfiable.

**The region flush**, at two levels:

- `AsmRun` level (`X86/FlushSemX.lean`, `MemCommitSemX.lean`, `FlushScaleX.lean`,
  `FlushMainX.lean`): `flush_runX_scaled` — the program `emitRegionFlushT x86Flush r` after the
  lowering's `spScale` pass leaves the EVM stack at `SymStack.denote`, x23 at `32 · newDepth`, the
  TOS reloaded, the `32n + 8` frame restored, the memory commit done with the spec's expansion
  gas, for every region.
- x86-64 machine level (`X86Xfer.lean`, `X86/FlushOkX.lean`): `flush_x86` — `xrun` of the lowered
  flush reaches `.done` in a state related to the `AsmRun` state above. The bridge is `sim_run`,
  fed by a proved liveness/provenance transfer (`xfer`, `xfer_sound`); each concrete piece is
  certified by kernel reduction with symbolic immediates.

The stack-cache assumptions both interpreters rely on are listed in
[`trusted-surface.md`](trusted-surface.md).

**Not proved:** the chunk around the flush (head charge, op sites, terminators) and the
trampolines' own code; the encoder's bytes against the ISA (gated against clang, below).

## 6. Gates

| script | checks |
|---|---|
| `scripts/verify-x86-emit.sh` | every structured gadget's x86-64 text lowering assembles (the Lean side proves coverage: no «unlowered» marker) |
| `scripts/verify-x86-encode.sh` | `X86Encode.encode` byte sequences equal clang's for the same text |
| `scripts/verify-x86-items.sh` | the two lowerings agree: `encode (x86Items i)` = clang (`emitX86 i`) for every instruction of the gadget set (`X86Items.lowerings_align`) |
| `scripts/verify-x86-asm.sh` | whole gadgets, the gas routines, the frame, `execute_program` and the corpus chunks assembled by `X86Asm.assemble` (with relaxation) equal clang's bytes |
| `scripts/verify-x86-interp.sh` | the interpreter file assembles in both flavours (Mach-O, ELF) with no «unlowered» marker |
| `scripts/verify-x86-run.sh` | runs `X86Asm` output (`X86RunVectors`) and checks each program's result (Rosetta 2 on Apple Silicon) |

The Lean checks `x86_chunks_lower`, `x86_chunks_only_abs64` and `x86_chunks_no_alias` run over the
fixture corpus's chunks. Conformance on x86-64 Linux is the same as on ARM64: the fixture
battery ([`testing.md`](testing.md)), and replayed ranges compared line for line
with the ARM64 logs (per-tx gas against the receipts, the header gate).
