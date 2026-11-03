# An x86-64 backend (#238) — what has to be derived first

Goal: run the replay (threaded interpreter **and** chunk JIT) on x86-64 as well as
ARM64, so a second, cheaper machine can carry a chain — and so two independently
lowered backends agreeing on gas and state root become a cross-check that neither
one alone can give.

It is not automatically derivable today. This file records why, what the real
boundary is, and the order that fixes it. The register decision is already
machine-checked in `lean/Evm/CL/Target.lean`; everything else below is the plan.

## Where the ISA boundary actually sits (measured, 2026-10-13)

**Already ISA-neutral and reusable unchanged:**

- The IR and gas layer. Every handler's static cost comes from `IR.Op.metadata`,
  never from the asm; the SSTORE/CALL gas plans, `MemExpandSpec`, the host-seam
  decisions emitted to `host.lisp`, and the chunk/pre-charge structure are all
  independent of the target.
- `AsmCore.Mach` — the abstract machine the **37 correctness theorems** (1
  `sorry`) are stated over. It has no registers and no flags: stack slots,
  memory, gas, state fields. Those theorems carry to any target as they are.

**ARM64-specific, in four pieces:**

| | what | why it matters |
|---|---|---|
| 1 | **~660 lines of raw ARM64 mnemonic strings**: 233 in `AsmCore.lean`, 137 `ARM64.lean`, 120 `ARM64/JIT.lean`, 89 `SstoreGas`, 46 `CallGas`, 26 `RunProgram`, 9 `Interp` | these have **no denotation at all** — nothing can be derived for a string, so this is the blocking work |
| 2 | `AsmEncode.Insn.encode : Insn → UInt32`, and `Item.width` = 4 | fixed-width encoding is baked into label resolution; x86-64 is variable-length |
| 3 | `AsmCore.Reg` is `x6 \| x7 \| … \| x24`, and `AInstr` is an ARM64 instruction subset (`addLsl5`, `cselHi`, `b.cs`) | there is no role layer for a second target to instantiate |
| 4 | Platform runtime: Mach-O↔ELF transform for `handlers.S`, the RW/RX double-mapped code arena, `eita_clear_icache` (`csu_shim` supplies `__libc_csu_init`/`__libc_csu_fini` for the Lean toolchain's old-style `Scrt1.o` against glibc ≥ 2.34) | the easy part, and x86-64 Linux is *friendlier* than Apple Silicon |

Piece 1 is also the gap that hid #24 (MSIZE returning `mp` instead of the aligned
size), #260 (CALL memexp u256 truncation), the chained-`sbcs` Z-flag trap, and the
`retakeRem` unchecked gas re-take. So stage 1 pays for itself even if the x86
target is never built.

## The register decision (settled; `lean/Evm/CL/Target.lean`)

ARM64 commits **16 registers to named jobs** — TOS limbs ×4, NOS limbs ×4, and
eight singletons (state, pc, gas, sp, stackBase, dispatch, codeBase, cont) — plus
4 scratch, so 20 of its 31. x86-64 has 16 GPRs, one of which is `rsp`.

**Two of the eight singletons are not needed on x86-64:**

- `cont` — ARM64 threads through `br x27` because `adr`+`br` is how that ISA
  gets a computed return. x86-64 has `call`/`ret` with a return-stack-buffer
  predictor: subroutine threading uses the hardware stack and needs no register.
  It is likely *faster* than the indirect branch, since `ret` is predicted.
- `dispatch` — ARM64 keeps the 256-entry table base in x25 because it cannot
  address it otherwise. x86-64 reaches it RIP-relatively: `jmp *table(,%rax,8)`.

That is exactly enough for **TOS to stay cached with 5 scratch registers**:

```
r8-r11  TOS limbs 0..3        rbx  EvmState*     r12  stack base
rax,rcx,rdx,rsi,rdi  scratch  rbp  pc            r13  sp
rsp     hardware stack (threading)               r14  code base
                                                 r15  gas
```

10 named + 5 scratch + `rsp` = exactly 16, nothing left over. **NOS is dropped**:
keeping it would leave ONE scratch register, on the ISA whose two-operand
destructive forms (`add dst, src` overwrites `dst`) need *more* scratch than
ARM64's three-operand forms, not less. The second stack item is read from
`[stackBase + 32·(sp-2)]`.

Baseline is **x86-64-v3** (Haswell+): BMI2 `shlx/shrx/sarx` keeps a variable
shift count out of `cl`, and `mulx` avoids the implicit `rdx`. Without v3 the
scratch pool would have to reserve both.

Dropping NOS also retires a bug class rather than porting it. The ARM64 handlers
may read NOS registers only under "if sp ≥ 2 then stack memory at sp-2 equals
x10-x13"; #272 was precisely a speculative `stack[depth-2]` read one slot below
the live stack. A target with no NOS cache has nothing to keep in step. Note the
direction this implies: **the memory read is the specification and the register
cache is the refinement**, which makes x86-64 the simpler instantiation.

## Status (2026-10-14)

Stages 1 and 2 are closed. Every hand-written asm construct in the threaded
interpreter now has a denotation (stage 1, `c382d3f`), and the instruction layer
is target-parametric with a working x86-64 text lowering (stage 2, `48566af`).

| | commit | result |
|---|---|---|
| 1 | `c382d3f` | all asm denoted, no `sorry`; found two live consensus bugs (JUMP/JUMPI and RETURN/REVERT u256 truncation) while writing the denotations |
| 2a | `5039207` | branch relaxation proved monotone + terminating; ARM64's single pass is the degenerate case |
| 2b | `df14a00` | scratch pressure measured: peaks 4,4,5,5,5,5 — five is exactly enough, zero headroom |
| 2c | `75c3c3c` | the temporary map is FORCED: interference graph is K₆ minus one edge, so x4/x16 must share rdi |
| 2d | `66f75c3` | two-operand lowering classified; no gadget needs a spill |
| 2e | `96eebf2` | one emitter, two targets; NOS costs nothing (read-only + memory operands) |
| 2f | `48566af` | `scripts/verify-x86-emit.sh`: 6/6 gadgets assemble, 310 instructions |

Measured outcomes that changed the plan:

* **NOS stays dropped and costs nothing.** No gadget writes a NOS register, and
  x86 arithmetic takes a memory operand, so a NOS read is an addressing mode.
  The price is a representation difference: r13 holds sp as a byte offset
  (32·sp) rather than a word index, because the SIB scale is 1/2/4/8.
* **No spill slot anywhere.** Five scratch registers cover every gadget, with
  the assignment determined rather than chosen.
* **~25% more instructions** (242 → 302 across the gadget set), a constant
  factor rather than a multiple.
* **The assembler is a required gate, not a formality.** Coverage proofs and
  hand spot-checks passed an unencodable address; `clang -arch x86_64` found it
  in one line. See stage 2f.

**2026-10-15.** Stage 3 closed (`X86Encode`/`X86Items`, 611 encodings and 3572
lowerings gated against clang; 108 programs run under Rosetta). Stage 4 has its
first native result: `lake exe emitX86Interp elf` prints the whole x86-64
threaded interpreter — the same program registry (`Interp.handlerProgs`, now
the source of the ARM64 file too, byte-identical), every one of its 292
handlers through `Op.instrsX86?` and the x86-64 lowering, the `X86Run` frame
with a run loop that CALLS handlers (terminators `jmp` to `sync_and_ret`,
which unwinds through the new `EvmState.frame_sp`), the per-fork address
tables and `set_fork` — and `make test_interp` on x86-64 Linux (Zen 3, Linux) passes
ADD/MUL/SUB/SHL/KECCAK on the first run. Gates: `verify-x86-interp.sh` (both
flavours assemble, no unlowered form), `verify-x86-asm.sh` (frame bytes ==
clang). Also closed on the ARM64 side: the gas routines are now DENOTED
(`AsmSem`, `CallGasSem`, `SstoreGasSem`: program → plan → spec).

The host-facing gas routines followed (`X86CallGas`, `X86SstoreGas`): the
same plans as `AInstr` programs over the registers whose x86-64 homes are the
SysV argument registers, the six SSTORE predicates packed into one register
as bits (nine caller-saved registers, not thirteen), proven under `AsmSem`
(`X86CallGasSem`, `X86SstoreGasSem`: program → plan → spec, as on ARM64) and
byte-exact against clang whole (`verify-x86-asm.sh`, 19/19). `libeita.so`
links natively on x86-64 Linux with every `eita_*` symbol the replay dlsyms.

**Stage 5, first gate (2026-10-15).** `src/evm/` on x86-64 Linux with
`libeita.so` built from the derived x86-64 file, interp tier
(`EITA_NO_JIT=1`): LegacyTests/Constantinople ValidBlocks **1393/1393**, the
Mac's number. The first run was 308/512 with three SBCL memory faults; every
cause was a register-aliasing hazard in callback-argument staging that the
Rosetta vectors could not see (their callbacks ignore their arguments) plus
one `spScale` gap — see the stage-5 commits and `X86Alias.no_alias_hazards`
(exact liveness, now a theorem) and `c/test_interp.c`'s checking callback.

Then the Arc mainnet cross-backend diff (lazy mode, cache-only, interp tier,
blocks 23501090…): the Mac and x86-64 Linux logs agree line for line on every
completed block, every transaction `✓ exact` against its on-chain receipt
gas. GST (LegacyTests/Cancun) per directory: x86-64 Linux == Mac on every
directory compared (both tiers carry the same pre-existing interp-tier
failures — `scripts/compare-batteries.sh`).

### Stage 6: the x86-64 JIT tier (`lean/Evm/CL/X86JIT.lean`)

The chunk algebra (`ARM64.JIT.emitChunkGen` over `ChunkOut`) got its x86-64
instance. Three changes to the shared algorithm, each keeping the ARM64 output
byte-identical (`chunk_text_derived`, `handlers.S`, the jit-emit and snapshot
gates):

* `ChunkOut.callSym` — an op site (enter a flat handler, continue at the label
  after) is now distinct from `tailSym` (a terminator). ARM64 prints both as
  `b sym`; x86-64 prints `call [rip + Lsym_sym]` and, for a terminator, adds
  `jmp Lx_sync`.
* `FlushTarget` — the region flush (`emitRegionFlushT`) is one algorithm over
  a record of target choices: the right-operand quad of a binary core (NOS
  registers on ARM64; the temporaries x15/x17/x16/x0 — rdx/rsi/rdi/rax — on
  x86-64, keeping rcx for the address scratch that `sbcsZr` also needs),
  immediates, scratch-slot addressing, frame open/close (`32·n + 8` on x86-64
  so helper call sites sit at rsp ≡ 0 mod 16), fault jumps, helper argument
  registers and call form, base-register stores, and the cache reload (TOS only
  on x86-64). `armFlush` reproduces the stage-4s text exactly.
* `spScale` learned `add d, x23, k` (the exit-prefix store addresses); no
  handler used the form, so the interpreter text is unchanged.

Everything else is reuse: the x86-64 pieces go through the handlers' own
lowering (`spScale` then `x86Items`), so a chunk is made of the instruction
forms the batteries already run. Every external reference is an abs64 slot
(`QuadSym`, relocation kind 5, which the SBCL loader writes as eight bytes);
the fault symbols and `_eita_sync_and_ret` are reached through per-chunk
trampolines (`lea rax, [rip + Lsym_x]; jmp [rax]`, rax dead on every such
path), so a mapped image needs no `rel32` reach to `libeita.so`. The gas
gadgets are `sub r15, n; jb Lx_oog` — `GInstr.denote`'s `n ≤ gas` as the carry
flag. `_eita_execute_program` is an `XItem` frame unit in `X86Interp`
(manifest and runner in r12/r13, SIB-encoded bases); the image's chunk runner
is `X86Run`'s production prologue plus `jmp rsi`. `emitJIT` picks the image for
the host (`System.Platform.target`; `EITA_JIT_ARCH` overrides).

Gates added: `x86_chunks_lower` / `x86_chunks_only_abs64` /
`x86_chunks_no_alias` over the fixture corpus (the alias gate's `succ` had an
off-by-one for a body that ENDS with a conditional branch — a handler never
does, a chunk piece does — which Lean reported as an index panic rather than
a false pass); the 16 corpus chunks and `execute_program` joined the
byte-vs-clang `verify-x86-asm.sh` battery (36/36).

Status: x86-64 Linux ValidBlocks at the JIT tier 1393/1393 in 67 s (frames-jit
109 735, frames-interp 0, manifest-misses 0 — every frame on the JIT, no
dispatch gap); GST (LegacyTests/Cancun, 85 directories) at the JIT tier on x86-64 Linux:
every directory equals the interpreter tier or betters it (stEIP1559,
stTimeConsuming and VMTests/vmArithmeticTest, which exhaust the interpreter
tier's heap, pass in full on the JIT; stLogTests, VMTests/vmLogTest and
stMemoryTest have 30 fewer failures each; the rest are identical), ~2 M JIT
frames. Two anomalies during the battery — 2621 no-jit codes in stStackTests
and 612 manifest misses in vmBitwiseLogicOperation — were artefacts of the
box swap-thrashing with a budget-less daemon the OOM killer took at 26 GB;
clean reruns of both directories are all-JIT with zero misses, matching the
Mac's ARM64 JIT line for line (`jit: codes=355 … frames-jit=741`).
stQuadraticComplexityTest reruns to the interpreter tier's 188/2 with its two
over-budget contracts logged as `jit-fallback … over the JIT tier's budget`. The Arc mainnet range (23501090–23501300, 2155
transactions) at the JIT tier on x86-64 Linux is line-for-line the interpreter tier's
log — every transaction exact against its receipt, zero gate mismatches, cache
only (`rpc-calls=0`), JIT images loaded for every frame.

A size budget joined `emitJIT` on the way: chunks overlap (each runs through
interior JUMPDESTs to its terminator), so stQuadraticComplexityTest's
21 126-JUMPDEST contract is 223 M chunk ops and took the daemon an hour per
fork set on either target; over 4 M chunk ops the daemon now refuses loudly
and the replay counts the program `no-jit` and runs it on the interpreter
tier. The per-chunk image append was quadratic too and is now one
preallocated concatenation (output byte-identical). Unproven, by inspection + batteries: the x86-64 gas
gadgets and flush pieces against `GInstr.denote` / the ARM64 flush (no x86-64
machine semantics yet; `AsmSem` is ARM64-only).

## The x86-64 semantics (2026-10-16, `lean/Evm/CL/X86Sem.lean`, `X86FlagProv.lean`)

Until now the x86-64 gas routines and gadgets were proven under the ARM flag
model (`AsmSem`) and trusted through the lowering's byte identity with clang.
`X86Sem` gives the lowering's instruction subset its own machine — registers,
CF/ZF/SF/OF as the SDM defines them for `add`/`sub`/`adc`/`sbb`/logic, byte
memory, local-label fragments with fault exits (`xrun`), SysV helper calls as
an oracle — and states the **lowering simulation**: `x86Items i` run on it
tracks `AsmRun.step i`, under a relation indexed by

* the **live set** (x1/x15, x2/x17, x3/x4/x16 share a home; NOS x10-x13 is
  the word at `[r12 + r13 - (64 - 8l)]`), the semantic counterpart of
  `X86Alias.no_alias_hazards`, and
* the **flag provenance**: after a `sub`-type instruction every lowered
  condition agrees (x86 CF = borrow = ARM ¬C); after an `add`-type one, or a
  `tst`, only `eq`/`ne`/`lt` do — ARM's `lo` is the carry CLEAR, which x86's
  `jb` is not. `adc`/`bcsOog` need `add` provenance, `sbb`/`bloOog`/`bhiOog`
  need `sub`, and the x86 `add`/`sub`/logic/shift/`imul`/`lzcnt`/`shld`
  clobber flags their ARM originals leave alone.

Proven so far (0 sorry): the relation through register writes, stores and
rsp moves; the two-operand expansion (`twoOp`) and the three-way `cmov`
expansion; `addReg`/`subReg`/`and3`/`orr3`/`eor3`, `adds`/`subsReg`,
`adcs`/`sbcs`/`sbcsZr` (the carry chain, polarity-specific), `subsImm`,
`cmpImm`/`cmpImmWHex`/`cmpReg` (register and NOS-left forms)/`subsZr`,
`lsrImm`/`lslImm`, `mulReg`, `addLsl` (the `lea` form), `shiftThenAdd`,
`cselHi`/`csel`, `cset`, `tstImm`, `rev`, `mvn`, `movImm`/`movzImm`/`movReg`,
`ldrOff`/`ldrBase`/`ldpOff`/`ldrbOff`/`ldrbReg`, `strOff`/`stpOff`/`strbOff`/
`strZr` (register sources), `addSp`/`spSub`/`spAdd`; and the x86-64 gas
gadgets `gasX86` directly on the x86 machine (`charge_x86`, `handBack_x86`,
`retake_x86`: `sub r15, n ; jb Lx_oog` is `GInstr.denote`, exiting to the OOG
trampoline iff it halts). Shifts and `imul` leave the flags opaque
(`clobXF`), so nothing downstream can depend on them.

`X86FlagProv.no_flag_provenance_hazards` is the static side of the same fact:
a forward dataflow over every handler body, gas routine and corpus chunk
piece, checking each flag consumer against every provenance that can reach it.
It passes — so no emitted program relies on a carry condition after a `tst` or
an `adds`, which the simulation could not have proven.

**The control theorem** (`lean/Evm/CL/X86SemCtrl.lean`, `sim_run`): for a
fragment with an annotation — the live set and provenance code may assume at
each local label — `Ok` threads the live set and provenance down the
fall-through path, checking every branch against its target's annotation
(`condOkP` for the lowered condition, `Target` for the live set and
provenance), and `LabelsOk` says every local branch target is defined. Under
`Ok`, `LabelsOk` and the relation at entry, `AsmRun.run` of the fragment and
`xrun` of its lowering both fall off the end, or both `ret`, with the exit
annotation related (`OutRel`). The pieces: `x86Items` produces a label item
only from `.label` and a `ret` only from `ret`/`brCont` (both by a full case
split over `AInstr`), so `AsmRun.skipTo` and `xskipTo` agree on a fragment and
its lowering (`skipTo_progItems`, both using the assembler's `Nf` rule); the
compare-and-branch forms lower to `cmp ; jcc`, so both successors continue
with unknown provenance; a data instruction contributes through `DataSim`,
which the per-form lemmas above discharge.

`AsmRun.Helpers` now carries the argument convention (`conv`: AAPCS64 x0-x3
on ARM64, `armConv`; the x86-64 frame stages x3, x2, x1, x14, the SysV homes
rdi, rsi, rdx, rcx), so the x86-flavoured flush program has a correct
`AsmRun` meaning at its helper calls; the ARM64 theorems take
`H.conv = armConv`. The x86 flush's far exits are `AInstr.bTramp sym`
(`jmp Lx_<sym>` on x86-64, text and items identical to the former local
jump; `b sym` on ARM64), which `AsmRun.ctrl` classifies as a far exit.

`sim_run` now also covers helper calls (`blSym` against `call [rip + Lsym_h]`:
`sim_blSym`, under the x86 convention, with the junk-below-sp oracles agreeing
and the loader's slot binding `HX.sym`), the far exits (`bTramp`/`bcTramp`
against `jmp`/`jcc Lx_<sym>`: ARM `fault sym` corresponds to x86 `exit
(trampLabel sym)`), the `addImm`/`subImm` shapes and the NOS-source stores
through the scratch temporary. The x86 gas gadgets emit `bcTramp .lo
"_eita_oog"` (same text and items as before), so they have an `AsmRun`
meaning too.

Not yet: the transport of the flush (`FlushSem` generalised over the
`FlushTarget` with the byte-scaled depth register, then `sim_run` over the x86
flush program with its annotation).

### Stage 8e–8f: the x86-64 flush, from `AsmRun` down to the bytes (2026-10-16)

The region flush at the x86-64 target is now a theorem at two levels.

* **`AsmRun` level** (`lean/Evm/CL/X86/FlushSemX.lean`, `MemCommitSemX.lean`,
  `FlushScaleX.lean`, `FlushMainX.lean`): `flush_runX_scaled` — the production
  program `emitRegionFlushT x86Flush r` after the lowering's `spScale` pass
  (byte-scaled depth immediates, the stack-address idiom as a plain add; the
  scaled program is `emitRegionFlushX r`, piece by piece, `scale_emitRegionFlush`)
  leaves the EVM stack at `SymStack.denote`, x23 at `32 · newDepth`, the TOS
  reloaded, the `32n + 8` frame restored, the memory commit done with the
  spec's expansion gas, for EVERY region (writes included). Derived from the
  ARM64 modules by substituting the target's pieces (x86 right quad
  x15/x17/x16/x0, helper convention x3/x2/x1/x14, trampoline exits, TOS-only
  reload).
* **x86-64 machine level** (`lean/Evm/CL/X86Xfer.lean`, `X86/FlushOkX.lean`):
  `flush_x86` — `xrun HX (lowerX (emitRegionFlushT x86Flush r)) x = .done x'`
  with `x'` related (`Rel Lend .unknown`) to the `AsmRun` state above. The
  bridge is `X86SemCtrl.sim_run`, fed by a PROVEN liveness/provenance transfer:
  `xfer i L p` computes the exit annotation of a data instruction (or `none`)
  and `xfer_sound` turns a hit into the `DataSim` obligation (one case per
  form, each discharged by the stage-8b simulation lemma); `ctrlB`/`fragB`
  thread it through labels, local branches, helper calls and trampoline exits,
  `Frag` composes fragments (`append`, `mono` via `Ok_mono`, `flatMap`,
  `ite`), and `lokB`/`Lok` certify `LabelsOk` structurally (only `5`–`9` are
  defined inside; every branch finds its label; no trampoline label is
  defined). The parametric program is certified piece by piece with symbolic
  immediates: each concrete piece is `Frag.ofB_sup _ rfl (by decide)` — the
  checker runs by kernel reduction, immediates never reach the live set.

Two model refinements the proof forced:

* **Dead code after a trampoline exit.** `Ok` used to continue after `bTramp`
  with the empty live set and still demanded the next label's `At` check, which
  made every label after an unconditional exit unannotatable. Dead code is now
  marked by `deadL = [x5]` — the unhomed `x5` makes `Rel` unsatisfiable, so
  anything proved from it is vacuous — and `.label t` skips `At` when `Dead L`.
* **The fourth helper argument.** `sim_blSym` demanded x14 (rcx) in sync for
  every call, but binary helpers never stage it (`call2` sets x3/x2/x1 only)
  and the previous helper call clobbers it on both machines. The requirement is
  now `ternary h = true → x14 ∈ L`, matching `callHelper`/`xcall`, which read
  the fourth argument only for `addmod`/`mulmod`.

Live sets: `Lend = {x6..x9, x20, x21, x22, x23, x24, x26}` between regions
(TOS cache + pinned registers), `Lnode = Lend − TOS` inside the DAG (a helper
call clobbers r8–r11); labels `5`/`6` carry the expansion gadget's x0/x14.
What `flush_x86` does NOT yet cover: the chunk around the flush (head charge,
op sites, terminators) and the trampolines' own code.

## Stages

**Stage 1 — close the denotation gap (the bulk).** Bring the ~660 asm-string
lines under structured instructions with a denotation on `Mach`, file by file,
keeping `handlers.S` byte-identical at every step (`AsmCore` already works this
way: `memExpandEmit` is byte-identical to the hand-written `memExpandStr` it
replaced, and `verify-jit-emit.sh` checks 110/110 byte-exact). Order by what a
bug would do: gas arithmetic first (`SstoreGas`, `CallGas`, the JIT pre-charge and
hand-back), then copy/memexp, then control flow. Gate: ValidBlocks 441/0 and the
legacy 1393/0 unchanged, byte-identical emit, after every step.

**Stage 2 — make the instruction layer target-parametric.** *(closed — see
Status above. The variable-length assembler's relaxation algorithm is proved in
`Evm/CL/Relax.lean`; the register story is settled in `Pressure.lean`; the
lowering and its coverage gate are in `Lowering.lean` + `verify-x86-emit.sh`.)* `AsmCore.Reg`
becomes `Target.RegRole`; `AInstr` becomes ISA-neutral operations (4-limb
add/sub-with-carry chains, compare-and-branch, load/store at a role-relative
offset, gas charge with an OOG branch) with per-target lowering: `emit : AInstr →
String` and `encode : AInstr → List UInt8`. The assembler needs variable-length
support — `Item.width` becomes target-dependent and label resolution becomes
iterative branch relaxation. This is the one genuinely new piece of machinery.

**Stage 3 — the x86-64 encoding.** The text lowering exists and assembles; what
remains is `encode : AInstr → List UInt8` (ModRM/SIB/REX), gated against the
system assembler's bytes the way `verify-asm-encode.sh` gates ARM64. Instantiate
`Target.x86_64` and prove each
lowering refines the same denotation. The 37 `AsmCore` theorems are reused
verbatim; only the per-target lemmas are new. Flags are where the care goes:
`U256.addChain`/`subChain` transfer unchanged, but x86's `sbb` has the
**inverted** borrow sense versus ARM's carry, and `setcc` replaces `cset` — the
exact shape of bug that a hand-port gets wrong silently.

**Stage 4 — platform runtime.** ELF x86-64 `handlers.S` derivation, the code
arena (plain `mmap` RW/RX; no W^X fight, and the icache flush becomes a no-op
since x86 caches are coherent), relocation kinds, Makefile
and lakefile targets.

**Stage 5 — the gates.** Byte-exact emit per target; ValidBlocks 441/0 and legacy
1393/0 on x86-64; GST 30694/30694; then the same block range replayed on both
machines, compared on per-tx gas and state root. Two independently lowered
backends agreeing is the real prize.

## Why not hand-write the x86 backend

It would run sooner. It would also reproduce the #24 / #260 / `retakeRem` class in
a second copy, with no cross-check and no theorem — and the whole reason those
bugs cost weeks is that the emitted asm had no denotation to check against. The
derived route is slower to first boot and the only one that makes the second
backend *evidence* rather than a second thing to debug.
