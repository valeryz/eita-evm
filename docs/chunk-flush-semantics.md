# The chunk JIT's flush, proven (stage 7 of #238)

The JIT's chunk pieces — the gas gadgets, the u256 cores, the region flush —
used to be *derived* (one `AInstr` algebra, text byte-identical to the
hand-written emitters) but not *denoted*: nothing related the instructions
to what the region means. This stage closes that for ARM64.

## The semantics: `Evm.CL.AsmRun`

A fragment semantics for `AInstr`, alongside `AsmSem` (which runs a routine
to its `ret` over word cells and proves the gas routines):

* byte memory (`Mem := BitVec 64 → BitVec 8`; `ld64`/`st64`, `ld256`/`st256`
  little-endian), the stack pointer, the carry chain (`adcs`/`sbcs` as the
  ARMv8 65-bit `AddWithCarry`), `rev`, `strb`, the sp frame forms;
* register-only instructions delegate to `AsmSem.step` through a view with
  a dummy memory — one semantics for `adds`, `csel`, `cset`, `cmp`, …;
* `run : List AInstr → RS → Outcome` with `done` (fell off the end), `ret`,
  `fault sym` (a far branch to a fault stub), `stuck`; `run_append` composes
  closed fragments (every forward label reference resolves inside);
* helpers (`bl _eita_helper_*`) are an oracle `Helpers`: the value written at
  `out`, junk in the caller-saved registers and in a 64 KiB window below sp.
  `Helpers.Spec` pins the values to the `Expr.eval` arms — the same trust the
  DSL already places in the C helpers (`Mach.helperFn`).

`AsmRunMem` is the memory lemma library (round trips, frame rules on
disjoint ranges, the limb view `ofLimbs`). Addresses are uniformly
`base + ofNat k` (`off`), so disjointness is interval arithmetic for `omega`.

## What is proven (0 sorry)

| module | theorem | says |
|---|---|---|
| `ARM64/ChunkGasSem` | `ginstr_run` | each gas gadget's program is `GInstr.denote`: continues with the denotation's gas, or faults to `_eita_oog` iff the denotation halts |
| `ARM64/CoreSem` | `addCore_run` … `sgtCore_run` | the ten u256 cores compute the 256-bit operation on the four limbs (`bv_decide` over the carry chain) |
| `ARM64/FlushSem` | `node_run` | every `evalNodeT` kind (constant, entry read, the cores, isZero/not, the twelve helper calls) leaves `eval e es` in its slot and nothing else but its slot and the helper window |
| `ARM64/FlushSem` | `dag_loop` | evaluating the slot list in order establishes `Inv` for every slot |
| `ARM64/DagSlots` | `fold_wf`, `slotIdx_spec/inj` | the reference `dagSlots` is duplicate-free, closed (kids before parents), contains the roots; its index function is faithful |
| `ARM64/FlushSem` | `exit_loop`, `frameOpen/Close_run`, `depthUpdate_run`, `cacheReload_run`, `underflow/overflowCheck_run` | each remaining piece of the flush |
| `ARM64/FlushMain` | **`flush_run`** | the whole write-free flush: the EVM stack holds `SymStack.denote r.ss es` position by position, x23 is the new depth, TOS/NOS are reloaded, sp/fp/lr and every kept register are restored, memory outside the stack arena, the frame and the helper window is untouched |
| `ARM64/RegionBuild` | `built_wf` | every region the builder reaches from `{}` by `Region.step` over `regionStep`'s fold / sym / store outcomes satisfies `RegionWF` once it is write-free: `consumed ≤ need`, every `stackAt k` in the exit DAG has `k < need` (by a bound `LB` carried through `pop`/`popN`/`peek`/`push`/`pushAll`, every `symStep` arm, the constant folder and the absorbed store), the net growth is within `maxNet` |
| `ARM64/RegionBuild` | `flushed_built`, `flushed_wf` | the regions `emitChunkGen` flushes (read off the chunk at the region-collecting algebra `regionsOut`) are all built; so write-free ones are `RegionWF` — no hypothesis on the ops |
| `ARM64/RegionBuild` | **`chunk_flush_run`** | `flush_run` for exactly those regions: the layout and entry facts are the only hypotheses left |
| `ARM64/MemCommitSem` | `memExpand_run` | the expansion gadget is EELS's `memoryExpansionCost` delta (`mcost_eq_spec`/`ecost_eq_spec` are `rfl` against `Gas.memoryCost`/`memoryExpansionCost`): faults to `_eita_oog` iff the writes' end is past the capacity or the delta is past the gas left; otherwise x22 drops by the delta and `memory_size` becomes the aligned new end (unchanged when no expansion) |
| `ARM64/MemCommitSem` | `mpUpdate_run`, `memWrite_run`, `writes_run` | `mp` becomes `max mp maxEnd`; each buffered write lands at `buffer + off` as the value's low byte (MSTORE8) or its 32 big-endian bytes (MSTORE; `stBE_byte`: byte `j` is `v.extractLsb' (8·(31−j)) 8`), reading its slot; the writes apply in order (`applyW` fold) |
| `ARM64/MemCommitSem` | **`memCommit_run`** | `memCommitT` on a non-empty write list: the three outcomes above composed, every other byte of memory untouched (the struct words and the buffer are the only ones written) |
| `ARM64/FlushMain` | **`flush_run`** (now all regions) | as before plus: x22 drops by `memGas` (0 without writes), `MemOut` (the new `memory_size`, `mp`, the buffer bytes), the struct and buffer are the only extra memory touched; `flush_run_oog`: when the capacity or gas check fails the flush faults to `_eita_oog` (after the depth checks pass) |

The flush was restated as list combinators (`exitOneT`, `exitStoresT`,
`memCommitT`, `depthUpdate`) with no change to the text
(`chunk_text_derived`, the snapshot, `handlers.S`, 36/36, 110/110).
`emitChunkGen`'s two `for` loops were likewise restated as folds (`dynCosts`,
`bodyStep` over `BodySt`), text identical by the same gates, so the body pass
is a `List.foldl` an invariant can be carried through. `symStep` now refuses
`dup 0` (not an EVM op; the decoder emits `dup 1..16`) exactly as it refused
`swap 0` — the one place where an entry read could have escaped `need`.

## Hypotheses (the trust surface, stated)

* `Lay`: no address wrap, the frame (and the saved fp/lr above it) disjoint
  from the 1024-slot stack arena, both outside the helper window.
* `MLay`: the EvmState struct words (`mp` +24, buffer pointer +40,
  `memory_size` +48, capacity +56) and the byte buffer `[mb, mb+cap)` are
  disjoint from the frame, the arena and each other, outside the helper
  window; `cap < 2^32` (so the cost arithmetic cannot wrap). Entry facts:
  x20 is the struct, `memory_size ≤ cap`.
* `RegionWF` (`consumed ≤ need`, every `stackAt k` in the DAG — write values
  included — has `k < need`, the net growth is within `maxNet`, every
  write's end fits 64 bits) is a theorem about the builder
  (`RegionBuild.flushed_wf`), not a hypothesis.
* The success conditions `need ≤ d`, `d < 1025 − maxNet`, `maxEnd ≤ cap` and
  `memGas ≤ gas`; the fault paths are the two check lemmas and
  `flush_run_oog`.
* The buffer bytes are stated against `applyW` (`stBE`), i.e. the machine's
  big-endian layout; the tie to the spec's `Memory.write`/`toBytesBE` is by
  definition of big-endian, not a theorem yet.
* `dagSlots`'s `implemented_by` (pointer-memoised) is trusted to agree with the
  reference definition the proofs are about, as before.

## Not yet

* The spec-side memory model: `MemOut`'s buffer bytes against
  `Frontier.Vm.Memory.write`/`U256.toBytesBE`, and `memory_size`/`mp` against
  the spec's `Memory.words`.
* ~~The x86-64 twin~~ — done (2026-10-16): `X86/FlushMainX.flush_runX_scaled`
  is this theorem at the x86-64 target under `AsmRun`, and `X86/FlushOkX.flush_x86`
  carries it to the lowered x86-64 bytes through `X86SemCtrl.sim_run` with the
  proven liveness transfer `X86Xfer` (see `docs/x86-64-backend.md`, stage 8e–8f).
* The chunk-level composition (`emitChunkGen` as a whole: head charge, op
  sites, flushes, terminators) against `IR.execChunk`; the body pass is a
  fold now, and its flushed regions are known good, so this is the remaining
  glue.
