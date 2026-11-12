# velvet-slots: the native slot table, proved in Velvet and printed to C

The slot table's decisions (`c/world_slots_emit.c`) are [Velvet](https://github.com/verse-lab/velvet) methods
(verse-lab/velvet `b2a349a`, Apache-2.0), proved for **every capacity** against core's model
`lean/Evm/CL/WorldSlotsModel.lean`, and printed to C by `Slots/CPrint.lean`. A Lake package of its own, on core's
toolchain (`lean-toolchain` links to `../../lean/lean-toolchain`): it needs only Velvet (and Velvet's plausible),
not Mathlib, so core's `lean/` package gains no dependency. Core's model file is compiled here in place (the
`WorldSlotsModel` lib in `lakefile.toml`: `srcDir = "../../lean"`); it imports nothing.

Check: `scripts/verify-velvet-slots.sh` (in CI) builds every proof and the printer, checks the axioms, runs the
printer's negative tests and re-emits `c/world_slots_emit.c`, which must equal the committed file. The emitted C
itself is checked by core's `make -C c test_world_slots test_world_slots_model` (ASan + UBSan, randomized and on
a trace of the Lean model) and `c/cbmc/run.sh` (11 CBMC proofs at capacities 4 and 8).

## What is proved (every capacity)

| method | what is proved |
|---|---|
| `find` | `ins_first`: the insertion index is the first non-full slot on the probe path (pins it to the C's answer) |
| `place` | every invariant kept; the put relation; count/used bookkeeping |
| `remove` | every invariant kept; the erase relation; `used` unchanged |
| `rehash`, `grow` | the full invariant incl. occupancy `4·used ≤ 3·cap`; room for the next place; same map; aborts only when `maxCap < newCap` |
| `put` | the full invariant incl. occupancy; the put relation; `put_models` lifts it to the map |
| `lookup` | hit / miss against the table's contents |
| `next` | the first full slot at or after i, or cap |
| `create`, `fresh` | an empty table satisfying every invariant (`fresh`: capacity 4) |
| `dirGrow` | result > id, ≥ n, = n when id < n; aborts only when `n ≤ id ∧ id ≥ 2^40`; generic in `WS_DIR_MIN` |
| `copyArrs` | the copies equal the source arrays |

World level (`Slots/World.lean`, mirroring the glue `c/world_slots.c`): `touch`, `wput`, `wremove`, `wdrop`,
`wget`, `table_hasTable`, `wcopy` each equal the model's operation (`put`, `remove`, `drop`, `get`, `hasTable`,
`copy`) under `absW`, keep the world invariant, and state exactly when they abort. `walk` (the glue's `next` loop)
visits exactly the full slots in index order; `walk_rep`: exactly the present (key, value) pairs, distinct keys.
Axioms (`Slots/Axioms.lean`, 26 `#print axioms`): only `propext`, `Classical.choice`, `Quot.sound`.

## The printer (`Slots/CPrint.lean`)

- Proof-carrying indexing only: `rd`/`wr` (`Slots/Mem.lean`) index under `if h : i < a.size … else oob`, and their
  specs make the bound a vcgen goal, so every array access in the emitted C is in bounds by proof. The checked
  branch is emitted only for methods whose proved spec rules out failure. `a[i]!`, `set!`, `a[i]?`, a stray
  `oob`, and `oob` in a method that may fail are rejected (`PrinterNeg.lean`, `#guard_msgs`).
- `wsAbort` becomes `fputs` + `abort()`. A linearity check rejects any array use after an in-place store or a
  mutating call; each emitted function names the array parameters it may write.
- Still trusted (docs/trusted-surface.md, "Table primitives"): the printer; `Nat` fits in 64 bits (the emitted
  aborts keep cap and id below 2^40); the glue `c/world_slots.c`.

## Rebuild by hand

`lake build Slots Slots.CPrint && lake env lean Slots/Emit.lean && lake env lean PrinterNeg.lean` (the printer is
not in the default target; Velvet is pinned by full SHA in `lake-manifest.json`).

Velvet friction met here: anonymous goal names (`rename_i`); `simp` shows `set!` as `setIfInBounds`, so two lemma
forms are needed; specs must use `⌜φ⌝ ⊓ post` (not `∧`) for vcgen to split them; anonymous-constructor notation
doesn't see through a `def`; a callee's `given` ghost becomes an unsolvable goal at the call site (ghost-free inner
contracts instead).
