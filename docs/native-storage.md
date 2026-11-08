# Native storage: SLOAD/SSTORE without the Lisp host (plan, owner note 6)

Status: built (steps 2-6): the native slot tables, every storage path routed; native SLOAD; native SSTORE with
its journal entry and the native type-0 revert; the hook tiers; and (step 6, the owner's addendum 2) one execution
path: the Lisp SLOAD/SSTORE effects are deleted, every SLOAD/SSTORE runs the C-emitted effect, and Lisp is called
only for data (an account's id, a lazy world's fault-in) and observation (the per-access hook). Branch
`perf-native-storage` off `perf-x86`.

## Why

On x300 (perf-x86 9f633ff, 30k mainnet blocks) the Lisp host is ~30 % of the replay thread. Inclusive:
`spec-sload-effect` 6.2 %, `spec-sstore-effect` 4.6 % (the CALL path is larger but is not this plan's subject).
Their leaves are the slot table (`slots-find` 2.7 % inclusive, `slots-get` 1.6 %), the account intern (1.4 %, twice
per SLOAD: once for the fault test, once for the read), the bignum the value becomes (`words-u256` 1.2 %), the
access-set and original-value records (C, behind Lisp wrappers), and the callback round trip itself (native ->
Lisp -> native). A native path removes all of it on a hit: the value never leaves limbs. Expected 5-8 % of the
replay thread; each step is measured.

## Design

### 1. One owner per slot

Native slot tables (c/world_slots.{h,c}) hold every loaded slot:

    ws_world  = per account table: a directory, account id -> ws_slots (or none)
    ws_slots  = one account's slots: key (u256) -> value (u256), four limbs each
    entry     = 8 limbs (key, value) + a state byte (empty / full / tombstone)
    probe     = linear, power-of-two capacity, at most 3/4 used; grown by rehash

Built (step 2) as one table per account under a directory, not the single world-wide table first planned:
a wipe (SELFDESTRUCT, a failed CREATE, the EIP-161 sweep) and an account's slot walk (the root checker, a journaled
wipe, a layer write) then cost the account's slots, not a scan of the world's; and with the Lisp table's hash,
probe, tombstones and growth kept exactly, an account's slots are walked in the same order as before, so the
journal of a wipe, the layer files and the observers see the same sequences. A hit costs one directory load and
one probe sequence. A ws_world belongs to an account table (ids are per table; a freeze hands the frozen layer
its table and so its slots), is made on the table's first write and freed with it (a finalizer). The native
tables are THE copy: the Lisp `slots` struct and its table code are deleted. Lisp reads and writes go through
`acct-slot-get`, `acct-slot-put!`, `acct-slot-present-p`, `acct-slots-map`, `acct-slots-drop!` and `%ws-copy`
(state/world.lisp), which pass limbs, so bignums are made only where Lisp needs an integer.

Since the Velvet swap the table is no longer hand-written: `c/world_slots_emit.c` is printed from Velvet methods
proved for every capacity against `WorldSlotsModel` (proofs in a separate Velvet package, to be published), and
`c/world_slots.c` is the glue (struct packing, frees, the directory's pointer array); the ABI, the CBMC harness and
the tests are unchanged. Trust: docs/trusted-surface.md, "Table primitives".

Per-tx records stay where they are today, in the native TxState (c/tx_state.h): the EIP-2929 accessed-slot set,
EIP-2200 originals (first-touch value and order), transient storage, refunds. Nothing moves; the native SLOAD/SSTORE
reads and writes them directly instead of through Lisp wrappers.

### Every Lisp path that touches storage today (the routing list)

Each must read/write through the native accessors before the Lisp tables can go. Core (`src/`):

| path | file | what it does | route to |
|---|---|---|---|
| `world-storage-get` / `world-storage-set` / `world-get-storage-table` | state/world.lisp | the raw table ops | `eita_ws_get` / `_put` / `_remove` |
| `storage-of`, `(setf storage-of)` (+ the read/write stream: `view-log-read/-write :storage`) | state/world.lisp | the effect layer's one view | the same, stream unchanged |
| `fault-slot!`, `*fault-slot-hook*` (snapshot `snap-fault-slot`, RPC lazy state) | state/world.lisp, state/snapshot-world.lisp, chains/driver.lisp | first-touch load | miss path: the hook installs into the native table |
| `world-storage-wipe!`, `*storage-wipe-hook*` | state/world.lisp, state/snapshot-world.lisp | SELFDESTRUCT / CREATE-over-storage wipe | `eita_ws_wipe(account)` |
| `storage-wipe-journaled!` (+ `*cold-storage-map-hook*`, `snap-cold-storage-map`) | evm/calls.lisp, state/snapshot-world.lisp | a journaled wipe of RAM + cold-tier slots | `eita_ws_map` over the account, journal entries as today |
| `account-uncreate!` | state/world.lisp | revert of a CREATE drops the account's storage | `eita_ws_wipe` |
| `spec-restore-journal-entry` type 0 (generated) | generated/host.lisp | revert of an SSTORE | native restore in `eita_ts_revert` (mixed journal, one order) |
| `spec-sload-effect`, `spec-sstore-effect` (generated) | generated/host.lisp | the effects | step 3/4: the C-emitted twins; step 6: deleted (with `spec-sstore-gas-dispatch` and `sstore-gas-native`) |
| `do-storage-changes`, `observe-slot-touch!`, `observe-tx-end!` | evm/observe-tx.lisp | observers' pre/post values | tier (a): read the native originals + current value |
| `write-ram-tables`, `ram-layer-op`, `back-world!`, snapshot layers | state/snapshot-world.lisp | checkpoints, layered snapshots | `eita_ws_map` per account |
| `copy-world*`, `populate-world`, `world-state-root` | state/worlds.lisp | fixtures, roots | copy / map the native table |
| `mpt-full-slot-list`, `mpt-account-snapshot(-full)`, `mpt-post-block-hook` | state/mpt-live.lisp | the incremental root checker | `eita_ws_map`; its dirty set unchanged |
| `load-genesis-alloc` | state/anchors.lisp | genesis | `eita_ws_put` |
| `compare-post` | fixtures/runner.lisp | fixture post-state check | `eita_ws_get` |
| `storage`, `set-storage` | eita.lisp | public API | the accessors |
| Arc: `arc-slot-read!`, `arc-slot-write-gas!`, `arc-slot-store!`, `arc-read-gas-values`, `arc-store-gas-values!`, `arc-blocklisted-unmetered-p` | chains/arc-precompiles.lisp | the 0x1800 native-USDC precompile and system state | through `storage-of` (already the one view) |
| chain system calls (block-start/end), OP/Base deposits | chains/*.lisp | system writes | through `storage-of` / `world-storage-set` |

Node and bench: `node/factlog/factlog-writer.lisp` (`do-storage-changes`: the fact log), `node/acquire/acquire.lisp`
(`world-storage-set` on load), `bench/source.lisp` (`slots-put` when it loads the working set). Step 2 greps again
(`acct-storage`, `slots-*`, `world-storage-*`, `storage-of`, the hooks) and must find no other caller.

### 2. Spec-first effect logic

SLOAD/SSTORE's effect (warm/cold, gas, refunds, the original-value record, the journal entry) is generated from Lean
today as Lisp (`EffectIR` -> `toCL`, src/generated/host.lisp). Add a C printer for the subset these two use
(`EffectIR.toC`: let, if, arithmetic on u64 gas and on limb values, the host calls as C calls), emit
`c/generated/storage_effect.c`, commit it, and extend `verify-host-emit.sh` with its drift check. `Stmt.run` and the
effect proofs are untouched (only a printer is new); gas stays Lean-derived (`check-derived-gas.py` must pass, and is
extended to the C file).

### 3. Journal natively

SSTORE writes its type-0 entry into the existing native journal arena (#248). `eita_ts_revert` restores type 0
natively (into WorldSlots); the Lisp revert loop keeps handling the other host types in the same reverse order, so the
journal stays one mixed sequence.

### 4. Data paths stay in Lisp

A key absent from a lazy world's table calls out once (`cb-storage-fault`): the Lisp fault-in (snapshot / RPC)
installs the value in WorldSlots and the native effect continues (still absent: the value is zero). An account
first seen under a world calls out once for its id (`cb-storage-learn`). Wipes and cold-storage maps likewise call
into Lisp. No effect runs in Lisp (step 6).

### 5. Hooks in three tiers

(a) batch, the default: observers read the native first-touch/original record and the current value at tx/block end
(`do-storage-changes`, the fact log, folds, the storage view, read-set recording);
(b) filtered synchronous hooks: a watch filter (empty in normal runs) probed per access, calling into Lisp only on a
hit;
(c) full hook mode: the native effect plus one Lisp call per access (`cb-storage-hook`) while the read stream is on
(it sees each read and write: the storage view), and per changing SSTORE while the incremental root checker
tracks dirty slots. Steps 3-5 swapped the vtable to the Lisp handlers instead; step 6 deleted them.

## Trusted surface (owner addendum)

The SLOAD/SSTORE effect logic is derived (generated from the effect IR; `Stmt.run` and the effect proofs untouched).
What is trusted: (1) the new IR -> C printer, the same class as today's IR -> Lisp printer (`toCL`); (2) the C
primitives the generated code calls. C adds a memory-safety obligation Lisp with safety did not have. So:

- Few, tiny primitives, each listed with its contract in core `docs/trusted-surface.md`: probe, insert, resize,
  remove, wipe(account), map(account); limb compare / copy / zero-test; journal append.
- Limb primitives: defined in Lean limb by limb as the C computes them and proved equal to the U256 operation,
  reusing perf-opaque's `lean/Evm/CL/WordOps.lean` (def68c3: `eq_ofBV`, `isZero_ofBV`, `lt_ofBV`, `sub_ofBV`,
  `add_ofBV`, on `Limbs.ofBV`/`toBV`), and the C is EMITTED from those definitions (no hand transcription) into
  `c/generated/limb_ops.h`, drift-checked by `verify-host-emit.sh`.
- The table (mutable, hard to emit): a Lean finite-map model (`Evm/CL/WorldSlotsModel.lean`: get/put/remove/wipe on
  `(acct, key) -> value`); a randomized differential test of the C table against the model's semantics and against
  today's Lisp slot table; a CBMC harness for memory safety (bounds, index arithmetic overflow, pointer validity) and
  functional correctness against the model at small capacities (cbmc from apt, or a release binary under
  /data/eita-bench/opt); ASan + UBSan builds of every C unit test.
- End to end: the differential mode (native path vs the Lisp path, sampled txs) in the gated runs, the header gate,
  every SSTORE/refund/revert conformance test.
- CI: a step in core `.github/workflows/ci.yml` for the sanitizer unit tests and the CBMC harness if it runs in under
  10 minutes; otherwise a script and a note.

Trust classification, reported per new piece:

| piece | class |
|---|---|
| SLOAD/SSTORE effect logic (C) | derived (emitted from the effect IR; the IR -> C printer trusted, like toCL) |
| limb eq / zero / compare / copy (C) | proved (Lean, WordOps) + emitted |
| WorldSlots probe / insert / resize / remove / wipe / map | proved (Velvet, every capacity) + emitted; glue trusted; still model-checked (CBMC) + tested (randomized vs model, sanitizers) |
| native journal append / type-0 restore | model-checked + tested |
| Lisp accessors routed to the native table | tested (differential, fixtures, 30k replay) |
| hook tiers (a)-(c) | tested (fact-log rows and storage view identical to the Lisp path's over the 30k range; fixture rows and watched accesses equal a digest recorded from it) |

## Steps (each: A/B on x300, 0 mismatches, the differential on in at least one gated run, fixtures incl. every
## GeneralStateTests SSTORE/refund/revert directory, asdf:test-system, the Lean gates)

1. This plan (docs/native-storage.md).
2. WorldSlots + the native accessors; Lisp still runs the effect logic through them. No speed goal; every path in the
   routing list routed. Randomized table test (insert / update / revert / wipe / grow against a Lisp reference).
3. Native SLOAD fast path (hit native, miss -> Lisp fault-in), effect from the C printer. Measure.
4. Native SSTORE fast path incl. journal and refunds. Measure.
5. Observers on the native records (tier a), the watch filter (b), the hook-mode swap (c), with tests that the
   fact-log rows and the storage view are byte-identical to the Lisp path over the 30k range.
6. (Addendum 2) One execution path: delete the Lisp SLOAD/SSTORE effects (and their Lisp printings); hook mode is
   the native path plus a callback per access; the differential compares the tiers against each other and the
   interpreter-level references (fixtures) rather than a Lisp storage path.

## Tests

- Table: randomized ops vs a Lisp reference (puts, overwrites, removes, wipes, grows, colliding keys, reverts).
- Effects: the C-emitted SLOAD/SSTORE vs the Lisp-emitted ones on random (fork, warm/cold, original, current, new)
  tuples, gas and refund deltas equal; the EIP-2200/2929/3529 vectors.
- Engine: the differential mode (EITA_DIFF_TIERS), JIT vs interpreter (to step 5 tier B also ran the Lisp storage
  path; from step 6 both tiers run the one native path), every tx over 30 blocks and sampled over the 30k; fixtures incl. GeneralStateTests stSStoreTest, stRefundTest,
  stRevertTest, stSelfBalance / create-collision dirs; the 30k replay with 0 mismatches.
- Observers: the fact-log rows and the storage view byte-identical between native and Lisp paths over 30k (step 6:
  against the outputs recorded from step 5's Lisp path).
- Arc: x300 has no Arc bundle. Run the core's Arc regression that needs no production data if one exists; the owner's
  session must run regress-arc / the image gate before merge.

## Complexity

A feature. It deletes the Lisp `slots` storage tables and their front cache (state/world.lisp), and (step 6) the
Lisp SLOAD/SSTORE effects, their Lisp printings, the Lisp SSTORE dispatch and the hook-mode swap. Net line delta reported per step;
`complexity exception: pending owner approval` for any remainder.
