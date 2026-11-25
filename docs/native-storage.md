# Native storage: SLOAD and SSTORE in C

SLOAD and SSTORE run entirely in native code: the slot tables are C (`c/world_slots.{h,c}`),
the effects are C printed from the Lean effect IR (`c/generated/storage_effect.c`), and the
host that binds them is C (`c/storage_host.{h,c}`). Lisp is called only for data (an account's
id, a lazy world's fault-in) and for observation (a per-access hook when one is on). On a hit the
value never leaves its four 64-bit limbs: no bignum, no Lisp call.

The trust classification of every piece is in
[`trusted-surface.md`](trusted-surface.md#the-native-storage-path).

## 1. The slot tables

`c/world_slots.h` holds every loaded slot, the one copy:

    ws_world  = per account table: a directory, account id -> ws_slots (or none)
    ws_slots  = one account's slots: key (u256) -> value (u256), four limbs each
    entry     = 8 limbs (key, value) + a state byte (empty / full / tombstone)
    probe     = linear, power-of-two capacity, at most 3/4 used; grown by rehash

One table per account, under a directory: a wipe (SELFDESTRUCT, a failed CREATE, the EIP-161
sweep) and an account's slot walk (the root checker, a journaled wipe, a layer write) cost the
account's slots, not a scan of the world's. The hash, probe, tombstone and growth rules fix the
walk order of an account's slots, so the journal of a wipe, the layer files and the observers
see a deterministic sequence. A hit costs one directory load and one probe sequence. A
`ws_world` belongs to an account table (ids are per table; a freeze hands the frozen layer its
table and so its slots), is made on the table's first write and freed with it (a finalizer).

The table decisions are not hand-written: `c/world_slots_emit.c` is printed from Velvet methods
proved for every capacity against `lean/Evm/CL/WorldSlotsModel.lean` (proofs and printer:
`verify/velvet-slots/`, checked by `scripts/verify-velvet-slots.sh`), and `c/world_slots.c` is
the glue (struct packing, frees, the directory's pointer array).

Lisp reads and writes go through `acct-slot-get`, `acct-slot-put!`, `acct-slot-present-p`,
`acct-slots-map`, `acct-slots-drop!` and `%ws-copy` (`src/state/world.lisp`), which pass limbs,
so bignums are made only where Lisp needs an integer.

Per-tx records live in the native TxState (`c/tx_state.h`): the EIP-2929 accessed-slot set,
EIP-2200 originals (first-touch value and order), transient storage, refunds. The native SLOAD
and SSTORE read and write them directly.

## 2. Every storage path (the routing list)

Every Lisp path that touches storage goes through the native accessors. Core (`src/`):

| path | file | what it does | native call |
|---|---|---|---|
| `world-storage-get` / `world-storage-set` / `world-get-storage-table` | state/world.lisp | the raw table ops | `eita_ws_get` / `_put` / `_remove` |
| `storage-of`, `(setf storage-of)` (+ the read/write stream: `view-log-read/-write :storage`) | state/world.lisp | the effect layer's one view | the same |
| `fault-slot!`, `*fault-slot-hook*` (snapshot `snap-fault-slot`, RPC lazy state) | state/world.lisp, state/snapshot-world.lisp, chains/driver.lisp | first-touch load | miss path: the hook installs into the native table |
| `world-storage-wipe!`, `*storage-wipe-hook*` | state/world.lisp, state/snapshot-world.lisp | SELFDESTRUCT / CREATE-over-storage wipe | `eita_ws_drop` (the account) |
| `storage-wipe-journaled!` (+ `cold-storage-wipe!`) | evm/calls.lisp, state/world.lisp | a creation's wipe: RAM slots journaled, the cold tier by the WIPED bit | `eita_ws_map` over the account, one journal entry per RAM slot |
| `account-uncreate!` | state/world.lisp | revert of a CREATE drops the account's storage | `eita_ws_drop` |
| `spec-restore-journal-entry` type 0 (generated) | generated/host.lisp | revert of an SSTORE | restored natively by `eita_sh_revert_storage` first (§4) |
| `do-storage-changes`, `observe-slot-touch!`, `observe-tx-end!` | evm/observe-tx.lisp | observers' pre/post values | the first-touch log and the current value (§5) |
| `write-ram-tables`, `ram-layer-op`, `back-world!`, snapshot layers | state/snapshot-world.lisp | checkpoints, layered snapshots | `eita_ws_map` per account |
| `copy-world*`, `populate-world`, `world-state-root` | state/worlds.lisp | fixtures, roots | copy / map the native table |
| `mpt-full-slot-list`, `mpt-account-snapshot(-full)`, `mpt-post-block-hook` | state/mpt-live.lisp | the incremental root checker | `eita_ws_map`; its dirty set through the hook |
| `load-genesis-alloc` | state/anchors.lisp | genesis | `eita_ws_put` |
| `compare-post` | fixtures/runner.lisp | fixture post-state check | `eita_ws_get` |
| `storage`, `set-storage` | eita.lisp | public API | the accessors |
| Arc: `arc-slot-read!`, `arc-slot-write-gas!`, `arc-slot-store!`, `arc-read-gas-values`, `arc-store-gas-values!`, `arc-blocklisted-unmetered-p` | chains/arc-precompiles.lisp | the 0x1800 native-USDC precompile and system state | through `storage-of` |
| chain system calls (block-start/end), OP/Base deposits | chains/*.lisp | system writes | through `storage-of` / `world-storage-set` |

## 3. Effects from the spec

The SLOAD and SSTORE effects (warm/cold, gas, refunds, the original-value record, the journal
entry) are the terms `Evm.CL.EffectSload.term` and `Evm.CL.EffectSstore.term` of the effect IR,
proved against every fork's handler ([`effect-layer-derivation.md`](effect-layer-derivation.md)
§4.4, §4.5). `Evm.CL.EffectC` prints them as C (`lake exe emitStorageC`): let, if, arithmetic on
u64 gas and on limb values, and each host primitive as one C call. The fork's SSTORE schedule is
chosen by the emitted dispatch `eita_spec_sstore_plan`, whose routines are the proved
`eita_sstore_gas_*` natives. The 256-bit comparisons and copies are `c/generated/limb_ops.h`,
printed from `lean/Evm/CL/LimbC.lean` (`lake exe emitLimbC`). `scripts/verify-host-emit.sh`
fails on drift of either file, and `scripts/check-derived-gas.py` checks that the hand-written C
(`c/storage_host.*`, `c/world_slots.*`) holds no gas constant.

The callbacks vtable's SLOAD and SSTORE slots are `eita_cb_sload` / `eita_cb_sstore`
(`c/storage_host.c`), the opcodes' one execution path. Each binds the frame account and key, runs
the emitted effect, and calls the Lisp hook only when one is on (§5). The frame account's id comes
from a 64-entry cache keyed by the slot tables' serial; an address not in it is learned once from
Lisp (`cb-storage-learn`). Lisp sets the host's world, TxState, fork and flags at every frame
entry (`storage-host-sync!`).

## 4. The journal

SSTORE writes its type-0 entry (address, key, old value) into the native journal arena
(`c/tx_arena.h`), in the layout of the Lisp `journal-push!`, so the journal stays one mixed
sequence. On a revert `eita_sh_revert_storage` walks the slice newest first and restores each
type-0 entry of an account with a known id into the slot table, retyping it so the Lisp loop and
`eita_ts_revert` skip it; it stops at the first un-create entry (type 10), below which the Lisp
loop replays in order. While the read stream is on, the Lisp restore runs instead, so each restoring
write is streamed.

## 5. Data paths and hooks

A key absent from a lazy world's table calls out once (`cb-storage-fault`): the Lisp fault-in
(snapshot / RPC) installs the value in the slot table and the native effect continues (still
absent: the value is zero). An account first seen under a world calls out once for its id
(`cb-storage-learn`). Wipes call into Lisp. No effect runs in Lisp.

Observers see storage in three tiers:

- **(a) batch**, the default: the observers' first-touch log (`eita_sh_touch`: every slot the tx
  touches, once, in first-touch order, with its value then) and the current value, read at tx and
  block end (`do-storage-changes`, the fact log, folds, read-set recording);
- **(b) the watch filter**: up to 16 accounts (`storage-watch!`, empty in normal runs) whose every
  SLOAD/SSTORE calls the hook, which calls `*storage-access-hook*` synchronously, in execution
  order;
- **(c) the hook mode**: the native effect plus one Lisp call per access (`cb-storage-hook`) while
  the read stream is on (it sees each read and write: the storage view), and per changing SSTORE
  while the incremental root checker tracks dirty slots.

## 6. Tests

- Table: `c/test_world_slots` (randomized puts, overwrites, removes, wipes, grows, colliding keys,
  under ASan + UBSan, and on a trace of the Lean model, `lake exe worldSlotsVectors`), the CBMC
  harness (`c/cbmc/run.sh`, in CI), `tests/world-slots.lisp`.
- Effects: the EIP-2200/2929/3529 vectors and every GeneralStateTests SSTORE, refund and revert
  directory (`stSStoreTest`, `stRefundTest`, `stRevertTest`, `stSelfBalance`, the create-collision
  directories).
- Engine: the tier differential (`EITA_DIFF_TIERS`: each top-level frame on the JIT and the
  interpreter, both on the native path), and a mainnet replay range with the header gate.
- Observers: `tests/native-storage-hooks.lisp` (fixture rows equal with and without the watch;
  rows and watched accesses equal a recorded digest).
