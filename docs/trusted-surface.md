# The trusted surface

Eita's EVM semantics are written in Lean 4 as a clause-by-clause translation of the Ethereum
execution specs (EELS), and the parts that execute — the ARM64 and x86-64 interpreters, the
gas routines and the host's effect code (`src/generated/host.lisp`) —
are **emitted from that spec** and drift-checked (`scripts/verify-host-emit.sh`). What remains is
code that is *trusted, not derived*: hand-written C and C++, and the third-party libraries it
links. This page lists all of it, so a reader knows exactly where a bug could hide that the
proofs do not rule out.

Everything below is linked into `c/libeita.{so,dylib}` (see `c/Makefile`) unless noted.

## Hand-written C: EVM arithmetic and buffers — `c/eita_compute.c` (614 lines)

Called from the generated handlers for operations too large to inline:

| Functions | What |
|---|---|
| `eita_helper_div`, `_sdiv`, `_mod`, `_smod`, `_addmod`, `_mulmod`, `_mul`, `_exp` | 256-bit arithmetic (word-wise Knuth division) |
| `eita_helper_shl`, `_shr`, `_sar`, `_byte`, `_signextend` | 256-bit bit operations |
| `eita_helper_calldataload`, `_calldatacopy`, `_codecopy`, `_returndatacopy`, `_returndata_to_mem`, `_mcopy` | reads past the end of a buffer yield zeros; offsets are full 256-bit values |
| `eita_helper_keccak256`, `eita_keccak256` | KECCAK256 over memory |
| `eita_jumpdest_map`, `eita_run`, `eita_run_program` | jump-destination analysis and the entry trampolines |

**How it is checked:** `c/test_compute.c` compares every helper against GMP on edge constants and
random operands (about 17.9M cases), including the 64-bit wrap of buffer offsets; the Ethereum
test fixtures run through these helpers.

## Hand-written C: transaction-scoped state — `c/tx_state.c` (205 lines)

`eita_ts_*`: the EIP-2929 warm sets (`access_addr`, `access_slot`), original storage values for
SSTORE gas (`orig_record`, `orig_get`), the refund counter, EIP-1153 transient storage
(`tstore`, `tload`), accounts created in the transaction, and their revert journal
(`revert`, `reset`). **Checked by** `c/test_tx_state.c` and the fixtures.

## Hand-written C/C++: hashes and precompiles — `lean/c/`

| File | What | Built on |
|---|---|---|
| `keccak.c`, `keccak_sha3.c`, `keccak_batch.c` (404) | Keccak-256 (opcode, addresses, tries), batched for the trie | own implementation |
| `sha256.c` (98), `ripemd160.c` (171) | precompiles 0x02, 0x03 | own implementations |
| `ecrecover.c` (87) | precompile 0x01 and sender recovery | libsecp256k1 |
| `modexp.c` (134) | precompile 0x05 (its gas is computed in Lean) | GMP `mpz_powm` for moduli ≤ 64 bytes, OpenSSL `BN_mod_exp` above; the two are cross-checked by `c/test_modexp.c` |
| `bn254.cpp` (250), `mcl_curve.cpp` (42) | precompiles 0x06–0x08 (alt_bn128 add, mul, pairing) | mcl |
| `blake2f.c` (122) | precompile 0x09 | own implementation; checked against the pure-Lean RFC 7693 F (`Evm.Crypto.Blake2f`, which the Lean replay runs) by `lake exe cryptoTests` |
| `point_evaluation.c` (134) | precompile 0x0a, EIP-4844 KZG point evaluation | blst (vendored) |
| `bls12381.cpp` (415) | precompiles 0x0b–0x11, EIP-2537 BLS12-381; and the Lean oracle `lean_bls_oracle_*` (the same blst calls) | blst (vendored) |
| `p256verify.c` (124) | secp256r1 verify (RIP-7212 / EIP-7951) | OpenSSL libcrypto |
| `rust/pq` (separate `libeita_pq`) | Arc's post-quantum precompile: SLH-DSA-SHA2-128s verify | the `slh-dsa` crate at the version arc-node pins |
| `rust/base` (separate `libeita_base`) | Base's native precompiles from Beryl: the B-20 factory and tokens, the policy and activation registries, from Cobalt the transaction-context and nonce-manager precompiles. Their logic is not restated: it is base/base's `base-common-precompiles` at the release Base runs, linked with base/base's own `Cargo.lock`; the shim forwards and holds no rule. Which addresses they are, the call boundary and the price of every world operation they perform are Lean (`Evm.Optimism.Beryl.Spec.NativePrecompiles`), emitted into `src/chains/op.lisp`'s host | base/base `crates/common/precompiles` @ v1.5.6 |

**How they are checked:** the ethereum/tests precompile fixtures, the EIP test
vectors for 2537 and 4844 (`c/test_bls12381.cpp`, `c/test_point_evaluation.c`), `lake exe
cryptoTests` (below), and mainnet replay with state-root checks. Gas for every precompile is computed in Lean, not here.

## Crypto oracles of the Lean semantics

The EIP-2537 and P256VERIFY precompiles are proved against EELS's wrappers (lengths, field
ranges, curve equation, subgroup-check placement, gas, failure modes, output encoding) for
EVERY crypto oracle (`Evm.Prague.Spec.Refinement.*_sound`, `Evm.Osaka.Spec.Refinement.
p256Verify_sound`). The Lean replay instantiates one oracle per library; that is what is
trusted, and `lean/AxiomAudit.lean`'s extern inventory enumerates its `@[extern]`s:

- BLS12-381 operations (G1/G2 addition, scalar multiplication, subgroup test, map-to-curve,
  pairing check) as computed by blst v0.3.17 (vendor/blst), via `lean/c/bls12381.cpp`
  (`Evm.Crypto.Bls12381.native`).
- P-256 ECDSA verification as computed by OpenSSL libcrypto 3.x `ECDSA_do_verify` (Homebrew
  openssl@3 on macOS, the distribution's libssl on Linux), via `lean/c/p256verify.c`
  (`Evm.Crypto.isValidP256Signature`).

What each oracle is assumed to compute is stated in Mathlib terms in
`lean/Evm/Crypto/Contracts.lean` (the Weierstrass group law over Fp / Fp2, `n • P` on the
order-r subgroup, the subgroup as `r • P = 0`, map-to-curve into the subgroup, an abstract
bilinear non-degenerate pairing, FIPS 186-5 ECDSA over Mathlib's P-256 curve) — assumptions,
not axioms. `lake exe cryptoTests` checks them on random inputs against the libraries (and
the Lean wrappers against the production C entries). BLAKE2F needs no oracle: F is pure Lean.

## Assumptions of the interpreter's stack-cache proof (ARM64, x86-64)

`Evm.CL.CacheSound.cacheIncoherent_sound` and `Evm.CL.ARM64.Interp.handler_runs_cache_coherent` (core
c3a1366) prove that every ARM64 interpreter handler keeps the register-cached top of the EVM stack (x6–x9,
x10–x13) equal to the stack's words at every dispatch exit. They assume, and do not prove:

- **Calls.** A C helper (`bl`, `blr`, far calls) preserves the AAPCS64 callee-saved registers, including x23
  (depth), x24 (stack base) and sp; everything else, all memory included, may change.
- **Memory separation (`Sep`).** A store the analysis does not place on the EVM stack (EVM memory, the state
  struct, the C frame), and any instruction outside the modelled semantics (`AsmRun.step`), leaves the stack
  words within sp₀ ± 65,538 unchanged.
- **Entry.** The stack depth is within [0, 1024] on entry.

Only `br x27` (dispatch) exits carry the obligation; fault and sync exits do not.

**x86-64.** `Evm.CL.X86CacheSound.xcacheIncoherent_sound` and `x86_handler_runs_cache_coherent` prove that
every x86-64 handler, in both lowerings the interpreter file links (flat: `brCont` = `ret`; threaded:
`brCont` = `nextItems`), keeps the cached top word (r8–r11) equal to stack[sp−1] at every dispatch exit
(`ret`, `jmp [mem]`, `jmp reg`). The proof is over the lowered `XItem` list and `X86Sem.xstep`, with the x86
register file, so ARM names sharing an x86 home and the lowering's temporaries are seen (`xrun_ret_coherent`
restates it for `X86Sem.xrun`). The checker it replaced, an x86 mode of the ARM64 analysis over ARM names,
was unsound five ways (`rejects_*`). It assumes, and does not prove:

- **Calls.** A helper or callback (`call [rip+slot]`, `call reg`) preserves the SysV callee-saved registers,
  including r13 (depth, bytes), r12 (stack base) and rsp; everything else, all memory included, may change.
- **Memory separation (`Sep`).** A store the analysis does not place on the EVM stack (EVM memory, the state
  struct, the C frame, `push`), and any instruction outside `xstep`, leaves the stack words within
  sp₀ ± 65,538 unchanged.
- **Entry.** r13 is a whole number of words, within [0, 1024], on entry.
- **Branches** land where `X86Cache.target` says: `xskipTo`'s forward rule, or back to a named label's
  definition (JUMPI's `_eita_jumpi_pop`); a branch to a label the body defines but `target` does not
  resolve is rejected, one to a label it does not define (a trampoline) leaves the body.

## Platform glue (no EVM semantics)

`lean/c/x86_run.c` (the x86-64 emitter's test
harness), `lean/c/csu_shim.c` (a glibc ≥ 2.34 link shim). A bug here can crash a run but cannot
change a result silently.

## Concurrency protocols of the state layer: modelled in Veil (`verify/protocols/`)

**Modelled, not derived.** The layer stack's protocols (freeze, the layer writer and GC's pins, minor and major
compaction and their swaps, background root checks, `rollback-to!`, the background fence) are Veil transition systems,
one action per step of the code they cite.

- **Proved:** `LayerGcFixed` (`ic3_safe`, kernel-checked); `Compaction` and `CompactionDeepReorg` (an inductive
  invariant, every verification condition a proof term rebuilt by lean-smt with `veil.smt.trust false`,
  kernel-checked). Axioms: propext, Classical.choice, Quot.sound only.
- **Violations of the old variants:** `LayerGcOld` has a kernel-checked `ic3_unsafe`; `LayerGcSwapped` and
  `CompactionDeepReorgOld` rest on Veil's explicit-state model checker and cvc5 1.3.2's `sat trace` (trusted).
- **Trusted, not proved:** that each action faithfully abstracts its code (kept current by `CheckCode.lean`: the
  `; @veil` markers in the Lisp and 9 structural ordering checks); the atomicity each action assumes; sequential
  consistency (ARM64 publication order is argued from the write barriers, which an ordering check enforces); for
  `Compaction` only, the caller's fork bound (`CompactionDeepReorg` holds without it).
- `scripts/verify-protocols.sh --quick` runs in CI (the code check and six models, under 14 GB); `CompactionDeepReorg`
  (over 32 GB) runs by hand on a large machine.
- **Design models, ahead of their code:** `RootWorker` and `CompactionV2` (snapshot v2's per-block root worker and
  its layer stack, `docs/state-snapshot-format.md`) are proved the same way, against the specification: their changed
  steps cite `@planned` names, which `CheckCode.lean` fails on once the code exists, so each becomes a checked `@code`
  citation in the change that writes it.

## The per-block state root (snapshot v2, specified)

The root worker (`docs/state-snapshot-format.md`, "The root worker"; its code is not yet written) mirrors
`lean/Evm/Trie/Frontier.lean` by hand, as `src/state/root.lisp` mirrors `Trie.Stack`. The gap is stated:
`layered_frontier_root_eq` (R, `sorry`) says the worker's two-level step over the layered store's composition yields
the fork's `stateRootBytes`. It assembles the proved lemmas F1–F3 with three stated ones (`patricialise_assemble`, L2;
`build_emits_frontier`, L1′; `stateRoot_two_levels`, L4), which wait on the total trie spec. Until R is proved, the
run-time checks are the header root of every block (every catch-up interval, bisected on mismatch), DenseAbove on
every recomputed dense branch, 32-byte references, the compaction's in-pass root with its entry-by-entry frontier
comparison, and the resume self-check.

## Statements pinned by the Lean comparator

A proof is only as good as the statement it proves. Forty-one headline theorems have their
statements written out in `lean/Comparator/Challenge.lean`, which is the human-reviewed record
(CODEOWNERS routes it for review, and `scripts/generated/comparator-challenge.sha256` must change
with it). They cover Block-STM, the IR compiler, the effect layer, the stack-cache
check (ARM64, x86-64), the ARM64 call and SSTORE gas routines, the op semantics of JUMP/JUMPI and
the memory-expansion prologue, the precompile wrappers (BLAKE2F, BLS12-381, P-256), and recent-fork
opcodes. `scripts/verify-comparator.sh` (in CI) runs `lake comparator`, the judge built into Lean
since v4.35.0 (the former `leanprover/comparator`), which builds and exports the challenge
and `lean/Comparator/Solution.lean` (each statement proved by the real theorem, at the real theorem's own type) in a
`bwrap` sandbox, with no network. It accepts only if every real theorem's kernel statement is the reviewed
one, every constant the statement mentions is the same in both, no proof uses `sorry` or an axiom outside the
config's list, and the kernel accepts the whole proof closure. So a weakened statement, an added
hypothesis, a `sorry` or a new axiom fails CI. Two lists:

- `comparator.json` (33 theorems): `propext`, `Quot.sound` and `Classical.choice` only.
- `comparator-native.json` (8 theorems: the handler cache-coherence verdicts and the gas routines'
  machine-code runs): those three plus 34 auxiliary axioms, each named, that `native_decide` /
  `bv_decide` generate. Each one states `decide p = true` for a closed `p` that Lean's compiled
  evaluator computed. Here the compiler is trusted, not the kernel. The script also rejects any
  source that names something `_native`, so no hand-written axiom can pass as one of them.

What it does not pin: the **definitions** the statements mention (`Refines`, `IsFrameRun`,
`IsClzStep`, …). The challenge imports them from `Evm.*`, so they are judged by reading them, and
the modules the challenge imports are trusted not to run hostile code at build time.

## Third-party libraries

| Library | Used for | License |
|---|---|---|
| libsecp256k1 | ECRECOVER, sender recovery | MIT |
| mcl | alt_bn128 precompiles | BSD-3-Clause |
| blst (vendored, pinned) | BLS12-381 precompiles, KZG point evaluation | Apache-2.0 |
| OpenSSL libcrypto | MODEXP, P-256 verify | Apache-2.0 |
| GMP (libgmp10, linked dynamically) | MODEXP for moduli ≤ 64 bytes | LGPL-3 / GPL-2 |
| zlib | compressed block files | zlib |
| `slh-dsa` (Rust) | Arc's SLH-DSA precompile | Apache-2.0 OR MIT |
| `base-common-precompiles` and its dependencies (Rust, base/base) | Base's native precompiles | MIT |

Other trusted pieces outside C, for completeness: the SBCL runtime and compiler, the Lean kernel
and the emitters' printers (the emitted text is what runs), and the Common Lisp host code that is
not yet emitted from Lean (listed in `scripts/generated/refinement-coverage.md`).

## `native_decide`

A proof by `native_decide` trusts the Lean compiler: the decision procedure is compiled and run, and its
answer is admitted through an auxiliary axiom (`…._native.native_decide.ax_…` in an axiom closure). Eita uses
it for finite checks over emitted code and tables (counts per component in
`scripts/generated/verification-stats.md`); `lean/AxiomAudit.lean`'s extern rule fails if such a proof
runs an `@[extern]` / `@[implemented_by]` constant outside its short reviewed list, so what is evaluated is
Lean code, not a C library.

## The native storage path

The design is [`native-storage.md`](native-storage.md). The effect logic (warm/cold, gas, refunds, original values, the journal entry) is not on this list: it is generated
from the effect IR, whose semantics (`Stmt.run`) carry the effect proofs. What is trusted is (1) the IR -> C printer,
the same class as the IR -> Lisp printer (`EffectIR.toCL`), and (2) the C primitives below. C has no bounds or type
checks: memory safety is an obligation of its own.

Classes: **derived** (emitted from a verified source), **proved** (a Lean theorem about the definition the C is emitted
from), **model-checked** (CBMC: memory safety, and equivalence to the Lean model at small sizes), **tested** (randomized
differential tests, sanitizer builds, the replay).

### Limb primitives — proved, emitted

`lean/Evm/CL/LimbC.lean`: each primitive is a term of a small limb language (expressions, conditions,
four-limb assignments) with a meaning, proved equal to its 256-bit operation through `Evm.CL.WordOps`
(`eq_ofBV`, `isZero_ofBV`, `toBV_ofBV`), and PRINTED to `c/generated/limb_ops.h` from the same
term by `lake exe emitLimbC`; `scripts/verify-host-emit.sh` fails on drift. No hand transcription.

| primitive | contract | theorem |
|---|---|---|
| `limb_eq(a, b)` | 1 iff the 256-bit values are equal | `eqB_spec` |
| `limb_is_zero(a)` | 1 iff the value is 0 | `isZeroB_spec` |
| `limb_copy(dst, src)` | dst := src | `copyA_spec` |
| `limb_zero(dst)` | dst := 0 | `zeroA_spec` |

### The SLOAD effect in C — derived

`c/generated/storage_effect.c` (`eita_spec_sload_effect`) is `Evm.CL.EffectSload.term` printed as C by
`Evm.CL.EffectC` (`lake exe emitStorageC`, drift-checked); the term and its proof (`sload_refines`) are
untouched, and this is the term's only printing. Trusted: the printer (the same class as `toCL`;
it fails on any construct outside its subset rather than skipping it) and the primitives below.

### The SLOAD/SSTORE host — tested

`c/storage_host.{h,c}`: `eita_cb_sload` / `eita_cb_sstore` in the callbacks vtable's SLOAD/SSTORE slots are the
opcodes' one execution path. Each binds the frame account and key (the account's id from a 64-entry
cache keyed by the slot tables' serial, a freed table's address may be reused; an address not in it is
learned once from Lisp, `cb-storage-learn`), runs the emitted effect, then calls the Lisp hook
(`cb-storage-hook`) when the read stream is on, the account is watched, or (SSTORE) the slot changed while the
incremental root checker tracks dirty slots. Its primitives: `eita_sh_fault` (`eita_ws_get`; a key absent from a
lazy world is loaded through `cb-storage-fault`, the world's fault hook, and read again; absent = zero; the
observers' first touch), `eita_sh_sload` (`limb_copy`, and the value kept as the current one),
`eita_sh_access_slot` / `eita_sh_orig_record` (the native TxState, unchanged). **Checked by** the fixtures
(every GeneralStateTests storage directory), a 30,000-block mainnet replay,
and `tests/native-storage-hooks.lisp`; the lint `check-derived-gas.py` covers its C (no gas constant outside the
emitted file).

### Table primitives — proved in Velvet for every capacity, emitted

`c/world_slots.h` (the ABI) over `c/world_slots_emit.c` (generated, do not edit) and `c/world_slots.c` (glue):
per account id, one open-addressed table of slot -> value, under a directory per account table. The Lean model is
a finite map (`lean/Evm/CL/WorldSlotsModel.lean`: get / put / remove / drop / copy).

| primitive | contract (on the model) | memory-safety obligations |
|---|---|---|
| `eita_ws_probe(t, key)` | index of the key's entry, or -1 - the insertion point (first tombstone on the path, else the empty entry ending it) | index < capacity; terminates (used < capacity) |
| `eita_ws_get(w, id, key)` | the value's limbs iff (id, key) present, else NULL | reads only inside the entry array |
| `eita_ws_put(w, id, key, val)` | map[(id, key)] := val; id has a table | grows before the load passes 3/4 (4 used <= 3 cap kept); sizes cannot overflow (cap <= 2^40) |
| `eita_ws_remove(w, id, key)` | (id, key) absent; id has a table | tombstone; count never negative |
| `eita_ws_drop(w, id)` | id has no table and no keys | frees the table once |
| `eita_ws_copy(dst, id, src)` | dst's id := src's table (contents, own arrays) | copies exactly cap entries |
| `eita_ws_map(w, id, fn)` / the Lisp walk `acct-slots-map` | fn(key, value) for every key of id, in table order | no write to id during the walk |
| growth (`ws_grow`, inside put) | the map unchanged; capacity doubled when over half full, else a same-size rehash | the old arrays freed after the copy |

**Proved.** Every table decision is a Velvet method (Lean, Velvet's vcgen; the proofs use only `propext`,
`Classical.choice` and `Quot.sound`, no `sorry`, no `native_decide`, no solver axiom), proved for EVERY capacity
against the model, and `c/world_slots_emit.c` is printed from those methods: the probe and its insertion index
(the first non-full slot on the probe path), place, remove, the load test and the growth rule, the rehash
(occupancy `4·used <= 3·cap` kept, the map unchanged, aborts only past `WS_MAX_CAP`), lookup, the walk step,
the 4-entry fresh table, the directory size rule (aborts only for an id >= 2^40) and the array copy. At the world
level, the glue's operations (touch, put, remove, drop, get, has-table, copy) are proved equal to the model's
under the abstraction, the walk visits exactly the present (key, value) pairs in index order, and every abort
condition is stated exactly. The printer indexes arrays only under a proved bound, so every array access in the
emitted C is in bounds by proof. The proofs and the printer are `verify/velvet-slots/`, a Lake
package of its own (Velvet, on core's toolchain; `lean/` gains no dependency) that compiles core's
`WorldSlotsModel.lean` in place; `scripts/verify-velvet-slots.sh` (in CI) builds every proof, checks the axioms,
regenerates `c/world_slots_emit.c` and fails on any difference.

**Still trusted.**
- The Velvet C printer: Lean method bodies -> C, the same class as the effect IR's printers.
- `Nat` fits in 64 bits: the methods compute on `Nat`, the C on `uint64_t`. Informally bounded: the emitted
  aborts keep capacities and ids below 2^40, so `8·cap`, `4·(used+1)` and the directory size cannot wrap.
- The glue `c/world_slots.c` (135 lines, 90 of code): packs and unpacks the struct, frees the arrays a grow replaced,
  keeps the directory's pointer array, calls the map callback. It makes no table decision; the package's
  world-level proofs (`verify/velvet-slots/Slots/World.lean`) mirror it line by line, but the glue itself is hand-written C.

**Also checked.** CBMC (`c/cbmc/run.sh`, 11 proofs, in CI): for an arbitrary
table of capacity 4 or 8 satisfying the probing invariant, get, place, remove and grow are memory-safe (bounds,
pointers, frees, leaks, overflow, conversions) and agree with the model; the directory with concrete ids. Since
the Velvet proofs cover every capacity, CBMC is a cross-check of the C as compiled (the printer, the glue, the
`Nat`/`uint64_t` gap). Randomized: `c/test_world_slots` under ASan + UBSan and on a
trace of the Lean model itself (`lake exe worldSlotsVectors`); `tests/world-slots.lisp`; the fixtures (every
GeneralStateTests storage directory) and the mainnet replay.

### The SSTORE effect in C, its journal entry and the native revert — derived + tested

`eita_spec_sstore_effect` and `eita_spec_sstore_plan` (c/generated/storage_effect.c) are
`Evm.CL.EffectSstore.term` and `SstoreSched.ofFork` printed as C (their only printing;
`sstore_refines` untouched); the schedules themselves are the
emitted native routines (`eita_sstore_gas_*`, proved in `Evm.CL.ARM64.SstoreGasSem`). The host primitives
(c/storage_host.c, tested):

| primitive | contract |
|---|---|
| `eita_sh_orig_get` | the slot's original value (the native TxState's record, else the current value) |
| `eita_sh_sstore_gas` | runs the fork's schedule on (refund, original, current, new, cold); refund counter := its new refund via `eita_ts_refund_add` (journaled, as `refund-add!`); returns the cost |
| `eita_sh_set_storage` | appends a type-0 entry in `journal-push!`'s layout (type, addr, key, old = the current value), then (self, key) := w, removed when w = 0 in a full world (`world-storage-set`); the root checker's dirty slot through the hook |
| `eita_sh_revert_storage` | for a revert's slice, newest first: each type-0 entry restored into the slot table (the id from the cache, or from learn on a miss) and retyped 255 (skipped by the host loop and `eita_ts_revert`); returns the count; stops at the first un-create entry (type 10), below which the host replays in order; off while the read stream is on (the Lisp restore streams each write) |

**Checked by** the fixtures (every SSTORE/refund/revert directory), `c/test_storage_host.c` (the native revert alone restores a slice whose accounts
collide in the cache) and the replay.

### Lisp accessors and hook tiers — tested

The routed Lisp accessors (the routing list in docs/native-storage.md) and the hook tiers:
(a) the observers' first-touch log (c/storage_host.c `eita_sh_touch`: one ordered log of every slot's first
touch in a tx with its value then, written by the native effects and by `observe-slot-touch!`, read by
`do-storage-changes`); (b) the watch filter (up to 16 accounts whose SLOAD/SSTOREs call the hook, which calls
`*storage-access-hook*`); (c) the hook mode: the native effect plus `cb-storage-hook` per access while the read
stream is on. **Checked by** the differential, the fixtures, the mainnet replay and
`tests/native-storage-hooks.lisp` (observed fixtures: rows equal with and without the watch; rows and watched
accesses equal a recorded digest).

## The gas formulas in C, for hosts with no Lisp — derived + tested

`src/generated/host.lisp` prints the consensus gas formulas as Common Lisp, where every
intermediate is a bignum for free. A host on a 32-bit microcontroller has no Lisp and no
bignum, and hand-writing a gas schedule there would be exactly the parallel copy
CONTRIBUTING rule 4 forbids (and `scripts/check-derived-gas.py` refuses in the Lisp). So
`Evm.CL.GasEmitC` adds a **second printer over the same `Evm.CL.GasEmit.Expr` terms**:
`lake exe emitHostC` writes `c/generated/host.{c,h}`, freestanding C over `uint64_t` with
no runtime, which compiles for `rv32imac` as it does for the host (4.7 KiB of rv32 text for
the whole set). The terms, their `eval` and the EIP-number kernel checks are untouched.

**Trusted.**
- The printer `Expr.toC` — the same class as `toCL`: it fails on any construct outside its
  subset rather than emitting something approximate.
- The checked-arithmetic prelude (`GasEmitC.preludeC`, 11 helpers of one line each): `add`,
  `mul`, `sub` (truncated, = `toCL`'s `(max 0 (- a b))`), `fdiv`, `max`, `min`, `blen`
  (= CL `integer-length`), `pow2`, a 4-limb `u256_blen`, and `fake_exponential` — the one
  loop the IR has, mirroring the already-hand-written `GasEmit.fakeExponentialCL` line for
  line (the Lean meaning is `Evm.Cancun.Spec.fakeExponential`).
- That `Nat` fits in 64 bits for the formulas emitted. This is *not* taken on faith:
  `add`, `mul`, `pow2` and division call `eita_spec_overflow` (declared `noreturn`) rather
  than wrapping, so the gap is a loud stop and never a wrong number. A replay host may
  abort there; a signing device must refuse to sign.

**Restricted on purpose.** `GasEmitC.Dom` splits the table into `gas` (bounded by the block
gas limit, so 64 bits hold every value *and* every intermediate) and `wei` (bounded by
nothing the chain enforces). Only `gas` formulas are emitted; the `wei` ones —
`spec-block-base-reward`, `spec-uncle-inclusion-bonus`, `spec-uncle-reward`,
`spec-blob-base-fee`, `spec-effective-gas-price` — wait for a 256-bit printer, and
`c/generated/host.h` lists them. The reason is concrete rather than cautious: an ether
reward is ~5·10^18 before it is multiplied by anything, and `uncle-reward` trapped on its
own first vector. The Lisp host emits all of them.

**Checked by** `c/test_host_gas.c` (emitted by `lake exe emitHostC --vectors`): 670 vectors
over every emitted function, each expected value computed by `Expr.eval` *in Lean* — the
meaning the printer is a second view of. `fork-ord` is swept over every fork, sizes over the
thresholds the formulas branch on (32/33, 64/65, 1024/1025), and the one 256-bit input
(MODEXP's `exp-head`) past 2^64, which is what would catch a truncated limb.
`scripts/verify-host-emit.sh` regenerates all three artifacts, fails on drift, and runs the
vectors (`make -C c test_host_gas`); `make -C c host_gas_rv32` compiles the same C
freestanding for the target.

## The message-call gas — derived + **proved**

`Evm.CL.GasEmit.callExtraGas` and `callStipendGas` (emitted as
`spec-call-extra-gas` / `spec-call-stipend-gas`) are what a host charges and
forwards for the CALL family. A host has to own that arithmetic — the
interpreter's call gadget fills `CallParams` and charges whatever
`CallResult.gas_used` says — so written by hand they would have been a parallel
copy of EELS `calculate_message_call_gas`, which CONTRIBUTING rule 4 forbids
and `scripts/check-derived-gas.py` refuses on the Lisp side.

`Evm.CL.GasEmitCall` proves them instead: equal to
`Evm.Berlin.Vm.Effect.callGasPlan`'s `charge` and `stipend`, for every fork from
Berlin on, over every combination of cold / value-bearing / new-account.

**Axiom closure: `propext`, `Quot.sound`.** No `native_decide`, no
`bv_decide`, no `sorry` — the smallest trust class in the tree, and an
exception to this page's premise, which is why it is listed rather than
omitted.

**Not covered** (so: trusted if ever reached):
- the pre-Berlin eras `callExtraGas` also encodes — EIP-150's flat 700
  (Tangerine Whistle) and Frontier's 40 — against those forks' own
  `callGasPlan`. The rv32 wallet host refuses any fork below Berlin.
- EIP-7702 delegation: `delegatedCost` is taken as 0. A host supporting
  delegated EOAs must add `spec-delegate-access-gas`, and that addition is a
  new trusted step.
- `callGasPlan.forward` is not proved equal to `retain63of64` applied to
  `avail - charge`, though the two are written to be the same quantity.

A consumer's own trusted surface still includes deciding `cold`,
`value-nonzero` and `new-acct` correctly, and adding the sub-frame's
consumption. Those three predicates are the consumer's obligation, not this
repo's: nothing here can check that a host classified a slot as warm honestly.

## The SSTORE gas schedules in C — derived + **proved**

`_eita_sstore_gas_{legacy,eip1283,eip2200,berlin,london}` exist twice as
emitted ASSEMBLY — `Evm.CL.ARM64.SstoreGas` (proved in `SstoreGasSem`) and
`Evm.CL.X86SstoreGas` (proved in `X86SstoreGasSem`). A 32-bit target can use
neither: the bodies could be lowered, but not ENTERED, because on ILP32 a
`uint64_t` parameter takes an ALIGNED register pair, so `refund` lands in a2:a3
and `cold` past a7 and onto the stack. x86-64's constraint looked similar but
was register PRESSURE inside an unchanged ABI; this is the ABI.

`Evm.CL.SstoreGasC` prints them as C instead, and `c/Makefile` links that for
rv32 **in place of** the assembly — never alongside it, since both define the
same five symbols. This is a third derivation, not a second owner:
`ARM64.SstoreGasDenote.plan*` remains the single definition.

**Why it is small.** Every plan is a function of SEVEN BOOLEANS — origZero,
curZero, newZero, origEqCur, curEqNew, origEqNew, cold — and a refund counter
that only ever enters as

    refund' = ((refund + add1) - sub) + add2        (saturating subtraction)

Four of the five are that with `add2 = 0`; `eip2200`'s chain needs the trailing
add because its subtraction saturates BETWEEN the two additions and cannot be
folded. So each schedule is a table of `(cost, add1, sub, add2)` over those
bits, and the bits collapse hard — eip1283's 64 patterns give 11 distinct rows.
The whole file is 212 lines.

**Proved** (`propext`, `Quot.sound` only — no `native_decide`, no `sorry`):
`applyRow_is_legacy`, `applyRow_is_eip1283`, `applyRow_is_eip2200`,
`applyRow_is_2929`. Each says `plan* refund preds = (row.cost, applyRow refund
row)`, universally quantified over the refund counter AND over all seven
predicates — not a sample of patterns, because the rows are stated over the
booleans rather than over a packed index.

**Trusted — one line.** That the emitted C expression implements `applyRow`.
The C is text, not a Lean term, so no theorem reaches it. Pinned instead by
`c/test_sstore_gas.c` (emitted): every reachable predicate pattern at nine
refund counters chosen around the saturation edges, with expected values from
Lean's own `plan*` — 1350 checks. The unreachable patterns (contradictory
predicate combinations, e.g. `origEqCur` with `orig` zero and `cur` not) are
skipped, and the reachable COUNT is asserted, because a build that silently
skipped everything would otherwise read as a pass. `applyRow_is_*` covers all
128 patterns regardless.

**Also checked on the target**: the rv32 self-test calls the London schedule
for a warm set, a cold set and a reset-to-zero, so the same emitted C compiled
for rv32imac runs under `qemu-system-riscv32`. 20000 / 22100 / 2900 with 4800
added to the refund counter are independently recognisable London numbers.

Under QEMU, *not* on silicon: the bao1x board has run the self-test's first
seven checks (the arithmetic, the helper-call path and `gas(ADD)`), which is
the build that was flashed when the five bring-up bugs were fixed. The
SSTORE-schedule check and the jump, signed-compare, EXP and CLZ checks that
came later are QEMU-verified only. The distinction matters here more than
usual, because QEMU *emulates* misaligned loads and stores and this core traps
them — the one failure class an emulator structurally cannot reproduce.
