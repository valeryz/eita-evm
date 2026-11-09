# The trusted surface

Eita's EVM semantics are written in Lean 4 as a clause-by-clause translation of the Ethereum
execution specs (EELS), and the parts that execute — the ARM64 and x86-64 interpreters, the
JIT's chunk code, the gas routines and the host's effect code (`src/generated/host.lisp`) —
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
| `eita_jumpdest_map`, `eita_run`, `eita_run_program`, `eita_clear_icache` | jump-destination analysis and the entry trampolines |

**How it is checked:** `c/test_compute.c` compares every helper against GMP on edge constants and
random operands (about 17.9M cases), including the 64-bit wrap of buffer offsets; the Ethereum
test fixtures run through these helpers on both execution tiers.

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

**How they are checked:** the ethereum/tests precompile fixtures on both tiers, the EIP test
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

`lean/c/uds.c` (the JIT emit server's socket), `lean/c/x86_run.c` (the x86-64 emitter's test
harness), `lean/c/csu_shim.c` (a glibc ≥ 2.34 link shim). A bug here can crash a run but cannot
change a result silently.

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

Other trusted pieces outside C, for completeness: the SBCL runtime and compiler, the Lean kernel
and the emitters' printers (the emitted text is what runs), and the Common Lisp host code that is
not yet emitted from Lean (listed in `scripts/generated/refinement-coverage.md`).

## Planned: the native storage path (owner note 6; docs/native-storage.md)

Each section is filled in as its step lands. The effect logic (warm/cold, gas, refunds, original values, the journal entry) is not on this list: it is generated
from the effect IR, whose semantics (`Stmt.run`) carry the effect proofs. What is trusted is (1) the IR -> C printer,
the same class as today's IR -> Lisp printer (`EffectIR.toCL`), and (2) the C primitives below. Unlike the Lisp it
replaces, C has no bounds or type checks: memory safety is an obligation of its own.

Classes: **derived** (emitted from a verified source), **proved** (a Lean theorem about the definition the C is emitted
from), **model-checked** (CBMC: memory safety, and equivalence to the Lean model at small sizes), **tested** (randomized
differential tests, sanitizer builds, the replay).

### Limb primitives — proved, emitted (built: step 3)

`lean/Evm/CL/LimbC.lean`: each primitive is a term of a small limb language (expressions, conditions,
four-limb assignments) with a meaning, proved equal to its 256-bit operation through `Evm.CL.WordOps`
(core def68c3: `eq_ofBV`, `isZero_ofBV`, `toBV_ofBV`), and PRINTED to `c/generated/limb_ops.h` from the same
term by `lake exe emitLimbC`; `scripts/verify-host-emit.sh` fails on drift. No hand transcription.

| primitive | contract | theorem |
|---|---|---|
| `limb_eq(a, b)` | 1 iff the 256-bit values are equal | `eqB_spec` |
| `limb_is_zero(a)` | 1 iff the value is 0 | `isZeroB_spec` |
| `limb_copy(dst, src)` | dst := src | `copyA_spec` |
| `limb_zero(dst)` | dst := 0 | `zeroA_spec` |

### The SLOAD effect in C — derived (built: step 3)

`c/generated/storage_effect.c` (`eita_spec_sload_effect`) is `Evm.CL.EffectSload.term` printed as C by
`Evm.CL.EffectC` (`lake exe emitStorageC`, drift-checked); the term and its proof (`sload_refines`) are
untouched, and since step 6 this is the term's only printing. Trusted: the printer (the same class as `toCL`;
it fails on any construct outside its subset rather than skipping it) and the primitives below.

### The SLOAD/SSTORE host — tested (built: steps 3-6)

`c/storage_host.{h,c}`: `eita_cb_sload` / `eita_cb_sstore` in the callbacks vtable's SLOAD/SSTORE slots are the
opcodes' one execution path (step 6). Each binds the frame account and key (the account's id from a 64-entry
cache keyed by the slot tables' serial, a freed table's address may be reused; an address not in it is
learned once from Lisp, `cb-storage-learn`), runs the emitted effect, then calls the Lisp hook
(`cb-storage-hook`) when the read stream is on, the account is watched, or (SSTORE) the slot changed while the
incremental root checker tracks dirty slots. Its primitives: `eita_sh_fault` (`eita_ws_get`; a key absent from a
lazy world is loaded through `cb-storage-fault`, the world's fault hook, and read again; absent = zero; the
observers' first touch), `eita_sh_sload` (`limb_copy`, and the value kept as the current one),
`eita_sh_access_slot` / `eita_sh_orig_record` (the native TxState, unchanged). **Checked by** the fixtures
(every GeneralStateTests storage directory), the differential (JIT vs interpreter), the 30k replay, the fact
log and storage view of the 30k range compared with the ones step 5's Lisp path wrote, and
`tests/native-storage-hooks.lisp`; the lint `check-derived-gas.py` covers its C (no gas constant outside the
emitted file).

### Table primitives — proved in Velvet for every capacity, emitted (built: owner note 6 step 2; emitted since the Velvet swap)

`c/world_slots.h` (the ABI) over `c/world_slots_emit.c` (generated, do not edit) and `c/world_slots.c` (glue):
per account id, one open-addressed table of slot -> value, under a directory per account table. The Lean model is
a finite map (`lean/Evm/CL/WorldSlotsModel.lean`: get / put / remove / drop / copy). Until this swap the table was
164 lines of hand-written C (126 of code), model-checked by CBMC at capacities 4 and 8 only.

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
emitted C is in bounds by proof. The proofs, the printer and a drift check that regenerates
`c/world_slots_emit.c` and fails on any difference live in Eita's separate Velvet package (its own Lean toolchain;
core gains no Lean dependency); they will be published.

**Still trusted.**
- The Velvet C printer: Lean method bodies -> C, the same class as the effect IR's printers.
- `Nat` fits in 64 bits: the methods compute on `Nat`, the C on `uint64_t`. Informally bounded: the emitted
  aborts keep capacities and ids below 2^40, so `8·cap`, `4·(used+1)` and the directory size cannot wrap.
- The glue `c/world_slots.c` (135 lines, 90 of code): packs and unpacks the struct, frees the arrays a grow replaced,
  keeps the directory's pointer array, calls the map callback. It makes no table decision; the package's
  world-level proofs mirror it line by line, but the glue itself is hand-written C.

**Still checked** (unchanged, now on the emitted C). CBMC (`c/cbmc/run.sh`, 11 proofs, in CI): for an arbitrary
table of capacity 4 or 8 satisfying the probing invariant, get, place, remove and grow are memory-safe (bounds,
pointers, frees, leaks, overflow, conversions) and agree with the model; the directory with concrete ids. Since
the Velvet proofs cover every capacity, CBMC is now a cross-check of the C as compiled (the printer, the glue, the
`Nat`/`uint64_t` gap) rather than the only evidence. Randomized: `c/test_world_slots` under ASan + UBSan and on a
trace of the Lean model itself (`lake exe worldSlotsVectors`); `tests/world-slots.lisp`; the fixtures (every
GeneralStateTests storage directory) and the 30k replay.

### The SSTORE effect in C, its journal entry and the native revert — derived + tested (built: step 4)

`eita_spec_sstore_effect` and `eita_spec_sstore_plan` (c/generated/storage_effect.c) are
`Evm.CL.EffectSstore.term` and `SstoreSched.ofFork` printed as C (their only printing since step 6;
`sstore_refines` untouched); the schedules themselves are the
emitted native routines (`eita_sstore_gas_*`, proved in `Evm.CL.ARM64.SstoreGasSem`). The host primitives
(c/storage_host.c, tested):

| primitive | contract |
|---|---|
| `eita_sh_orig_get` | the slot's original value (the native TxState's record, else the current value) |
| `eita_sh_sstore_gas` | runs the fork's schedule on (refund, original, current, new, cold); refund counter := its new refund via `eita_ts_refund_add` (journaled, as the Lisp's `refund-add!`); returns the cost |
| `eita_sh_set_storage` | appends a type-0 entry in `journal-push!`'s layout (type, addr, key, old = the current value), then (self, key) := w, removed when w = 0 in a full world (`world-storage-set`); the root checker's dirty slot through the hook |
| `eita_sh_revert_storage` | for a revert's slice, newest first: each type-0 entry of an account with a known id restored into the slot table and retyped 255 (skipped by the host loop and `eita_ts_revert`); stops at the first un-create entry (type 10), below which the host replays in order; off while the read stream is on (the Lisp restore streams each write) |

**Checked by** the fixtures (every SSTORE/refund/revert directory), the differential (to step 5 native vs the
Lisp effect, journal entries byte for byte, on every tx of the storage fixtures and sampled on the 30k replay;
from step 6 JIT vs interpreter on the one path) and the replay.

### Lisp accessors and hook tiers — tested (built: steps 2, 5 and 6)

The routed Lisp accessors (the routing list in docs/native-storage.md) and the hook tiers:
(a) the observers' first-touch log (c/storage_host.c `eita_sh_touch`: one ordered log of every slot's first
touch in a tx with its value then, written by the native effects and by `observe-slot-touch!`, read by
`do-storage-changes`); (b) the watch filter (up to 16 accounts whose SLOAD/SSTOREs call the hook, which calls
`*storage-access-hook*`); (c) the hook mode: the native effect plus `cb-storage-hook` per access while the read
stream is on (step 5 swapped the vtable to the Lisp callbacks instead; step 6 deleted them). **Checked by** the
differential, the fixtures, the 30k replay, `tests/native-storage-hooks.lisp` (observed fixtures: rows equal with
and without the watch; rows and watched accesses equal a digest recorded from step 5's Lisp path), and the fact
log and storage view of the 30k range compared with the ones the Lisp path wrote (step 5: rows and content
hashes in every sealed segment; step 6: against step 5's Lisp-path outputs).
