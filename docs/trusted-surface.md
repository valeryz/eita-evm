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
| `blake2f.c` (96) | precompile 0x09 | own implementation |
| `point_evaluation.c` (134) | precompile 0x0a, EIP-4844 KZG point evaluation | blst (vendored) |
| `bls12381.cpp` (280) | precompiles 0x0b–0x11, EIP-2537 BLS12-381 | blst (vendored) |
| `p256verify.c` (114) | secp256r1 verify (RIP-7212 / EIP-7951) | OpenSSL libcrypto |
| `rust/pq` (separate `libeita_pq`) | Arc's post-quantum precompile: SLH-DSA-SHA2-128s verify | the `slh-dsa` crate at the version arc-node pins |

**How they are checked:** the ethereum/tests precompile fixtures on both tiers, the EIP test
vectors for 2537 and 4844 (`c/test_bls12381.cpp`, `c/test_point_evaluation.c`), and mainnet
replay with state-root checks. Gas for every precompile is computed in Lean, not here.

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

### Limb primitives — proved, emitted

Defined in Lean limb by limb as the C computes them, proved equal to the U256 operation (the WordOps.lean pattern of
core def68c3: `eq_ofBV`, `isZero_ofBV`, `lt_ofBV`, `sub_ofBV`, `add_ofBV` over `Limbs.ofBV`/`toBV`), and emitted to
`c/generated/limb_ops.h`; `verify-host-emit.sh` checks the emitted file for drift.

| primitive | contract |
|---|---|
| `limb_eq(a, b)` | 1 iff the 256-bit values are equal |
| `limb_is_zero(a)` | 1 iff the value is 0 |
| `limb_copy(dst, src)` | dst := src, 4 limbs |
| `limb_zero(dst)` | dst := 0 |

### Table primitives — model-checked + tested (built: owner note 6 step 2)

`c/world_slots.{h,c}` (about 150 lines): per account id, one open-addressed table of slot -> value, under a
directory per account table. The Lean model is a finite map (`lean/Evm/CL/WorldSlotsModel.lean`: get / put /
remove / drop / copy, with the lemmas each primitive is tested for).

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

**How it is checked.** CBMC (`c/cbmc/run.sh`, 11 proofs, about 5 minutes, in CI): for an ARBITRARY table of
capacity 4 or 8 satisfying the probing invariant, each of get, place (a put with room), remove and grow is
memory-safe (bounds, pointers, frees, leaks, overflow, conversions), keeps the invariant and the load bound, and
agrees with the finite-map model on an arbitrary key; the directory (growth, independent accounts, drop, copy)
with concrete ids. Not covered by CBMC: the doubling from 8 to 16 (beyond the memory cap; the randomized tests
grow through 2^17). Randomized: `c/test_world_slots` under ASan + UBSan (random ops against a reference map,
bulk growth) and on a trace of the Lean model itself (`lake exe worldSlotsVectors`); `tests/world-slots.lisp`
against a finite map and against the Lisp table it replaced, walk order included; the fixtures (every
GeneralStateTests storage directory) and the 30k replay.

### Journal — model-checked + tested

| primitive | contract |
|---|---|
| `journal_append_sstore(arena, acct, key, old)` | appends one type-0 entry at journal_count, increments it; never past the arena's capacity |
| type-0 restore in `eita_ts_revert` | for each type-0 entry above the target, in reverse order: map[(acct, key)] := old |

### Lisp accessors and hooks — tested

The routed Lisp accessors (the routing list in docs/native-storage.md) and the hook tiers are tested: the differential
mode (native path vs the Lisp path), the fixtures including every SSTORE/refund/revert directory, the 30k replay
(0 mismatches), and byte-identical fact-log rows and storage view against the Lisp path.
