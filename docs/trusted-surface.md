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
| `modexp.c` (101) | precompile 0x05 (its gas is computed in Lean) | OpenSSL `BN_mod_exp` |
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
| zlib | compressed block files | zlib |
| `slh-dsa` (Rust) | Arc's SLH-DSA precompile | Apache-2.0 OR MIT |

Other trusted pieces outside C, for completeness: the SBCL runtime and compiler, the Lean kernel
and the emitters' printers (the emitted text is what runs), and the Common Lisp host code that is
not yet emitted from Lean (listed in `scripts/generated/refinement-coverage.md`).
