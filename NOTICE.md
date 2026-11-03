# Notices and third-party material

Eita is MIT-licensed (`LICENSE`, copyright Valeriy Zamaraiev). It vendors, links, derives
from, or tests against the following works. Their licenses apply to those parts.

## Vendored source

| path | work | license |
|---|---|---|
| `vendor/blst` (git submodule, pinned commit) | [supranational/blst](https://github.com/supranational/blst) — BLS12-381 (EIP-2537, EIP-4844 point evaluation) | Apache-2.0 |
| `lean/c/ripemd160.c` | RIPEMD-160 after the public-domain reference implementation (Bosselaers, Dobbertin; COSIC) | public domain (reference); this file MIT |
| `lean/c/keccak.c`, `keccak_sha3.c`, `keccak_batch.c` | Keccak-f[1600] (Ethereum's pre-FIPS-202 padding); first written after the structure of [tiny_sha3](https://github.com/mjosaarinen/tiny_sha3) (Saarinen, MIT), since rewritten | MIT |
| `lean/c/sha256.c`, `blake2f.c` | FIPS 180-4 SHA-256 and the BLAKE2b F function (RFC 7693, EIP-152), written for this project | MIT |
| `lean/c/point_evaluation.c` | embeds one point of the Ethereum KZG ceremony's trusted setup (`[s]G2`), as given in EELS `crypto/kzg.py` and c-kzg-4844 `trusted_setup.txt` | CC0 (EELS) / Apache-2.0 (c-kzg-4844) |
| `chains/ethereum/genesis.json` | Ethereum mainnet genesis allocation (public chain data) | — |

## Linked libraries (not vendored; installed by the build)

| library | used for | license |
|---|---|---|
| [libsecp256k1](https://github.com/bitcoin-core/secp256k1) | ECRECOVER, sender recovery | MIT |
| [mcl](https://github.com/herumi/mcl) | BN254 (EIP-196/197) | BSD-3-Clause |
| OpenSSL `libcrypto` | MODEXP bignums, P256VERIFY (EIP-7951 / RIP-7212) | Apache-2.0 |
| zlib | reading gzip'd block and fixture files | zlib |
| [slh-dsa](https://github.com/RustCrypto/signatures) (Rust crate, via `rust/pq`) | Arc's post-quantum precompile (FIPS 205) | Apache-2.0 OR MIT |

## Lean dependencies (fetched by Lake, `lean/lake-manifest.json`)

| package | license |
|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) and its dependencies (batteries, aesop, Qq, ProofWidgets, plausible, importGraph, LeanSearchClient, Cli) | Apache-2.0 |
| Lean 4 toolchain | Apache-2.0 |

## Common Lisp dependencies (ocicl, pinned by digest in `ocicl.csv`; fetched, not vendored)

cffi (MIT), jsown (MIT), cl-fad (BSD-2-Clause), alexandria (public domain / MIT-style); and
theirs: babel (MIT), trivial-features (MIT), bordeaux-threads (MIT), global-vars (MIT),
trivial-garbage (public domain). The ocicl runtime that loads them (`build.sh`) is MIT.

## Specifications the Lean semantics translate

- **Ethereum execution specs** ([ethereum/execution-specs](https://github.com/ethereum/execution-specs), "EELS"),
  CC0-1.0. The Lean fork modules under `lean/Evm/<Fork>/` translate EELS clause by clause and
  cite it by file and line. EELS is the reference; the Yellow Paper is not.
- **OP Stack specs** ([ethereum-optimism/specs](https://github.com/ethereum-optimism/specs)), MIT —
  `lean/Evm/Optimism/` (cited per file).
- **Arc** ([circlefin/arc-node](https://github.com/circlefin/arc-node)), Apache-2.0 — `lean/Evm/Arc/`,
  `src/chains/arc-precompiles.lisp`, `src/chains/arc.lisp` port its precompiles and system
  rules, citing files and commits. No arc-node source is copied.
- EIPs (CC0-1.0).

## Test vectors

- `lean/c/testdata/kzg-verify-proof-vectors.txt`: from c-kzg-4844 v2.1.1 tests (Apache-2.0).
- `lean/c/testdata/bls12381-*.json`: inputs and outputs captured from the Arc chain's own execution (public chain data).
- The fixture battery runs [ethereum/tests](https://github.com/ethereum/tests) and
  [execution-spec-tests](https://github.com/ethereum/execution-spec-tests) fixtures (MIT), downloaded, not vendored.
