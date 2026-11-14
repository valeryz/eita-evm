# Eita

**An open-source EVM engine for Ethereum (non-validating at this point): it executes and
verifies every block from genesis, with EVM semantics written in Lean 4 — translated clause
by clause from the Ethereum execution specs (EELS) and proved — and native execution code
emitted from that spec, not written by hand. It is built so that turning it into a full
execution client is a small step: an Engine API block source (see Roadmap), plus the usual
client scaffolding.**

**EITA** — **E**VM **I**nline-**T**hreaded **A**rchitecture.
*(Alternatively unpacked as **E**VM **I**nductive **T**race **A**ccelerator —
same project, verification-flavored framing. Or, on Friday afternoons,
**E**thereum **I**s **T**ail-recursive, **A**llegedly.)*

Eita replays a chain and verifies it: every block's header against its parent (EELS
`validate_header`, `validate_ommers`), every transaction, the gas used, logs bloom and
receipts root, the senders against their signatures, and the state root against the header
at anchors — with full state from genesis, snapshots, and resume from a verified anchor. It
runs Ethereum mainnet from genesis and the ethereum/tests BlockchainTests battery green on
two execution tiers. Load it into a Lisp REPL and you can execute transactions against a
world you build, or against a test's pre-state, and inspect balances, storage, logs and the
state root.

**What it is not (yet).** Eita has no p2p networking and no Engine API: it does not sync
from peers or follow a consensus client. Blocks come from you, through a documented
block-source interface (`docs/block-input.md`); this repository ships a reader for
per-block JSON files you produce with your own node or tools.

## See it running: [eita.run](https://eita.run)

This engine is not a demo. It runs in production at **[eita.run](https://eita.run)**:

- **Ethereum mainnet, every block since genesis (2015)**, re-executed and checked, and now
  following the chain tip as new blocks arrive. Each block's header, gas, receipts and logs
  are checked against the chain, and the state root at every anchor.
- **Arc** (Circle's stablecoin L1), from its genesis, the same way: its native-USDC
  precompiles and system rules are part of the Lean spec.
- **Speed: 2.12 Ggas/s** re-executing recent mainnet blocks on one Google Cloud VM, **1.22×
  revm** (the EVM inside reth) measured on the same machines with the same inputs, at about
  two cents per teragas on a spot VM. Method, every run and the caveats:
  [eita.run/benchmark](https://eita.run/benchmark/).
- **Verified metrics, live.** Re-execution produces facts (state changes, value moves, logs,
  calls), and metrics are incremental *folds* over them, updated the moment a block lands and
  served with their provenance: the anchor whose state root was checked, the block range,
  the code that computed them. Because the folds see execution, not just logs, they show what
  log-based tools can't: ERC-20 Transfer events that the token's storage contradicts, upgrades
  and role changes made with no event, value moved inside calls that emit nothing, gas
  attributed to the contracts that actually ran. Open a chain's page from
  [eita.run](https://eita.run), and see what is proved, checked as it runs, or trusted at
  [eita.run/verified](https://eita.run/verified/).

The metrics service and the node scaffolding around this engine live outside this
repository; the engine, the spec, the proofs and the emitters are all here.

## How it is built

```
      EELS (Python, CC0)                              ethereum/tests, mainnet blocks
            │ translated clause by clause,                      │
            ▼ cited by file and line                            ▼
  lean/Evm/<Fork>/   Lean 4 spec, Frontier … Osaka (+ Amsterdam staged), OP Stack, Arc
            │ proofs: the derived pieces equal the spec
            ▼
  lean/Evm/CL/       emitters ──► c/handlers.S          ARM64 threaded interpreter
                              ──► c/handlers-x86-elf.S  x86-64 threaded interpreter
                              ──► emitJIT daemon        per-chunk native JIT
                              ──► src/generated/host.lisp
                                  gas formulas, fork tables, and the effect layer
                                  (CALL/CREATE/SSTORE/SELFDESTRUCT, tx application,
                                  fee settlement, block rewards), each proved equal to
                                  the fork spec (Evm.CL.Effect*Proof)
            │
            ▼
  src/       SBCL host (ASDF system "eita", one executable bin/eita): world state,
             frames, journal, callbacks, tx and block application; chain specs;
             the replay driver
```

- **The spec** (`lean/Evm/`): every fork from Frontier to Osaka as a delta over its
  predecessor (a fork's directory holds only what changed), EELS-faithful — EELS is the
  reference, not the Yellow Paper. Chain specs on top: OP Stack (Bedrock … Isthmus) and
  Arc (its native-coin and post-quantum precompiles and system rules).
- **The proofs**: the IR compiler's soundness against the spec; the emitted handlers'
  denotations (ARM64 and x86-64 instruction semantics in Lean); the effect layer against
  each fork's `processTransaction`, `SELFDESTRUCT`, system calls and block rewards; the
  call-gas and SSTORE gas routines; PUSH-n wide loads; the JIT code arena's safety; the
  header-validity rules. The axiom closure of the audited theorems is checked against a
  committed baseline (`scripts/verify-axioms.sh`): Lean's standard axioms, plus, for the theorems proved by
  evaluation, `native_decide`'s auxiliary axioms (listed; docs/trusted-surface.md). The statements
  of 41 headline theorems are pinned to an owner-reviewed file and judged by the Lean comparator
  (`scripts/verify-comparator.sh`; docs/trusted-surface.md). The native
  slot table is proved in Velvet for every capacity and printed to C (`verify/velvet-slots/`). The state layer's
  concurrent protocols (layer GC, compaction, root checks, rollback) are Veil models whose citations of the Lisp are
  checked (`verify/protocols/`).
- **Generated, not hand-written**: `c/handlers.S`, `c/handlers-x86-elf.S` and
  `src/generated/host.lisp` are committed and must be byte-identical to what the
  emitters produce (`scripts/verify-host-emit.sh`).
- **The host** (`src/`): Common Lisp (SBCL), the ASDF system `eita`. World state, frames, the callbacks the
  handlers yield to, tx and block application, the chain specs and the replay driver.
  Where it decides something the spec owns (a gas cost, a fork rule, an effect), it calls
  the emitted code.

## Status

- **What is proved, checked and trusted**: [`docs/VERIFIED.md`](docs/VERIFIED.md); the numbers per
  component in [`scripts/generated/verification-stats.md`](scripts/generated/verification-stats.md).
- **ethereum/tests**: the Cancun battery (`LegacyTests/Cancun/BlockchainTests`, 111,983
  tests, Frontier..Cancun) passes on both tiers, the threaded interpreter and the JIT:
  `pass=111835 fail=0 skip=40 xfail=108`, every expected failure listed with its reason
  (`docs/testing.md`, `src/fixtures/expected-failures.txt`). Also green: the current
  `ValidBlocks` (Cancun + Prague) and execution-spec-tests' blockchain fixtures (Cancun +
  Prague: 38,885 pass, 25 xfail). Invalid blocks must be rejected for the expected reason.
- **Mainnet**: Ethereum has been replayed from genesis to the chain head in full-state
  mode — every block's header reproduced (gas used, logs bloom, receipts root, the rules
  of EELS `validate_header`/`validate_ommers`, senders recovered from signatures) and the
  state root checked against the header at periodic anchors. Arc has been replayed from
  its genesis the same way; OP Stack chains (Base, OP Mainnet, World Chain) run in
  full-state mode from genesis (Base: tested over its first blocks) or lazy-state mode.
- **Open proof obligations**, tracked rather than hidden: 19 `sorry` remain in the spec
  layer (per-fork refinement theorems and three `Trie.Stack` lemmas; none in an executable
  definition), and several forks' refinement statements are still shape placeholders.
  `scripts/generated/refinement-coverage.md` lists every obligation; the debt may only go
  down (`scripts/verify-coverage.sh`).
- **Trusted, not proved**: the SBCL host code around the emitted functions (world tables,
  journal, frame plumbing), the C runtime and the precompile libraries (secp256k1, mcl,
  blst, OpenSSL), the Lean compiler and SBCL. The battery and mainnet replay are the
  evidence there, not a proof.
- **Not checked**: the proof-of-work seal (ethash); RLP-level block defects (the decoder
  reads JSON-RPC block objects, not raw RLP).
- **Platforms**: macOS arm64, Linux aarch64 and x86-64; interpreter and JIT tiers on each.

## Build

Prerequisites:

- **Lean 4** via [elan](https://github.com/leanprover/elan) (the toolchain is pinned by
  `lean/lean-toolchain`; Mathlib's prebuilt oleans are fetched by `lake exe cache get`).
- **SBCL** ≥ 2.4 and [ocicl](https://github.com/ocicl/ocicl) (run `ocicl setup` once). The
  Lisp dependencies (`cffi`, `jsown`, `cl-fad`, `alexandria` and theirs) are pinned by
  digest in `ocicl.csv`; `build.sh` installs exactly those.
- **C libraries**: libsecp256k1, OpenSSL (libcrypto), zlib, and
  [mcl](https://github.com/herumi/mcl) built with `MCL_FP_BIT=384`.
- **Rust** (cargo) for `rust/pq`, the SLH-DSA shim for Arc's post-quantum precompile.
- `vendor/blst` is a git submodule: clone with `--recurse-submodules`.

macOS (Apple Silicon):

```sh
brew install sbcl ocicl secp256k1 openssl@3 cmake rust
ocicl setup                     # once: installs ocicl's ASDF runtime
git clone --depth 1 https://github.com/herumi/mcl /tmp/mcl
cmake -S /tmp/mcl -B /tmp/mcl/build -DMCL_FP_BIT=384 -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/opt/homebrew
cmake --build /tmp/mcl/build -j && cmake --install /tmp/mcl/build
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

git clone --recurse-submodules https://github.com/valeryz/eita-evm && cd eita-evm
./build.sh                      # about 15 minutes the first time; ends with bin/eita
export DYLD_LIBRARY_PATH=/opt/homebrew/lib
```

Linux (Debian/Ubuntu, x86-64 or aarch64):

```sh
sudo apt-get install -y sbcl cargo zlib1g-dev
git clone --recurse-submodules https://github.com/valeryz/eita-evm && cd eita-evm
sudo scripts/provision-linux.sh # secp256k1, OpenSSL, mcl (from source), blst
# ocicl (https://github.com/ocicl/ocicl, then `ocicl setup`) and elan as above, then:
./build.sh
export LD_LIBRARY_PATH=/usr/local/lib:$(cd lean && lean --print-prefix)/lib
```

`./build.sh` ends with `bin/eita`, one executable holding the whole engine, with the native
libraries (and the `emitJIT` daemon) copied beside it: `bin/` can be moved as a whole.
`./build.sh --leanless` skips Lean: it builds libeita from the committed generated files,
and you run the interpreter tier (`EITA_NO_JIT=1`).

The heap is an SBCL runtime option: `bin/eita` starts with the one it was built with
(`EITA_HEAP_MB`, default 8192 MB); per run, give it before the command:

```sh
bin/eita --dynamic-space-size 16GB --end-runtime-options fixtures <dir>
```

From Lisp, with ocicl's runtime loaded and the repository on ASDF's path (as `build.sh`
does), `(asdf:load-system "eita")` loads the engine, `(asdf:test-system "eita")` runs the
test suites (`tests/`), `(asdf:make "eita/cli")` builds `bin/eita`.

The Lean build prints `declaration uses 'sorry'` warnings for the proof obligations still
owed, tracked in `scripts/generated/refinement-coverage.md`.

## Quickstart: a REPL with the verified EVM

```sh
bin/eita repl
```

```lisp
(in-package :eita)
(defparameter *w* (new-world :fork "Prague" :alloc '(("0xa11ce" :balance 1000000000000000000))))
(transact *w* :from "0xa11ce" :to "0xb0b" :value 1000 :gas 21000)   ; => (:STATUS 1 :GAS-USED 21000 ...)
(balance *w* "0xb0b")                                                 ; => 1000
(defparameter *c* (deploy *w* :from "0xa11ce"
                    :code "0x6018600c60003960186000f3600054600101806000558060005260206000a160206000f3"))
(transact *w* :from "0xa11ce" :to *c*)  ; a counter: slot 0 += 1, LOG1, returns the new value
(call *w* :to *c*)                      ; on a copy, like eth_call
(storage *w* *c* 0)                     ; => 1
(state-root *w*)                        ; => "0x…"
```

`docs/quickstart.md` walks through a session, including running a BlockchainTest's
pre-state; `examples/quickstart.lisp` is the same as a script
(`bin/eita repl --load examples/quickstart.lisp`). The API (`src/eita.lisp`, package `eita`)
is a thin layer over the functions every replay runs.

## Tests, and replaying a chain

```sh
bin/eita fixtures <BlockchainTests file or directory>...   # docs/testing.md
EITA_NO_JIT=1 bin/eita fixtures <...>                      # interpreter tier
scripts/verify-host-emit.sh                                # generated code == emitters
bin/eita replay --chain ethereum --blocks DIR --from 1 --to 1000   # docs/block-input.md
```

Eita replays blocks you supply as files — the JSON-RPC block objects your own node returns —
from genesis with full state and state-root checks: `docs/block-input.md`. Other block
sources (following a node, importing archives, lazy RPC-backed state) plug in through one
interface, documented there.

## Layout

| path | what |
|---|---|
| `lean/Evm/<Fork>/` | the EELS translation, per fork (`Vm/`; `Spec/` relations and refinement theorems) |
| `lean/Evm/IR`, `lean/Evm/CL` | the IR compiler and its soundness; the emitters (ARM64, x86-64, CL host), instruction semantics, proofs |
| `lean/Evm/Optimism`, `lean/Evm/Arc` | chain specs |
| `lean/Evm/Trie`, `Persist`, `Parallel` | state trie (streaming root), layered snapshots and recovery, Block-STM (spec + proofs) |
| `lean/*.lean` | executables: emitters, test-vector generators, the Lean interpreter's own replay (`lake exe replay`, `lean/REPLAY.md`) |
| `verify/velvet-slots/` | the slot table's Velvet proofs and its C printer (own Lake package; `scripts/verify-velvet-slots.sh`) |
| `verify/protocols/` | Veil models of the state layer's concurrent protocols and their code check (`; @veil` markers); own Lake package; `scripts/verify-protocols.sh` |
| `c/`, `lean/c/` | libeita: the emitted handlers, per-tx state tables, precompiles |
| `eita.asd`, `ocicl.csv` | the ASDF systems (`eita`, `eita/chains`, `eita/fixtures`, `eita/cli`, `eita/test`), the pinned Lisp dependencies |
| `src/native/`, `src/core/` | where the native libraries are and their FFI; u256, hex, RLP, keccak |
| `src/evm/` | the EVM host: tiers (JIT, threaded interpreter), frames, journal, callbacks, precompiles, tx application, the observation seam and event stream |
| `src/generated/host.lisp` | Lean-emitted: gas formulas, fork tables, the effect layer |
| `src/state/` | world state; full state: layered snapshots, anchors, state-root checks, resume; the trie |
| `src/input/` | block decoding and the block-source seam |
| `src/chains/` | the block pipeline (system calls, receipts and header gates), the chain-spec record, the driver; Ethereum, Arc, OP Stack |
| `src/fixtures/` | the BlockchainTests runner (`scripts/run-battery.sh` runs a tree) |
| `src/eita.lisp`, `src/cli.lisp` | the API package `eita`; `bin/eita` |
| `tests/` | the test suites of `(asdf:test-system "eita")` |
| `docs/` | design notes: start with `replay-architecture.md`, `effect-layer-derivation.md`, `x86-64-backend.md` |

## Roadmap

- **An Engine API block source**: `engine_newPayload` / `engine_forkchoiceUpdated` from a
  consensus client, plugged into the same block-source interface — the natural public path
  from a verifying replayer to a full execution client.
- The proof obligations listed in `scripts/generated/refinement-coverage.md`, down to zero.
- The x86-64 JIT's proofs at parity with ARM64: the chunk's head charge, op sites,
  terminators and trampolines under the x86-64 semantics (the handlers, gas routines and
  region flush are proved; the x86-64 JIT already passes the same test batteries); and JIT
  images for Leanless builds, which run the interpreter tier today.
- Block-STM parallel execution (spec in `lean/Evm/Parallel`, proved) in the replay.
- Amsterdam (staged in `lean/Evm/Amsterdam`).

## Contributing

See `CONTRIBUTING.md`. MIT licensed (`LICENSE`); third-party material in `NOTICE.md`.
