# Compilation Architecture

> **Status: historical** (written 2026-06). Accurate as of then; the current system is described in `docs/replay-architecture.md` and the code.

> *Why Eita bypasses LLVM and what we get in exchange.*

## The standard EVM execution pipeline

Production EVMs today run a variation of:

```
Rust EVM impl  →  LLVM IR  →  LLVM opt passes  →  Cranelift/x86_64 backend  →  machine code
```

revm, reth, evmone, evmone+AOT — all sit on top of LLVM's general-purpose
compiler infrastructure. LLVM does an enormous amount of work: SSA construction,
GVN, DCE, inlining, loop optimizations, vectorization, register allocation,
instruction scheduling, peephole patterns. The result is a fast binary
basically for free, given a well-typed source program.

The cost: you don't control any of those passes, you can't verify any of them,
and most of the work is unnecessary for EVM-shaped code.

## Eita's pipeline

```
EELS (informal spec)
   ↓  hand-port, citation-by-citation
Lean spec  (lean/Evm/, ~3000 LoC, 16 forks, 30694/30694 GST tests)
   ↓  per-opcode definition as a Form value
Form IR  (lean/Evm/CL/Extract.lean, ~30 primitives)
   ↓  Form.toX for target X
SBCL / ARM64 / AMD64+AVX / (future: WASM, GPU)
```

Each layer is a *refinement* of the previous one. The Lean spec is the
source of truth for opcode semantics. The Form IR is a representation
amenable to machine emission. Each backend is a per-target table mapping
elementary primitives to instructions.

## Why we skip LLVM

LLVM is industrial-strength general-purpose compilation. For EVM, most of
its work is unnecessary:

| LLVM pass | Why we skip it |
|---|---|
| Inlining | Form IR is already at the inlined level |
| Vectorization discovery | EVM hot spots are known a priori (U256 arith, KECCAK); AVX picked at the primitive level |
| Dead code elimination | The IR has no dead code; opcodes are exactly what gets emitted |
| Loop optimizations | We control which loops are emitted (chunked execution, peephole rewrites) |
| Register allocation (general) | EVM stack is bounded depth ≤ 1024; specialized allocator pins TOS/NOS to NEON/YMM, rest spills cheaply |
| Instruction scheduling | Hand-schedulable for the few patterns that matter |
| ABI lowering | No FFI boundary; we own the whole stack |
| Profile-guided optimization | EVM workloads have characteristic hot patterns (mapping accesses, balance reads) — known in advance |

What we lose:
- General-purpose compilation (we can only compile EVM-shaped programs).
- Battle-tested optimization passes (no GVN or LICM for free).
- Generality of source language (no C/Rust, only the Form IR).

What we gain:
- **End-to-end verification.** Form-spec ↔ Form-interp ↔ target-emission, all in Lean. revm cannot prove its compilation; we can.
- **Domain-specific optimizations** that LLVM can't see: KECCAK-mapping bypass (see `project_keccak_lazy_thunk`), chunk-level closed-form gas (see `project_chunk_gas_formulas`), stack-depth-aware register pinning, untamed-mode partial evaluation.
- **Tiny attack surface.** A few hundred lines of backend per target vs millions of lines of LLVM. We audit/verify all of it.
- **Cross-platform without polyfill.** ARM64 + AMD64 + AVX + future targets — each a small per-target table, no shared abstract machine with leaky abstractions.

## The Form IR

`lean/Evm/CL/Extract.lean` defines `Form` — an inductive type of ~30
primitives, each with two faces:

- `Form.toCL : Form → String` — emit CL source (today's only backend).
- `Form.interp : Env → CLState → Form → Option (U256 × CLState × Env)` — Lean operational semantics.

Per-opcode soundness becomes a Lean theorem: `stepOf opForm s = stepX s`,
where `stepX` is the spec-level step function. Each closed theorem
discharges one axiom that was previously a per-opcode trust claim.

The primitives are organized in two granularity tiers:

**Chunky primitives** (current state, partially elementary-decomposed):
correspond to project-specific CL helper macros (`mem-read-u256`,
`sload-from`, etc.). Each is one Form constructor; its `interp` matches
the helper's behavior. Closed theorems: arithmetic ops (ADD/SUB/MUL/...),
comparison (LT/GT/ISZERO), memory (MLOAD/MSTORE/MSTORE8), storage
(SLOAD under mock), world hooks (BALANCE/EXTCODE*/BLOCKHASH/SELFBALANCE).

**Elementary primitives** (in progress, see `whileLoop`, `memByteAppend`,
`memByteWriteAt`, `memLengthForm`, `mpFieldRead`, `mpFieldWrite`):
one CL form each, mapping to ~1-3 machine instructions on each backend.
Chunky primitives become Lean *functions* that produce trees of these.
The trust per primitive shrinks; reuse across opcodes amplifies validation.

### What is NOT in the Form IR (and why)

The Form IR covers ~75 of the EVM opcode set. Four classes deliberately
sit outside it:

| Opcode class | Lives in | Why not Form |
|---|---|---|
| **CALL / CALLCODE / DELEGATECALL / STATICCALL** | `lean/Evm/Frontier/Vm/Interpreter.lean` + host callback | Recurse into the interpreter; the Form's `interp` is non-recursive over Form. |
| **CREATE / CREATE2** | same | Same recursion shape. |
| **SELFDESTRUCT** | same + host callback | Touches the world state in ways not modeled in `CLState`. |
| **Precompiles (0x01–0x0a)** | `lean/Evm/Frontier/Vm/PrecompiledContracts/*.lean`, host callback | Fixed-function gadgets; not per-opcode work. |

These are wired as **host callbacks** in `EvmCallbacks` (see
`c/evm_state.h`): when the threaded interpreter encounters one of these
opcodes, the generated handler calls back into the host (Lisp / Rust /
whatever) which owns the call stack and recurses. The audit covers
per-opcode work; the recursive/cross-frame semantics are covered by
the Frontier-level refinement chain instead, which has its own theorems
in `lean/Evm/Frontier/Spec/CallStep.lean` and `CreateStep.lean`.

**This is a known and load-bearing boundary**: a single execution mixes
two semantic regimes (Form-IR-verified inside a frame, callback-verified
across frames). The handoff happens at exactly six opcodes plus the
precompile dispatch table. Surfacing this gap explicitly — rather than
papering it with a half-finished Form-IR encoding of CALL — matches
the project's "no silent gaps" discipline.

## Backend size estimates

For each target, the backend is a per-primitive table:

| Primitive | ARM64 | AMD64 | AVX-512 (for arithmetic) |
|---|---|---|---|
| `arrayRef arr idx` | `LDRB x, [arr, idx]` | `MOVZX rax, byte [arr+idx]` | n/a (scalar) |
| `arraySet arr idx v` | `STRB v, [arr, idx]` | `MOV byte [arr+idx], v` | n/a |
| `structGet sv field` | `LDR x, [s, #offset]` | `MOV rax, [s+offset]` | n/a |
| `structSet sv field v` | `STR v, [s, #offset]` | `MOV [s+offset], v` | n/a |
| `binOp "+" u256-scalar` | 4× `ADCS` chain | 4× `ADC` chain | `VPADDQ ymm + carry` |
| `binOp "*" u256` | hand-tuned NEON multi-limb | hand-tuned multi-limb | VPMULL with carry chain |
| `loopFor v 0 n body` | `SUB; CBNZ` counter | `LOOP` or `DEC; JNZ` | n/a |
| `whileLoop cond body` | `B.cond; loop label` | `JNE; loop label` | n/a |

~30 primitives × 1-3 instructions per backend = **~100 lines of emission
code per target**. LLVM is millions of lines. Cranelift is around 100K.

## Layered refinement chain

```
EELS Python    →     Lean spec        →    Form IR       →    Backend
   ↓                    ↓                       ↓                  ↓
informal           verified            structured-      target-specific
                   step funcs          + interp         emission

[hand-port,        [per-op theorems    [per-primitive    [per-primitive table,
citation-by-       like                 toCL + interp]   <100 lines per
citation]          add_extract_                          target]
                   correct]
```

Each arrow represents a refinement:
- EELS → Lean spec: hand-port with line citations; validated by replaying mainnet (1393/1393 ValidBlocks, 30694/30694 GST tests).
- Lean spec → Form IR: per-opcode `x_extract_correct` theorem.
- Form IR → backend: per-primitive emission table; correctness by inspection (each table entry corresponds to one primitive's `interp`).

What gets trusted at each level:

| Layer | Trust target |
|---|---|
| EELS spec | Reference implementation by Ethereum Foundation |
| Lean spec | Faithful port (validated by mainnet tests) |
| Form `interp` | Per-primitive pair (`toCL`, `interp`) is consistent |
| Backend emission | Per-primitive table maps `interp` to instructions |

The closer to the bottom, the smaller the trusted unit. Elementary
primitives shrink the Form layer's trust units to single CL operations;
backend emission is a table lookup. The end state has every level
mechanically verified except for the Lean ↔ SBCL/ARM64 bridge axiom
at the elementary-primitive level — which is small enough to audit
manually or via an SMT model of SBCL's eval.

## Related work

- **Cranelift** (Wasmtime). Small, domain-specific (WASM), fast. Same philosophy as Eita: skip LLVM, hand-roll a focused backend. Not verified end-to-end.
- **CompCert.** Verified C-to-assembly compiler. Demonstrates verified compilation is feasible but applied to C, not domain-specific.
- **WASM-cert / WasmCert-Coq.** Verified WebAssembly semantics + interpreter. Closest to our project in shape.
- **Bedrock2 / FoundationalC.** Verified low-level Coq-based systems compilation. Generic but heavy.
- **revm / revmc.** Rust-based EVM with optional AOT compilation via LLVM. Fast but unverified.
- **evmone.** C++ EVM with intel-optimized interpreter, sometimes AOT-compiled. Same.
- **MegaETH.** Forked evmone + custom AOT compiler. Optimized for throughput, not verification.
- **PyPy's tracing JIT.** Pre-identifies hot patterns at runtime. Eita identifies them architecturally instead.

## Practical implications

- **Adding a new backend is ~1-2 sessions of focused work**, not a multi-month port. The primitive table is the spec; the implementation is small.
- **AVX optimization is per-primitive**, not per-opcode. The AVX backend overrides ~10 primitives (the U256 arithmetic ones, maybe KECCAK-f rounds); everything else falls through to scalar.
- **GPU backend is conceptually viable** for parallel block execution: each tx is a stream, primitives map to compute kernels. Worth exploring after CPU backends settle.
- **The audit script will continue gating** the Form ↔ backend correspondence even after full verification, as a regression check. It's cheap and catches drift instantly.

## Compiled chunks as a portable, language-agnostic library

The natural end state for the compiled-chunk path is that **chunks become
a portable native library that any host language can load and call**. The
compiled machine code is just bytes; the ABI between chunk and host is a
small, stable contract.

### What's pure in compiled chunks (no host involvement)

- Arithmetic, bitwise, comparison.
- Memory ops (read/write the memory array within the state struct).
- Stack ops (read/write the stack array within the state struct).
- Local control flow (jumps within the chunk, or to a known sibling chunk).
- PC/gas counter manipulation.
- Push/dup/swap.

### What requires a host callback

| Primitive | Why |
|---|---|
| `SLOAD`, `SSTORE`, `TLOAD`, `TSTORE` | Storage backend (DB, cache, RPC). Host decides. |
| `BALANCE`, `EXTCODESIZE`, `EXTCODEHASH`, `EXTCODECOPY` | World state. Host owns the trie/DB. |
| `BLOCKHASH`, `SELFBALANCE` | World reads. |
| `LOG0`–`LOG4` | Event sink. |
| `CALL`, `DELEGATECALL`, `STATICCALL`, `CALLCODE` | Sub-frame execution. |
| `CREATE`, `CREATE2`, `SELFDESTRUCT` | Account-level state mutation. |
| `KECCAK256` | Deterministic — can be inlined, but typically a callback so hosts can swap in libsodium / intel-ipsec-mb / Apple Silicon HW crypto. |
| `RETURN`, `REVERT`, out-of-gas, invalid-opcode | Signal host to terminate frame. |

### ABI shape

Host provides a vtable of function pointers and an `EvmState` struct
allocation. Compiled chunk is a single entry point:

```c
struct EvmCallbacks {
  uint256_t (*sload)(StatePtr s, uint256_t slot);
  void      (*sstore)(StatePtr s, uint256_t slot, uint256_t val);
  uint256_t (*balance)(StatePtr s, uint256_t addr);
  uint256_t (*ext_code_size)(StatePtr s, uint256_t addr);
  void      (*log)(StatePtr s, uint8_t n_topics,
                   uint256_t *topics, uint8_t *data, uint64_t len);
  CallResult (*call)(StatePtr s, CallParams *p);
  /* ... 12-15 callbacks total ... */
};

struct EvmState {
  uint64_t   pc, gas_left, sp, mp;
  uint256_t *stack;        /* 1024-slot array */
  uint8_t   *memory;       /* resizable */
  uint8_t   *code;
  uint8_t   *calldata;
  uint256_t  self_address;
  /* ... fields chunks directly access ... */
};

void chunk_entry(struct EvmState *state, struct EvmCallbacks *cbs);
```

Field offsets in `EvmState` are baked into the compiled code. Host
allocates the struct (in whatever memory it wants), fills the callback
table (with whatever DB backend it has), passes both pointers, calls.

### Host-language matrix

| Language | Binding mechanism | Notes |
|---|---|---|
| C / C++ | direct | Trivial. |
| Rust | `extern "C"` + `dlopen`/static link | Cleanest. Could be `revm`-replacement. |
| Go | cgo | Standard. Some overhead per call. |
| Python | `ctypes` / `cffi` | Standard, no JIT. |
| JavaScript / Node | N-API / `ffi-napi` | Plugin to Hardhat etc. |
| Java | JNI | Standard. |
| Common Lisp | CFFI | Used by Eita itself. |
| WebAssembly | recompile via WASM backend | Browser/edge deployment. |

Same compiled chunks. Hosts differ only in:
- How they implement the callbacks (DB choice).
- How they manage the state-struct memory.
- How they handle CALL recursion (own stack, async, whatever).

### Verification boundary

```
  Compiled chunk machine code (pure compute)
  ──────────────────────────────────────────  ← Lean-verified per Form IR
        ↑                            ↓
   pure compute              indirect callback calls
        │                            │
        │                            ↓
        │                       EvmCallbacks vtable
        │                            │
        │                            ↓
        │                       Host implementation
        │                       ────────────────────  ← trusted (host's
                                                        responsibility)
```

Lean's correctness statement applies to the compute path: *given a state
struct and a callback table satisfying [contract X], the compiled chunk
leaves the state in a configuration matching the Lean spec.* The contract
on callbacks is a small precondition list — e.g., "SLOAD returns the value
last written to that slot, or 0 if never written" — that each host
discharges according to its DB semantics.

This is the same shape as WebAssembly's import model, but at the native
code level instead of bytecode. The compute path is verified once;
hosts swap in their state backends.

### The end state

Eita's compiled-chunk artifact becomes **a Lean-verified, native, host-
language-agnostic EVM compute library**. Closest analog: `libsecp256k1` —
a small, focused, performance-critical native library with a stable ABI
used across many languages.

Practically: a project could publish chunks as `libeita-evm-cancun.so`
(or .dylib, .dll), with a header file, and any EVM-using project could
link against it for the compute path. The host project keeps its own
storage backend, state representation, and tx scheduling — Eita
provides the verified arithmetic/control/memory layer.

This is the most ambitious framing of the project's contribution: not
"another EVM" but **a reusable verified EVM compute kernel** that other
EVM-using projects can adopt without adopting the whole stack.

## See also

- `lean/Evm/CL/Extract.lean` — Form IR + closed theorems.
- `lean/Evm/CL/MacroSpec.lean` — CLState and spec-level step functions.
- `lean/Evm/CL/OpRefinement.lean` — opaque + axiom (today) / theorem (target) bridges.
- `scripts/audit-macros.lisp` — runtime validation of Form.toCL against expected behavior.
- Project memories: `project_symbolic_compiler`, `project_chunk_gas_formulas`, `project_keccak_lazy_thunk`, `feedback_lean_first`.
