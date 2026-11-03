# Vericoding the host layer — trust-surface inventory & extraction plan

> **Status: historical** (written 2026-06). Accurate as of then; the current system is described in `docs/replay-architecture.md` and the code.

Status: plan · Related: #236 (Lean-specify journaling/rollback), #239 (emit createGasPlan), #241 (interp↔toCL differential), #238 (ARM64 DSL) · Principle: *no testing of verification gaps — audit verification status, mark the unverified code as a minimal explicit trust surface, close the gaps, only then test.*

## 0. Why

Today `src/generated/host.lisp` is **25 lines / 3 functions** — the entirety of Lean→CL extraction:
`spec-new-account-charged-pre`, `spec-new-account-charged-spurious`, `spec-restore-journal-entry`.
The consensus-semantic host layer is otherwise **~3,267 lines of hand-written, unverified CL** in `src/evm/`. Every correctness bug this cycle lived there or adjacent: #256 (deploy-OOG rollback order in `apply-tx`), the `out-copy` leak in `cb-call`, #258 (a C helper). We found them by *testing* (replay state-root mismatch chased via mainnet diff) — verification debt paid back as the most expensive currency, debugging time. This plan shrinks that surface to a small, named, justified core by **deriving** the rest from the spec (the way `host.lisp` derives the two predicates and `Evm.CL.Arena` derives the arena).

## 1. Trust-surface inventory

Three tiers. Lines are approximate ranges in `src/evm/`.

### Tier A — consensus semantics, hand-written, MUST close (bugs land here)

| Component | fns / lines | What it does | Bug history | Lean spec exists? |
|---|---|---|---|---|
| `apply-tx` | 2649–2945 | tx prologue (nonce/value/endowment), frame run, deploy, **revert/rollback**, epilogue | **#256** (revert order) | Homestead `Vm/Effect`, `Spec/*Step` — yes |
| `cb-call` | 1715–2013 | sub-frame setup, value transfer, call-gas, returndata, frame revert | `out-copy` leak; call-stipend gas | `Vm/Effect` make_message_call — yes |
| `cb-create` / `cb-create2` | 2028–2287 | create address, endowment, init run, deploy-OOG, collision | shares #256 class | `Spec/CreateStep` — yes |
| `cb-selfdestruct` | 2289–2349 | beneficiary transfer, mark, refund | self-beneficiary edge | Fork — yes |
| journaling | 1200–1258 | `journal-push!`, **`revert-journal-to`**, balance/nonce/created entries | the revert engine #256 rode | #236 (in progress) |
| call/create gas | `sstore-gas-native` 1310, `access-cost` 1335, `call-base`, `create-gas`, `intrinsic-gas` 3019 | per-fork gas composition | copy-op split, stipend | `Vm/Gas` + emitted natives (#229–232) — partial |
| state-read callbacks | `cb-sload/sstore/balance/extcode{size,hash,copy}/blockhash/keccak/log` 1343–2415 | world reads + access/gas | MSIZE #24-class | `Vm/Effect` per-op — yes |
| account model | `world-storage-{get,set}` 698, `fault-account!`/`fault-slot!` 763, `access-addr!`/`access-slot!` 1150, `touch!`/`sweep-empty-touched!` 1634, `orig-record!`/`orig-get!` 1178 | storage, lazy-load, warm/cold, EIP-161, EIP-2200 orig | #252 sweep, #258-adjacent | `Frontier/State`, Fork — yes |

### Tier B — emitted from Lean but NOT proven `==spec`

| Component | Status |
|---|---|
| ARM64 opcode handlers (`handlers.S` via `emitARM64`) | emitted from `AsmCore` IR (#238); only MSIZE + bitwise *proved* ==spec; rest emit-not-proven |
| `interp` ↔ `toCL` | independently hand-written, cross-check missing ([[feedback_interp_tocl_gap]]) |
| sstore/access-gas natives (#229–232) | emitted from Lean; refinement to the fork gas spec not closed |

### Tier C — legitimate, permanent trust surface (axiomatize + document, do NOT verify)

- **Replay driver** (`replay-mainnet.lisp`: DB fetch, block loop, checkpointing, state-root dump, swank) — infrastructure, not consensus.
- **FFI marshalling** (`u256-read`/`u256-write`, `mem-ref` accessors) — a thin, provable boundary; axiomatize against the byte layout.
- **Crypto primitives** (keccak, ecrecover, bn254, modexp, blake2f, sha256, ripemd) — external C/asm; axiomatize against test vectors, out of scope for derivation.

The endpoint is: Tier A → derived/proven, Tier B → proven, **Tier C is the whole residual trust surface** — short, named, justified.

### Lean proof trust surface (what `#print axioms` sees)

The tiers above are about the CL host layer. The Lean proof layer has
its own residual surface, audited by `scripts/verify-axioms.sh`
(`lean/AxiomAudit.lean` prints the axiom closure of the headline
theorems; the output is committed at `scripts/generated/axiom-audit.txt`
and any drift fails the gate):

- **Kernel-checked**: all headline theorems (`IR/Soundness`,
  `Effect*Proof`, gas emitters, `BlockSTM`) — `propext`,
  `Quot.sound`, `Classical.choice` only. The former `loom_smt`
  (SMT-solver discharge via a `trust_smt : ∀ p, p` axiom) was removed
  with the v4.29.1 toolchain upgrade; the gate hard-fails if it ever
  reappears.
- **`native_decide`** (~400 sites, gas constants + encoder round-trips
  only): decides by compiled native evaluation, adding
  `Lean.ofReduceBool` / `Lean.trustCompiler` to the closure — the Lean
  compiler's codegen is trusted for those. Deliberately absent from
  the headline soundness/refinement theorems.
- **`sorry`**: 19. 13 in per-fork `Spec/Refinement` obligations
  (Cancun 4, Byzantium 3, Constantinople 3, Istanbul, Petersburg,
  Frontier 1 each — REVERT/RETURNDATA/SSTORE/SAR/TSTORE/BLOBHASH-shaped),
  1 in `Frontier/Spec/StorageStep` (`State.setStorage`), 3 in
  `Trie/Stack`, 1 each in `CL/AsmCore` and `CL/StorageCache`. None are
  in executable defs.
- **Identity refinements**: in the other 11 forks (SpuriousDragon, Homestead,
  Berlin, London, Paris, Shanghai, Cancun, Prague, Osaka, Amsterdam, and one
  in Istanbul) the `Spec/Refinement` theorems are shape placeholders
  (`P → P`, suffixed `_shape`); the spec relation is not yet linked to the
  interpreter there. Only Frontier carries proved
  per-opcode refinements (arithmetic/comparison via the `runBinary`/
  `runUnary` shape lemmas).
- **Crypto axioms / opaques**: keccak/sha/ripemd/ecrecover/bn254/
  BLS/KZG/P256 are `opaque` + `@[extern]` (C/asm implementations), or
  postulated predicates in the spec relations. Tier C for the spec.

## 2. Extraction order (risk × leverage)

1. **Journaling + `apply-tx`/`cb-create` rollback (#236).** Highest risk — #256 lived here, and it's the revert engine every frame shares. Model the journal + revert as one term, two interpretations (value-state vs arena), prove equal — the `Arena.lean` pattern, which already proved the rollback *ordering* discipline. Outcome: the #256 bug class becomes unrepresentable.
2. **`cb-call`/`cb-create` value-transfer + gas composition (#239).** Derive `createGasPlan` and the call-gas formula (`call_base + forwarded − sub.gas_left`, stipend handling) from `Vm/Gas`; emit the value-transfer+revert decision over the world seam. Folds in the `out-copy` returndata buffer (the proven-safe arena slot) so #250's footprint half lands here too.
3. **State-read callbacks → emit from `Vm/Effect`.** `cb-sload/sstore/balance/extcode*` are thin: a world read + an access/gas charge. Emit the (offset, gas, access-class) tuple per op from the spec so the #24/MSIZE wrong-offset class is structurally impossible (extends `AsmCore`'s named-field guarantee to the host seam).
4. **Close Tier B: prove the emitted ARM64 handlers `==spec`** (finish `AsmCore` stage 2 — arithmetic/compare handlers) and **kill the interp↔toCL gap** with a single tagless-final source so the two interpretations cannot diverge ([[feedback_interp_tocl_gap]]).

## 3. Mechanisms (how a gap gets closed)

- **Derive** — generalize `emitHostCL` beyond pure predicates: emit the imperative host *steps* (Pred IR `eval`+`toCL` extended to effects over the world/journal seam), so the CL is generated from the same Lean term that defines the semantics.
- **Prove** — denote the impl, prove it equals the spec denotation (`AsmCore`, `Arena.lean`).
- **Make unrepresentable** — typed IRs where the bug can't be written (Arena escape-safety, AsmCore bare-sub-gas, named offsets).
- **One source, not two** — tagless-final / single-term so `toCL` and `interp` are projections of one definition, eliminating the cross-check entirely rather than testing it (#241 is the stopgap; this is the fix).

## 4. Definition of done

- Every Tier A row: derived from a Lean term or proven `== spec`, 0 `sorry` (or an explicit, named `sorry` lemma per [[feedback_no_silent_gaps]]).
- Tier B: handlers proven; interp↔toCL gap closed at the source.
- A one-page **TRUST.md** enumerating the residual Tier C surface (driver, FFI layout, crypto axioms) — each line justified. If it's not on that page, it's verified.
- `host.lisp` grows from 25 lines to the real generated host; `src/evm/`'s hand-written consensus core shrinks toward zero (driver + glue remain).

## 5. Sequencing

This is the post-5M-run program, not a detour from it. The current run establishes the *baseline* (a correct 0→5M under the present trust surface); the inventory above is then the backlog, ordered so the first thing verified is the thing that already bit us (#236 / rollback). Each step is "derive or prove, then the existing replay becomes a *confirmation* of verified code" — never the discovery mechanism again.
