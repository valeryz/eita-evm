# How Eita is verified

What in this engine is **proved** in Lean, what is **checked** on every block, and what is
**trusted** (tested, not proved). Every claim points at the file or gate that backs it; the
gates run in [CI](../.github/workflows/ci.yml) on every change. Numbers live in generated
files, not here:

- [`scripts/generated/verification-stats.md`](../scripts/generated/verification-stats.md):
  per component, statement and proof lines, theorems, `sorry`, `native_decide`, axioms.
- [`scripts/generated/refinement-coverage.md`](../scripts/generated/refinement-coverage.md):
  every refinement obligation and its status (Section A's total is the headline count).
- [`scripts/generated/axiom-audit.txt`](../scripts/generated/axiom-audit.txt): the axiom
  closure of the audited theorems.
- [`docs/trusted-surface.md`](trusted-surface.md): everything trusted, file by file.

## Proved in Lean

- **The spec.** EVM semantics in Lean 4 (`lean/Evm/<Fork>/`), translated clause by clause
  from the Ethereum execution specs ([EELS](https://github.com/ethereum/execution-specs),
  cited by file and line; EELS is the reference, not the Yellow Paper). Every fork from
  Frontier to Osaka is a delta over its predecessor, Amsterdam is staged, and the OP Stack and
  Arc chain rules sit on top.
- **Emitted code.** What executes is emitted from the spec, not written by hand: the ARM64 and
  x86-64 interpreters' opcode handlers, the JIT's chunk code, the gas formulas, the fork
  tables, the header rules, and the host's effect layer (CALL, CREATE, SSTORE, SELFDESTRUCT,
  transaction application, fee settlement, block rewards), which is proved equal to each
  fork's spec (`Evm.CL.Effect*Proof`). `scripts/verify-host-emit.sh` requires the committed
  generated files to be byte-identical to what the emitters produce now, the effect proofs to
  check with no `sorry`, and no gas constant to be copied into the host by hand.
- **The rest of the proofs**: the IR compiler's soundness against the spec, the handlers'
  denotations under ARM64 and x86-64 instruction semantics, Block-STM, the layered state and
  its recovery, the native slot table (Velvet, `verify/velvet-slots/`), the state layer's
  concurrent protocols (Veil models, `verify/protocols/`; what they assume is in
  [trusted-surface.md](trusted-surface.md#concurrency-protocols-of-the-state-layer-modelled-in-veil-verifyprotocols)).
- **Open debt, ratcheted.** The open refinement obligations and every `sorry` are listed in
  the coverage matrix; `scripts/verify-coverage.sh` fails CI if the debt rises (and if the
  statistics drift). `scripts/verify-axioms.sh` fails if an audited theorem's axiom closure
  changes or a banned axiom appears. Crypto inside the precompiles is a declared oracle
  ([trusted-surface.md](trusted-surface.md#crypto-oracles-of-the-lean-semantics)); BLAKE2F
  is pure Lean.

## Checked as it runs

- **Every block: the header gate.** Gas used, logs bloom, receipts root, transactions root
  and withdrawals root are recomputed from the execution, and every sender is recovered from
  its signature. The header is checked against its parent by EELS `validate_header` and the
  ommers by `validate_ommers`; the header rules are emitted from Lean
  (`lean/Evm/Frontier/Spec/HeaderValidity.lean`). Not checked: the proof-of-work seal
  (ethash). Code: `src/chains/block-system.lisp`, `src/chains/receipts.lisp`.
- **On a schedule: the state root**, recomputed from the replay's own state and compared with
  the header at anchors (`src/state/root.lisp`). Between anchors, the header gate is the
  check.
- **Conformance.** The ethereum/tests BlockchainTests battery on both execution tiers, the
  threaded interpreter and the JIT; results, skips and expected failures with their reasons
  in [`docs/testing.md`](testing.md). A sample runs in CI.

## Trusted, not proved

- **Native code and libraries**: the hand-written C and C++ (256-bit arithmetic, buffers,
  transaction-scoped state, the precompiles' glue) and the third-party libraries, each with
  how it is checked: [`docs/trusted-surface.md`](trusted-surface.md).
- **Runtime and toolchain**: the SBCL runtime and compiler, the Common Lisp host code not yet
  emitted from Lean (world tables, journal, frame plumbing), the Lean kernel and compiler
  (`native_decide`: [trusted-surface.md](trusted-surface.md#native_decide)), and the
  emitters' printers.
- **Consensus**: Eita does not validate consensus. It has no p2p networking and no Engine
  API, and takes its blocks from a node or an archive; it checks that the blocks it is given
  execute to the headers they carry.
- **Not yet run**: an independent comparator (each theorem checked against a reviewed copy of
  its statement in an isolated build).
