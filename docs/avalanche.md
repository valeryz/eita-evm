# Avalanche C-Chain in Eita

Eita supports the Avalanche C-Chain (Mainnet `43114` and Fuji `43113`) from **Etna** through **Fortuna**, **Granite**, and **Helicon (ACP-194 SAE)**. Pre-Etna blocks and legacy native multi-coin precompiles (`0x0100…0001/2`) are refused loudly.

## 1. Lean 4 Specifications & Emitted Rules

Every fork threshold, gas formula, SAE floor, Warp price, atomic gas formula, and SAE `GasClock` pricing formula is specified and proved in Lean 4 under [`lean/Evm/Avalanche/`](../lean/Evm/Avalanche/), audited in [`lean/AxiomAudit.lean`](../lean/AxiomAudit.lean) with zero new axioms and zero `sorry`, and emitted into [`src/generated/host.lisp`](../src/generated/host.lisp) by `lake exe emitHostCL`:

| Lean Module | Scope | Key Emitted Functions (`src/generated/host.lisp`) |
| --- | --- | --- |
| `Evm.Avalanche.Forks` | Mainnet & Fuji activation timestamps (Etna, Fortuna, Granite, Helicon), Cancun EL analog (`16`), Granite P-256 activation, `header.extraData` predicate offset (`80 / 24 / 0`) | `spec-avax-mainnet-fork-ord`, `spec-avax-fuji-fork-ord`, `spec-avax-eth-analog-ord`, `spec-avax-p256-active`, `spec-avax-sae-active`, `spec-avax-extradata-offset` |
| `Evm.Avalanche.Charging` | Coreth disabled refunds, full fee to coinbase (`0x0100…0000`), Helicon/SAE `ceil(gasLimit / 2)` floor, wei conservation | `spec-avax-sae-gas-floor`, `spec-avax-tx-gas-used` |
| `Evm.Avalanche.Warp` | Warp Messenger (`0x0200…0005`) gas schedule (Granite `graniteGasConfig`), predicate access-list pricing, `0xff` delimiter | `spec-avax-warp-blockchain-id-gas`, `spec-avax-warp-send-gas`, `spec-avax-warp-read-gas`, `spec-avax-warp-predicate-gas` |
| `Evm.Avalanche.Atomic` | Post-block codec v0 `ImportTx` / `ExportTx` gas schedule and AVAX nAVAX→wei conversion | `spec-avax-atomic-tx-gas` |
| `Evm.Avalanche.GasClock` | ACP-194 SAE `GasClock` (`BeforeBlock`, `BaseFee`, `AfterBlock`, saturating EIP-4844 `fake_exponential`) | `spec-avax-gasclock-target`, `spec-avax-gasclock-min-price`, `spec-avax-gasclock-price-at`, `spec-avax-gasclock-base-fee` |
| `Evm.Avalanche.Trie` | Coreth `NormalizeStateKey` (`slot[0] &= 0xfe` before `keccak256`) and 5-field `multiCoin` account RLP | Specification & idempotence proofs |
| `Evm.Avalanche.Header` | Exact 30-field Coreth `HeaderSerializable.EncodeRLP` layout and SAE `settledHeight ≤ number` invariants | Specification & monotonicity proofs |
| `Evm.Avalanche.Emit` | `Evm.CL.GasEmit.Expr` terms + 17 `*_eq_spec` equivalence proofs | Emitted via `lean/EmitHostCL.lean` |

## 2. Runtime Seams

- **Chain spec (`src/chains/avalanche.lisp`)**: thin seams over `spec-avax-*` (verified by `scripts/check-derived-gas.py` with zero allowlist additions). Supports:
  - Full 4-selector Warp Messenger (`getBlockchainID`, `sendWarpMessage`, `getVerifiedWarpMessage`, `getVerifiedWarpBlockHash`), access-list predicate withholding, and `header.extraData` `predicate.BlockResults` bitset parsing.
  - Coreth post-block atomic `ImportTx` / `ExportTx` state effects and gas accounting.
  - ACP-194 SAE `GasClock` (`gasclock-from-settled`, `gasclock-before-block!`, `gasclock-after-block!`, `gasclock-base-fee`), automatically seeded on resume from the settling header and cross-checked against dynamic-fee receipts when available.
  - Granite P-256 (`0x100`, EIP-7951 at 6,900 gas) via `*p256verify*`.
- **Coreth 30-field header hashing (`src/input/decode.lisp`)**: gated on `chain-spec-header-rlp` (`:coreth`, installed via `*header-rlp-mode*`), every Avalanche header is RLP-encoded in Coreth's exact `HeaderSerializable.EncodeRLP` order and verified cryptographically against `blk-hash` by `fetch-verified-block`.
- **Coreth Merkle-Patricia Trie (`src/state/mpt.lisp`, `mpt-live.lisp`, `snapshot.lisp`, `snapshot-world.lisp`, `convert.lisp`, `root.lisp`)**:
  - `chain-spec-normalize-slot-key` applies `NormalizeStateKey` (`slot[0] &= 0xfe`) before `keccak256` in live storage roots, incremental MPT, v2 snapshot lookups, v1→v2 conversion, and v2 layer writes.
  - `chain-spec-five-field-account` encodes Coreth's 5-field account leaves (`[nonce, balance, storageRoot, codeHash, multiCoin]`, with `0x80` for `false` and `0x01` for `true`); v2 account flag bit 3 (`+flag-multi-coin+ = 8`, specified in [`docs/state-snapshot-format.md`](state-snapshot-format.md)) preserves `multiCoin = true` across imports, v1→v2 conversion, layers, compactions, and `snapshot-root`.
- **Asynchronous SAE anchor verification (`src/chains/driver.lisp`, `src/state/anchors.lisp`)**: gated on `chain-spec-deferred-anchor-p`, on Helicon/SAE blocks (`settledHeight < number`) frozen anchor layers are recorded durably in `deferred-anchors.sexp` alongside `anchors.sexp` (surviving restarts and rollbacks) and wait for the subsequent settling header; `RootWorker` and `CompactionV2` in `verify/protocols/EitaVeil/` model and prove the deferred-anchor protocol states.

## 3. Running Replay

Full-state replay from a root-checked v2 snapshot (blocks stored in `<dir>/<n>.json` or any configured block source):

```bash
bin/eita --dynamic-space-size 16GB --end-runtime-options replay \
  --chain avalanche --state /path/to/state-dir --resume 95999994 \
  --blocks /path/to/blocks --from 95999995 --to 96000105
```

Unit tests (covering fork schedules, Coreth charging, SAE floor & `GasClock` including extreme Lean-vs-Lisp vectors, Warp, atomic batching, Coreth trie + on-chain WAVAX `eth_getProof` leaf, Coreth header gating, and durable deferred SAE anchors):

```lisp
(eita.test:run-all :only '("avalanche"))
```
