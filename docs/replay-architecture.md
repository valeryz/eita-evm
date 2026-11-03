# Replay architecture: generic EVM replay, chains as specs

Since 2026-10-17 the replay is one generic driver plus per-chain specs. Nothing in the
generic modules knows which chain it runs; a chain changes behaviour only through the
fields of a `chain-spec` (`src/chains/chain-spec.lisp`), which is the complete list of
extension points.

## Layers

| Module | Role |
|---|---|
| `src/evm/` (package `eita.evm`) | EVM core: per-fork semantics, the tiers, host callbacks, `apply-tx` (`tx.lisp`), the event stream (`stream.lisp`) and the observation seam (`observe.lisp`, `observe-tx.lisp`); chain hooks for precompiles, frame-init checks (`chain-frame-init`, the single entry point for tx, CALL and CREATE) and SELFDESTRUCT (`seams.lisp`) |
| `src/input/` (`eita.input`) | the block decoder (a JSON-RPC block object's bytes straight to a `chain-block`), and the **block source** seam: `fetch-block`, `fetch-verified-block`, `fetch-block-hash`, `fetch-receipts`, `fetch-uncles` ask `*block-source*`; `directory-block-source` reads per-block files (docs/block-input.md) |
| `src/evm/run-tx.lisp` | one user transaction: effective gas price, upfront debit, execution, refund cap (London+), EIP-7623 floor (Prague+), fee settlement; hooks: prewarm, upfront extra, fee |
| `src/chains/block-system.lisp` (`eita.chain`) | pre/post-block system calls: EIP-4788 (Cancun+), EIP-2935 (Prague+) by default; chain hooks |
| `src/chains/receipts.lisp` | receiptsRoot and logsBloom from our execution; `verify-block-header` (gas, bloom, receipts root) |
| `src/state/anchors.lisp` (`eita.state`) | full state: genesis alloc, checkpoint schedule, anchors, state-root checks (`eita check-root`, `src/state/root.lisp`) |
| `src/chains/driver.lisp` | `run-block`, reorg rollback, genesis start / anchored resume, `replay-main` (a bounded range; `tip` delegates to the source's `follow`); run policy from `EITA_<NAME>` or the chain's env prefix |
| `src/chains/chain-spec.lisp` | the `chain-spec` record, `install-chain-spec!` (sets every hook; unset = Ethereum default), registry |
| `src/chains/replay.lisp` | `eita:replay` / `eita replay`: a chain by name, its run settings, the driver |

Chain modules (system `eita/chains`): `src/chains/arc.lisp` + `arc-precompiles.lisp` (Arc:
`arc-mainnet`, `arc-testnet`), `src/chains/op.lisp` (OP-Stack: `base`, `opt`, `world`),
`src/chains/ethereum.lisp` (Ethereum, every fork; blocks, receipts and uncles as JSON-RPC
results from the block source).

Where blocks come from is not part of this repository's execution path: a block source
(`make-block-source` in `src/input/source.lisp`) supplies them. The shipped source reads files
you produce with your own node or tools; a source that follows a node over RPC, reads
archives, or serves lazy state is plugged in the same way (`--source FILE` / `EITA_SOURCE`,
a Lisp file that installs it, or an ASDF system that depends on `eita` and sets it).

## Adding a chain

1. Write `(defun <chain>-chain-spec () (make-chain-spec ...))` with only the fields that
   differ from Ethereum: identity and endpoint, `block-setup` (fork table, chain hardfork
   flags), system-call hooks, tx hooks, receipt encoding, precompiles, frame-init rules.
2. `register-chain-spec`, and a small entry that calls `install-chain-spec!` then
   `replay-main`.
3. Never add a hook outside `chain-spec`; a new extension point is a new field there and
   one call site in the generic code.

## Regression

- The fixture battery (docs/testing.md) runs every chain-neutral module on ethereum/tests.
- Full-state paths: a genesis run from block files (docs/block-input.md) checks the genesis
  root, every header, and the state root at the anchors.
