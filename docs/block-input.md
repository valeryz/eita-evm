# Replaying a chain from your own block files

Eita executes blocks; it does not fetch them. You supply blocks — from your own node, an
archive you exported, a test generator — as files, and the replay driver runs them with
the same code paths it runs everywhere: the chain spec's fork table and rules, the
transactions, the system calls, the header gate (EELS `validate_header`/`validate_ommers`),
the receipts root and logs bloom, and, in full-state mode, the state root at anchors.

## The block file format

One file per block in a directory: `<dir>/<n>.json` or `<dir>/<n>.json.gz` (`n` in decimal).
Each file is one of:

1. the block object — the `result` of `eth_getBlockByNumber(n, true)` (full transactions);
2. a whole JSON-RPC reply carrying it (`{"jsonrpc":"2.0","id":1,"result":{...}}`);
3. a wrapper with optional side data:

```json
{
  "block":    { ...eth_getBlockByNumber(n, true) result... },
  "receipts": [ ...eth_getBlockReceipts(n) result... ],
  "uncles":   [ ...eth_getUncleByBlockNumberAndIndex(n, i) results, in order... ]
}
```

What the decoder reads (`src/input/`, `decode-block`):

- **Header**: every field that is in the block's RLP header, under its JSON-RPC name
  (`parentHash`, `sha3Uncles`, `miner`, `stateRoot`, `transactionsRoot`, `receiptsRoot`,
  `logsBloom`, `difficulty`, `number`, `gasLimit`, `gasUsed`, `timestamp`, `extraData`,
  `mixHash`, `nonce`, `baseFeePerGas`, `withdrawalsRoot`, `blobGasUsed`, `excessBlobGas`,
  `parentBeaconBlockRoot`, `requestsHash`), plus `hash`. The header is re-encoded and
  hashed; a block whose fields do not hash to its `hash` is refused.
- **Transactions**: `type`, `from`, `to`, `nonce`, `gas`, `gasPrice`, `maxFeePerGas`,
  `maxPriorityFeePerGas`, `value`, `input`, `accessList`, `blobVersionedHashes`,
  `maxFeePerBlobGas`, `authorizationList`, `chainId`, `v`/`yParity`, `r`, `s`, `hash`, and
  for OP deposits `sourceHash`, `mint`, `isSystemTx`. The sender (`from`) is not trusted:
  it is recovered from the signature and checked. The transactions are re-encoded into
  the `transactionsRoot` the header commits to.
- **Withdrawals** (Shanghai+): `index`, `validatorIndex`, `address`, `amount`.
- **Uncles**: blocks that have ommers (`uncles` non-empty) need the ommer headers, in the
  wrapper's `uncles`; they pay the ommer rewards and are checked by `validate_ommers`.
- **Receipts** (optional): `gasUsed`, `status`, `effectiveGasPrice` (and the OP fee fields).
  With receipts, every transaction's gas and status are compared as it runs; without them
  the block is checked against its header (gas used, logs bloom, receipts root), which
  commits to every receipt anyway.

Other fields are skipped. Hex quantities and data are the usual `0x…` strings.

### Producing files with your own node

Any node that serves the standard JSON-RPC API will do. One block, with `curl` and `jq`:

```sh
n=46147; mkdir -p blocks
curl -s -X POST -H 'content-type: application/json' "$RPC" \
  --data "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"eth_getBlockByNumber\",\"params\":[\"$(printf 0x%x $n)\",true]}" \
  | jq '{block: .result}' > blocks/$n.json
```

(add `uncles` from `eth_getUncleByBlockNumberAndIndex` for blocks that have them). How you
batch, cache or follow the head is up to you; Eita only reads the files.

## Running a range

```sh
bin/eita replay --chain ethereum --blocks /path/to/blocks --from 1 --to 1000 --checkpoint-every 500
```

(or, from Lisp, `(eita:replay "ethereum" 1 :to 1000 :blocks "/path/to/blocks" :checkpoint-every 500)`).
Every flag is also an environment variable the driver reads (`EITA_<NAME>`, or the chain's
prefix: `ETH_`, `ARC_`), as deployments set them: `--blocks` is `EITA_BLOCKS_DIR`, `--state`
`EITA_STATE_DIR`, `--checkpoint-every` `EITA_CHECKPOINT_EVERY`, `--resume` `EITA_RESUME_FROM`,
`--genesis` `EITA_GENESIS`, `--source` `EITA_SOURCE`, `--observer` `EITA_OBSERVER`; full
state is `<PREFIX>_FROM_GENESIS`.

- Full state (the default for Ethereum and Arc; `--lazy` turns it off): the world starts as the chain's genesis allocation
  (`chains/ethereum/genesis.json` for Ethereum mainnet), checked against block 0's state
  root, which must be in the directory too. Every block's header is verified; the state
  root is checked at every anchor (`src/state/root.lisp`, in a child process).
  Anchors fall on a schedule that widens with the block number
  (`Evm.Trie.CheckpointSchedule`: every 1,024 blocks early on, up to 2^20);
  `EITA_CHECKPOINT_EVERY=<k>` anchors every k blocks instead. Snapshots and anchors go
  to `--state DIR` (default `/tmp/eita-state/`; see `docs/layered-snapshots.md`); a
  later run resumes from an anchor with `--resume <block>`. The root check runs
  `bin/eita check-root` in a child process. To record what
  execution did (state changes, transfers, logs, call frames), install an observer
  (`--observer FILE`, the observation seam in `src/evm/observe.lisp`).
- Without full state, a run needs a block source that also serves state (lazy state: each
  account and slot loaded on first touch at the block before the range). The file source
  serves blocks only, so it refuses lazy runs.
- The other chains run the same way: `--chain arc-mainnet` / `arc-testnet`
  (`src/chains/arc.lisp`; the chain's `genesis.json` via `--genesis`), `--chain base` /
  `opt` / `world` (`src/chains/op.lisp`, OP Stack: `--genesis FILE` runs them from the
  chain's genesis alloc — Base's is the superchain-registry `base.json.zst` of the last revision that listed
  Base (`5b055be`), decompressed with that revision's `superchain/extra/dictionary` —, with
  the deposit receipts in the receipts root and the L1 data fee computed from the L1Block
  predeploy; `--lazy` with a state-serving source runs them without full state).
- `EITA_NO_JIT=1` runs the threaded interpreter only; by default hot code is compiled by
  the Lean-emitted JIT.

## Other block sources

A block source is a set of functions (`make-block-source` in `src/input/source.lisp`):
only `:block` is required; `:hash`, `:receipts`, `:uncles`, `:refetch`, `:prepare`,
`:begin`, `:forget-above`, lazy state (`:fault-account`, `:fault-slot`, `:prestate`) and
`:follow` (follow a chain head: `--to tip`) are optional. Put the definition in a Lisp file
that sets `eita.input:*block-source*`, and pass it with `--source FILE` (`EITA_SOURCE`); the
driver loads it before the run. A program building on Eita can instead depend on the ASDF
system `eita` and set the source itself before calling `eita:replay`. Execution never calls anything else of the source, so a
source cannot change what a block does — only which blocks arrive.
