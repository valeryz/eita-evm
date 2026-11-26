# Run a node: Eita next to a consensus client

`bin/eita engine` is an execution client for a consensus client (CL) such as Nimbus. The CL
sends each new block over the Engine API (`engine_newPayloadV4`, `engine_forkchoiceUpdatedV3`);
Eita executes it with the same driver a replay runs and answers VALID, INVALID or SYNCING.
It validates only: it builds no blocks, so the CL must run no validators.

```
consensus client ──HTTP + JWT──▶ eita-engine-api ──local socket──▶ eita engine
 (Nimbus, …)        :8551         (rust/engine-api)  <state>/engine.sock   (src/engine/engine.lisp)
```

`eita engine` starts the edge (`eita-engine-api`) itself; the two stop together.

## Build

```sh
./build.sh            # or ./build.sh --leanless (no Lean: the committed generated files)
```

`build.sh` builds `bin/eita` and `bin/eita-engine-api` (needs `cargo`); the README's Build
section lists the other prerequisites.

## The JWT secret

The CL and Eita share a 32-byte hex secret (execution-apis `authentication.md`). The file
must be readable by its owner only; Eita refuses to open the port otherwise.

```sh
openssl rand -hex 32 > jwt.hex && chmod 600 jwt.hex
```

## Start

```sh
bin/eita engine --chain hoodi --state /path/to/state --jwt jwt.hex
nimbus_beacon_node --network=hoodi --el=http://127.0.0.1:8551 --jwt-secret=jwt.hex
```

A devnet runs the same way with `--chain devnet --genesis genesis.json`, the file its other
clients start from; its blocks are built by another execution client.

| flag | |
|---|---|
| `--chain ethereum\|hoodi\|devnet` | the network: mainnet, the Hoodi testnet, or a devnet on mainnet's rules |
| `--genesis FILE` | the devnet's geth `genesis.json` (its chain id and fork times); required for `devnet` |
| `--state DIR` | the state directory: snapshots, anchors, the executed blocks, the socket |
| `--jwt FILE` | the JWT secret file (mode 0600) |
| `--engine-listen ADDR` | the Engine API address, default `127.0.0.1:8551` |
| `--blocks DIR` | the block files of the file replay that produced the starting anchor (below) |

The heap is a runtime option before the command, as for every `bin/eita` command:
`bin/eita --dynamic-space-size 8GB --end-runtime-options engine …`.

### Where the node starts

Eita does not sync from peers: its state at the CL's head comes from one of two places.

- **From the genesis.** With an empty state directory the node starts at block 0, built
  from the network's `genesis.json` (`chains/<network>/genesis.json`, or `--genesis`). This
  is the path for a devnet whose CL starts at genesis; on a long-running network the CL
  sends blocks far above block 0, which stay SYNCING.
- **From an anchor.** A file replay (`docs/block-input.md`) leaves anchored snapshots in its
  state directory; `eita engine` on that directory starts on the newest one, with `--blocks`
  naming the same block files (the head block and the 256 below it: the BLOCKHASH window
  and the header gate's parent):

  ```sh
  bin/eita replay --chain hoodi --blocks BLOCKS --state STATE/ --from 1 --to N --checkpoint-every 10000
  bin/eita engine --chain hoodi --state STATE --blocks BLOCKS --jwt jwt.hex
  ```

  The replay must end on an anchor (N a multiple of `--checkpoint-every`). The node is
  VALID from the first `newPayload` whose parent is its head; payloads above a gap stay
  SYNCING until the blocks in between arrive.

After a restart the node resumes from its newest anchor; every block it accepts is one, so
it resumes at its last VALID block (`bin/eita recovery peek STATE/` prints it).

## What the answers mean

| answer | when |
|---|---|
| VALID | the block's parent is the head, and the block passed every check below; it is the new head |
| INVALID, `latestValidHash` = the parent | the block failed a check after execution started; the state is rolled back to the parent, and the next payload is judged on its own |
| INVALID, `latestValidHash` null | the payload is not the block it names: its header does not hash to `blockHash`, blob versioned hashes, beacon root or requests differ, or a signature does not recover |
| INVALID, the parent's `latestValidHash` | the parent was INVALID |
| SYNCING | the parent is not held (the payload is stored and runs once its parent is VALID), or no verdict within 7 s (the verdict is recorded for the CL's retry) |
| `-38005` | the timestamp is before Prague or past the last fork Eita implements |

The checks behind VALID: the header against its parent (EELS `validate_header`), every
transaction executed, the gas used, the logs bloom, the receipts root, the transactions and
withdrawals roots, the senders, the requests hash, and the state root. The state root is
checked by the anchor's root check: the block's state is frozen into a layer and the root
of the composed snapshot is computed in a child process before VALID is answered.

`forkchoiceUpdatedV3` answers VALID for the head, records the safe and finalized blocks
(which must be on the head's chain, else `-38002`), and refuses payload attributes with
`-38003`. The node also serves `engine_exchangeCapabilities`, `engine_getClientVersionV1`,
`eth_chainId`, `eth_syncing`, `eth_blockNumber`, `eth_getBlockByNumber` and
`eth_getBlockByHash` for the blocks it holds.

## Limits

- **Validate-only.** No payload building: `engine_getPayload*` is not served.
- **No sync, no reorgs.** A payload whose parent is not held is stored and waits; a
  forkchoice update to a head off the node's chain answers SYNCING.
- **The state root per block costs a root check.** About a second per block on a small
  state, more as the state grows; an incremental state root replaces it.
- **Prague and Osaka only.** `newPayloadV4` covers Prague, Osaka and the BPO1/BPO2 blob
  schedules of the chain's Lean fork schedule: mainnet, Hoodi, and devnets on mainnet's
  rules.

## Checks

- `(asdf:test-system "eita")` runs the engine suite (`tests/engine.lisp`): block 0 from each
  network's `genesis.json` hashes to its genesis hash, and the fork window per network.
- `cd rust/engine-api && cargo test`: JWT rules, the secret file's mode, the JSON-RPC
  envelope over a stand-in socket.
- `tests/engine-checks.py`: the Engine API rules against a running node on a geth `--dev`
  chain (the script is the CL); usage in its header.
