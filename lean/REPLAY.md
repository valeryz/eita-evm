# Replaying transactions against the Lean EVM

This document started as a survey of replay formats. As of 2026-05-30
it covers the harness in `Replay.lean` plus the cluster of
correctness fixes that landed during the validation push — three
crash classes closed and the entire precompile-dispatch layer
rewritten across Byzantium→Amsterdam.

## Validation snapshot (2026-05-30)

`lake exe replay` over the legacy Constantinople corpus, run as
`DYLD_LIBRARY_PATH=/opt/homebrew/lib`:

| Corpus | Pass | Fail | Crashes |
|---|---|---|---|
| ValidBlocks (Frontier→Istanbul) | 1393 | 0 | 0 |
| GeneralStateTests (Frontier→Istanbul, 50 dirs) | 30694 | 0 | 0 |

**100% pass.** No directory has a remaining failure. The
pre-validation snapshot was 21841 / 111 / 6 crashes; we closed
+8853 passes, -111 fails, all 6 crashes. The fixes that landed
during this push:

| Fix | Closes | Commits |
|---|---|---|
| bn254 FFI: switch to `bn_c384_256.h` to match installed libmcl CTV=46 | ~1800 stZeroKnowledge fails | c40c2ee |
| bn254 FFI: invalid input → zero-length output → wrapper raises OOG | ~80 remaining bn256 fails | c40c2ee |
| bn254 FFI: reject Fp coords ≥ field modulus | 6 perturb-by-field-modulus fails | 4484549 |
| Per-fork precompile-table dispatch (7 sites) | ~830 stPreCompiledContracts* fails | d3a257f / 9b531d4 / 02bf102 / dafe057 / 2adc558 |
| Istanbul EIP-1108 bn256 reprice | bn256 gas at Istanbul+ | f436599 |
| modexp square-and-multiply (`Nat.pow` panic fix) | aborted directories | a63bbed |
| JUMPDEST bitmap cache | 3 timeouts | 2ab5378 |
| mclBn_init fallback | 3 segfaults | afc6ae3 |
| CREATE/CREATE2: keep sender nonce bump on init-code OOG / REVERT | 12 fails across forks | d5ab122 |
| CREATE/CREATE2 collision check includes pre-existing storage | 36 fails across 5 dirs | 3714456 |
| Frontier/Homestead CREATE collision consumes forwarded gas | 2 CreateHashCollision fails | e1c3e77 |

### Fixes that landed this push

1. **bn254 FFI mclBn_init fallback.** The installed libmcl reports
   init failure (rc=-4604, a config mismatch). We were ignoring the
   return code and calling mcl APIs anyway, returning garbage or
   segfaulting on edge inputs. Now we check, set a "stub mode" flag,
   and return zero bytes from all three bn256 entry points without
   ever touching mcl. Closed three GST segfaults.

2. **JUMPDEST bitmap cache.** `Runtime.isJumpDest` rescanned the
   code on every jump — O(code · jumps). `Evm.fresh` now
   pre-computes a byte-per-PC bitmap; JUMP / JUMPI consult it in
   O(1). Closed three GST timeouts (the `JUMPDEST_AttackwithJump`
   et al.).

3. **modexp square-and-multiply.** Lean's `Nat.pow b e` blows up
   on multi-thousand-bit exponents. The
   `modexp_3_09984_39936_*` corpus has ~320 K-bit exponents and
   tripped this on every call. Switched to
   `pow b·b mod m | e/2` style reduction at every step.

4. **Per-fork precompile-table dispatch (the big one).** Every
   fork from Byzantium through Paris (and Shanghai/Osaka/Amsterdam)
   was calling unqualified `PrecompiledContracts.lookup` at both
   the tx-level dispatch site and the inner CALL yield sites.
   `open Evm.Frontier.Vm` meant the lookup resolved to Frontier's
   4-precompile table (0x01..0x04). Any CALL to 0x05 MODEXP /
   0x06-0x08 bn256 / 0x09 BLAKE2F at these forks ran the
   empty-account-code path instead of the precompile — charged
   only intrinsic gas, returned empty output, and any contract
   that depended on the result took its failure branch. This was
   the actual root cause of the "modexp_0_0_0 122-gas drift"
   mystery: the contract CALL'd MODEXP, got nothing back, skipped
   its SSTORE.

   Fixes: Byzantium / Constantinople / Petersburg now consult
   `Evm.Byzantium.Vm.PrecompiledContracts.lookup` (0x01..0x08);
   Berlin / London / Paris / Shanghai consult
   `Evm.Istanbul.Vm.PrecompiledContracts.lookup` (0x01..0x09);
   Osaka / Amsterdam consult `Evm.Cancun.Vm.PrecompiledContracts.
   lookup` (0x01..0x0a). Istanbul's registry itself was
   `Frontier ++ [BLAKE2F]` and lost 0x05..0x08; rebased on
   Byzantium's registry. EIP-1108 bn256 reprice added at Istanbul.

   stPreCompiledContracts:  1083 / 758 → 1841 / 0
   stPreCompiledContracts2:  699 /  18 →  717 / 0

### Outstanding work

- Fix the libmcl install so bn256 actually computes (currently
  ~1800 stZeroKnowledge fails are bn256 stub outputs).
- Type-1 / type-2 tx parser for the Berlin+ corpora (#157).
- Shanghai `DecodedBlock` + withdrawals parser (#158).
- The remaining ~750 fails after this push are in scattered dirs
  (stCreate2 / stSStoreTest / etc.) — small handfuls each, no
  single root cause; needs per-dir triage (#160).

## Current status

Harness lives in `lean/Replay.lean`, exposed as `lake exe replay`. Test
corpus is the LegacyTests Constantinople BlockchainTests, sparse-cloned
under `lean/external/ethereum-tests/`. (Upstream moved `LegacyTests` out of
`ethereum/tests` into `ethereum/legacytests` — same layout minus the
`LegacyTests/` prefix; CI clones that repo. The local checkout predates the
move.)

```
lake exe replay external/ethereum-tests/LegacyTests/Constantinople/BlockchainTests/ValidBlocks
```

Memory: the harness retains per-block state — the full Constantinople
ValidBlocks corpus (1393 blocks) peaks at ~26 GB RSS (measured). On
memory-constrained machines, replay one subdirectory at a time (process exit
frees everything); CI replays a fixed ~100-block sample for the same reason.

The harness dispatches to per-fork `applyBlock` by the test JSON's
`network` field. Currently dispatched: `Frontier`, `Homestead`,
`EIP150` (TW), `EIP158` (SD), `Byzantium`, `Constantinople`,
`ConstantinopleFix` (Petersburg), `Istanbul`, `Berlin`, `London`,
`Paris` / `Merge`. Berlin+ corpora additionally need a type-1 / type-2
tx parser before any of those tests actually parse. New forks just
need their `Fork.applyBlock` (and any `stateRoot` deltas) written and
added to `Replay.applyBlockFor`.

| Corpus | Frontier | Homestead | EIP150 (TW) | Total |
|---|---|---|---|---|
| ValidBlocks | 192 / 192 | 195 / 195 | 185 / 185 | **572 / 572** |
| GeneralStateTests | 929 / 929 | 1931 / 1931 | 1014 / 1015 | **3874 / 3875** |
| **Combined** | | | | **4446 / 4447 — 99.98%** |

One remaining: `tx_e1c174e2_d0g0v0_EIP150` — gas diff of 25011 against
a 10 KB compiled Solidity contract; specific NEW_ACCOUNT edge case in
one opcode. The rest of the corpus says the overall CALL / new-account
rule is right.

Bugs fixed during the Tangerine Whistle bring-up:

- **CREATE collision** at EIP-150 was zeroing the caller's `gasLeft`
  like at Frontier. Under the 63/64 rule that's wrong — the caller
  retains `gas/64` after the forwarded portion is consumed.
- **Sender nonce was not bumped on CREATE collision** (all three
  forks). EELS bumps it; on Frontier/Homestead the bump is reverted
  along with the rest of the tx because the caller OOGs, but at
  EIP-150 the tx survives so the missing bump showed up.
- **`NEW_ACCOUNT` rule at TW** was initially value-gated when ported;
  the tests follow Frontier's "charge iff `!accountExists`" rule.
  EIP-161 introduces the empty-account distinction at Spurious Dragon.

Bugs fixed during the Homestead bring-up:

- `Homestead.applyBlock` was missing uncle-reward distribution (only
  credited the miner the base reward, no uncle bonus, no uncle-coinbase
  rewards). Fixed the 11 `bcUncleTest` / `bcMultiChainTest` cases.
- **Tx-level precompile dispatch was absent in both forks** — when
  `tx.to` was a precompile address, `processTransaction` ran the
  callee's (empty) code instead of the precompile, so the precompile
  cost wasn't charged and tests that depended on it OOG-ing got the
  wrong gasUsed. Fixed the `randomStatetest644/645` cases.
- **Value-zero outer-tx transfer was unconditionally `addBalance`-ing
  the recipient**, creating ghost accounts in state when the recipient
  didn't already exist. Same pattern as the SELFDESTRUCT bug from the
  Frontier triage, just at a different entry point.

Multi-chain tests (chain re-orgs) are handled by dispatching each block
via its `parentHash` through a state-map keyed by block hash. The
canonical chain head is read from the test's `lastblockhash` field, so
we never have to compute total difficulty ourselves.

Wall-clock: ~5s ValidBlocks, ~16s GeneralStateTests.

Bugs fixed during triage (chronological): uncle/ommer rewards,
BLOCKHASH thread-through, pre-EIP-150 CALL gas pre-payment, precompile
dispatch in CALLCODE/DELEGATECALL, BLOCKHASH index formula, EVM
divisor-zero convention for DIV/MOD/SDIV/SMOD, NEW_ACCOUNT charge rule
(`accountExists`, not `isEmpty`), SELFDESTRUCT end-of-tx deletion,
CREATE address-collision (opcode + tx), CREATE-init-failure
nonce-bump persistence, plus (during MPT triage):

- **`logs`, `refundCounter`, `selfDestructSet` moved from per-frame `Evm`
  to shared `Environment`** — sub-frames were each starting with an
  empty `selfDestructSet`, treating every SELFDESTRUCT as "first time"
  and adding 24000 to the refund counter. The spam test does ~8500
  SELFDESTRUCTs of the same address → refund capped at gasUsed/2 in
  the wrong direction. Putting these three on `env` lets sub-frames
  see the parent's running totals; mergeChild becomes `env := child.env`.
- **SELFDESTRUCT beneficiary creation** — EELS Frontier credits the
  beneficiary even on a zero-balance transfer, which creates the
  account in state if absent. This is the pre-EIP-161 behaviour; the
  empty-beneficiary suppression is a Spurious-Dragon-era change.

## Outstanding

(Nothing for Frontier.)

Natural next steps:
- Point the harness at Homestead-tagged tests (it already filters on
  `network == "Frontier"`; needs to dispatch on the `network` field to
  the matching fork's `applyBlock` + `stateRoot`).
- Extend through Spurious Dragon / Byzantium / ... toward Prague.
- Real mainnet replay via geth's `geth export` RLP stream — needs an
  RLP block-stream decoder and a genesis-allocation loader.

## Mainnet genesis + header replay

`Mainnet.lean` + `lake exe mainnet`. Two modes:

1. **`genesis <genesis.json>`** — load the alloc, compute state root,
   compare to the canonical mainnet genesis state root
   `d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544`.

   ```
   $ lake exe mainnet genesis ../chains/ethereum/genesis.json
   loaded 8893 genesis accounts
   computed: 0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544
   mainnet:  0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544
   match:    true
   ```

   This is end-to-end validation of keccak + RLP + the MPT + state
   encoding against the actual hash every Ethereum client computes.

2. **`headers <genesis> <jsonl> <max>`** — replay empty mainnet blocks
   from the JSONL header dump in `data/blocks/headers/`. For each
   block with `transaction_count = 0` AND empty `sha3_uncles`, apply
   the 5 ETH miner reward and verify that the resulting state root
   matches `header.state_root`. Stops at the first block that isn't
   pure-miner-reward.

   On mainnet, blocks 0–2 fit (block 3 already has uncles). All three
   verify successfully. To extend past block 3, the JSONL needs to
   include uncle headers (sha3_uncles is just a hash; we can't compute
   uncle rewards from a hash).

## Source of truth

## What we want

- **Offline.** No live RPC dependency. The user can hand us a file and
  we run.
- **Pre-state + post-state pairs.** So we can check that our
  `applyBlock` is correct, not just runs without errors.
- **Per-fork coverage.** Since the Lean side already mirrors EELS's
  per-fork structure, the test corpus should let us pick which fork's
  semantics to exercise.
- **A small, parseable format.** Lean has JSON in core (`Lean.Json`),
  but RLP we already have. Either is workable; we want to avoid
  pulling in a heavyweight dependency.

## Options

### 1. `ethereum/tests` — BlockchainTests (recommended start)

`https://github.com/ethereum/tests/tree/develop/BlockchainTests`

Canonical EVM-implementation test suite, used by every client (geth,
besu, nethermind, reth, …). ~10s of thousands of JSON files. Each test
specifies:

- `network` (the fork: `Frontier`, `Homestead`, `Byzantium`, …)
- `pre` — initial state as `address → { balance, code, nonce, storage }`
- `blocks` — a list, each with both a full `rlp` (hex) **and** the
  decoded `blockHeader` / `transactions` / `uncleHeaders` fields
- `postState` — expected state after applying all blocks
- `lastblockhash` — sanity check

Pros:
- Stable JSON schema, both hex strings and decoded fields available.
- Tests are organized per-fork, so we can run only the ones for forks
  we already implement.
- Comprehensive negative-test coverage (malformed txs, exceptional
  halts, gas-exhaustion edge cases).

Cons:
- Synthetic, not real mainnet. Sufficient for spec validation; not the
  same as historical-block replay.
- A handful of tests rely on undocumented edge-case behaviour; expect
  some "wontfix" gaps initially.

**Sub-directory of interest:** `BlockchainTests/ValidBlocks/` for the
positive path; `InvalidBlocks/` for negative tests.

### 2. `ethereum/execution-spec-tests` (EELS fixtures)

`https://github.com/ethereum/execution-spec-tests`

The newer test-generation framework that produces the same JSON
fixture format as (1) but from Python test sources. Releases ship
pre-compiled fixture tarballs per fork. Schema-compatible with (1) and
ahead on newer EIPs (Cancun / Prague era).

Use this once we hit Berlin or later — for Frontier / Homestead the
older `ethereum/tests` corpus is more complete.

### 3. Geth / Erigon RLP export — real mainnet blocks

```
geth export blocks-0-1000.rlp 0 1000
```

Produces a concatenation of RLP-encoded blocks. Replaying requires:

- Genesis state file (mainnet allocation).
- Sequential `applyBlock` from block 0.
- A trie / state-root oracle to verify each post-state (we don't have
  a real MPT yet, so this becomes useful only after that's done).

Pros: real history, no synthetic tests.
Cons: needs a synced node to produce the file; ~1 GB per 100k blocks;
state-root verification needs a working MPT.

**Recommended for later**, once the BlockchainTests suite passes and
we have a real `Trie.root`.

### 4. JSON-RPC dump (per block)

`eth_getBlockByNumber` + `eth_getTransactionByHash` from any archive
node, plus `debug_traceBlockByNumber` for the expected state diff. Dump
to JSON. Useful for spot-checking specific historical blocks (e.g.,
"why does block 4,370,000 behave this way?") but heavier per-block
than (3).

## Recommendation

Start with **option 1** (ethereum/tests BlockchainTests):

1. Pick a fork we've implemented end-to-end — Frontier or Homestead.
2. Add a `BlockchainTest.lean` driver that reads one of these JSON
   files (parse via `Lean.Json` in core), reconstructs the pre-state,
   calls `applyBlock`, and compares against `postState`.
3. Add a CLI entry (`lean_exe replay`) that iterates a directory of
   fixture files and reports pass/fail.

That gives us a self-contained, offline conformance-test loop. Once we
pass a meaningful fraction of (1), we'll have the confidence to layer
on (3) for real mainnet replay.

## Open questions to resolve before implementing

1. **Trie root.** `BlockchainTests` validate the post-state trie root.
   Until our MPT is real, we'd have to either skip that check or hash
   the canonical-form serialisation ourselves. Initially: skip; verify
   by walking the account+storage maps directly.
2. **Signature recovery.** Tests use real signatures, so this needs
   `ecrecover` (we now have it) plus the fork's signing-hash variant
   (Frontier has it; EIP-155 lands at Spurious Dragon).
3. **Gas-exhaustion tests vs. our `Exception` type.** Some tests expect
   specific exception kinds; our `Exception` enum is per-fork. We may
   need to widen the comparison or relax tests.
4. **Concurrency / batch size.** A few tens of thousands of tests fit
   in memory easily; running them in parallel is straightforward via
   `lake exe`'s thread pool.

## Where to put the test driver

Sibling to the spec, not inside it:

```
lean/
├── Evm/                 # the spec
├── replay/              # JSON parsing + harness, new
│   ├── BlockchainTest.lean
│   └── Replay.lean
└── lakefile.lean        # add `lean_exe replay`
```

This keeps the spec itself free of `IO` and JSON-parsing dependencies.
