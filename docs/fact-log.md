# The fact log: every verified block as rows

A replay can record what each block did: its header, its transactions with their results,
every call frame, every committed log and native transfer, and every account and storage
slot whose value changed, with the values before and after. These records are the **fact
log**: seven tables, written only for blocks that verified, append-only, block-range
sharded, and carrying a history index that answers "what was this slot (or balance) at the
end of block N" without a replay.

The format is defined once, in Lean (`lean/Evm/FactLog/Format.lean`, `History.lean`), with
proofs that decoding inverts encoding and that the history index answers what folding the
changes would. The schema the readers use is emitted from those definitions.

**Glossary.**
- *fact*: one row of one table, stamped with its block and its transaction.
- *shard*: the rows of one table for one block range (1000 blocks by default).
- *group*: a run of rows inside a shard, columnar and compressed; the unit a reader decodes.
- *footer*: the `.sealed` file describing a finished shard (its blocks, rows, digests).
- *`committed`*: the newest block whose rows are all on disk; readers stop there.
- *history index*: per shard, the rows of the two state tables sorted by key, with a Bloom
  filter of the keys.

## Recording

```sh
bin/eita replay --chain ethereum --blocks DIR --from 1 --to 100000 --factlog /data/factlog/
```

`--factlog DIR` (or `EITA_FACTLOG_DIR=DIR`; from Lisp, `(eita:replay … :factlog DIR)`) installs
the writer before the first block. Without it nothing of the writer runs. `EITA_FACTLOG_SHARD`
sets the blocks per shard (default 1000); keep it the same for the life of a log. A replay
that resumes (`--resume`) continues the same log: the rows a resumed run cannot re-derive are
kept (see *Sealing and durability*).

The writer is an observer on the engine's observation seam and a subscriber of the replay's
event stream (`src/factlog/writer.lisp`). It never changes execution: a replay produces the
same verdicts, state and outputs with or without it.

## The tables

`tx` is the transaction's index in its block; the block's system work (beacon root,
block-hash history, withdrawals, rewards) has `tx` = −1 before the transactions and 10⁹ after
them. Addresses, hashes and values are integers.

| table | one row per | columns |
|---|---|---|
| `block` | block | block, timestamp, coinbase, base_fee, gas_used, gas_limit, prev_randao, blob_gas_used, excess_blob_gas (the last two absent before Cancun) |
| `tx` | transaction | block, tx, hash, from, to (absent for a creation), value, type, gas_used, status (1 success, 0 revert or halt, −1 not executed), egp (the effective gas price) |
| `call` | executed call frame | block, tx, frame (pre-order index, 0 the top frame), parent (−1 for the top frame), depth, kind (0 CALL, 1 CALLCODE, 2 DELEGATECALL, 3 STATICCALL, 4 CREATE, 5 CREATE2), from, to (the code address; for a creation the new address), value, selector (first 4 input bytes, −1 if shorter), input_len, gas (the frame's budget), gas_used, status (0 return, 1 revert, 2 exceptional halt) |
| `log` | committed log | block, tx, log_index (within the tx), address, topics, data |
| `transfer` | committed native value move | block, tx, kind (0 the tx's value, 1 CALL, 2 CREATE endowment, 3 SELFDESTRUCT, 4 a chain's own move), depth, from, to, value |
| `storage_diff` | slot changed by a tx | block, tx, address, slot, pre, post |
| `account_diff` | account changed by a tx | block, tx, address, nonce_pre, nonce_post, bal_pre, bal_post, code_pre, code_post (code hashes, 0 for no code) |

What the rows mean:

- **State changes are net per transaction.** A slot written three times in one transaction is
  one row, its value before the transaction and after it; writes inside a frame that reverted
  net out. A transaction's state rows are in key order (address, then slot).
- **Logs and transfers are the committed ones**: those of a successful transaction, outside any
  reverted frame. A failed transaction has its `tx` row and its state rows (the fee, the
  nonce), no logs and no transfers.
- **Call frames are all the executed ones**, inside failed transactions and reverted parents
  too; a frame's effects survive iff it and every ancestor returned. A call refused before a
  frame exists (depth, balance, address collision) has no row.
- A chain records a subset of the tables when its chain spec says so (`:observe-kinds`).

## Layout on disk

```
DIR/committed                         the newest block whose rows are all on disk
DIR/<table>/<lo>-<hi>.fct             rows: groups, then (state tables) the history index
DIR/<table>/<lo>-<hi>.sealed          the footer, once the range is finished
DIR/<table>/<lo>-<hi>.at-N            checkpoint prefix: the rows of blocks lo..N (a digest)
DIR/<table>/<lo>-<hi>.was             a footer being replaced by a rewrite of the range
DIR/<table>/blooms.idx                every sealed shard's key filter, in one file
DIR/rewrites.sexp                     for each rewritten range: identical to what it replaced?
DIR/code/<version>.txt                what each code version that wrote rows is made of
```

The directory is the index: a block's rows of a table are in the one shard whose range holds
it. A footer is a property list:

```lisp
(:kind :storage_diff :lo 24538000 :hi 24538999 :rows … :first-block 24538000 :last-block 24538999
 :min-block … :max-block … :bytes … :fnv "…" :content "…"
 :index … :bloom-bits … :bloom-k 7 :keys …
 :version "…" :versions ((24538000 . "…")))
```

`:first-block`/`:last-block` say which blocks the shard covers (a shard with no rows of its
table is the fact "no rows here"); the range is **complete** when they are `lo` and `hi` (the
log's first range starts at block 1: block 0 is the genesis). `:bytes` and `:fnv` (FNV-1a 64)
digest the rows file; `:content` hashes the rows themselves, independent of grouping and
compression; `:index` is the history index's offset; `:versions` names the code that wrote
each run of blocks.

## Shards and groups

A rows file is a sequence of self-delimiting groups (`Format.lean encodeGroup`):

```
"EFG1" · groupLen u32 · rows u32 · firstBlock u64 · lastBlock u64 · ncols u8
per column: codec u8 (0 raw, 1 zstd) · rawLen u32 · encLen u32
payloads, one per column, in schema order
```

A column is its fields concatenated (little-endian fixed width: integers u8 to u64 and i64,
addresses 20 bytes, u256 32 bytes; an optional field is a flag byte and the value; a topic list
a count byte and 32 bytes each; data a u32 length and the bytes), zstd-compressed when that is
smaller. A group never straddles a block and is flushed at each commit, so every group
boundary is a consistent cut: a reader decodes whole groups, and a resume truncates at one.
A reader decodes only the columns it asks for.

**Schema evolution.** A table only gains optional columns at its end. A group's `ncols` is its
version: a reader takes the table's first `ncols` columns (`Format.lean colsAt`), so an older
group decodes to shorter rows. `block` rows without the blob-gas columns have 7 fields.

## Sealing and durability

The writer moves `committed` forward only when the rows of every block up to it are on disk,
so a reader that reads `committed` first and then the rows never sees a half-written block.
On a crash `committed` can only lag; it never names a block whose rows were lost, and it is
never an empty or torn file.

- **The barrier.** Durability is one step: on Linux one `syncfs(2)` of the log's filesystem,
  elsewhere `fsync` of every file and directory written since the last barrier. A step that
  must follow durability (a footer's rename, a deletion) waits for the next barrier, so files
  become visible in the order they were written.
- **When.** At the chain's tip, and in a lazy-state run, every commit is a barrier and moves
  `committed`. While catching up, a barrier at every checkpoint, and `committed` at most every
  30 seconds: a crash there restarts from the newest verified anchor and runs those blocks
  again.
- **Sealing.** When the replay moves past a range (or the run ends) each table's shard gets
  its history index, its rows are made durable, its footer is written to a temporary file and
  renamed into place after the barrier: a footer on disk always describes rows on disk.
- **Checkpoint prefixes.** A checkpoint at block N can fall inside a range. The writer then
  publishes `<lo>-<hi>.at-N`, the digest of that shard's rows so far (exactly the rows of
  blocks lo..N), before the state is saved. A run that resumes at N+1 cannot re-derive those
  rows (no state before N is loaded): it truncates the rows file to the prefix and appends. A
  resume that would drop rows without a prefix to keep them refuses to start.
- **Code versions and rewrites.** A complete range is skipped on a re-run only if the code that
  wrote it is the code running now (the code version: a hash of the sources, the native
  libraries and the pinned dependencies). Otherwise the range is rewritten: its footer is kept
  as `.was` until the new rows are sealed, and `rewrites.sexp` then records whether the new
  rows are identical (`:content`) to the ones they replaced. A consumer that folded the old
  rows reads it to decide whether to fold again. `code/<version>.txt` lists what each version
  hashes.
- **Rollbacks.** A reorg rolls the chain back to a checkpoint N: every row above N is
  forgotten (live shards truncate to their `.at-N` prefixes, sealed ranges above N are
  rewritten) and `committed` is set to N before the new branch's blocks arrive.

## The history index and `state_at`

Each shard of `storage_diff` and `account_diff` ends with an index section (`History.lean`):

```
"EFI1" · sectionLen u32 · rows u32 · bloomK u8 · bloomBytes u32 · perm (rows × u32) · bloom
```

`perm` lists the shard's row positions sorted by key (the address's 20 big-endian bytes, then
the slot's 32) and then by file order; the Bloom filter (10 bits per distinct key, k = 7,
double hashing from the key's FNV-1a 64) says whether a key may have changed in the shard,
with no false negatives. `DIR/<table>/blooms.idx` collects every sealed shard's filter, so a
lookup does not open the shards a key never touched; `python3 scripts/factlog.py DIR index`
appends the filters of shards sealed since the last run (run it after sealing; a lookup works
without it, opening each shard's own filter instead).

**The value of key K at the end of block N** (`History.lean lookup`): the last change of K at
or before N gives its `post`; if there is none, the first change after N gives its `pre`;
if K never changed in the log, the answer is `:unknown` (its value is older than the log).
Across shards a reader walks down from N's shard through the shards whose filter admits K,
then up for the first change after N. `lookup_eq_foldValue` proves this equals folding every
change of K in order, given what the writer's rows satisfy: sorted by block and transaction,
and chained (consecutive changes of a key join, `post = next pre`).

**Costs.** A lookup (`state-at`) or a key's history (`key-history`) reads, per shard the filter
admits, the key and value columns, and finds the key's rows by binary search in `perm`: the
cost grows with the number of shards that changed the key, not with the range. A scan
(`map-rows`) reads every group of a table over the range, decoding only the columns it names;
with `:where` it decodes one column first and the rest only at the matching rows.

## Reading

**Common Lisp**, `src/factlog/format.lisp` (package `EITA-FACTLOG`; standalone: it needs SBCL and
libzstd, nothing of the engine, and is part of `bin/eita`):

| function | answer |
|---|---|
| `(state-at dir kind key block)` | a slot's value (`kind :storage_diff`, `key (address slot)`) or an account's `(nonce balance code-hash)` (`:account_diff`, `(address)`) at the end of BLOCK, or `:unknown` |
| `(key-history dir kind key lo hi)` | every change of KEY in [LO, HI]: `((block tx pre post) …)` |
| `(map-rows fn dir kind lo hi &key cols where)` | FN on every row of KIND in [LO, HI], one group in memory at a time |
| `(fact-scan (open-factlog dir) kind lo hi)`, `(fact-logs fl address topic0 lo hi)` | the same rows as a list |
| `(shard-ranges dir kind)`, `(read-footer path)`, `(footer-complete-p footer lo hi)`, `(read-shard path)` | the shards, their footers, their rows |

A row is a list in the table's column order: integers, `NIL` for an absent field, a list of
topics, the log data as a lower-case hex string.

**Python**, `scripts/factlog.py` (the same format, decoded independently): `rows(d, table, lo,
hi)`, `state_at(d, table, key, block)`, `footer`, `committed`, `Tailer` (follows the live
shards up to `committed`), and a command line:

```sh
python3 scripts/factlog.py DIR status                     # the shards and their state
python3 scripts/factlog.py DIR rows tx --block 24538111   # rows, one per line
python3 scripts/factlog.py DIR state storage_diff 0xA0b8…eB48 0x9 24538111
python3 scripts/factlog.py DIR index                      # (re)build blooms.idx
```

Worked examples (a balance at a block, a value's history, a token's transfers, daily
analytics, a fold from the log continued live) are in `examples/history/`; docs/hooks.md,
"Querying history", walks through them.

## The fact log and hooks

Hooks (docs/hooks.md) and the fact log see the same thing: the writer and the hooks
subscriber are two subscribers of one event stream, and a hook's records are the fact log's
rows as property lists. A fold can therefore run either way:

- **live**, subscribed while the replay runs;
- **from the log**: `(eita:backfill DIR FROM TO)` hands the subscriptions blocks FROM..TO
  rebuilt from the facts, without executing them; a replay from TO+1 then continues the same
  subscription. The facts carry no block hash, parent hash, transaction nonce or gas limit:
  those record fields are `NIL` in a backfill, and within a transaction the state changes come
  in key order.

A fold that needs only the fields the log carries gives the same state both ways (the
`history` test suite checks this for the hook examples).

## What is proved and checked

- `Format.lean`: the field, row, column and group codecs invert (`decodeGroup_encodeGroup`, for
  any column codec that inverts itself; zstd's round trip is the one assumption), grouping is
  invisible to a reader (`decodeShard_encodeShard`), a torn tail is detected where it starts
  (`decodeShard_append_tail`), and the rows of blocks ≤ N are a prefix of a shard
  (`takeWhile_block_le`).
- `History.lean`: `lookup_eq_foldValue` (the index's answer equals folding the changes),
  `mem_bloom` (no false negatives), `decodeIndex_encodeIndex`.
- `scripts/verify-factlog-emit.sh`: the emitted schema (`src/generated/factlog-schema.lisp`,
  `scripts/generated/factlog_schema.py`) and vectors match the Lean, and both readers decode
  every vector to its rows, encode the rows back to the bytes, hash them to the content hash
  and build the same index.
- Tests: `tests/history.lisp` (the writer on a mainnet block; every query and the backfill
  against what the replay delivered), `tests/factlog-resume.lisp` (resumes, crashes and power
  loss never drop rows; `committed`'s cadence), `tests/factlog-blooms.py` (blooms.idx: bounded
  memory, torn tails, the same answers with and without it, in both languages).

Not proved: that the Lisp and Python code equals the Lean functions (they are checked on the
vectors and in the tests), and that the writer's rows satisfy the index's hypotheses (sorted,
chained; they hold by how the net per-transaction changes are emitted, and the tests check
the answers on a real block).
