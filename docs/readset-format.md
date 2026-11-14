# Read sets: what each transaction read (format version 1)

A replay with `EITA_READSET_DIR=<dir>` records, for every transaction, the state it read: the
accounts (and which of their fields), the storage slots, the code (by hash) and the block
hashes. Pre-block and post-block system calls are recorded as transactions of their own. The
recorder is `src/evm/readset.lisp`. It subscribes to the event stream (`src/evm/stream.lisp`)
and takes the storage view's read/write stream (`src/state/world.lisp`), runs on its own
thread, and does not change execution. `tests/readset.lisp` checks that the files are exactly
that stream and that every net state change is covered.

The format is meant to become the input of a stateless re-execution of one transaction or one
block. Version 1 carries the **keys**. The values read and the Merkle proofs against the
pre-state root are planned sections (see "Extending it").

## Files

`<dir>/<first>-<last>.rset` (both block numbers 10 digits, zero-padded) is one **segment**: the
blocks first..last, gzip-compressed. Segments are cut at multiples of 10,000 blocks, at every
layer point (checkpoint), at the end of the run, and at the first block boundary after a segment's
tables reach 2^19 accounts and slots (its memory bound; a dense range cuts every few hundred blocks). Each is written to a `.tmp` and renamed; at a
layer point and at the end of the run it and every segment since the last such point are fsynced
with the directory, so a layer at block N is published only after the segments through N are
durable (a segment cut at a range end between layer points may be lost or torn by a machine
crash: the restart is at an anchor at or below the last layer point). A run deletes the segments whose
first block is at or after its own first block, and a reorg rollback to N deletes those after N.
Where two segments still overlap, the segment with the **greater first block** wins for the
blocks they share.

## A segment (after gunzip)

```
"ERS"  version u8 (= 1)  first u64  last u64        big-endian
section*                                            tag u8, length varint, bytes
```

Varints are unsigned LEB128. A reader skips sections whose tag it does not know. Ids are
indices into the segment's own tables, in first-use order.

| tag | section | contents |
|---|---|---|
| 1 | accounts | n, then n × address (20 bytes) |
| 2 | slots | n, then n × (account id varint, slot key 32 bytes) |
| 3 | codes | n, then n × code hash (keccak256, 32 bytes) |
| 4 | blocks | the blocks, below |

**Blocks** (tag 4): for each block that has records, in order:
- `varint` the block number minus the previous one (the first block's predecessor is first−1)
- its transactions, each:
  - `varint` the tx index + 2 (1 = the pre-block system calls, 2 = tx 0, …; post-block = 10^9 + 2)
  - `varint` the number of accounts, then for each, by ascending id: `varint` the id delta from
    the previous one, `u8` mask, and `varint` code id when the mask has bit 4
  - `varint` the number of slots, then for each, by ascending id: `varint` ((id delta) << 1 | written)
  - `varint` the number of block hashes read, then for each `varint` (this block − the block read)
- `varint 0`, the end of the block's transactions

**Account mask**: 1 balance, 2 nonce, 4 code (its bytes: CALL, EXTCODESIZE/COPY; code id = its
hash), 8 code hash (EXTCODEHASH: the leaf's hash and emptiness, not the bytes), 16 existence
(the empty-but-present set), 128 written (a field, or the whole account, was written or credited).
Mask 0 means the transaction touched only the account's storage. A slot's written bit is set
when the transaction wrote it. Each key appears once per transaction, as soon as the
transaction touched it, and reads and writes are merged.

## Scope (version 1)

- Recorded: everything the effect layer reads or writes inside a transaction window, which
  covers user transactions and system calls (EIP-4788, EIP-2935, a chain's pre-block hooks).
- **Not recorded**: state effects outside any transaction window, such as Ethereum's block
  reward and withdrawal credits and a chain's post-block balance deltas. These are writes with
  no read, so a block-level witness must still add the coinbase and withdrawal accounts from the
  block itself.
- A key a transaction reads after an earlier transaction of the same block wrote it is listed
  like any other read. Per-tx re-execution needs its value as of that tx, and block-level
  re-execution does not need it from the pre-state.

## Size (measured)

| input | per-tx encoding | the same, one set per block |
|---|---|---|
| Ethereum mainnet block 24,538,111 (756 txs) | 111,495 B | 105,368 B (−5.5 %) |
| Arc 1..300,000 (light: system calls only) | 6.7 B/block | — |

The tables of 20- and 32-byte keys dominate the size. Splitting the sets per transaction costs
little, so version 1 records per transaction.

## Extending it (planned, same files, new section tags)

- **5 values**: for each (tx, key) entry, the value the transaction first read (account fields
  per mask, slot value). This is what per-tx stateless re-execution needs.
- **6 code bytes**: the bytes for each code hash of section 3 that is not in an earlier segment.
- **7 headers**: the RLP headers for the block hashes read, which a verifier checks by hash chaining.
- **8 trie nodes**: the MPT nodes (deduplicated by hash) that prove section 5's values against the
  block's pre-state root (`eth_getProof` per key; a block's union is the execution witness's `state`).

## Relation to `debug_executionWitness`

geth's and reth's `debug_executionWitness(block)` returns one block's stateless input: `state`
(the RLP trie nodes), `codes` (bytecode), `keys` (the preimages of the hashed trie keys:
addresses and slots; reth) and `headers` (the ancestors that BLOCKHASH needs). It is per block,
unordered, and proof-shaped (the values are inside the nodes). It has no per-tx split and no
field-level information. Our format is a superset in granularity. A block's union of sections
1–3, plus the planned 6–8, projects onto it directly: `keys` = accounts + slots, `codes` =
section 6, `headers` = section 7, `state` = section 8. So we align at that projection (an
exporter) and keep our own storage format, because per-tx sets are the unit a light client
re-executes.
