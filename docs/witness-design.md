# Read sets and state witnesses: a Lean-specified, C-callable interface (design)

Status: design, 2026-11-13. Nothing here is built. Owner direction (2026-11-13): the read set of a
transaction or a block is a first-class concept for Eita's users, and the open core exposes it,
together with **state witnesses**, through a C interface specified in Lean, for stateless
re-execution. The first consumer is the RISC-V / Baochip light client: a hardware-wallet-class
device that simulates a transaction on-chip before signing. It replays a transaction only when it
holds all of the transaction's inputs, and a missing input must fail hard.

Related work: the read-set recorder (core branch `readset`, `src/evm/readset.lisp`, format in
`docs/readset-format.md` on that branch), the persistence review §8 (incremental MPT) and §9
(archive read API) in the private repository, and `lean/Evm/Parallel/Reads.lean`, where reads are
already a first-class notion for Block-STM.

## 0. Principles

1. **Lean first.** The read set, the witness, proof verification and the stateless executor are
   defined in Lean. The C is derived from those definitions or pinned to them. EELS is the spec for
   execution; the Yellow Paper, Appendix D, together with EELS `trie.py`, is the spec for the trie.
2. **A missing read is a hard failure, never a default.** The executor stops with the exact key it
   lacks. The theorem `runP_missing` (§2.3) makes this hold by construction.
3. **Safety does not depend on the recorder or on the provider.** A recorder that misses a key, an
   access list that is wrong, or a provider that lies can only make a run *fail*. None of them can
   make it return a wrong result. Correctness rests on proof soundness (§2.1) and on the executor's
   refinement of the spec (§2.3). The recorder only affects liveness.
4. **Provider-agnostic (owner, 2026-11-13).** The executor must work with more or less any Ethereum
   RPC provider, not only with an Eita server. A witness can be built from standard JSON-RPC alone
   (`eth_getProof`, `eth_getCode`, `eth_createAccessList`, `eth_getBlockByNumber`). Where a provider
   exposes `debug_executionWitness`, the executor accepts its output as is. Eita's own server is one
   provider among others; its extra is precomputed, exact per-tx read sets.
5. **The trust anchor is a header, not a provider.** A proof is only as good as the root it is
   checked against. The root comes from a block header that the client trusts independently of the
   RPC (§4.3).
6. **One owner per concern.** One read-key type serves the recorder, Block-STM's read log
   (`Parallel/Reads.lean`) and the witness. One lookup algorithm handles both proof sources. One
   executor serves the chip and the companion host.

## 1. Definitions (Lean)

Proposed home: `lean/Evm/Witness/` (fork-invariant, beside `Evm/Trie`). The statements below
typecheck against the current core. The spike files are `witness-scratch/WitnessSpike.lean` and
`OracleProg.lean`, outside the tree. `OracleProg.lean` is fully proved; `WitnessSpike.lean` contains
`sorry`.

### 1.1 ReadSet

```lean
inductive ReadKey where
  | exists_   (a : Address)              -- in the trie at all (NEW_ACCOUNT pre-161, EIP-161 emptiness)
  | nonce     (a : Address)
  | balance   (a : Address)
  | codeHash  (a : Address)              -- EXTCODEHASH, emptiness: the leaf only
  | code      (a : Address)              -- the bytes (CALL, EXTCODECOPY, EXTCODESIZE)
  | storage   (a : Address) (slot : U256)
  | blockHash (n : Nat)
abbrev ReadSet := List ReadKey           -- per tx; a block's is §2.4
```

The read kinds are those of the storage view's read stream (`src/state/world.lisp`: `:present
:nonce :balance :code :storage`) plus the recorder's additions (`:codehash :blockhash`, branch
`readset`). The recorder's per-tx record (an account mask, slots, codes by hash, block hashes) is
exactly a `ReadSet` together with a written-bit. Field granularity is kept because dependency and
MEV consumers want it. A witness, however, covers an account as a whole, since one account proof
yields all four fields.

`Parallel/Reads.lean`'s abstract `Key` becomes `ReadKey`. One read-set notion remains, and its
`Faithful`/`Deterministic` conditions become theorems about the executor instead of hypotheses
(§2.3).

### 1.2 Witness

```lean
structure Witness where
  pool    : Pool          -- trie-node preimages, account and storage tries together
  codes   : List Bytes    -- contract codes, found by keccak
  headers : List Bytes    -- RLP headers, newest first: the parent (its stateRoot = the pre-root)
                          -- and ancestors back to the oldest BLOCKHASH read
  keys    : List Bytes    -- optional preimages of hashed keys (addresses, slots)
structure Pool where nodes : List Bytes   -- content-addressed: a node is found by hashing it
```

This is the shape of `debug_executionWitness` (reth `ExecutionWitness { state, codes, keys,
headers }`, geth `stateless.Witness`), so one format serves both acquisition paths (§5). The
witness does not carry values. Every value is the result of a lookup in the pool, and a lookup *is*
the verification.

### 1.3 Lookup (proof verification)

```lean
inductive Lookup | found (v : Bytes) | absent | missing (h : Bytes) | malformed
def walk   (p : Pool) : Nat → Rlp.Item → List UInt8 → Lookup  -- total (fuel 2·64+2)
def lookup (p : Pool) (root key : Bytes) : Lookup               -- key = keccak(addr) / keccak(slot)
```

`walk` resolves a 32-byte reference by finding a pool node whose keccak is the reference. It takes
an inline (< 32 bytes) node as given, follows branches, extensions and leaves, and returns `absent`
on a proof of exclusion. The spike contains a complete definition, about 60 lines. It is total and
structurally recursive, so it can be proved about.

### 1.4 PartialState

```lean
structure PartialState where
  root    : Bytes         -- trusted pre-state root (from a trusted header, §4.3)
  w       : Witness
  overlay : Diff          -- the executor's own writes: accounts (none = deleted), slots, wiped storages
```

Reads go to the overlay first, then to `lookup`. The partial state's oracle is
`po : ReadKey → Option Answer`: `some` comes from a `found`/`absent` lookup or from the overlay, and
`none` comes from `missing`/`malformed`. No PartialState is built eagerly, so loading a witness
only builds an index (§3).

### 1.5 The executor as an oracle program (the key move)

The spec's `Evm.Frontier.Vm.Tx.run k …` (one definition for every fork) reads a concrete `State`
directly, so nothing in it marks which keys it read. Instead of adding a second "reads" function
beside it (a second copy), the stateless executor is defined as an **oracle program**. It reads
its pre-state only by asking queries:

```lean
inductive Prog (Q : Type) (A : Q → Type) (α : Type) where
  | ret (a : α)
  | ask (q : Q) (k : A q → Prog Q A α)
def Prog.run   (o  : (q : Q) → A q)          : Prog Q A α → α            -- full state
def Prog.asked (o  : (q : Q) → A q)          : Prog Q A α → List Q       -- THE read set
def Prog.runP  (po : (q : Q) → Option (A q)) : Prog Q A α → Except Q α  -- partial: error = the key
```

The read set is then *defined by the program*: `asked` is the trace of queries. It cannot drift
from the execution, because there is nothing separate to drift.

## 2. The theorems

### 2.1 (a) Proof soundness

```lean
def Collision : Prop := ∃ x y : Bytes, x.data ≠ y.data ∧ keccak256Bytes x = keccak256Bytes y

theorem lookup_found_sound (p : Pool) (items : List (Bytes × Bytes)) (key v : Bytes)
    (wk : WellKeyed items) (hk : key.size = 32)
    (h : lookup p (Evm.Trie.rootBytes items) key = .found v) :
    find? items key = some v ∨ Collision
theorem lookup_absent_sound … (h : lookup p (Evm.Trie.rootBytes items) key = .absent) :
    find? items key = none ∨ Collision
theorem lookup_complete …  -- liveness: the ≤ 129 nodes on the key's path answer it
```

The pool is arbitrary, so the provider is unconstrained. Keccak is an opaque `@[extern]`, so its
collision resistance cannot be proved. The statement therefore extracts a collision instead of
assuming an axiom. This is the standard reduction: a forged proof is a Keccak collision. The
account layer composes the state-trie lookup, the RLP decode of `[nonce, balance, storageRoot,
codeHash]`, a storage-trie lookup under that `storageRoot`, and `keccak(code) = codeHash`. Headers
are checked by `keccak(rlp(header)) = parentHash` back from the trusted header.

**Proof sketch.** Induct along the path. At each hashed reference, the honest node `N` has
`ref = keccak(encode N)`. The pool node `n` with `keccak n = ref` is either `encode N` (and then
`decode (encode N) = some N`) or the second half of a collision. Non-canonical RLP accepted by the
decoder is therefore harmless. The structural heart is `walk` over `patricialise items` =
`find? items`.

**Prerequisite (W0).** `Rlp.encode`, `Rlp.decodeAt`, `Trie.patricialise` and `Trie.nodeRef` are
`partial def`s today, which makes them opaque to the kernel. They must be made total, and
`decode (encode i) = some i` must be proved. This is the same prerequisite that
`Trie/Incremental.lean` (`Canonical`) and `Trie/Stack.lean` (the `sorry`s of
`build_eq_patricialise`) already record, so one stage pays for all three.

### 2.2 (b) Witness sufficiency

```lean
def AgreeOn (R : ReadSet) (s t : State) : Prop          -- every read in R answers alike
def Sufficient (c : TxCtx) (R : ReadSet) (s : State) : Prop :=
  ∀ s', AgreeOn R s s' → SameOutcome s s' (c.run s) (c.run s')   -- gas, status, logs, same Diff
theorem sufficiency (hs : RootOf s root) (hs' : RootOf s' root) (hR : Sufficient c R s)
    (hc : Covers root W R) : SameOutcome … ∨ Collision
```

`SameOutcome` compares the post-states as a diff, `ObsEq r.state (d.apply s)`, because the spec's
`State` is a list and so not extensional. This is the semantic statement, and it is what a reader
of the API needs: a witness covering a sufficient read set determines gas, status, logs and the
state diff.

### 2.3 (c) Read-set completeness, and missing read = hard failure

These hold *generically* for every oracle program. They are proved now, without `sorry`, in the
spike `OracleProg.lean` (Lean v4.35.0, about 60 lines):

```lean
def Consistent (po) (o) : Prop := ∀ q v, po q = some v → v = o q        -- what (a) gives
theorem runP_sound       (hc : Consistent po o) : p.runP po = .ok a → p.run o = a
theorem asked_sufficient : (∀ q ∈ p.asked o, o q = o' q) → p.run o = p.run o' ∧ p.asked o = p.asked o'
theorem runP_missing     (hc : Consistent po o) : p.runP po = .error q → q ∈ p.asked o ∧ po q = none
theorem runP_complete    : (∀ q ∈ p.asked o, po q = some (o q)) → p.runP po = .ok (p.run o)
```

- `runP_sound`: a stateless run that completes returns exactly the full run's result.
- `asked_sufficient`: the asked set is a sufficient read set. This is `Reads.Tx.Deterministic`,
  now a theorem.
- `runP_missing`: a failure names a key the full execution really reads and the witness really
  lacks. This is the Baochip requirement.
- `runP_complete`: a witness that covers the asked set always completes.

**The one specific obligation** connects the oracle program to the spec:

```lean
def txProg (c : TxCtx) : Prog ReadKey Answer (Except String TxResult)
theorem txProg_refines (c : TxCtx) (s : State) :
    SameOutcome s s ((txProg c).run (oracleOf s)) (c.run s)      -- for every fork k, as apply_tx_refines
```

`txProg` is not hand-written beside the spec. It is the spec's own run with every pre-state read
turned into an `ask`, while the program keeps its writes in the overlay. The reads are already
isolated:

- In the frame, state is touched only through the state yields (`YieldEffect.sload / balance /
  extcodesize / extcodecopy / blockhash / …`), which are answered by the total `handleYield`
  (`Frontier/Vm/Effect.lean`).
- In the effect layer, every world read is a named primitive of the effect IR (`Evm.CL.EffectIR`,
  for example `faultSlot`, `sload`, account reads), and `Stmt.run` gives their meaning.

So the work is twofold. First, give `Stmt.run` an `ask` meaning for its read primitives, which is
one induction over `Stmt` and covers CALL, CREATE, SSTORE, SLOAD, settle, end-of-tx and tx at once.
Second, give the tx/call/create glue in `Vm/Tx.lean`, `Call.lean` and `Create.lean` its reads as
`ask`s. `txProg_refines` then follows the existing `Effect*Proof` refinements. It needs a total
trampoline with fuel (`runFrameR` exists; `trampoline` is `partial`), which is the same shape the IR
soundness theorems already use.

Composed: (a) gives `Consistent (poOf ps) (oracleOf s)` for every full state `s` whose root is
`ps.root`, up to `Collision`. `runP_sound` and `txProg_refines` then give the **stateless soundness
theorem**:

```lean
theorem stateless_sound (ps : PartialState) (s : State) (h : RootOf s ps.root) :
    (txProg c).runP (poOf ps) = .ok r → SameOutcome s s r (c.run s) ∨ Collision
```

This is the theorem the C interface is pinned to (§3.4). Note that it does not mention the
recorder.

### 2.4 (d) Composition: block witnesses from tx witnesses

A block is `Prog`'s bind: the txs run in order over one overlay, with the pre-block system calls
(EIP-4788, EIP-2935) first and withdrawals and rewards last. Reads that hit the overlay are not
asked. Hence:

```lean
theorem block_asked (o) : (blockProg b).asked o =
  pre.asked o ++ (tx₀.asked o₀) ++ … ++ (txₙ.asked oₙ)
  -- oᵢ = o overlaid with the diffs of the txs before i; a key some tx before i wrote is never asked
def blockReads : List (ReadSet × Diff) → ReadSet   -- union, minus earlier txs' writes (and wiped storages)
```

As a consequence, a block witness is the union of its tx witnesses taken at the block's pre-root,
minus the writes of earlier txs. Conversely, **the witness of tx i at its true pre-state** (inside
a block) is the block-prefix witness: the parent's root together with the reads of txs `0..i-1`.
Post-Byzantium headers carry no per-tx intermediate root, so there is no other root to prove tx i's
reads against. The wallet case (a pending tx) is simpler: it runs as the first tx on top of the
latest trusted header, against that header's `stateRoot`, with the semantics of `eth_call` at
`latest` (§4.4).

**Post-state root.** Recomputing the post-state root statelessly needs more nodes than the reads
do. Deleting a key can collapse a branch into its sibling, so the sibling node is needed even
though nothing read it. reth's witness includes these nodes "during state root recomputation";
proofs from `eth_getProof` do not. A wallet does not need the post-root, and a stateless block
validator does. `post_root` (§3) reports `missing` for such a node like any other read.

## 3. The C interface

### 3.1 Shape

A single header, `c/eita_witness.h`. There is no global state. The caller owns every buffer. There
is no `malloc`: all working memory comes from one caller-provided arena, and exhausting it is an
explicit status. Builds target RV32IMC, RV64 and the hosts. The ABI uses no 64-bit pointers and no
FPU.

```c
typedef struct { const uint8_t *ptr; uint32_t len; } eita_buf;      /* borrowed; may live in flash/XIP */

typedef enum {
  EITA_WX_OK = 0,
  EITA_WX_MISSING,          /* a read the witness cannot answer: see eita_wx_miss (exact key) */
  EITA_WX_MALFORMED,        /* witness/tx/header bytes do not parse */
  EITA_WX_HEADER_CHAIN,     /* headers do not hash-chain to the trusted header */
  EITA_WX_ENOMEM,           /* arena exhausted: cannot simulate (never reported as out-of-gas) */
  EITA_WX_UNSUPPORTED,      /* fork / tx type outside this build */
  EITA_WX_INVALID_TX        /* the spec's validity rules reject the tx (reason code in result) */
} eita_wx_status;

typedef struct {            /* the exact missing read: what the companion host fetches next */
  uint8_t kind;             /* EITA_RK_{EXISTS,NONCE,BALANCE,CODEHASH,CODE,STORAGE,BLOCKHASH} */
  uint8_t addr[20]; uint8_t slot[32];
  uint8_t node_hash[32];    /* the missing trie node / code hash (diagnostic) */
  uint64_t block;           /* for BLOCKHASH */
} eita_wx_miss;

typedef struct eita_wx eita_wx;   /* opaque, lives at the start of the arena */

/* Index the witness (borrowed): one keccak per node and code, a sorted (hash -> offset) table in
   the arena; check the header chain back from `trusted_header_hash`; take the pre-state root from
   the newest header. Re-hashes everything: the provider is untrusted. */
eita_wx_status eita_wx_open(void *arena, uint32_t arena_len, const uint8_t trusted_header_hash[32],
                            eita_buf witness, eita_wx **out);

/* Append more nodes/codes/headers (the iterative loop, §4.2). Keeps the overlay empty. */
eita_wx_status eita_wx_extend(eita_wx *wx, eita_buf more);

/* Point reads: verified account / slot at the pre-state (an eth_getProof verifier in one call). */
eita_wx_status eita_wx_account(eita_wx *wx, const uint8_t addr[20], eita_wx_account *out, eita_wx_miss *miss);
eita_wx_status eita_wx_storage(eita_wx *wx, const uint8_t addr[20], const uint8_t slot[32],
                               uint8_t value[32], eita_wx_miss *miss);

/* Execute. The block environment is built from the trusted header (`eita_wx_env_next` derives the
   next block's: number+1, base fee by the emitted EIP-1559 formula, the timestamp the caller
   gives); the chain config (chain id, fork schedule) is the caller's, never the provider's. */
eita_wx_status eita_wx_env_next(eita_wx *wx, uint64_t timestamp, const uint8_t coinbase[20],
                                eita_wx_env *env);
eita_wx_status eita_wx_run_tx(eita_wx *wx, const eita_wx_env *env, eita_buf signed_tx,
                              eita_wx_tx_result *res, eita_wx_miss *miss);
eita_wx_status eita_wx_run_block(eita_wx *wx, eita_buf block_rlp, eita_wx_block_result *res,
                                 eita_wx_miss *miss);

/* Results: gas, status, logs (borrowed views into the arena, valid until reset), the diff as an
   iterator (accounts: pre/post fields; slots: pre/post; wiped storages), the receipt bytes. */
int            eita_wx_diff_next(eita_wx *wx, eita_wx_diff_iter *it, eita_wx_diff_entry *e);
eita_wx_status eita_wx_receipt(eita_wx *wx, uint32_t tx_index, uint8_t *out, uint32_t cap, uint32_t *len);
eita_wx_status eita_wx_post_root(eita_wx *wx, uint8_t root[32], eita_wx_miss *miss);
/* The read set the run asked (Prog.asked), for the host's loop and for consumers. */
int            eita_wx_reads_next(eita_wx *wx, eita_wx_reads_iter *it, eita_wx_readkey *k);
void           eita_wx_reset(eita_wx *wx);   /* drop the overlay and results, keep the index */
```

**Probe mode, for the companion host only.** `eita_wx_run_tx` with `EITA_WX_PROBE` answers a
missing read with zero or empty, *records* it, and continues. The result is discarded, and the
recorded keys only predict what to fetch, so one round trip collects several missing keys. A probe
result is never returned as a simulation. The chip build compiles probe mode out.

### 3.2 Memory (embedded target)

| what | size |
|---|---|
| node/code index | 36 B per node (hash + offset), sorted in place, binary search |
| overlay | per written account/slot, ~100 B |
| EVM stack | 32 B per *used* slot, from the arena (not 1024 × 32 B reserved per frame) |
| memory | gas-bounded: 30M gas buys ≤ ~3.9 MB in one frame (3w + w²/512) |
| call depth | 63/64 bounds it near ~700 at 30M gas; frames ~200 B + their stack and memory |

A typical wallet transaction (a transfer, an approval, a router swap) has a witness of roughly
50–500 KB. Code dominates it: up to 24 KB per contract. Its working memory is under 1 MB. These
are estimates to measure in W5, not numbers measured on the Baochip. An adversarial transaction can
exceed any fixed arena. The answer is then `ENOMEM` ("cannot simulate, do not sign blind"), never a
wrong result, because running out of arena aborts the run like a missing read and has no gas
semantics. The witness buffer is read in place, so it may sit in flash.

### 3.3 What is derived and what is glue

| part | source | checked by |
|---|---|---|
| opcode handlers, gas formulas, fork tables | emitted from Lean (existing; RV32/RV64 is the third AsmCore lowering, or C via the limb ops) | existing emit drift checks, AsmCore proofs for the lowering |
| effect layer: CALL, CREATE, SSTORE, SLOAD, settle, end-of-tx, tx | effect IR → **C** printer (`Evm.CL.EffectC`, today SLOAD/SSTORE only; extend to every term) | `Effect*Proof` (spec refinement), printer trusted like `toCL` |
| oracle seam: overlay-then-lookup, `missing` | **emitted**: `walk`/`lookup` are first-order and total, printed to C like `LimbC` | `lookup_*_sound`, plus CBMC on the printed C (bounds, no OOB on adversarial bytes) |
| RLP decode, hex-prefix | emitted from the totalized `Rlp.decodeAt` (W0) | round-trip theorem, CBMC |
| keccak | `lean/c/keccak.c` (existing, trusted) | test vectors (trusted surface) |
| ecrecover (sender) | libsecp256k1 (existing, trusted) | fixtures |
| arena, index sort, header parsing, API marshalling | hand-written glue (~400 lines) | CBMC harness (`c/cbmc/` pattern), property tests vs the Lean reference |

The native accounts plus CALL/CREATE in C is the same work as the "all-C core" the RISC-V port
needs (new-ideas item 5). The witness interface is that core's world-view implementation, and it
does not add a second core.

### 3.4 Pinning

`lean/Comparator/Challenge.lean` gains, with owner review, `lookup_found_sound`,
`lookup_absent_sound`, `runP_sound`, `runP_missing`, `txProg_refines` and `stateless_sound`. The
standard axioms are enough: keccak appears as an opaque constant inside `Collision`, not as an
axiom. The C side is pinned to the same terms. The printed C is byte-checked against the emitter
(like `storage_effect.c`), and the property test runs the C and `Prog.runP` in Lean on the same
witnesses (random pools, truncated pools, flipped bytes) and requires identical statuses and
results. Conformance comes from the ethereum/tests BlockchainTests battery, run statelessly: build
the witness from the fixture's pre-state with the Lean reference and require the fixture's post-
state.

## 4. Producing witnesses

### 4.1 Path A: `debug_executionWitness` (where offered)

geth and reth return, for block N, the nodes, codes, key preimages and ancestor headers needed to
re-execute N on N-1's state, including the nodes for the post-root (reth `debug_executionWitness` /
`debug_executionWitnessByBlockHash`). The output is accepted as is (§5).

Hosted availability is uneven:

- Alchemy documents the method on several chains: Base, Polygon PoS, Ronin, BOB, Arc and others,
  at 40 CU.
- QuickNode's status page records a fix "to avoid returning incomplete witness data" in its July
  2026 Reth/Erigon upgrade for Ethereum mainnet, which implies the method is served. No method page
  was found.
- No Infura listing was found for Ethereum mainnet.
- Public endpoints generally do not expose `debug_*`.

This path is therefore an option, never a requirement. It is block-level only: there is no
per-call witness, so a pending wallet tx needs path B.

### 4.2 Path B: standard JSON-RPC only (every provider)

All on the companion host, at a fixed block `N` (the trusted header's):

1. `eth_createAccessList(tx, N)` gives predicted accounts and slots.
2. Add the sender, the `to`, the coinbase, the EIP-7702 delegates of the accounts listed, and the
   system contracts the block touches. geth's access list omits the sender, the recipient and
   precompiles.
3. `eth_getProof(addr, slots, N)` per account (EIP-1186), batched in one JSON-RPC batch.
   `accountProof` and every `storageProof[].proof` are flattened and deduplicated into the pool.
4. `eth_getCode(addr, N)` for each account whose `codeHash` is not the empty hash. The executor
   checks `keccak(code) = codeHash`.
5. Headers come from `eth_getBlockByNumber`, for BLOCKHASH back from N. The executor checks the
   hash chain.
6. **Run strictly** (`eita_wx_run_tx`). On `EITA_WX_MISSING`, fetch the reported key with
   `eth_getProof`, `eth_getCode` or a header, `eita_wx_extend`, and rerun. To cut the number of
   round trips, run in probe mode first and fetch everything it recorded in one batch.
7. **Bounded:** at most 8 rounds or 512 keys, then give up ("cannot simulate").

The access list has honest gaps:

- It is computed by one execution on the provider's view. A branch that depends on gas (the
  63/64 rule under different gas, `GAS` opcodes) or on values (an oracle price, a balance) can read
  keys the prediction did not.
- It does not list code or block hashes.
- It is advisory: a provider can return anything.

The loop closes all three, and none of them can cause a wrong result (§0.3).

**Cost.** Each round costs one batched RPC round trip, about 50–300 ms to a hosted provider, plus a
local rerun of a few milliseconds on a host. In the expected case the access list plus probe mode
needs zero or one extra round. The worst case is the bound.

**Where it runs.** The loop runs on the companion host (phone or PC), which is online and runs the
*same* C library. The chip is offline. It receives only the final witness, the trusted header (or
verifies it, §4.3) and the tx, then re-runs strictly. If the chip's own run hits `MISSING` or
`ENOMEM`, it refuses to show a simulation, so the host cannot make the chip trust a result the chip
did not compute.

### 4.3 Trust model

- **Trusted:** the root. The client checks a header it trusts independently of the RPC:
  - a beacon light client (Altair sync committee: a `LightClientUpdate` with ≥ 2/3 of the 512-member
    committee's BLS aggregate signature; from Capella, the `LightClientHeader` carries the
    execution payload header, `state_root` and `block_hash`, under a Merkle branch to the beacon
    `body_root`);
  - or a checkpoint the user pins: a block hash, or a weak-subjectivity checkpoint for the sync
    committee.

  BLS verify uses blst, which is already vendored for EIP-2537.
- **Then the provider is untrusted.** A wrong value, node, code or header fails verification
  (`lookup_*_sound`: a forgery is a Keccak collision). Withholding data fails the run with
  `MISSING`.
- **What the provider still controls:**
  - availability (denial of service);
  - freshness, if the client lets the provider choose N. The client must take N from its light
    client, not from the provider.
- **What the client must own:** the chain config. The fork schedule and the chain id select the
  semantics, so they are never taken from the provider.
- **Core theorem:** `stateless_sound`. Under a trusted root, the device's result is the spec's
  result for the state with that root, or there is a Keccak collision.

### 4.4 What a simulation means

The result is what the tx does if executed as the first tx on the post-state of the trusted block
N, which is `eth_call` at `latest`. Txs included before it in the next block can change the
outcome. A front-run is outside what any pre-state proof can rule out. The UI must say "as of block
N".

### 4.5 Path C: Eita's server (one provider among others)

Eita adds three things:

1. **Exact per-tx read sets** from the recorder (branch `readset`), so a replayed tx needs no
   access-list guessing and no loop.
2. **Block-prefix witnesses** for historical txs at their true pre-state (§2.4).
3. **The same format.**

What it needs in order to produce proofs:

- **Nodes at a root.** Eita keeps no persistent trie today: `mpt-live.lisp` is refused at startup,
  and roots are checked per anchor by the stack build (`src/state/root.lisp`, `Trie/Stack.lean`),
  which hashes nodes and discards them.
- **Minimal path (W4a): witnesses at anchors.** Give the stack build a *proof-extraction* mode: for
  a sorted set of target keys, emit every node whose key range contains a target, at the moment it
  closes. One streaming pass over the anchor's snapshot then serves every request batched for that
  anchor. It costs minutes per pass on Ethereum, adds no new trie store, and is the same code as
  the root check.
- **Tip (W4b):** stage 8's incremental trie (persistence review §8) holds the tip's nodes, so
  `eth_getProof` and witnesses at the tip are reads of it.
- **Arbitrary historical N:** stage 8 together with §9's archive (state at N, from the nearest
  snapshot plus diffs), or a stack build over the state at N. This comes last and is gated on
  measured demand.

## 5. Format

**Interchange (JSON):** exactly `debug_executionWitness`'s object, `{"state": [hex node…], "codes":
[hex…], "keys": [hex…], "headers": [hex rlp…]}`. A reth or geth response is a valid input as is.
The eth_getProof path produces the same object: the proof nodes go to `state`, the codes to
`codes`, the addresses and slots to `keys`. Optional Eita extensions sit under `"eita"`: the format
version, the trusted block hash, and the typed read set (§1.1). An extension is never required for
verification.

**On-device (binary):** an RLP list `[version=1, trustedHash, headers, nodes, codes, keys, ext]`.
RLP is used because the chip must parse RLP for nodes, headers and txs anyway, which keeps one
parser and no new framing. Order inside a section is free, because the index sorts by hash.

**Where it differs from debug_executionWitness, and why:**

1. `headers` must include the trusted header itself. Eita requires the chain to end at a hash the
   caller trusts, and reth's ordering is not relied on.
2. `keys` are optional. Verification never needs preimages, because the keys are hashed on the
   device; they are only for display and diffs.

The read-set recorder's segment format (`docs/readset-format.md`) is a separate archive of
*keys*, not values. A witness is built *from* it (path C), so the two do not overlap.

## 6. Staging, effort, dependencies, risks, complexity

| stage | what | effort | needs |
|---|---|---|---|
| **W0** | totalize `Rlp.encode/decodeAt`, `Trie.patricialise/nodeRef`; `decode ∘ encode = some`; `patricialise` characterization (items ↔ structure) | 2–3 wk | — (also unblocks `Trie/Stack` `sorry`s and `Incremental.Canonical`) |
| **W1** | `Evm/Witness/{ReadKey,Pool,Lookup}.lean`; prove (a) and the account layer; `Prog` + the four generic theorems (done in the spike) | 1–2 wk | W0 |
| **W2** | `txProg`: effect IR `ask` semantics (one induction over `Stmt`), frame state yields as `ask`, tx/call/create glue reads; `txProg_refines` for every fork; block bind (d) | 4–8 wk | existing `Effect*Proof`, total trampoline with fuel |
| **W3** | C: `lookup`/RLP printed from Lean, glue + arena, `eita_wx_*`; CBMC harness; property tests vs Lean; stateless BlockchainTests on host | 3–4 wk | W1; effect IR → C for the remaining terms (all-C core) |
| **W4a** | path B on the host (access list + getProof loop + probe), against two hosted providers and one public endpoint; path A ingestion | 1–2 wk | W3 |
| **W4b** | path C: stack-build proof extraction at anchors; recorder read sets → witnesses | 2 wk | `readset` branch merged |
| **W5** | RV32 build, Baochip RAM/flash measurement on real wallet txs; light-client header verification (sync committee, blst) | 3–5 wk | RISC-V lowering, all-C core |
| **W6** | stateless block validation with post-root (deletion siblings); tip witnesses | later | stage 8 incremental MPT |

The critical path is W0 → W1 → W2, which is proof work. W3 and W4a can run against the Lean
reference before W2 is closed, and (c) holds for any `Prog` already. Until `txProg_refines` is
proved it is a listed open obligation in the coverage matrix, which raises the debt ratchet
explicitly. It is not a hidden gap.

**Risks.**

1. W2's size. The tx glue reads `State` directly in many places, and turning each read into an
   `ask` without forking the spec needs care.
   - Mitigation: route the glue's reads through a small set of accessors first (a refactor, proved
     equal), then make the accessors the `ask` points.
2. The all-C core (native accounts + CALL/CREATE in C) is a prerequisite for the chip but is not
   built.
3. Baochip RAM: the actual part's SRAM/PSRAM is unconfirmed (believed RV32 with a few MB). W5
   measures it before committing to a large-tx story.
4. Provider behavior: `eth_createAccessList` quirks and `debug_executionWitness` gaps (QuickNode's
   own "incomplete witness" fix).
   - Mitigation: the loop, and hard failure.
5. Post-root nodes for deletions (W6) are absent on path B.

**Complexity budget.** This is an owner-approved feature, and it should replace ad-hoc pieces.
Proposed offsets, each of which removes a second copy or an unverified path:

1. **Delete `lean/Evm/Frontier/Trie.lean`** (44 lines). It is a placeholder whose `root` returns a
   constant and whose only user is an unused import in `Frontier/Fork.lean`. `Evm.Trie` and
   `Witness.Lookup` supersede it. Delete it in W1.
2. **Replace the Base track's unverified lazy RPC state** (`src/chains/op.lisp`: the
   prestateTracer overlay, the disk cache and `eth_getStorageAt`/`eth_getCode` faults, where a miss
   is "counted + warned"). It becomes the witness path: the same fault hooks, proof-verified
   against the header `stateRoot`, with a miss as a hard failure. Alchemy serves
   `debug_executionWitness` on Base. Done in W4a. It removes the overlay and cache code, an
   estimated 100+ lines, and closes a silent-gap class.
3. **One read-key type.** `Parallel/Reads.lean`'s abstract `Key` and its `Faithful`/`Deterministic`
   hypotheses are replaced by `ReadKey` and the `Prog` theorems, done in W1. The recorder's kinds
   are the same enumeration.
4. **The stack build's proof extraction** (W4b) is a mode of the existing root check, not a new
   trie store.

Estimated net: W1–W3 add about 1,500 Lean and about 600 C/glue lines. The offsets above recover
several hundred. The rest is the feature's cost and is stated in each stage's commit.

## 7. Open questions (for the owner)

1. Is the Baochip target RV32 with how much SRAM/PSRAM? This decides whether large-swap witnesses
   (~0.5 MB of code) must stream from flash (supported: the witness is borrowed and read in place).
2. Should the light client (sync committee) live in the core or in the wallet project? Proposal:
   in the wallet. The core takes a trusted header hash.
3. Should `txProg` be *the* spec run, so that `Tx.run := (txProg c).run (oracleOf s)`, which leaves
   one owner and the spec read through an oracle? Or should it stay a refinement of `Tx.run`? The
   first is cleaner and is a larger diff in the spec.
4. Should the coinbase fee credit be a **delta** (`Reads.lean`)? Then the coinbase need not be in a
   tx witness unless it is read, which shrinks every wallet witness by one proof. The cost is
   reporting the coinbase's diff as "+δ", not an absolute balance.
5. Should EIP-7864 / Verkle (EIP-6800) or the binary-trie transition be planned for? `Pool`/`lookup`
   is the only trie-specific part. A binary-trie `lookup` with its own soundness theorem slots in
   beside it, and `Prog`, the executor and the C API are unchanged.
6. Does Arc/OP need anything beyond the header's `stateRoot`? Arc's native-USDC precompile state is
   ordinary storage, so it should not.

## Sources

- EIP-1186 (`eth_getProof`): https://eips.ethereum.org/EIPS/eip-1186
- reth debug namespace (`debug_executionWitness`): https://reth.rs/jsonrpc/debug
- Alchemy `debug_executionWitness` (Base): https://www.alchemy.com/docs/chains/base/base-api-endpoints/debug-execution-witness.md
- QuickNode Ethereum Reth/Erigon upgrade, July 2026 ("incomplete witness data" fix): https://status.quicknode.com/incidents/9rxc70tnymdn
- Witness struct with headers/codes/state (geth `core/stateless`, fork mirror): https://pkg.go.dev/github.com/tenderly/net-xlayer/core/stateless
- EIP-6800 (Verkle state tree): https://eips.ethereum.org/EIPS/eip-6800
