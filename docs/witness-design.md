# Read sets and state witnesses: a Lean-specified, C-callable interface (design)

Status: design, 2026-11-13. Nothing here is built. Owner direction (2026-11-13): the read set of a
transaction or a block is a first-class concept for Eita's users, and the open core exposes it,
together with **state witnesses**, through a C interface specified in Lean, for stateless
re-execution. The first consumer is the RISC-V / Baochip light client: a hardware-wallet-class
device that simulates a transaction on-chip before signing. It replays a transaction only when it
holds all of the transaction's inputs, and a missing input must fail hard.

The device (owner, 2026-11-13) is Baochip "dabao": RV32 (RV32IMC per the owner; the published
Baochip-1x core is a 350 MHz VexRiscv RV32-IMAC), 2 MiB SRAM, 4 MiB ReRAM (non-volatile, like
flash), attached to a host machine over USB (the chip has a USB 2.0 high-speed device port) or
Bluetooth. The simulation runs **interactively during signing**: the chip runs the executor and
asks the host for state as it goes (§3). A pre-built witness is the secondary mode, for tests,
offline replays and other users of the core.

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
   (`Parallel/Reads.lean`) and the witness. One lookup algorithm handles every proof source. One
   executor serves the chip and the companion host.
7. **Interactive on the device, the host only fetches.** The chip runs the executor, and on each
   state read it asks the host for that key's proof nodes. It verifies every answer against the
   trusted root before using it. The host is untrusted: any RPC provider can sit behind it, and it
   only fetches and forwards. The chip's read set is then exactly the set of keys it asked for
   (`Prog.asked`, theorem (c)), so the device needs no access-list prediction. Paths A and B (§4)
   run on the host to prefetch and cache, which cuts round trips but never decides a value.

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

There are two device modes, and both run the same program `p`:

- **One-shot** (`runP`): every answer comes from a pre-built `PartialState`. This mode is for
  tests, offline replays and other users of the core.
- **Interactive** (`runI`, the device's primary mode): each `ask` goes to the host, and the
  device's verifier `ver` checks the answer against the trusted root before it is used.

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
spike `OracleProg.lean` (Lean v4.35.0, about 90 lines with `runI_sound` below):

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

The interactive mode has its own theorem, also proved in the spike. The host's answer may depend on
the whole history of queries, which models an adaptive and malicious host:

```lean
def runI (ver : List Q → (q : Q) → Option (A q)) (hist : List Q) : Prog Q A α → Except Q α
def ConsistentI ver o : Prop := ∀ h q v, ver h q = some v → v = o q    -- (a), per answer
theorem runI_sound (hc : ConsistentI ver o) : p.runI ver hist = .ok a → p.run o = a
```

**Whatever the host sends, a completed interactive run is the full run.** The proof needs only that
each answer the device accepts passes verification. The order of answers, how they are batched,
when they arrive and which answers are withheld all affect liveness and nothing else.

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

This is the theorem the C interface is pinned to (§3.8). It does not mention the recorder.
`interactive_sound` is the same statement with `runI` and the device's verifier in place of
`runP`.

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

## 3. The device and the C interface

### 3.1 Two modes, one executor

| mode | who answers a read | a missing read | used for |
|---|---|---|---|
| **interactive** (primary on the device) | the host, per request or batch; the chip verifies each answer against the trusted root | a request to the host; terminal only on timeout, refusal or a failed proof | signing on the Baochip |
| **one-shot** (secondary) | a pre-built witness (`Witness`, §1.2) | terminal `EITA_WX_MISSING`, with the exact key | tests, offline replays, the host's own probe runs, other users of the core |

Both modes run the same executor (`txProg`). Only the oracle behind the read seam differs: a pool of
nodes the device holds (one-shot) or a pool that grows from the host's answers (interactive). The
lookup (`walk`, §1.3) is the same code in both. The theorems are `runP_*` for one-shot and
`runI_sound` for interactive (§2.3).

### 3.2 Wire protocol (interactive mode)

Messages are RLP lists, so the chip keeps its one parser, framed on the transport: USB bulk
endpoints, or a BLE L2CAP channel / GATT characteristic with fragmentation in the transport layer.
A message is at most 64 KiB, and a sender splits anything larger.

**Chip → host**

| message | fields |
|---|---|
| `HELLO` | `[ver=1, chainId, trustedNumber, trustedHash, maxMsg, cacheHint]` |
| `GET` | `[reqId, trustedHash, [key, …]]`, at most 32 keys. Each key is one of: `[ACCOUNT, addr]` (the leaf, plus the code if its hash is not cached), `[STORAGE, addr, slot]`, `[CODE, codeHash]`, `[NODE, hash]` (after an eviction, or for a post-root sibling), `[HEADER, number]` (BLOCKHASH) |
| `DONE` | `[status, resultDigest]`, informational: the host can show progress |

**Host → chip**

| message | fields |
|---|---|
| `SESSION` | `[headerRlp, txRlp, env]`. The chip checks `keccak(headerRlp)` against the hash it trusts (§4.3), takes `stateRoot`, and derives the block environment from the header and its own chain config |
| `ANSWER` | `[reqId, [item, …]]`, one item per key: `[key, [nodeRlp, …], code?]`. Only nodes not yet sent in this session are included. **There is no value field**: the chip reads the value out of the verified leaf. Alternatively `[key, ERR, reason]` (the provider failed, or the proof window passed) |
| `PUSH` | `[nodes, codes, headers]`, unsolicited prefetch at any time. The chip may drop it. It is verified lazily, on use |
| `ABORT` | `[reason]` |

**Per-key response size.**

- Nodes: an account path is about 9 nodes, and a storage path is 2–8 more. Measured with
  `eth_getProof` on mainnet: USDC's account proof is 9 nodes, 3,847 B; one of its storage proofs is
  7 nodes, 3,054 B.
- A branch node is at most 532 B, so an item is at most about 20 × 532 B ≈ 10.6 KB of nodes.
- Code is up to 24,576 B (EIP-170). Initcode can be up to 49,152 B (EIP-3860).

**Errors and timeouts.**

- Each `GET` has a deadline (default 5 s, enough for a host-side RPC call) and is re-sent once. The
  `reqId` makes duplicate answers harmless.
- An answer that fails verification is discarded, and the key is requested once more. A host on
  the wrong block is the likely cause. If it fails again the run ends with `EITA_WX_BAD_PROOF`. A
  host can delay the chip this way but can never make it accept a value.
- A whole simulation has a budget (default 30 s). Past it, the chip reports "cannot simulate", and
  the wallet must not sign blind.
- Proof windows are short. A public endpoint refused `eth_getProof` a few blocks behind its head
  ("distance to target block exceeds maximum proof window", publicnode, 2026-11-13). The host
  fetches at the trusted block promptly. If the window closes, the session restarts on a newer
  trusted header.

**Batching and prefetch** turn per-read round trips into roughly one:

1. On `SESSION`, the host runs the *same* executor in probe mode (§3.4) against its RPC provider,
   at the same block. Its inputs are `eth_createAccessList`, then one batched round of
   `eth_getProof`/`eth_getCode`, and the probe loop. It then `PUSH`es the whole predicted witness.
2. Without prefetch the chip still works, with one round trip per new key. A `GET` that names an
   account also brings its code, and the chip asks for every independent key it already knows
   about, such as an access list's slots.

### 3.3 What lives where (2 MiB SRAM, 4 MiB ReRAM)

| memory | contents | size |
|---|---|---|
| ReRAM | executor firmware: handlers, effect layer, RLP/trie, keccak, secp256k1 (small tables); BN254/BLS12-381/KZG precompiles out of the chip build (a call to one is `UNSUPPORTED`) | est. 0.4–0.8 MiB |
| ReRAM | trust state (§4.3): seeded checkpoint, current and next sync committee (2 × ~24.6 KB), latest verified period header, in A/B slots; the vendor key is in read-only key storage | ~100 KB, one commit per 27.3 h period |
| ReRAM | chain config: chain id, fork schedule | < 4 KB, rarely written |
| ReRAM | code cache keyed by code hash (USDC, routers, Aave pools recur) | 1–2 MiB, LRU |
| SRAM | executor state: frames, the stack (32 B per *used* slot), memory (gas-bounded), the overlay of writes | typical wallet tx < 100 KB; capped by the arena |
| SRAM | verified values: accounts ~120 B, slots ~96 B | Aave supply: 24 + 51 keys ≈ 8 KB |
| SRAM | node cache with eviction: the account trie's top two levels pinned (17 nodes ≈ 9 KB, shared by every account proof), the rest LRU | 256 KB |
| SRAM | code being run (copied from ReRAM or straight from the answer) | up to the tx's code, measured ≤ 223 KB |
| SRAM | I/O buffers | 2 × 64 KiB |

A typical wallet tx needs about 0.4–0.8 MiB of SRAM, which fits in 2 MiB with room to spare. The
firmware runs from ReRAM; if it cannot execute in place, part of it must be copied into SRAM, which
tightens the budget (open question 1).

**Wear.** ReRAM write endurance is not published for this part. Embedded RRAM is typically rated
10⁴–10⁶ cycles, so the design assumes 10⁴. Writes are therefore rare and spread out:

- the trust state uses A/B slots, with one commit per sync period (≈ 3,200 writes per cell over 20 years, §4.3.2);
- a code is cached only when it is seen a second time (most codes recur);
- the cache never rewrites an entry in place.

At 1 MiB of code churn per day over a 2 MiB cache, each cell is written about every second day, so
10⁴ cycles last for decades. Nothing per-read and nothing per-session goes to ReRAM.

### 3.4 C API

There are no globals and no `malloc`. All working memory comes from one caller-provided arena, and
exhausting it is an explicit status. Builds target RV32IMC, RV64 and the hosts.

```c
typedef struct { const uint8_t *ptr; uint32_t len; } eita_buf;      /* borrowed */

typedef enum {
  EITA_WX_OK = 0,
  EITA_WX_MISSING,      /* one-shot only: the witness lacks a read (exact key in eita_wx_miss) */
  EITA_WX_IO,           /* interactive: the host timed out, refused (ERR) or aborted */
  EITA_WX_BAD_PROOF,    /* interactive: an answer failed verification twice */
  EITA_WX_MALFORMED,    /* bytes do not parse */
  EITA_WX_HEADER_CHAIN, /* the header is not the trusted one / ancestors do not hash-chain */
  EITA_WX_ENOMEM,       /* arena exhausted: cannot simulate (never reported as out-of-gas) */
  EITA_WX_UNSUPPORTED,  /* a fork, tx type or precompile outside this build */
  EITA_WX_INVALID_TX    /* the spec's validity rules reject the tx (reason in the result) */
} eita_wx_status;

typedef struct {        /* the exact read: a GET key, or the one-shot mode's missing key */
  uint8_t kind;         /* EITA_RK_{ACCOUNT,STORAGE,CODE,NODE,HEADER} */
  uint8_t addr[20]; uint8_t slot[32]; uint8_t hash[32]; uint64_t number;
} eita_wx_key;

typedef struct {        /* the device's trust inputs, never the host's */
  uint8_t  trusted_hash[32];   /* from the light client or a pinned checkpoint (§4.3) */
  uint64_t chain_id;
  const struct eita_fork_schedule *forks;
} eita_wx_trust;

typedef struct {        /* the transport (USB/BLE), supplied by the firmware */
  void *ctx;
  /* send one message, wait for the reply to it (or a PUSH) up to timeout_ms */
  int (*exchange)(void *ctx, eita_buf msg, uint8_t *reply, uint32_t cap, uint32_t *len, uint32_t timeout_ms);
} eita_wx_io;

typedef struct eita_wx eita_wx;  /* opaque, at the start of the arena */

/* Interactive: a session bound to one trusted header. The arena holds the node cache, the verified
   values, the overlay and the executor; nothing of the witness is held beyond the cache. */
eita_wx_status eita_wx_session(void *arena, uint32_t arena_len, const eita_wx_trust *trust,
                               const eita_wx_io *io, eita_buf header_rlp, eita_wx **out);
/* One-shot: the same object over a borrowed pre-built witness (debug_executionWitness shape, §5). */
eita_wx_status eita_wx_open(void *arena, uint32_t arena_len, const eita_wx_trust *trust,
                            eita_buf witness, eita_wx **out);
eita_wx_status eita_wx_extend(eita_wx *wx, eita_buf more);           /* one-shot: append data */

/* Point reads, verified (an eth_getProof verifier in one call). */
eita_wx_status eita_wx_account(eita_wx *wx, const uint8_t addr[20], eita_wx_account *out, eita_wx_key *k);
eita_wx_status eita_wx_storage(eita_wx *wx, const uint8_t addr[20], const uint8_t slot[32],
                               uint8_t value[32], eita_wx_key *k);

/* Execute (either mode). The env is derived from the trusted header: the next block's number,
   base fee by the emitted EIP-1559 formula, the caller's timestamp. */
eita_wx_status eita_wx_env_next(eita_wx *wx, uint64_t timestamp, const uint8_t coinbase[20], eita_wx_env *env);
eita_wx_status eita_wx_run_tx(eita_wx *wx, const eita_wx_env *env, eita_buf signed_tx, uint32_t flags,
                              eita_wx_tx_result *res, eita_wx_key *k);   /* flags: EITA_WX_PROBE (host only) */
eita_wx_status eita_wx_run_block(eita_wx *wx, eita_buf block_rlp, eita_wx_block_result *res, eita_wx_key *k);

/* Results: gas, status, logs (views into the arena, valid until reset); the diff (accounts with
   pre/post fields, slots with pre/post, wiped storages); the receipt; the read set asked. */
int            eita_wx_diff_next(eita_wx *wx, eita_wx_diff_iter *it, eita_wx_diff_entry *e);
eita_wx_status eita_wx_receipt(eita_wx *wx, uint32_t tx_index, uint8_t *out, uint32_t cap, uint32_t *len);
eita_wx_status eita_wx_post_root(eita_wx *wx, uint8_t root[32], eita_wx_key *k);
int            eita_wx_reads_next(eita_wx *wx, eita_wx_reads_iter *it, eita_wx_key *k);
void           eita_wx_reset(eita_wx *wx);  /* drop the overlay and results, keep the cache */
```

`eita_wx_session` is bound to one trusted root, and every answer is checked against it. In
interactive mode a missing read is not a status: the executor calls `io->exchange` with a `GET`,
verifies the `ANSWER`, and continues. It suspends inside the read seam on the firmware's stack, so
the executor needs no restartable state machine. **Probe mode** (`EITA_WX_PROBE`) is for the host:
it answers a missing read with zero or empty, records the key and continues. The result is
discarded, and only the recorded keys are used, as prefetch predictions. The chip build compiles
probe mode out.

### 3.5 RV32 implications

- **256-bit words on 32-bit limbs.**
  - The core's limb primitives (`c/generated/limb_ops.h`, printed from `Evm.CL.LimbC`) are four
    64-bit limbs. On RV32 a word is eight 32-bit limbs.
  - Carries come from `sltu`. `mul`/`mulhu` (M extension) give 32×32→64, so MUL is 64 partial
    products and MULMOD/EXP are the cost centres.
  - There are two derived routes:
    - a 32-bit `LimbC` printing, proved like the 64-bit one;
    - the RV32 lowering of AsmCore, the third backend after ARM64 and x86-64 (new-ideas item 4).

    The C route comes first, because it is portable and checkable with CBMC.
- **Keccak in software.**
  - IMC has no rotate instruction (Zbb), so lanes are bit-interleaved 32-bit halves, as in XKCP's
    32-bit implementations.
  - Estimate: about 20k cycles per Keccak-f[1600], i.e. per 136 bytes. Verifying the largest
    measured tx (Aave, 360 KB of nodes and code) is about 2,650 permutations ≈ 53 M cycles ≈ 0.15 s
    at 350 MHz.
  - If the Baochip's hash accelerators cover Keccak, the cost becomes negligible. The published
    material says only "a variety of cryptographic accelerators" (open question 1).
- **secp256k1** (ECRECOVER in permits): libsecp256k1's 10×26 field arithmetic runs on 32-bit, at an
  estimated tens of ms per recovery at 350 MHz.
- **Interpreter.** On RV32 the handlers are C at first, not the JIT. A wallet tx is about 50–300k
  gas. At an estimated 100–300 cycles per opcode, that is 10–50 ms.
- **Code size.** An estimated 0.4–0.8 MiB in ReRAM (§3.3), to be measured in W5. The pairing and
  KZG precompiles are left out of the chip build.

### 3.6 Budget, from measured read sets

**Read sets, real (keys per tx).**

1. *Ethereum*, recorder output (branch `readset`): mainnet block 24,538,111, 756 txs, from the
   core's repro fixture, run locally with the recorder on. Accounts include the sender, the
   recipient and the coinbase, and the codes column counts code reads.

   | class (n) | accounts p50/p90/max | slots p50/p90/max | codes p50/p90/max | code bytes p50/p90/max |
   |---|---|---|---|---|
   | ETH transfer (305) | 3/3/3 | 0/0/0 | 2/2/2 (empty) | 0/0/23 |
   | ERC-20 transfer (308) | 3/4/6 | 7/7/11 | 2/3/5 | 11.1K/25.7K/27.0K |
   | ERC-20 approve (8) | 4/4/4 | 2/4/4 | 3/3/3 | 18.2K/25.7K/25.7K |
   | Uniswap router (3) | 7/10/10 | 16/25/25 | 6/9/9 | 45.2K/91.9K/91.9K |
   | other (132) | 6/15/85 | 9/46/483 | 5/15/84 | 29.4K/136K/304K |
   | all (756) | 3/5/85 | 2/8/483 | 2/4/84 | 10.6K/25.7K/304K |

2. *Arc*, the re-replay's read sets on x300 (`/data/eita/arc-rr/readset`, blocks 1–1,392,640, 986
   user txs; Arc's early chain is light): accounts p50/p90/p99/max 4/7/13/67, slots 4/7/22/243,
   codes 3/5/11/65.

3. *Witness bytes, real (path B on a public endpoint).* `eth_createAccessList` + `eth_getProof` +
   `eth_getCode` at Ethereum head (blocks 26,404,614–26,404,624) via ethereum-rpc.publicnode.com,
   with nodes de-duplicated per tx. The access list omits the coinbase and precompiles, so the key
   counts are a little under the recorder's.

   | class (n) | accounts | slots | nodes | node bytes | code bytes | total |
   |---|---|---|---|---|---|---|
   | ETH transfer (5) | 2 | 0 | 16–17 | 6.6–7.3 KB | 0 | ~7 KB |
   | ERC-20 transfer (6) | 2–3 | 2–7 | 24–60 | 9.4–24.9 KB | 3.3–25.7 KB | 13–51 KB |
   | Uniswap Universal Router (9) | 3–8 (p50 5) | 1–19 (p50 7) | 34–155 | 13.7–61.2 KB (p50 26) | 28.7–87.8 KB (p50 53) | 42–149 KB (p50 ~79) |
   | Aave v3 Pool (2) | 12, 24 | 21, 51 | 188, 382 | 71, 137 KB | 87, 223 KB | 158, 360 KB |
   | other contract calls (13) | 2–8 (p50 3) | 1–17 (p50 6) | 21–143 | 8.6–56 KB (p50 20) | 5.7–79 KB (p50 24) | — |

   The rule of thumb that falls out:
   - An account proof is about 8 nodes ≈ 3.3 KB once the root is shared.
   - Each further slot in a known account adds about 5 nodes ≈ 1.8 KB.
   - Code is half or more of the bytes; a warm code cache removes it.

   The provider latencies measured on the same runs were `eth_getProof` 67–157 ms (avg ≈ 80 ms) and
   `eth_createAccessList` 57–125 ms.

**Transport.**

| link | effective throughput | per round trip |
|---|---|---|
| USB 2.0 high speed (the Baochip's port) | assume ≥ 10 MB/s for an MCU bulk stack (480 Mbit/s raw) | ~1 ms |
| USB full speed (fallback) | ~1 MB/s | ~1–2 ms (1 ms frames) |
| BLE, phone host | iOS ≈ 50–60 kB/s, Android ≈ 140 kB/s at a 15 ms interval, 2M PHY (measured, Silicon Labs BGX13 table) | ≥ 2 connection intervals ≈ 30–60 ms; 15 ms is iOS's minimum interval (Punch Through) |

**Round trips per tx.**

- Without prefetch, about one per new key (accounts + slots; code rides with its account):
  - ETH transfer 2–3;
  - ERC-20 transfer about 4–10;
  - swap about 8–27;
  - Aave about 33–75.
- With the host's probe-run prefetch, about 1 (one `PUSH`) plus rare misses.

**Simulation time during signing** (cold code cache; warm removes the code bytes):

| tx | bytes | USB HS | BLE iOS | chip compute |
|---|---|---|---|---|
| ETH transfer | ~7 KB | < 1 ms | ~0.15 s | < 10 ms |
| ERC-20 transfer | ~27 KB (p50) | ~3 ms | ~0.5 s | ~15 ms |
| Uniswap swap | ~79 KB (p50), 149 KB max | ~8–15 ms | ~1.4–2.7 s | ~50 ms |
| Aave supply/borrow | 158–360 KB | ~16–36 ms | ~2.9–6.5 s (warm: 1.3–2.5 s) | ~0.1–0.3 s |

Add to that the host's prefetch: one access-list call, one batched proof round and 0–1 probe-loop
rounds, about 0.2–0.5 s against a hosted provider (measured latencies above). Over BLE without
prefetch, add rounds × 30–60 ms (Aave: 2–4.5 s). The result:

- **USB: under one second for every class measured.**
- **BLE: a few seconds** for DeFi txs. The code cache is what makes repeat DeFi interactions fast.

All of this is well inside 2 MiB of SRAM (§3.3).

### 3.7 What is derived and what is glue

| part | source | checked by |
|---|---|---|
| opcode handlers, gas formulas, fork tables | emitted from Lean (existing; on RV32 as C over the 32-bit `LimbC`, later the RV32 AsmCore lowering) | existing emit drift checks, AsmCore proofs for a lowering |
| effect layer: CALL, CREATE, SSTORE, SLOAD, settle, end-of-tx, tx | effect IR → **C** printer (`Evm.CL.EffectC`, today SLOAD/SSTORE only; extend to every term) | `Effect*Proof` (spec refinement), printer trusted like `toCL` |
| read seam: overlay, then `lookup`; the one-shot pool or the interactive request | **emitted**: `walk`/`lookup` are first-order and total, printed to C like `LimbC` | `lookup_*_sound`, `runI_sound`, CBMC on the printed C (bounds, no OOB on adversarial bytes) |
| RLP decode, hex-prefix | emitted from the totalized `Rlp.decodeAt` (W0) | round-trip theorem, CBMC |
| keccak | `lean/c/keccak.c` (existing, trusted; a 32-bit interleaved variant for RV32) | test vectors (trusted surface) |
| ecrecover | libsecp256k1 (existing, trusted) | fixtures |
| arena, node cache, protocol codec, header parsing, API marshalling | hand-written glue (~600 lines) | CBMC harness (`c/cbmc/` pattern), property tests vs the Lean reference, a fuzzing host (random reorderings, drops, forged nodes) |

The native accounts plus CALL/CREATE in C is the same work as the "all-C core" the RISC-V port
needs (new-ideas item 5). The read seam is that core's world view, and it does not add a second
core.

### 3.8 Pinning

`lean/Comparator/Challenge.lean` gains, with owner review, `lookup_found_sound`,
`lookup_absent_sound`, `runP_sound`, `runP_missing`, `runI_sound`, `txProg_refines`,
`stateless_sound` and `interactive_sound`. The standard axioms suffice: keccak appears as an opaque
constant inside `Collision`, not as an axiom.

The C side is pinned to the same terms:

- The printed C is byte-checked against the emitter, like `storage_effect.c`.
- The property test runs the C and `Prog.runP`/`runI` in Lean on the same witnesses and on the same
  scripted hosts (random pools, truncated pools, flipped bytes, reordered and withheld answers). It
  requires identical statuses and results.
- Conformance comes from the BlockchainTests battery run statelessly: the fixture's pre-state
  serves as the host, and the result must match the fixture's post-state.

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

On the device this path is a **host-side prefetch** for interactive mode (§3.2): it predicts and
pushes the witness, and the chip still asks for anything it lacks. On its own it also builds a
one-shot witness. It runs on the host, at a fixed block `N` (the trusted header's):

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

**Where it runs.** The loop runs on the host (phone or PC), which is online and runs the *same* C
library in probe and one-shot modes. Measured on a public endpoint, one round is about 60–160 ms
per call (§3.6). In interactive mode the chip is the final judge: it runs strictly, asks for what
the prefetch missed, verifies every answer, and on `IO`, `BAD_PROOF` or `ENOMEM` it refuses to show
a simulation. So the host cannot make the chip trust a result the chip did not compute.

### 4.3 Device trust model

**The host is a courier.** It can make the device say "cannot simulate now" or "this is from an
older block". It cannot make the device show a false outcome. The rest of this section is what that
sentence requires.

#### 4.3.1 The root must not come from the host

Proof soundness (`lookup_*_sound`) is relative to the root. A malicious host can build a fake
state, compute its root and serve perfectly valid proofs against it. The chip would then faithfully
simulate a state that does not exist and show a false outcome: "you receive 1,000 USDC" when the
contract actually drains the wallet.

The signed bytes are never at risk: the device shows the tx fields and signs exactly those. But the
simulation exists to defend against a compromised host or dapp, and a simulation whose root the
host chooses defends against nothing.

- **v1** may take the root from the host only if the device says so plainly on its own display:
  "simulation trusts the connected computer".
- **v2** takes it from an on-device light client (below). `stateless_sound` and `interactive_sound`
  are theorems about a root the device already trusts. They never vouch for the root.

#### 4.3.2 The Ethereum light client on the device

The device follows the beacon chain's **sync committee**: 512 validators, rotated every 256 epochs
(8,192 slots × 12 s ≈ 27.3 h).

- **Per period.** A `LightClientUpdate` carries the next committee's 512 BLS keys and its SSZ
  Merkle branch to the attested beacon state. It is signed with the *current* committee's aggregate
  signature, with participation ≥ 2/3 of 512. The device verifies it against the committee it
  stores:
  1. aggregate the participants' G1 keys (≥ 342 point additions);
  2. one pairing check, with blst (already vendored);
  3. SHA-256 for the SSZ branch and the committee root.
- **Per simulation.** A finality or optimistic update for a recent header, signed by the current
  committee, plus the `execution_branch` (Capella and later) from the beacon block body to the
  execution payload header gives `state_root`, `block_hash`, `block_number` and `timestamp`. That
  `state_root` is the session's trusted root. A verified header is cached in SRAM for the session
  only.
- **ReRAM state.** The current and next committees (512 × 48 B + 48 B aggregate ≈ 24.6 KB each)
  and the latest verified period header, in **A/B slots**. A write goes to the inactive slot, then a
  versioned commit marker (with a CRC) flips the active slot, so an interrupted write never corrupts
  the state. Total about 100 KB.
- **Wear.**
  - Writes are about one per period, i.e. about one per day. Per-session headers stay in SRAM.
  - Over a 20-year device life that is 20 × 365 × 24 / 27.3 ≈ 6,400 commits. Split across the A/B
    slots, that is about 3,200 writes per cell, a third of a pessimistic 10⁴-cycle endurance.
  - With four rotating slots it is about 1,600 per cell.
- **Catch-up after a gap.** The device applies one update per missed period, in order: a month is
  ≈ 27 updates, a year ≈ 321. The cost is one BLS aggregate verify each.
  - Estimate: the 342-point G1 aggregation is small next to the pairing check, which is roughly
    0.3–1 s on a 350 MHz RV32 without a big-number engine.
  - That gives about 10–30 s per month of gap and about 2–5 min per year.
  - This is to be measured in W5. If the Baochip's accelerators include a big-number engine, it
    shrinks.
  - A per-simulation header costs one more verify; a cached session header avoids repeating it.

#### 4.3.3 Seeding: the root of trust

At the vendor, in a trusted environment:

- a **vendor public key** goes into read-only storage (the Baochip has protected key slots);
- the **initial checkpoint** goes into ReRAM: a finalized beacon block root, its sync committee and
  the chain config.

Everything later arrives through the untrusted host and is accepted only if it is consistent with
what ReRAM holds:

- a committee update is accepted only if the stored committee signed it;
- a checkpoint is accepted only if the vendor key signed it;
- firmware is accepted only if the vendor key signed it (§4.3.6).

#### 4.3.4 The staleness limit (long-range attacks)

Sync-committee signatures are not slashable, and the validators of an old committee may have exited
long ago. Their keys could sign an alternative history at no cost, so the further the stored
committee lags, the less its signature on a "next committee" is worth.

The device therefore keeps a **staleness limit**. If the stored committee is older than the limit,
it refuses to fast-forward and requires a fresh checkpoint. The limit is derived from the consensus
specs' weak-subjectivity period (`compute_weak_subjectivity_period`, a function of the validator
count, the balance-based churn and `MIN_VALIDATOR_WITHDRAWABILITY_DELAY`) and the sync committee's
27.3 h rotation. It is computed when the device is seeded and stored in the chain config, and it is
on the order of weeks to a few months.

A fresh checkpoint must carry its own proof, from one of two sources:

1. **Vendor-signed checkpoints**, published regularly and relayed by the host. This is the same root
   of trust as firmware updates.
2. **The user confirming a short hash out of band**, for example against several block explorers.
   This is secondary and error-prone.

#### 4.3.5 Freshness

The host can withhold newer updates and show an old but genuine header. The device can detect this
only with a trusted clock: a battery-backed RTC set at the factory (open question 1). So:

- The device **always displays the block number and timestamp** the simulation used.
- With a trusted clock, it refuses state older than a few minutes. At the 12 s slot time, a
  default of 5 minutes is 25 slots.
- Without a clock, staleness is visible to the user but not enforced.

#### 4.3.6 Firmware updates

Firmware arrives through the host too. It must be vendor-signed and verified on the device before
it is installed. The Baochip's one-way counters give the anti-rollback version. Otherwise the chain
of trust is moot, because a malicious host would replace the verifier.

#### 4.3.7 The whole chain

```
vendor public key (read-only)  +  initial checkpoint: finalized root + committee (ReRAM)
  → committee updates, one per 27.3 h period, verified on the device   (BLS, ≥ 2/3 of 512)
  → after a gap beyond the staleness limit: a vendor-signed checkpoint (vendor key)
  → per simulation: a committee-signed header + execution_branch → the execution state_root
  → eth_getProof-style proofs against that state_root, per read      (lookup_*_sound)
  → execution on the device                                          (interactive_sound)
  → the outcome, shown with its block number and timestamp
```

What each party can do:

| party | can | cannot |
|---|---|---|
| host / RPC provider | delay, withhold ("cannot simulate now"), serve an older genuine header (shown as "block N, time T"; refused with a trusted clock) | change a value, a code, a header or the outcome |
| dapp | send any tx | change what the device simulates or displays |
| a past sync committee beyond the staleness limit | — | move the device, which demands a vendor-signed checkpoint |

The assumptions are:

- an honest ≥ 2/3 of the current sync committee within the staleness limit;
- the vendor key;
- Keccak and SHA-256 collision resistance;
- the BLS and Ed25519 implementations;
- the spec refinement (`txProg_refines`).

#### 4.3.8 Arc

The structure is the same, with Arc's consensus in place of the sync committee. Read from
`~/arc-node`, commit 6e76402:

- **Consensus.** Malachite BFT. Each height has a **commit certificate**: height, round,
  `block_hash` (the `ValueId`), and Ed25519 precommit signatures from validators, 64 B each
  (`crates/types/src/commit_http.rs`). It is valid when the signers hold a quorum of voting power
  (Malachite `verify_commit_certificate` with `ThresholdParams`). It is served by consensus
  `GET /commit?height=…` and by the JSON-RPC method `arc_getCertificate`
  (`crates/evm-node/src/rpc/get_certificate.rs`). Finality is per block, with no separate finality
  gadget.
- **Validator-set changes are in EVM state.** The signing set for height H is the result of
  `getActiveValidatorSet()` on the `ValidatorRegistry` proxy `0x3600…0002`, evaluated on the state
  of block H−1 (`get_signing_validator_set`: `block_height = consensus_height − 1`;
  `abi_decode_validator_set`). Each entry is a status, a public key and a voting power.
- **What the device verifies.** The device holds a trusted (height h₀, validator set S₀). For a new
  header H, the host relays:
  - `arc_getCertificate(H)`;
  - header H and header H−1 (H−1 is checked through `parentHash`);
  - the registry's storage proofs at `stateRoot(H−1)`.

  The device then:
  1. checks that the certificate carries more than 1/3 of S₀'s voting power: the skipping rule, so
     at least one honest signer within the trusting period;
  2. derives set(H) **by running `getActiveValidatorSet()` statelessly** on `stateRoot(H−1)`. This
     is the same executor and the same proofs (`interactive_sound`), so the light client reuses the
     witness machinery;
  3. checks that the certificate has a quorum of set(H)'s voting power;
  4. stores set(H) as the new trusted set when it changed.

  If the set rotated so far that the >1/3 overlap fails, the host supplies intermediate heights
  (bisection).
- **Costs.**
  - Ed25519 verify is an estimated ~1–3 M cycles on RV32; measured in W5.
  - Each certificate needs one verify per signer, so a set of a few tens of validators costs well
    under a second.
  - The stored set is small: keys and powers, a few KB, in the same A/B slots.
- **Staleness and seeding** are as for Ethereum: a vendor-signed (height, set) checkpoint at the
  factory and after long gaps. The trusting period is derived from Arc's unbonding and governance
  rules for the permissioned validator manager. Its value is open (§7).
- **Provider requirement.** `arc_getCertificate` is an Arc-node method, not standard Ethereum
  JSON-RPC, so the host needs an Arc RPC that exposes it (or the consensus HTTP `/commit`).

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

**One-shot binary:** an RLP list `[version=1, trustedHash, headers, nodes, codes, keys, ext]`. It is
used by tests, offline replays and other users of the core. RLP is used because the executor must
parse RLP for nodes, headers and txs anyway, which keeps one parser and no new framing. Order inside
a section is free, because the index sorts by hash.

**Interactive:** the wire protocol of §3.2 carries the same pieces: nodes, codes and headers inside
`ANSWER`/`PUSH`. A host can therefore feed a `debug_executionWitness` response to the chip as one
`PUSH`.

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
| **W3** | C: `lookup`/RLP printed from Lean, glue + arena + node cache, `eita_wx_*` (session and one-shot), the wire protocol codec; CBMC harness; property tests vs Lean with scripted adversarial hosts; stateless BlockchainTests on host | 4–5 wk | W1; effect IR → C for the remaining terms (all-C core) |
| **W4a** | the host program: the protocol's host side, path B prefetch (access list + getProof + probe loop) against two hosted providers and one public endpoint, path A ingestion, PUSH | 2 wk | W3 |
| **W4b** | path C: stack-build proof extraction at anchors; recorder read sets → witnesses | 2 wk | `readset` branch merged |
| **W5** | RV32IMC build (32-bit `LimbC`, interleaved keccak), on the dabao: code size in ReRAM, SRAM high-water, cycles per class (§3.6 classes), USB HS and BLE timings; ReRAM code cache; the on-device light client (§4.3: sync-committee updates with BLS aggregate verify, A/B trust slots, staleness limit, vendor-signed checkpoints and firmware; Arc certificates with Ed25519 and the stateless validator-set call), with BLS and Ed25519 verify timed | 5–8 wk | all-C core; the dabao board |
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
3. Device fit. The firmware size and whether it runs in place from ReRAM are estimates
   (0.4–0.8 MiB), and the cycles per Keccak and per opcode on the VexRiscv are unmeasured. W5
   measures all of them. A tx that exceeds the arena is `ENOMEM` ("cannot simulate"), never a wrong
   answer.
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

1. *(Answered 2026-11-13: dabao, RV32IMC, 2 MiB SRAM + 4 MiB ReRAM, USB/BLE to a host,
   interactive during signing.)* Still open about the part:
   - Can firmware execute in place from ReRAM?
   - Do the "cryptographic accelerators" include Keccak (which would remove ~0.15 s on the largest
     tx) or a big-number engine (for secp256k1)?
   - Is the core IMC or IMAC (the published core is IMAC; atomics are not needed)?
   - What is ReRAM's rated write endurance?
   - Is BLE a separate radio module, and what is its link layer?
   - Is there a battery-backed RTC that can be set at the factory? Freshness enforcement needs it
     (§4.3.5).
   - Which read-only key slot holds the vendor key?
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

7. What is Arc's trusting period for the skipping rule (§4.3.8)? It follows from how fast the
   permissioned validator manager can rotate keys and from what a removed validator risks.
8. Should v1 ship with the root taken from the host, which requires the plain on-device warning of
   §4.3.1, or should signing-time simulation wait for the light client (v2)?

## Sources

- Ethereum light client (sync protocol, LightClientUpdate, execution_branch): https://github.com/ethereum/consensus-specs/blob/dev/specs/altair/light-client/sync-protocol.md ; weak subjectivity: https://github.com/ethereum/consensus-specs/blob/dev/specs/phase0/weak-subjectivity.md

- Baochip-1x (bunnie, 2026): https://www.bunniestudios.com/blog/2026/baochip-1x-a-mostly-open-22nm-soc-for-high-assurance-applications/ ; dabao board (USB 2.0 high-speed device, RV32-IMAC 350 MHz): https://www.cnx-software.com/2026/03/04/dabao-board-features-open-source-hardware-baochip-1x-risc-v-mcu/
- BLE throughput on phones (iOS 15 ms minimum interval, ~50 % airtime): https://punchthrough.com/ble-throughput-optimization-faq/ ; measured iOS/Android rates at 15 ms, 2M PHY: https://docs.silabs.com/gecko-os/1/bgx/1.x/throughput

- EIP-1186 (`eth_getProof`): https://eips.ethereum.org/EIPS/eip-1186
- reth debug namespace (`debug_executionWitness`): https://reth.rs/jsonrpc/debug
- Alchemy `debug_executionWitness` (Base): https://www.alchemy.com/docs/chains/base/base-api-endpoints/debug-execution-witness.md
- QuickNode Ethereum Reth/Erigon upgrade, July 2026 ("incomplete witness data" fix): https://status.quicknode.com/incidents/9rxc70tnymdn
- Witness struct with headers/codes/state (geth `core/stateless`, fork mirror): https://pkg.go.dev/github.com/tenderly/net-xlayer/core/stateless
- EIP-6800 (Verkle state tree): https://eips.ethereum.org/EIPS/eip-6800
