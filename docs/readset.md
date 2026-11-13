# Read sets: the definition

A **read set** of an execution (one transaction, a system call, or a whole block) is a set of
pre-state keys whose values the execution observed, such that **changing any value outside the
set cannot change the result**: the gas used, the status, the logs and the state diff. Its
companion is the **write set**: the keys whose values the execution changed (the keys of its
diff), and for credits, the keys it added to without reading them (below).

One owner: the definition is in Lean, `lean/Evm/Witness/ReadSet.lean`. The recorder
(`src/evm/readset.lisp`, on-disk format in [`readset-format.md`](readset-format.md)) implements
it for replays. The witness design ([`witness-design.md`](witness-design.md)) builds stateless
execution on it. Neither keeps a second definition.

## The Lean definitions

```lean
inductive ReadKey where
  | exists_ (a : Address) | nonce (a : Address) | balance (a : Address)
  | codeHash (a : Address) | code (a : Address)
  | storage (a : Address) (slot : U256) | blockHash (n : Nat)
abbrev ReadSet := List ReadKey                  -- membership only; order and duplicates mean nothing

def Answer : ReadKey → Type                     -- Bool, Nat, U256, Bytes, Bytes, U256, Option Hash32
abbrev Oracle := (k : ReadKey) → Answer k        -- a pre-state seen through its keys
def oracleOf (s : Frontier.State) (hashes : Nat → Option Hash32) : Oracle

def AgreeOn (R : ReadSet) (o o' : Oracle) : Prop := ∀ k ∈ R, o k = o' k
def Sufficient (obs : σ → Oracle) (same : β → β → Prop) (run : σ → β) (R : ReadSet) (s : σ) : Prop :=
  ∀ s', AgreeOn R (obs s) (obs s') → same (run s) (run s')
```

`Sufficient` is stated for any execution `run` over pre-states `σ`, with `obs` its view of the
pre-state and `same` the outcome comparison. For the EVM, `σ` is the transaction's pre-state,
`obs` is `oracleOf` with the block-hash window, `run` is a fork's transaction run, and `same` is
`SameOutcome`: equal gas, status and logs, and equal state diffs. A diff and not the post-state,
because two pre-states that differ outside `R` have post-states that differ there too, and the
spec's `State` is a list, so not extensional.

Proved (no `sorry`):

- `AgreeOn.refl / symm / trans`, `AgreeOn.nil` (every pair agrees on the empty set),
  `AgreeOn.mono` (agreement on a superset gives agreement on a subset),
  `AgreeOn.append_iff` (agreement on a union is agreement on both parts).
- `Sufficient.mono`: **a superset of a sufficient read set is sufficient**. This is why an
  over-approximating recorder is safe (a key read after the tx's own write, a whole account where
  one field was needed). `Sufficient.append_left / append_right`: a union with a sufficient set
  is sufficient.
- `Sufficient.nil_iff`: the empty set is sufficient exactly when the outcome is constant.
- `Sufficient.agree` (sufficiency transfers along agreement), `Sufficient.weaken` (a weaker
  outcome relation, e.g. gas only, keeps sufficiency).

Stated, not yet proved (they need the oracle-program executor of witness-design §1.5 and §2.3):

- **The recorder's sets are sufficient.** For the spec, `Sufficient (oracleOf · hashes)
  SameOutcome (Tx.run k c) R s` for the set `R` the executor asks. In the design this is
  `asked_sufficient` (proved generically for every oracle program) composed with `txProg_refines`
  (the obligation that ties the program to the spec's run).
- **Minimality is not claimed.** Any sufficient set is a valid read set. The one an execution
  asks is the natural one, but a value can be read and then not influence the result (a
  comparison whose both branches agree), so the asked set need not be minimal.

## Key kinds

| key | value | read by |
|---|---|---|
| `exists_ a` | is `a` in the state | pre-EIP-161 NEW_ACCOUNT gas, EIP-161 emptiness, CREATE collision |
| `nonce a` | nonce | tx validity, CREATE address, CREATE collision |
| `balance a` | balance | BALANCE, SELFBALANCE, value transfer, fee prepayment |
| `codeHash a` | the leaf's code hash | EXTCODEHASH, emptiness, CREATE collision |
| `code a` | the code bytes | executing `a` (CALL family), EXTCODESIZE, EXTCODECOPY |
| `storage a k` | slot value (0 if absent) | SLOAD, SSTORE (original and current value) |
| `blockHash n` | hash of block `n` (`none` outside the 256-block window) | BLOCKHASH |

Field granularity is kept because Block-STM conflicts and dependency analysis want it (a balance
read does not conflict with a nonce write). A witness covers an account as a whole, since one
account proof yields all four fields: the witness's key set is the read set's projection onto
accounts and slots. The recorder's account mask is these kinds as bits (`readset-format.md`).

## The subtle cases

**Implicit reads.** Reads that no opcode names are still reads, and the recorder lists them
because they all go through the storage view (`src/state/world.lisp`), the effect layer's one path
to world state:
- the sender's balance and nonce at tx start (validity, fee prepayment, nonce increment);
- the callee's existence and emptiness for the new-account charge (pre-161: `exists_`; 161+:
  emptiness, i.e. nonce, balance and code);
- the CREATE / CREATE2 target's nonce, code hash and existence (the address-collision check);
- SSTORE's original value: the slot's value before the tx, read on the tx's first access of the
  slot, so `storage a k` is in the set even when the tx only writes the slot;
- EIP-7702 delegation: reading the delegate's code is a `code` read of the delegate.

**Warm/cold access sets are not pre-state.** The EIP-2929 accessed addresses and slots and the
EIP-2930 access list are transaction-local state, determined by the tx and its own execution.
They are not keys of the pre-state, so they are not in a read set. (They influence gas, but only
through things already in the set or in the tx itself.) Transient storage (EIP-1153) is the same:
it starts empty in every tx.

**Value-blind credits are delta writes without reads.** The coinbase fee credit, block rewards
and withdrawals add an amount to a balance without reading it. They are write-set entries
(deltas), not reads: `lean/Evm/Parallel/Reads.lean` models them as commutative deltas exempt from
validation. But a *read* of a credited key is an ordinary read (BALANCE of the coinbase, a tx
from the coinbase, the EIP-161 emptiness check of a value transfer to it), and it must see every
earlier credit. The recorder marks a credited account as written with no field read (mask 128).

**Per-block work runs as pseudo-transactions.** System calls (EIP-4788 beacon root, EIP-2935
history, a chain's pre-block hooks) run in their own transaction windows, before tx 0 and after
the last tx, with their own read sets (tx index −1 and the post-block index in the format).

**Chain precompiles touching state.** Arc's 0x1800… native-USDC precompiles read and write
balances and their own storage. They go through the same storage view, so their reads are
recorded like any opcode's. A chain hook that bypassed the view would be a recorder bug, not a
new key kind.

**Per-tx vs per-block.** A tx's read set is taken at its true pre-state: the parent state plus
the writes of the earlier txs of the block. Post-Byzantium headers carry no per-tx root, so
proving tx `i`'s reads needs the parent root plus the reads of txs `0..i-1`. A block's read set
is the union of its txs' sets minus the keys an earlier tx wrote (witness-design §2.4). The
recorder lists a key a tx read after an earlier tx wrote it like any other read; that is right
per tx and is subtracted for the block.

## Known gap of the recorder (format v1)

Effects **outside any transaction window** are not recorded: Ethereum's block reward and
withdrawal credits, and a chain's post-block balance deltas. They are value-blind writes with
no read, so no read set is missing a key. But the write side is incomplete: a block-level
witness, and anything that needs the block's full write set (a Block-STM commit, a post-state
root), must add the coinbase and the withdrawal recipients from the block itself. Closing it
means giving those credits a pseudo-transaction window like the system calls. The recorder also
has no proof of its own sufficiency yet (above); its test (`tests/readset.lisp`) checks the
decoded sets against the raw read stream and that every net state change is covered as
written.

## Consumers

- **Stateless execution and witnesses** (`witness-design.md`): a witness that covers a
  sufficient read set determines the outcome (§2.2). On the device, the read set is whatever
  the executor asks, so a missing key fails hard and names the key; a recorder that missed a key
  only costs liveness, never correctness.
- **Block-STM conflicts** (`lean/Evm/Parallel/`): a tx's logged reads are validated against the
  committed prefix; `Reads.Tx.Deterministic` is exactly "the logged read set is sufficient". The
  delta refinement keeps coinbase credits out of the conflict graph unless the coinbase is read.
- **Prefetch and layout** (persistence): the read sets of the next blocks are the keys to fetch
  ahead and to keep together on disk.
- **Archive view calls**: an `eth_call` at an old block needs exactly the read set's values as of
  that block.
- **Dependency analysis**: which txs and contracts depend on which state, from read and write sets
  across a block range.

## Open

- **One key type.** `lean/Evm/Parallel/Reads.lean` still uses its own `Key := Nat` with
  `Val := Nat` (and `CL/EffectSettleProof.lean` maps addresses into it for the delta theorems).
  Folding it into `ReadKey` is not mechanical: Reads' storage is `Key → Nat` with arithmetic
  deltas, while `Answer` is dependent per key kind. The fold is to make `Reads` generic over the
  key and value types (`[DecidableEq K]`, an additive value for deltas), instantiate it at
  `ReadKey`, and restate `Faithful`/`Deterministic` as `AgreeOn`/`Sufficient`. It goes with the
  oracle-program work (witness-design W2), where `Deterministic` becomes a theorem.
- The EVM instance of `Sufficient` (`SameOutcome`, `Tx.run`) and the theorem that the asked set is
  sufficient: witness-design §2.2, §2.3.
- The recorder gap above (credits outside tx windows).
