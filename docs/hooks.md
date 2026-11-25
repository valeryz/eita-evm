# Hooks: metric folds and notifications on verified blocks

Eita runs your Common Lisp code inside the node, fed every block after the node has verified
it. Two things are built this way:

- a **metric fold**: metrics are folds over the chain's history. A fold is a reduce: a
  function of (state, block) to state, run on each block in order, its state kept in the
  node's heap;
- a **notification service**: conditions checked on each block, and an action (a message,
  a webhook) when one holds.

The examples below are in `examples/hooks/`; each runs on the mainnet block shipped in
`tests/data/` and is tested by the `hooks` suite (`tests/hooks.lisp`).

## Concepts

**Blocks, transactions, records.** The replay executes a block's system work (before and
after the user transactions: beacon root, block-hash history, withdrawals, rewards) and its
transactions. Each produces records: the transaction itself with its result (status, gas
used, effective gas price), its committed **logs**, its native value **transfers**, and its
net **state changes** (balance, nonce, code, storage: the value before and after the
transaction). A reverted frame's logs and transfers are not among them.

**Verified before delivered.** A block reaches your handlers after the node's verifier has
checked it against its header: gas used, logs bloom, receipts root, the body's roots (the
state root is checked at anchors). A block that does not verify stops a full-state run and is
never delivered. A lazy-state run (`--lazy`) reports a header mismatch and goes on; its
blocks are delivered either way.

**State in the heap scales with the output, not the history.** A fold keeps what its answer
needs: running sums, a window of recent blocks, a bounded top-k. A fold that keeps a record
per transaction or per address grows with the chain; it belongs in a database the fold
writes to, not in the heap.

**Threads.** The replay thread executes blocks and captures their records; a hooks thread
runs your handlers, one block at a time, in chain order; your own threads do anything slow.

```
replay thread     block N ──capture──► queue (≤ 256 blocks) ──► hooks thread: wait for N's verdict,
verifier thread   check N's header ─────────────────────────►   then the handlers (fold lock held)
your worker                                                      ──► your queue ──► deliver (HTTP, …)
```

The replay runs ahead of the handlers by up to 256 blocks. A handler slower than the replay
fills the queue, and then the replay waits for it.

## The API

| function | what |
|---|---|
| `(eita:subscribe name &key start block tx log transfer state-change checkpoint rollback finalize)` | subscribe the handlers under NAME; a subscription with the same name is replaced |
| `(eita:unsubscribe name)` | remove it: no handler of it runs after this returns |
| `(eita:subscriptions)` | each as `(name :handlers kinds :error why)`, WHY NIL while it runs |
| `(eita:with-fold-state (&optional block) body…)` | run BODY while no handler runs; BLOCK is the newest block delivered |

The handlers, each a function (or a symbol naming one):

| handler | called with | when |
|---|---|---|
| `:start` | `n` | before the subscription's first block, N |
| `:tx` | a tx record | each user transaction of the block, in order |
| `:transfer` | a transfer record | each committed native value move |
| `:log` | a log record | each committed log |
| `:state-change` | a change record | each net state change |
| `:block` | a block record | after the block's other handlers |
| `:checkpoint` | `n` | the node is about to make block N a layer point: persist through N now |
| `:rollback` | `n` | a reorg rolled the chain back to block N |
| `:finalize` | | the run ends |

The records are property lists:

| record | fields |
|---|---|
| block | `:number :hash :parent-hash :timestamp :coinbase :base-fee :gas-limit :gas-used :txs` (the tx records) |
| tx | `:block :index :hash :type :from :to` (NIL: a creation) `:value :nonce :gas-limit :gas-used :status` (1 success, 0 revert or halt) `:gas-price` (effective) `:logs :transfers :changes` |
| log | `:block :tx :index` (the block's logIndex) `:address :topics` (integers) `:data` (octets) |
| transfer | `:block :tx :kind` (`:tx` the transaction's value, `:call`, `:create`, `:selfdestruct`, `:chain` a chain's own move) `:depth :from :to :value` |
| change | `:block :tx :kind` (`:balance`, `:nonce`, `:code` with code hashes, 0 for none, `:storage`) `:address :slot` (storage) `:pre :post` |

`:tx` in a log, transfer or change is the transaction's index, or `:pre-block` / `:post-block`
for the block's system work (which has no tx record). Addresses, hashes and values are
integers; `eita:hex` prints them.

**Guarantees.**

1. **Order.** Blocks arrive in chain order. Within a block, for each subscription: the
   records in execution order (system work before the transactions, the transactions by
   index, system work after), each transaction's `:tx` first and then its transfers, logs
   and changes; `:block` last.
2. **Verified and complete.** A block is delivered once its verdict passed, and whole: a
   subscription starts at a block boundary (`:start` names its first block), and a block
   that never commits (an invalid block of a test, a run that stops mid-block) is dropped.
3. **Checkpoints.** `:checkpoint n` arrives after block N's handlers. The node publishes its
   layer at N, and so can resume from N, only after every subscription's `:checkpoint`
   handler returned.
4. **Rollbacks.** After `:rollback n`, the blocks above N arrive again, from the new branch.
   A rollback comes from a reorg, or from the Engine API execution client refusing a block
   after delivery (it checks each block's state root last). A subscription without a
   `:rollback` handler that has seen a block above N is detached instead: it would be ahead
   of the chain.
5. **Failures are contained.** A handler that signals detaches its subscription (the reason
   is kept in `eita:subscriptions`); the other subscriptions and the replay go on.
6. **Observe, never steer.** Execution, verification and every output are the same with or
   without subscriptions (the `hooks` and `readset` suites check this).
7. **Free when unused.** With no subscription nothing is captured; a block start costs one
   function call.

## Running hooks

A file of subscriptions is given to a replay as `--observer FILE` (`EITA_OBSERVER`), loaded
before the first block:

```sh
bin/eita replay --chain ethereum --blocks DIR --from 1 --to 100000 --observer examples/hooks/gas-per-block.lisp
```

From a REPL, load the file and run blocks: a replay (`eita:replay`), or BlockchainTests,
which run through the same event stream (each test a run of its own: `:start`, its blocks,
`:finalize`). With the block shipped in the repository:

```lisp
$ gzip -dc tests/data/mainnet-24538111.json.gz > /tmp/block.json
$ bin/eita repl --load examples/hooks/gas-per-block.lisp --load examples/hooks/transfers.lisp
* (run-fixture-file "/tmp/block.json")
PASS mainnet_24538111
* (hooks.gas:summary)
(:BLOCK 24538111 :WINDOW-BLOCKS 1 :WINDOW-GAS 59896574 :WINDOW-FEES 10362677504136862
 :GAS-PER-SECOND NIL :TOTALS (:BLOCKS 1 :TXS 756 :GAS 59896574 :BURNT 2298267182841530 :TIPS 8064410321295332))
* (hooks.transfers:summary 2)
(:BLOCK 24538111 :COUNTS (:ERC20 550 :NATIVE 511 :NATIVE-WEI 204704243708362920395)
 :TOP-SENDERS (("0x2393d38400cad1d0ffae85b37d76de05bb7eddc6" 30 3)
               ("0xf48a3f7c0575c85cf4529aa220caf3c055773f1c" 29 0))
 :TOP-TOKENS (("0xdac17f958d2ee523a2206206994597c13d831ec7" 218 0)
              ("0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48" 147 0)))
* (subscriptions)
(("gas-per-block" :HANDLERS (:START :BLOCK :ROLLBACK) :ERROR NIL)
 ("transfers" :HANDLERS (:START :LOG :TRANSFER :BLOCK :ROLLBACK) :ERROR NIL))
```

(This block's pre-state is partial, so its state root is not checked; its gas, receipts root
and bloom are.)

## Examples

### A per-block fold: gas and fees, a rolling hour (`gas-per-block.lisp`)

Each block becomes a row (gas used, fees burnt and paid as tips); the fold keeps the rows of
the last hour, their sums, and totals since it started. The window ends at the newest block's
timestamp, so a row leaves it when a newer block is an hour later:

```lisp
(defun on-block (block)
  (multiple-value-bind (burnt tips) (fees block)
    (let ((r (make-row :number (getf block :number) :timestamp (getf block :timestamp)
                       :gas-used (getf block :gas-used) … :burnt burnt :tips tips)))
      (push r *window*)
      (count-row r 1)
      … rows older than (- (row-timestamp r) *window-seconds*) leave the window …)))

(eita:subscribe "gas-per-block" :start 'on-start :block 'on-block :rollback 'on-rollback)
```

`fees` sums `gas-used × base-fee` (burnt) and `gas-used × (gas-price − base-fee)` (tips) over
the block's transactions. A rollback removes the rows above the fork point; `:start` starts
over unless the fold ends at the block before.

### Token transfers, top senders in bounded memory (`transfers.lisp`)

An ERC-20 transfer is a log whose first topic is `keccak256("Transfer(address,address,uint256)")`,
with three topics and 32 bytes of data (ERC-721's has a fourth topic); a native move is a
transfer record with a positive value. The fold counts both and ranks senders and tokens with
Space-Saving: K counters (`*k*`, 256) however many addresses there are; a reported count is
at most its error above the true count.

```lisp
(defun on-log (log)
  (when (erc20-transfer-p log)
    (counted :erc20 1)
    (add *senders* (ldb (byte 160 0) (second (getf log :topics))))
    (add *tokens* (getf log :address))))
```

Each block's additions go to an undo log of the newest 128 blocks, which `:rollback` replays
backwards. On the shipped block: 550 ERC-20 transfers and 511 native moves from 713 senders,
256 of them kept.

### A state watch (`watch.lisp`)

```lisp
(hooks.watch:watch "0x…token…" :slot 3)                                  ; print each change
(hooks.watch:watch "0x…account…" :kind :balance :notify 'my-function)    ; or call yours
```

One `:state-change` subscription serves every watch with one hash lookup per change. A change
is a transaction's net change: a slot written twice in one transaction reports one change,
and a write that a revert undid reports none. `:rollback` tells every watcher, so it can
retract what it reported above the fork point.

### A notification service (`notify.lisp`)

Conditions run in the handlers and only queue a message; a worker thread delivers it:

```lisp
(defun on-transfer (x)
  (when (>= (getf x :value) *large-value*)
    (notify *notifier* (list :event "large-transfer" :block (getf x :block) :tx (getf x :tx)
                             :from (eita:hex (getf x :from)) :to (eita:hex (getf x :to))
                             :value (princ-to-string (getf x :value))))))
```

`notify` never waits. A token bucket bounds the rate (`:burst` at once, `:rate` a second
after); a message over the rate or over the queue's `:capacity` is dropped and counted
(`notifier-stats`). The worker calls `:deliver` on each message: by default `json-line`, one
JSON object per line on standard output. A webhook is a function you supply:

```lisp
(hooks.notify:start :rate 2 :burst 20
  :deliver (lambda (m)
             (uiop:run-program (list "curl" "-fsS" "-H" "content-type: application/json"
                                     "-d" (with-output-to-string (s) (hooks.notify:json-line m s))
                                     "https://hooks.example.invalid/eita"))))
```

A failed delivery is counted and logged; it does not reach the handlers. `:finalize` waits
for the queue to empty, so a bounded run ends with its notifications delivered.

### Restarts and reorgs (`durable.lisp`)

The heap does not survive a restart. A full-state node resumes from a layer point (an
anchored block), and its subscriptions see `:start` with the block after it; a fold that
checkpoints at every layer point resumes from the same block:

```lisp
(defun on-checkpoint (n)            ; written whole, then renamed: a checkpoint is never torn
  … (prin1 *state* tmp) (rename-file tmp (checkpoint-path n)) …)

(defun on-start (n)
  (cond ((eql (getf *state* :block) (1- n)))                   ; this heap is at N-1 already
        ((probe-file (checkpoint-path (1- n))) (load-checkpoint (1- n)))
        (t (start-over n))))                                    ; and :from says where it starts
```

Layer points come every quarter of the anchor interval (`--checkpoint-every K`: every K/4
blocks), and at every block while following the tip; the fold keeps its newest 8
checkpoints. A fold without a checkpoint at the resume point starts over at that block and
records `:from`, so its coverage is visible; to cover the blocks before, replay them with the
fold subscribed. Lazy-state runs have no layer points.

A reorg undoes the newest blocks; the fold keeps a delta per block for the newest 128
(`:rollback` subtracts them, newest first) and signals when a rollback reaches past its undo
log.

## Developing hooks live from Emacs

`bin/eita` serves a Swank REPL (SLIME's) while it runs `replay`, `engine` or `repl`, when
`EITA_SWANK_PORT` names a port. It listens on 127.0.0.1 only:

```sh
EITA_SWANK_PORT=4005 bin/eita replay --chain ethereum --blocks DIR --from 1 --to 100000 --observer my-hooks.lisp
EITA_SWANK_PORT=4005 bin/eita repl                       # or a REPL session, no replay
```

The server is Swank from SLIME 2.32, pinned in `ocicl.csv` and compiled into `bin/eita`; use
SLIME 2.32 in Emacs (another version connects, after a version warning). A port in use leaves
the command running without a REPL (`[swank] not started on 127.0.0.1:4005: …`). A connection
that fails is logged and the server goes on listening.

- **Connect:** `M-x slime-connect`, host `127.0.0.1`, port 4005.
- **A remote node:** forward the port over SSH, then connect to `127.0.0.1:4005` locally:
  `ssh -L 4005:127.0.0.1:4005 user@node-host`.
- **SLY** speaks to Slynk, not Swank: load Slynk from your SLY checkout in the hooks file
  instead, `(load "/path/to/sly/slynk/slynk-loader.lisp") (slynk-loader:init)
  (setf slynk::*loopback-interface* "127.0.0.1") (slynk:create-server :port 4006 :dont-close t)`.

A session:

```lisp
(load "examples/hooks/transfers.lisp")       ; subscribes: from the next block on
(hooks.transfers:summary 5)                  ; the fold's state, read under the fold lock
(eita:with-fold-state (n)                    ; a consistent copy, through block n
  (list n (copy-list hooks.transfers::*counts*)))
;; redefine a handler (C-c C-c on its defun): the next block uses it, because the
;; subscription names it by symbol
(eita:unsubscribe "transfers")
```

The rules:

- **Read a fold's state inside `eita:with-fold-state`.** Handlers run on the hooks thread and
  the REPL on another; inside it, no handler runs, so every fold reflects whole blocks. Copy
  what you need and leave: the handlers wait meanwhile, and behind them the replay.
- **Never walk the node's own tables from the REPL while blocks run**: the world state, the
  JIT cache and the engine's tables mutate on the replay thread without locks. Ask a fold for
  what you need instead.
- **Long computations run outside the lock**, on the REPL's thread or a thread of their own.
- **Unsubscribe before changing a handler's arguments**, then subscribe again; a redefinition
  with the same arguments takes effect at the next block.
- **Checkpoint by hand** inside the lock: `(eita:with-fold-state (n) (hooks.durable::on-checkpoint n))`.

## Performance

- **Capture** costs nothing without subscriptions. With any, each transaction's records are
  copied on the replay thread (its logs, transfers and net changes, which the node computes
  anyway): a few percent of a dense block's execution.
- **Handlers** run once per record. Keep them to arithmetic and hash lookups; filter early
  (`watch.lisp`: one lookup per change). Never wait in a handler: no network, no disk beyond
  a checkpoint, no sleep, no lock another thread holds for long.
- **The execution client** (`docs/run-a-node.md`) waits for every subscriber before it
  answers a payload: a handler's time is part of its latency.
- **Slow work** (HTTP, a database, an alert channel) goes to a worker through a queue that
  never blocks the handler, as `notify.lisp` does; decide there what to drop when it falls
  behind.
- **Memory** is the heap the replay runs in. Keep state bounded (windows, sketches, counters
  per tracked key) and do not keep records past their block.
- **Handlers name functions by symbol** (`'on-block`): one indirection per call, and live
  redefinition.

## Querying history

A question about the past is a fold over the past: replay the range with the subscription
loaded, and the same handlers that follow the chain live answer it for the range (a backfill;
`--from`/`--to`, or `--resume` from an anchor). A value the answer needs at a given block —
a balance, a slot — is a watch or a fold that records it as the block passes. The node's
snapshots (`docs/layered-snapshots.md`) are its resume points, not a query interface.
