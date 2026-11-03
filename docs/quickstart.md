# Quickstart: a REPL session

After `./build.sh` (README), from the repository root:

```sh
bin/eita repl
```

This is the engine — libeita, the Lean-emitted host code, the chains, the fixture runner —
with the `eita` package current, a thin REPL layer (`src/eita.lisp`). From your own SBCL,
the same is `(asdf:load-system "eita")` plus `(asdf:load-system "eita/fixtures")` for the
fixture functions, with ocicl's runtime loaded and the repository on ASDF's path:

```sh
sbcl --load ~/.local/share/ocicl/ocicl-runtime.lisp \
     --eval '(push (truename ".") asdf:*central-registry*)' \
     --eval '(asdf:load-system "eita/fixtures")' --eval '(in-package :eita)'
```

`bin/eita repl --load examples/quickstart.lisp` runs the session below as a script. The
heap: `bin/eita --dynamic-space-size 16GB --end-runtime-options repl` (README, Build). Every transaction runs through
`run-evm-tx`, the same function a mainnet replay runs for each user transaction: the
Lean-derived transaction effect (validation, upfront charge, access lists, EIP-7702, the
message), refund and calldata-floor rules, fee settlement, end-of-transaction deletions.

| function | what |
|---|---|
| `(new-world &key fork alloc)` | a world at a fork (`"Frontier"` … `"Cancun"`, `"Prague"`, `"Osaka"`); ALLOC: `((address :balance … :nonce … :code … :storage ((slot . value) …)) …)` |
| `(transact world &key from to value data gas gas-price nonce access-list)` | run and commit one transaction (TO nil: create); returns `(:status :gas-used :output :logs :created)` |
| `(deploy world &key from code value gas)` | create a contract from init code; its address |
| `(call world &key from to data value gas)` | like `eth_call`: run on a copy, the world unchanged |
| `(balance w a)`, `(nonce w a)`, `(code w a)`, `(storage w a slot)` | inspect |
| `(fund w a wei)`, `(set-code w a code)`, `(set-storage w a slot v)` | edit the world directly |
| `(state-root w)` | the Merkle-Patricia state root a block header would commit to |
| `(load-fixture file [test])` | a BlockchainTest's pre-state as a world, at its fork |
| `(run-fixture-file file-or-dir)` | run BlockchainTests as `bin/eita fixtures` does |
| `(hex x)`, `(addr x)` | conversions; addresses and data may be given as `"0x…"` strings |

Transactions are not signed: `:from` is the sender, as on a dev chain that lets you
impersonate accounts. Each `transact` runs as its own block (`eita:*block*` is the block
environment: number, timestamp, base fee 0, gas limit 30M, coinbase 0, chain id 1), without
the per-block system calls. To run real blocks, use the driver: `(replay "ethereum" 1 :to 1000
:blocks "/path/to/blocks")`, or `bin/eita replay` (`docs/block-input.md`).

## A session

(The transcript below is a real run; `EITA_NO_JIT=1` gives the same results on the
interpreter tier.)

The fixture part reads ethereum/tests from `lean/external/ethereum-tests` (`docs/testing.md`
says how to fetch it). The last transaction is refused by the rules (Bob holds 1,000 wei and
tries to send 5,000), which `transact` signals as an error naming the reason.

```lisp
$ bin/eita repl
* (defparameter *w* (new-world :fork "Prague" :alloc '(("0xa11ce" :balance 1000000000000000000))))
*W*
* (transact *w* :from "0xa11ce" :to "0xb0b" :value 1000 :gas 21000)
(:STATUS 1 :GAS-USED 21000 :OUTPUT #() :LOGS NIL :CREATED NIL)
* (balance *w* "0xb0b")
1000
* (nonce *w* "0xa11ce")
1
* (defparameter *c* (deploy *w* :from "0xa11ce" :code "0x6018600c60003960186000f3600054600101806000558060005260206000a160206000f3"))
*C*
* (hex *c*)
"0x55eb3f05725579313d96873983f9d1b00196629c"
* (hex (code *w* *c*))
"0x600054600101806000558060005260206000a160206000f3"
* (let ((r (transact *w* :from "0xa11ce" :to *c*))) (list (getf r :status) (getf r :gas-used) (hex (getf r :output)) (getf r :logs)))
(1 44145 "0x0000000000000000000000000000000000000000000000000000000000000001"
 ((490510380569082386323567615992469050615603290780 (1)
   #(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))))
* (hex (getf (call *w* :to *c*) :output))
"0x0000000000000000000000000000000000000000000000000000000000000002"
* (storage *w* *c* 0)
1
* (handler-case (transact *w* :from "0xb0b" :to "0xa11ce" :value 5000 :gas 21000) (error (e) (princ-to-string e)))
"blk=5 tx=0 is invalid: insufficient balance (sender nonce 0 balance 1000)"
* (state-root *w*)
"0x259aae2ad50517debbb62cba463cea21719f73dcb6ae33f66a490b183f516ea3"
* (defparameter *f* "lean/external/ethereum-tests/LegacyTests/Cancun/BlockchainTests/ValidBlocks/bcExample/basefeeExample.json")
*F*
* (defparameter *t* (load-fixture *f* "basefeeExample_Cancun"))
*T*
* *t*
#<EITA-REPLAY::WORLD 2 accounts {…}>
* (fork)
16
* (balance *t* "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b")
100000000000000000
* (length (code *t* "0x000f3df6d732807ef1319fb7b8bb8522d0beac02"))
97
* (run-fixture-file *f*)
PASS basefeeExample_Cancun
PASS basefeeExample_London
PASS basefeeExample_Paris
PASS basefeeExample_Shanghai
---
summary: pass=4 fail=0 skip=0 xfail=0
invalid blocks: rejected=0 rejected-other=0 accepted=0 undecoded=0 unchecked=0
jit: codes=2 no-jit=0 frames-jit=3 frames-interp=0 manifest-misses=0 chunk-evictions=0
NIL
```

## Where to go next

- `src/eita.lisp` is 130 lines: read it to see which engine functions it calls.
- `src/evm/run-tx.lisp` (`run-evm-tx`), `src/evm/tx.lisp` (`apply-tx`) and
  `src/evm/calls.lisp`, `callbacks.lisp` (the callbacks) are the host; `src/generated/host.lisp` is what Lean emitted for it.
- `lean/Evm/Prague/` is the spec of the fork you just ran, as a delta over Cancun.
- Hooks: a chain spec (`src/chains/chain-spec.lisp`) changes behaviour only through its
  fields — precompiles, fee routing, system calls, warming rules. `src/chains/arc.lisp` is a
  complete example.
