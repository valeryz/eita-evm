# Eita — Lean specification

> **Status: historical** (written 2026-05; the status and layout below are from then). The
> current state: the top-level `README.md`, `docs/testing.md` and `lean/REPLAY.md`.

The Lean 4 spec side of [Eita](../README.md). Reference implementation
of the Ethereum Virtual Machine that drives the test corpus and acts
as the verified semantics the Common Lisp side will refine.

## Status

- Full BlockchainTests + GeneralStateTests corpus passes (**5650 / 5650**)
  through Frontier, Homestead, TangerineWhistle, SpuriousDragon.
- All four implemented fork interpreters use the **yield-based
  Effect interpreter** (`Evm/*/Vm/Effect.lean`). The recursive
  `Interpreter.lean` mutual blocks are still present but no longer on
  the hot path — they'll be removed once correspondence proofs land.
- `Spec/Step.lean` demonstrates the inductive-step + correspondence
  pattern for ADD; extensible to every non-recursive opcode.

## Goal

Run every Ethereum mainnet block from Frontier (block 0) through
Prague against a Lean-defined operational semantics, with every
state transition spec-able as an `Yield` event or a pure step.

## Source of truth

Tracks [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
(EELS), the official executable Python spec. Each Lean module names
the EELS file it mirrors. When the two diverge, EELS wins and this
spec gets patched.

## Architecture

The interpreter is **yield-based** (defunctionalized free-monad
style). `runFrame : Evm → Step` runs the current frame until it
yields, halts, or errors. Sub-frame execution lives in the
**trampoline** (`Effect.trampoline`), structurally separate from
opcode dispatch — there is no recursion across frames inside
`runFrame` itself.

```
EVM bytecode
   │
   │  fork-specific step1 (opcode dispatch)
   ▼
StepResult ::= continue | yield | halt | error
   │
   │  runFrame loops until non-continue
   ▼
Step ::= yield e | halt out | error e
   │
   │  trampoline handles yield (spawns sub-frame, recursively trampolines, merges)
   ▼
final Evm state
```

The yields currently cover CALL / CALLCODE / CREATE / DELEGATECALL
(the structurally recursive opcodes). Storage / balance / log /
blockhash are *internal* in this pass — they'll move to yields when
the Block-STM parallel execution layer arrives (see
a design note (issue #6 of the original tracker)).

## Layout

```
lean/
├── lakefile.toml
├── lean-toolchain                  # leanprover/lean4:v4.35.0
├── Evm.lean                        # root re-exports
└── Evm/
    ├── BaseTypes.lean              # U8/U64/U256, Address, Hash32, Bytes
    ├── Rlp.lean
    ├── Trie.lean
    ├── Crypto/                     # FFI to keccak, sha256, ripemd160, ecrecover
    ├── Forks.lean                  # (blockNumber, timestamp) → ForkId
    ├── Frontier/                   # full implementation (template for other forks)
    │   ├── Fork.lean
    │   ├── ForkTypes.lean
    │   ├── State.lean
    │   ├── Vm/
    │   │   ├── Effect.lean         # yield-based interpreter (hot path)
    │   │   ├── Interpreter.lean    # recursive (legacy, will be removed)
    │   │   ├── Step.lean           # inductive small-step + correspondence
    │   │   ├── Instructions/       # per-opcode handlers
    │   │   └── PrecompiledContracts/
    │   ├── StateRoot.lean
    │   └── Utils/
    ├── Homestead/Vm/Effect.lean    # delta from Frontier (+ EIP-7, EIP-2)
    ├── TangerineWhistle/Vm/Effect.lean   # delta (+ EIP-150)
    ├── SpuriousDragon/Vm/Effect.lean     # delta (+ EIP-160/161/170)
    ├── DaoFork/                    # header
    ├── Byzantium/                  # header — TBD
    ├── Constantinople/             # header — TBD
    ├── Petersburg/                 # header
    ├── Istanbul/                   # header — TBD
    ├── MuirGlacier/                # header
    ├── Berlin/                     # header
    ├── London/                     # header
    ├── ArrowGlacier/               # header
    ├── GrayGlacier/                # header
    ├── Paris/                      # header (The Merge)
    ├── Shanghai/                   # header
    ├── Cancun/                     # header
    └── Prague/                     # header — most-elaborated template
```

## Build

```sh
lake build
lake exe replay external/ethereum-tests/LegacyTests/Constantinople/BlockchainTests/ValidBlocks
lake exe replay external/ethereum-tests/LegacyTests/Constantinople/BlockchainTests/GeneralStateTests
```

Requires Lean 4.35.0 via elan; libsecp256k1 for ECDSA recovery; the
`ethereum/tests` submodule initialized under `external/`.

## Build-out order

1. **Done.** Frontier full implementation; Homestead / TW / SD deltas;
   yield-based Effect interpreter across all four; full corpus 5650/5650.
2. **In progress.** `Spec/Step.lean` inductive-step + correspondence
   pattern.
3. **Next.** Byzantium delta (EIP-100, 140, 196/197/198, 211, 214 +
   new precompiles).
4. Then Constantinople, Petersburg, Istanbul, MuirGlacier, Berlin,
   London, ArrowGlacier, GrayGlacier, Paris (The Merge), Shanghai,
   Cancun, Prague.
5. Bridge proof: `Effect.runFrame` matches `Interpreter.runFrame`
   formally (currently only empirically via the test corpus).
