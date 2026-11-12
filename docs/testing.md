# Testing: the gates and the fixture battery

## The gates (run before every commit; CI runs the first three)

| gate | checks |
|---|---|
| `scripts/verify-host-emit.sh` | the committed generated files (`src/generated/host.lisp`, `c/handlers.S`, `c/handlers-x86-elf.S`) are byte-identical to what the Lean emitters produce now; the effect-layer proofs (`Evm.CL.Effect*Proof`) check, with no `sorry`; no gas-schedule constant copied by hand into the Lisp (`scripts/check-derived-gas.py`); the interpreter runs against checking callbacks (`c/test_interp`) |
| `scripts/verify-axioms.sh` | the axiom closure of the audited theorems (`lean/AxiomAudit.lean`) matches the committed baseline (`scripts/generated/axiom-audit.txt`): no new axiom, `sorry` or `native_decide` slips in |
| `scripts/verify-coverage.sh` | the refinement-coverage ratchet (`scripts/refinement_coverage.py`): the count of open refinement obligations may only go down; the same generator writes `scripts/generated/verification-stats.md` (per-component statement / proof lines, theorems, `sorry`, axiom closure) and the gate fails on its drift |
| `scripts/verify-jit-emit.sh`, `verify-asm-*.sh`, `verify-x86-*.sh` | the ARM64 and x86-64 encoders, instruction items and handler gadgets against their Lean denotations and test vectors |

## The Lisp test suites

`(asdf:test-system "eita")` (the system `eita/test`, `tests/harness.lisp`) runs, in one image
with the engine loaded: the native-handler checks (CALL family, STATICCALL, `eita_run`, the
u256-width regressions of JUMP, RETURN and CALL memory expansion), the modexp gas vectors, the
MPT oracles (mainnet genesis root, incremental trie = rebuild), the streaming state root
against the trie, layered snapshots against the Lean model, the Arc PQ precompile on its real
call, the recovery decisions and the call-gas and SSTORE-gas natives against the Lean vector
generators (`lake build recoveryVectors callGasVectors sstoreGasVectors`), the JIT against the
interpreter (`audit-jit`), and a BlockchainTests sample on both tiers (`EITA_TEST_FIXTURES`, a
`ValidBlocks` directory, else `lean/external/ethereum-tests`). A suite whose prerequisite is
missing is reported SKIP with the reason; `EITA_TEST_GATES=1` adds the three Lean gates above.

```sh
sbcl --load ~/.local/share/ocicl/ocicl-runtime.lisp --eval '(push (truename ".") asdf:*central-registry*)' \
     --eval '(asdf:test-system "eita")' --quit
```

## The fixture battery

`bin/eita fixtures` (`src/fixtures/runner.lisp`) runs BlockchainTests (ethereum/tests, execution-spec-tests) on the
same block pipeline a chain replay uses: the header gate (EELS `validate_header`,
`validate_ommers`), the header hash, the pre-block system calls, every transaction
(`run-evm-tx`), the post-block effects, `verify-block-header` (gas used, logs bloom,
receipts root, blob gas, requests hash, the body's roots), the state root after every
block, then the post-state account by account. Blocks marked `expectException` must be
rejected for the expected reason.

```sh
bin/eita fixtures <test.json | flat directory>...
scripts/run-battery.sh <fixture tree> [log]        # one SBCL per directory, a TOTAL line
```

Each runs on two tiers: the JIT (default: hot code compiled by the Lean-emitted JIT, via
the `emitJIT` daemon) and the threaded interpreter (`EITA_NO_JIT=1`). Both must give the
same verdict on every test (`diff <(grep pass= a.sum | sort) <(grep pass= b.sum | sort)`).

### The Cancun battery

The corpus is ethereum/tests (`develop` at `c67e485f`), its `LegacyTests/Cancun` snapshot:
`BlockchainTests/{GeneralStateTests,InvalidBlocks,TransitionTests,ValidBlocks}`, 111,983
tests in 3,288 files, Frontier..Cancun:

```sh
git clone https://github.com/ethereum/tests lean/external/ethereum-tests
git -C lean/external/ethereum-tests checkout c67e485f
B=lean/external/ethereum-tests/LegacyTests/Cancun/BlockchainTests
SBCL_ARGS="--dynamic-space-size 16GB" EITA_NO_JIT=1 scripts/run-battery.sh $B /tmp/interp.log > /tmp/interp.sum
SBCL_ARGS="--dynamic-space-size 16GB"               scripts/run-battery.sh $B /tmp/jit.log    > /tmp/jit.sum
diff <(grep pass= /tmp/interp.sum | sort) <(grep pass= /tmp/jit.sum | sort)
```

Expected on both tiers (about 30 minutes each, sequential):

    TOTAL pass=111835 fail=0 skip=40 xfail=108
    invalid blocks: rejected=5960 rejected-other=34 accepted=6 undecoded=498 unchecked=6

- **skip 40**: transition networks (`FrontierToHomesteadAt5`, …); the runner sets one fork per test.
- **xfail 108**: `src/fixtures/expected-failures.txt`, each section with its reason —
  EIP-7610 not applied (execution-specs #3417/#3508), the RIPEMD-160 exemption after an
  exceptional halt (`docs/effect-layer-derivation.md` §4.8), and the six
  `GasLimitHigherThan2p63m1` tests that EELS itself lists as incorrect (the **accepted 6**).
- **unchecked 6**: invalid blocks whose only defect is RLP-level; the runner reads the
  decoded block, never its RLP bytes.
- **undecoded 498**: invalid blocks without `rlp_decoded`, with a value past 2^256, or not
  on the canonical head.
- **rejected-other 34**: rejected for a different reason than the filler names, each time
  the one EELS raises first (clause order).
- Not checked: the proof-of-work seal (ethash).

Also green: `BlockchainTests/ValidBlocks` of the current corpus (882 tests, Cancun + Prague)
and execution-spec-tests' `fixtures_blockchain_tests.tgz` (Cancun + Prague: 38,885 pass,
25 xfail).

### A quick subset

```sh
V=lean/external/ethereum-tests/LegacyTests/Cancun/BlockchainTests/ValidBlocks
for d in bcExample bcStateTests bcEIP1559 bcEIP4844-blobtransactions bcUncleTest; do
  bin/eita fixtures $V/$d | tail -3
  EITA_NO_JIT=1 bin/eita fixtures $V/$d | tail -3
done
```

## Lean-side checks

`cd lean && lake build` builds the whole spec and every proof. `lake exe replay <dir>`
replays BlockchainTests on the Lean interpreter itself (`lean/REPLAY.md`), independent of
the native engine. `lake exe test` runs the Lean unit tests.
