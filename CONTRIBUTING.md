# Contributing

Issues and pull requests are welcome. A few rules keep the project what it is:

1. **EELS is the spec.** A change to EVM semantics starts in Lean (`lean/Evm/<Fork>/`),
   translated from the Ethereum execution specs with a file-and-line citation. When EELS
   and another client disagree, read EELS. New forks add only the files that differ from
   their predecessor.
2. **Generated code is generated.** Never edit `c/handlers.S`, `c/handlers-x86-elf.S` or
   `scripts/generated/*` by hand; change the Lean emitter and regenerate (`./build.sh`).
   Gas formulas and fork rules come from Lean; `scripts/check-derived-gas.py` refuses a
   schedule constant copied into the Lisp.
3. **No silent gaps.** A known divergence is fixed, made unrepresentable, or stated as an
   open obligation (`sorry` in a theorem, an entry in
   `src/fixtures/expected-failures.txt` with its reason). Never skipped quietly.
4. **One owner per decision.** A number or a rule is computed in one place; a second copy
   is a bug. Chains change behaviour only through `chain-spec` fields
   (`docs/replay-architecture.md`).

Before a pull request:

```sh
./build.sh
scripts/verify-host-emit.sh          # generated files == emitters; effect proofs check
scripts/verify-axioms.sh             # no new axioms
scripts/verify-coverage.sh           # proof debt does not grow
bin/eita fixtures <a relevant BlockchainTests directory>    # and with EITA_NO_JIT=1
sbcl --load ~/.local/share/ocicl/ocicl-runtime.lisp --eval '(push (truename ".") asdf:*central-registry*)' \
     --eval '(asdf:test-system "eita")' --quit            # the Lisp test suites (docs/testing.md)
```

For a change to execution, run the Cancun battery on both tiers (`docs/testing.md`) and
say so in the pull request. Commit messages say what changed and why; a proof or test that
covers the change is named.

By contributing you agree that your contribution is licensed under the MIT license.
