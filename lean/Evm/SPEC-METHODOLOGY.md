# Fork-delta Spec methodology

The Lean EVM is organized as a chain of forks, each a delta on its
predecessor. The same delta principle applies to **step relations**
in `Spec/` directories: a fork's `Spec/` holds only the relations the
fork *newly introduces* or *changes*. Unchanged relations are inherited
by import; you never copy a relation from one fork to the next "just
because."

## Why relations at all?

The implementation in `Vm/Effect.lean` is executable but big and
side-effectful. The spec relations in `Spec/` are pure mathematical
predicates: `IsAddStep : Evm → Evm → Prop`, etc. They serve three
purposes:

1. **Disambiguation.** "What does Constantinople's SSTORE *actually*
   do?" is answered by reading 30 lines of `Constantinople/Spec/
   StorageStep.lean`, not by re-reading 400 lines of trampoline code.
2. **Refinement target.** `Refinement.lean` proves each fork's
   `Effect.step1` matches the active relation for every opcode.
   Without a relation, "the implementation is correct" has no formal
   meaning.
3. **Theorem substrate.** Things like "every successful tx preserves
   wei conservation" are proven against the *relation*, not the
   imperative code. Once proven, the refinement gives you the same
   property on the implementation.

The Frontier-only situation we had before this methodology was a half
measure: full relations + refinement for Frontier's opcodes, then
nothing for the 13 forks after. That left every post-Frontier change
(EIP-1283, EIP-2200, EIP-2929, EIP-1559, EIP-6780, …) without a
spec-level statement.

## File layout

```
lean/Evm/
  Frontier/Spec/                  ← baseline (always relevant)
    Step.lean                     ← IsAddStep, IsSubStep, IsMulStep, …
    CallStep.lean                 ← IsCallStep, IsCallcodeStep
    StorageStep.lean              ← IsSloadStep, IsSstoreStep (Frontier sSet/sReset)
    MemStep.lean                  ← memory operations
    StepShapes.lean               ← runBinary/runUnary/runTernary patterns
    Tx.lean                       ← processTransaction relation
    FrameRun.lean, Invariants.lean, Refinement.lean

  Homestead/Spec/                 ← deltas
    CreateStep.lean               ← EIP-2: deposit failure REVERTS (was: leave empty code)
    DelegatecallStep.lean         ← EIP-7: new opcode 0xf4

  TangerineWhistle/Spec/          ← EIP-150 deltas
    CallStep.lean                 ← 63/64 forward rule
    GasConstants.lean             ← re-priced SLOAD/BALANCE/EXTCODE*/CALL/SELFDESTRUCT

  SpuriousDragon/Spec/            ← EIP-158/161/170 deltas
    TouchAccount.lean             ← touch semantics in process_message
    SweepEmpty.lean               ← end-of-tx empty-account pruning
    CodeSizeCap.lean              ← EIP-170 24KB cap on deployed code
    Sig.lean                      ← EIP-155 chainId in signing hash

  Byzantium/Spec/                 ← EIP-100/140/196/197/198/211/214/649/658
    RevertStep.lean               ← EIP-140 REVERT opcode
    StaticcallStep.lean           ← EIP-214 STATICCALL + static-context propagation
    ReturndataStep.lean           ← EIP-211 RETURNDATA*
    Bn256Step.lean                ← new precompiles 0x05..0x08

  Constantinople/Spec/
    BitwiseStep.lean              ← EIP-145 SHL/SHR/SAR
    Create2Step.lean              ← EIP-1014 CREATE2
    ExtcodehashStep.lean          ← EIP-1052 EXTCODEHASH
    StorageStep.lean              ← EIP-1283 net SSTORE (later reverted by Petersburg)

  Petersburg/Spec/
    StorageStep.lean              ← reverts to Byzantium SSTORE (re-imports it)

  Istanbul/Spec/
    StorageStep.lean              ← EIP-2200 net SSTORE (revised from EIP-1283)
    ChainidStep.lean              ← EIP-1344
    SelfbalanceStep.lean          ← EIP-1884 (selfbalance opcode)
    GasConstants.lean             ← EIP-1884 (SLOAD/BALANCE/EXTCODEHASH re-priced)
    Blake2fStep.lean              ← EIP-152

  Berlin/Spec/
    AccessList.lean               ← EIP-2929 warm/cold accounting predicate
    StorageStep.lean              ← EIP-2929 SSTORE cold surcharge
    CallStep.lean                 ← EIP-2929 CALL family cold surcharge

  London/Spec/
    BaseFee.lean                  ← EIP-1559 base fee formula + effective price
    BasefeeStep.lean              ← EIP-3198
    RefundCap.lean                ← EIP-3529 gas_used/5
    CodePrefix.lean               ← EIP-3541 0xEF reject
    Selfdestruct.lean             ← EIP-3529 SELFDESTRUCT refund removed

  Paris/Spec/
    NoBlockReward.lean            ← EIP-3675 (block reward = 0, ommers empty)
    PrevrandaoStep.lean           ← EIP-4399 (DIFFICULTY → PREVRANDAO semantics)

  Shanghai/Spec/
    Push0Step.lean                ← EIP-3855
    InitcodeCap.lean              ← EIP-3860 size cap + per-word surcharge
    WithdrawalsStep.lean          ← EIP-4895 (block-level)
    WarmCoinbase.lean             ← EIP-3651 (refines AccessList init)

  Cancun/Spec/
    TransientStorageStep.lean     ← EIP-1153 TLOAD/TSTORE
    McopyStep.lean                ← EIP-5656
    BlobhashStep.lean             ← EIP-4844 BLOBHASH
    BlobbasefeeStep.lean          ← EIP-7516 BLOBBASEFEE
    BlobTx.lean                   ← EIP-4844 blob transaction type-3 + gas market
    KzgStep.lean                  ← EIP-4844 point-evaluation precompile
    BeaconRoot.lean               ← EIP-4788
    Selfdestruct.lean             ← EIP-6780 only-same-tx

  Prague/Spec/
    Bls12381Step.lean             ← EIP-2537 (precompiles 0x0b..0x11)
    CalldataCost.lean             ← EIP-7623
    Requests.lean                 ← EIP-7685 (requestsHash)
    SetCodeStep.lean              ← EIP-7702 (set-code tx + CALL delegation)

  Osaka/Spec/                     ← TODO once Osaka EIPs are listed
  Amsterdam/Spec/                 ← TODO
```

## How relations compose

Each `<Fork>/Spec/<X>Step.lean` exports `IsXStep : Evm → Evm → Prop`.
For a fork F and opcode X, the **active relation** is the one in
the latest fork in F's lineage that defines `IsXStep`. Importers
should `open Evm.Frontier.Spec` for the baseline and additionally
`open Evm.<NewerFork>.Spec` for any fork whose changes apply.

For `Refinement.lean`, each fork's refinement file proves that
*its* `Effect.step1` satisfies the active relation for every opcode
the fork can dispatch. New refinement obligations are only for new or
changed relations — unchanged relations remain proven by the
predecessor's refinement file (re-exported as needed).

## What about state-machine deltas that aren't a single opcode?

Some EIPs change cross-cutting machinery: the touched-account set
(EIP-161), the warm/cold access lists (EIP-2929), the base-fee burn
(EIP-1559), withdrawals (EIP-4895). These get named state-machine
relations of their own, in the fork module that introduces them:

* `Evm.SpuriousDragon.Spec.TouchAccount : State → Address → State → Prop`
* `Evm.Berlin.Spec.AccessList`           (warm/cold predicate)
* `Evm.London.Spec.FeeMarket`            (effective price + burn)
* `Evm.Shanghai.Spec.WithdrawalsStep`    (per-Withdrawal balance credit)

Larger relations like `processTransaction` get a fresh spec when its
shape changes (London's `processTransaction` looks different from
Byzantium's because of EIP-1559). Smaller relations like `IsAddStep`
are written once in `Frontier/Spec/Step.lean` and never re-stated.

## Refinement proofs: what level of rigor?

The Frontier refinement file (`Frontier/Spec/Refinement.lean`) is the
template. Each opcode proof is:

* For uniform shape opcodes (binary arithmetic, comparison): one line
  via `runBinary_sound` / `runUnary_sound` shape lemmas.
* For state-touching opcodes (SSTORE, SLOAD, etc.): 5-20 lines of
  monadic do-block unfolding + state-lemma rewriting.
* For recursive opcodes (CALL/CREATE): 30-60 lines, often with
  `partial`-ish induction.

We tolerate `sorry`s on the heavier obligations as long as the *shape*
of the lemma is correct and the simple cases are closed. The four
existing `sorry`s in `Frontier/Spec/Refinement.lean` are CALL+CREATE-
shaped and acceptable.

Naming convention: an identity-shaped refinement (`P → P`, proved by
`intro h; exact h`) is a placeholder, not a discharge, and must be
named with a `_shape` suffix (e.g. `g1Add_sound_shape`) so it can't be
mistaken for a discharged obligation.

The debt is machine-ledgered: `scripts/refinement_coverage.py`
generates the coverage matrix — section A: every spec-relation theorem
in `Evm/*/Spec/*.lean` plus the curated IR composition layer, classified
PROVED / SORRY / SHAPE / SHAPE-UNSUFFIXED; section B: every registered
relation fully qualified, resolved ONLY by a theorem concluding it in
the impl→spec direction (theorems merely assuming it are listed as
structural and do not count), with MISSING/SHADOWED/STRUCTURAL-ONLY
reported — committed at `scripts/generated/refinement-coverage.md`.
`scripts/verify-coverage.sh` (CI) enforces drift (every status change
is a deliberate regeneration in the committing PR) and the debt ceiling
in `scripts/generated/refinement-debt-ceiling.txt`, stored separately
from the generated matrix so regeneration alone can never raise it. PROVED in the matrix is textual — no literal
`sorry` in the body — NOT an axiom check; the axiom-clean subset of the
derived layer is `scripts/verify-axioms.sh`. Run the generator after
any spec-theorem change.

For each new fork: write the same `Refinement.lean` covering the
fork's NEW relations only (the rest is by `import` of predecessor
refinement). Aim for `simp [unfold_chain]` one-liners
wherever the relation shape allows. (An earlier revision of this
line recommended `loom_smt`, an SMT-backed tactic whose discharge
rested on a `trust_smt` axiom; it was removed — keep these proofs
kernel-only so `#print axioms` stays clean.)

## Bug-class log — what to make sure your spec captures

When an implementation bug closes on EELS, the matching spec almost
always was missing the invariant the bug exposed. Lessons from the
2026-05-30 validation push:

1. **CREATE/CREATE2 sender nonce bump SURVIVES init-code REVERT and
   deposit-OOG.** The spec must mention the nonce-bump-persistence,
   not just "fail and push 0." Otherwise an implementation can
   silently roll back the bump and let the same sender retry at the
   same derived address. See
   `Homestead/Spec/CreateStep.lean::IsCreateDepositRevert` (now
   takes `sender`/`senderAccNonce`) and
   `Byzantium/Spec/CreateInitRevertStep.lean`.

2. **An account with non-empty STORAGE is "in use" for collision
   purposes,** even at `nonce = 0` and empty code. The naive
   `nonce > 0 ∨ code.size > 0` predicate misses tests like
   `stSStoreTest/InitCollision_*`. See
   `Constantinople/Spec/Create2Step.lean::AccountInUse`. EIP-7610
   makes this normative at Cancun; EELS enforces it pre-7610 too.

3. **Per-fork precompile-table dispatch.** Each fork's spec should
   pin the set of precompile addresses. An implementation that
   ships the wrong table (silently routing to an older / smaller
   table) is invisible at build time but produces "tx to MODEXP
   ran empty code" failures. See
   `Byzantium/Spec/PrecompileTable.lean` (`IsPrecompile`,
   `DispatchSound`) and `Istanbul/Spec/PrecompileTable.lean`'s
   `extends_byzantium` theorem.

4. **Invalid-input semantics for precompiles.** Returning "success
   with zero bytes" silently admits malformed input. EELS raises
   `OutOfGasError` for invalid bn256 points, out-of-range Fp
   coords, off-curve points, and bad ECPAIRING input size. See
   `Byzantium/Spec/Bn256Step.lean`'s `IsBn256AddFail` /
   `IsBn256MulFail` / `IsBn256PairingFail`.

5. **Post-London tx-level coinbase split.** Paris / Shanghai /
   Cancun MUST inherit London's EIP-1559 fee-market accounting:
   coinbase gets `gasUsed * priorityFee` only, `gasUsed * baseFee`
   is BURNT (not credited anywhere). An impl that defaults to
   `gasUsed * tx.gasPrice → coinbase` over-credits the miner by
   `baseFee * gasUsed` on every tx. Relations are already in
   `London/Spec/FeeMarket.lean::IsCoinbaseCredit` /
   `IsBaseFeeBurnt` / `IsTxFeeDebit` — Paris/Shanghai/Cancun
   spec files should add their own `processTransaction` clause
   that references these (or extends them with the fork's
   per-tx-type effective-price rule).

6. **Fork-inheritance chain integrity.** Each fork's `step1` must
   fall through to the IMMEDIATE predecessor's `step1`, not skip
   ahead to an older one. Paris was falling through directly to
   Byzantium, silently bypassing both London (EIP-3198 / 3529 /
   3541) and Berlin (EIP-2929 warm/cold for SLOAD / SSTORE /
   BALANCE / EXTCODE* / CALL family). Every test that depended on
   EIP-2929 surcharges at Paris+ was under-charged by 2000 gas per
   cold access. The fix is a one-line edit to the dispatch table's
   default arm; the spec equivalent is to assert
   `Paris.step1 falls back to London.step1` (transitively the whole
   chain). When adding a new fork, audit the previous fork's
   inheritance chain too — silent skips don't surface as type
   errors.

If you add an implementation fix, ask: "Did the corresponding
relation in `Spec/` admit my buggy behaviour?" If yes, tighten the
relation in the same commit (or a paired follow-up). Other ports
of this codebase rely on `Spec/` as the source of truth.
