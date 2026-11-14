# Deriving the effect layer from the Lean spec (stages 1–6, 2026-10-26)

The effect layer is the hand-written Lisp that changes state around the native EVM: the
host callbacks (`cb-call` 430 lines, `cb-create` 332, `cb-selfdestruct` 84 before this
work, `cb-sstore`), `apply-tx` (423), `run-evm-tx` and the fee settlement, the sweeps
(`sweep-empty-touched!`, `finalize-selfdestructs`), the block effects (`block-system.lisp`,
`chains/ethereum.lisp`). It produces the money-flow facts and was where most of this
month's bugs lived (SELFDESTRUCT-to-self, EIP-6780 deletion timing, CREATE warming order,
EIP-7610 collision, depth-limit CREATE gas, EIP-214, EIP-3860). It is also step S0 of
the Block-STM plan: an executor can only validate
a tx's reads if every read is logged.

Stage 1 delivered one storage-view seam (§2), a typed effect IR with a Lean meaning and a
CL printer (§3), the first derived callback, `cb-selfdestruct`, proved against every
fork's SELFDESTRUCT (§4), the gates (§6) and the migration plan (§7). Stage 2 derives the
next three steps of that plan: the fee settlement as commutative deltas (§4.2), the end of
a tx — the accounts_to_delete and the EIP-161 sweep (§4.3) — and `cb-sstore` (§4.4), each
proved for every fork; three spec-fidelity fixes and three latent replay divergences came
out of it (§5).

Stage 3 closes step 3 — the SSTORE fork dispatch is emitted and `cb-sload` derived (§4.5)
— and does step 4, `cb-create` (§4.6, §4.7). Deriving CREATE first required the spec to
have ONE CREATE: the per-fork copies disagreed with EELS in several ways (§5, items 7–10) and
are now one definition, `Evm.Frontier.Vm.Create`, every fork's CREATE/CREATE2 is bound to
by proof; the derived callback is proved against it for every fork and every child run.
One latent replay divergence (a reverted CREATE deleting an existing empty account) is
fixed (§5, latent divergences).

Stage 4 does step 5, `cb-call` (§4.8, §4.9). As for CREATE, the spec first got ONE call
family, `Evm.Frontier.Vm.Call`: the per-fork copies disagreed with EELS on the EIP-161
touch, the RIPEMD-160 exemption, a REVERTed child's warm-ups, the precompile tables and
EIP-7702 (§5, items 14–18). The derived callback is proved against it for every fork,
every precompile table and every child run; the hand-written callback's touch rule was
broader than EELS (§5, latent divergences).

Stage 5 does steps 6 and 7. The spec first got ONE transaction, `Evm.Frontier.Vm.Tx`, a port
of EELS `process_transaction` every fork's `processTransaction` is (§4.10): Prague, Osaka
and Amsterdam had run the Byzantium loop (§5.5, closed). `apply-tx` is now one emitted term
proved against it for every fork, frame run, precompile table and authority recovery
(§4.11). The fixture runner runs blocks on the generic driver's pipeline, so Prague, Osaka
and EIP-7702 are covered (§4.12), and the block's rewards and withdrawals are a derived term
(§4.13). Production divergences found are in §5 (stage 5); §7 gives what remains.

Stage 6 does step 8, the system calls (§4.14). The spec first got ONE system transaction,
`Evm.Frontier.Vm.System` (EELS `process_unchecked_system_transaction` /
`process_checked_system_transaction`), which Cancun's and Prague's `applyBlock` now call; the
system path is its own emitted term, proved for every fork and every chain rule. Owner
decision: EELS on Ethereum (nothing warm at the start, GASPRICE the base fee, no end of tx);
Arc keeps arc-node's rule (revm `run_system_call`), stated and proved separately.

## 1. Trust model

| layer | how it is trusted | where |
|---|---|---|
| the fork specs (`Evm.<Fork>.Vm`) | spec fidelity: EELS clause by clause (fixes in this work, §5) | `lean/Evm/*` |
| the effect terms vs the fork specs | **proved** (`selfdestruct_refines`, `settle_refines`, `endTx_refines`, `sstore_refines`, `sload_refines`, `create_refines` + `create_binding`, `call_refines` + `call_binding`, `tx_refines` + `apply_tx_refines`, `credits_refines`, `system_refines` + `checked_refines`; no `sorry`, axioms `propext`/`Quot.sound`, and `Classical.choice` in `createGas_eq` and `call_refines`) | `lean/Evm/CL/Effect*Proof.lean` |
| the emitted CL vs the term | by construction: `Stmt.toCL` prints each primitive as one seam call; the printer is the trusted base (as for `Pred.toCL`/`Expr.toCL`) | `lean/Evm/CL/EffectIR.lean` |
| each seam call vs its primitive's meaning | **assumed**: the contracts in §3.2, hand-written CL | `src/state/world.lisp` "The storage view" and the journal |
| the remaining hand-written callbacks | replay gates and fixtures only (§7 retires them) | `src/evm/` |

## 2. The storage view (seam)

One accessor set in `src/evm/` ("The storage view") is now the only path from
the effect layer to world state:

| accessor | reads / writes | event kind |
|---|---|---|
| `balance-of`, `(setf balance-of)`, `balance-clear!` | balance (absent = 0) | `:balance` |
| `nonce-of`, `(setf nonce-of)`, `nonce-clear!` | nonce | `:nonce` |
| `code-of`, `(setf code-of)`, `code-clear!` | code (absent = `#()`) | `:code` |
| `storage-of`, `(setf storage-of)` | one slot | `:storage` (slot = the slot) |
| `account-marked-p`, `account-mark!`, `account-unmark!` | the existence set (empty-but-present accounts) | `:present` |
| `storage-wipe-journaled!` | EELS `destroy_storage` at a creation: every nonzero slot (RAM + cold tier) to 0, one journaled storage write each | `:storage` per slot |
| `account-delete!` | EELS `destroy_account` (SELFDESTRUCT at tx end, EIP-161 sweep, the zero-fee coinbase rule); owns the incremental root check's whole-account re-read | `:account` |
| `balance-delta!` | balance += amount as a commutative delta (the settlement credits, OP's fee vaults); reads nothing; a zero delta is no access | `:delta` — `(:delta :balance block tx addr 0 amount)`, no read, no write |
| `account-uncreate!` | journal entry 10 (undo a CREATE) | `:account` |

What the accessors own, so no call site can forget it:

* an observer's account pre-image (the first write of a tx snapshots nonce/balance/code;
  `factlog-acct-write!` is gone);
* the **read/write stream**: while a subscriber takes it (`:on-access`;
  `*capture-reads*`, a subscriber property, no env toggle), `observe-tx-begin!` opens the
  tx's stream (`*view-log*`) and every access is a flat record — `(:read kind block tx addr
  slot value)` and `(:write kind block tx addr slot pre post)`, no list per access
  (`fw-access!`, `src/evm/stream.lisp`) — in the same buffer as the fact rows. This is the logged read set of `lean/Evm/Parallel/Reads.lean` (`Faithful`: the
  logged value is the value the view returned). Loading (`fault-account!`/`fault-slot!`
  hooks) and persistence run with the stream closed. Off, an access costs one
  special-variable test.

The generated journal-restore dispatch (`spec-restore-journal-entry`, emitted from
`HostEmit.RestoreAction.toCL`) calls the view too, so a revert is a logged write.

**Inventory.** Direct world-table accesses in the effect layer, before → after: 60 → 0
(replay-cl 39 = 36 `gethash`/`remhash` on the world tables + 3 raw storage get/set in
`cb-sload`/`cb-sstore`; arc-precompiles 9; block-system 2; generated restore dispatch 10
table references in 5 arms). The readiness audit counted 91 at `1272329`; the
`balance-of`/`nonce-of` accessors that landed since had absorbed the balance/nonce
`gethash` sites, which now log too. Left on the raw tables by design (not tx reads):
loading (`populate-world`, `chain-io`, `state-anchors`), persistence (`snapshot-world`,
`mpt-live`), fixture checks (`compare-post`, `capture-tx-state`), and an observer's own
pre-image/post reads.

Superseded and deleted: the #262 `EITA_RWSET` telemetry (`rw-read!`/`rw-write!` at 16
sites; keys only; nonce/code/presence reads missing; its consumer `conflict-graph.py` was
already gone).

## 3. The effect IR (`lean/Evm/CL/EffectIR.lean`)

### 3.1 Syntax

Sorts with explicit widths (`Ty.width`: bool 1, addr 160, word 256, gas 64) — a printer
for another target (Rust) needs no semantics the IR does not state:

* `AExp` (addr): named inputs.
* `WExp` (word): `var`, `zero`, `balance a`, `add/sub/mul` (wrapping mod 2^256, printed
  through the `u256` seam), `sload a k` (a slot), `orig a k fb` (the slot's cached
  original value, else `fb`).
* `BExp` (bool): literals, vars, `not/and/or`, `forkGe n` (the fork ordinal), `addrEq`,
  `pos w`, `weq a b`, and the world queries `present a` (`accountExists`), `dead a` (EELS
  `is_account_dead`), `created a` (EIP-6780), `destroyed a` (accounts_to_delete).
* `GExp` (gas): `lit`, `ofBool`, `forkOrd`, `ite`, `add`, and `formula0/formula1` — a
  `GasEmit.Expr` printed as a call to its emitted `spec-*` defun, so each number keeps one
  owner.
* `Stmt`: `skip`, `seq`, `ite`, `letW`, `letB`, `warm gate a x s` / `warmSlot gate a k x s`
  (EIP-2929; bind "was cold"), `forEach set x body` (one bounded loop: the body once per
  member of a per-tx set — `destroyed` or `touched` — as it stands at loop entry; a list
  fold in Lean, a `maphash` in CL, order-independent by `destroy_perm`/`sweep_perm`), and
  the effect primitives below.

### 3.2 Primitives: meaning and seam contract

The Lean meaning (`Stmt.run`) is over `HState` — exactly the parts of the spec's
`Frontier.Vm.Environment` an effect can change (`state`, `selfDestructSet`, `touched`,
`accessedAddresses`, `createdAccounts`, `refundCounter`; `HState.ofEnv`) plus the gas the
callback returns and its transfer facts.

| primitive | Lean meaning | CL (one seam call) | contract the CL must meet (assumed) |
|---|---|---|---|
| `balance a` | `state.getBalance a` | `(balance-of *current-world* a)` | balance-of = getBalance (absent = 0) |
| `present a` | `state.accountExists a` | `(world-account-present-p a)` | = `accountExists` (seam contract) |
| `dead a` | absent or `isEmpty` | `(world-account-empty-p a)` | = `is_account_dead` (seam contract) |
| `created a` | `a ∈ createdAccounts` | `(created-p! a)` | native created set = EIP-6780 set |
| `destroyed a` | `a ∈ selfDestructSet` | `(destroyed-p a)` | the account id's per-tx bit; `*selfdestructed*` lists the ids = accounts_to_delete |
| `warm g a x s` | if g: x := a ∉ accessed; accessed ∪= {a} | `(let ((x (and g (access-addr! a)))) …)` | `access-addr!` = `warmAddr` (returns cold), journaled natively |
| `fault a` | identity | `(fault-account! a)` | loads only, never changes a value |
| `touch a` | fork ≥ 4: touched ∪= {a} | `(touch! a)` | = `touchAddr`, journaled (type 12) |
| `markPresent a` | `state.touchAccount a` | `(mark-account-present! (current-arena) a)` | = touchAccount, journaled (type 11) |
| `markDestroyed a` | selfDestructSet ∪= {a} | `(mark-destroyed! a)`: guarded bit + list + journal type 3 | journaled |
| `refund g` | refundCounter += g | `(refund-add! g)` | native counter, journaled |
| `setBalance a w` | `setAccount a {… balance := w}` | `journal-balance!` + `(setf balance-of)` | journaled (type 2) |
| `credit a w` | `addBalance a w` | `journal-balance!` + `incf balance-of` | no 2^256 wrap occurs (total supply ≪ 2^256) |
| `transferFact k s d w` | facts ++ [(k,s,d,w)] | `(observe-transfer! k *call-depth* s d w)` | revert-scoped like the journal |
| `charge g` | gas += g | `(incf %gas g)` | the defun returns `%gas` to the native handler |
| `delta a w` | w = 0: nothing; else `addBalance a w` | `(balance-delta! *current-world* a w)` | not journaled (tx level only); no 2^256 wrap; logged as a delta |
| `deleteAccount a` | `State.deleteAccount a` | `(account-delete! *current-world* a)` | = `destroy_account`; not journaled (tx level only) |
| `add/sub/mul` | `BitVec 256` arithmetic | `(u256 (op a b))` | `u256` = mod 2^256 |
| `forEach s x b` | `l.foldl (b with x := a)` over the list | `(dolist (x (tx-set-addrs *selfdestructed*/*touched*)) …)` | the set's ids hold the list's members once (the bit is set at most once; the spec's sets are duplicate-free, `insertSet`); any order (`destroy_perm`, `sweep_perm`); `b` does not change the set |
| `sload a k` | `getStorage a k` | `(storage-of *current-world* a k)` | storage-of = getStorage |
| `faultSlot a k` | identity | `(fault-slot! a k)` | loads only |
| `warmSlot g a k x s` | if g: x := (a,k) ∉ accessedStorageKeys; insert | `(let ((x (and g (access-slot! a k)))) …)` | `access-slot!` = `warmSlot`, journaled natively |
| `origRecord a k w`, `orig a k fb` | `cacheOriginal` / `getOriginal` on `storageOriginals` | `(orig-record! a k w)`, `(orig-get! a k fb)` | the native table records every slot at its first read or write in the tx and is not journaled; where it holds an entry the spec's (frame-reverted) cache lacks, the value is the slot's current one (no write without a prior record) — so `orig-get!` answers `getOriginal`; at Constantinople/Istanbul it answers `originalState` (`horig`) |
| `sstoreGas o c n cold` | `(cost, refund') := sstorePlan fork refund o c n cold`; refund := refund'; gas += cost | `(sstore-gas-native (ts-refund) o c n cold)`, then `refund-add!` of the difference | `sstore-gas-native` marshals the words and calls the emitted dispatch (below); each native = its spec schedule (`Evm.CL.ARM64.SstoreGasSem`) |
| `setStorage a k w` | `setStorage a k w` | journal entry 0 + `(setf storage-of)` | journaled |
| `ret w` | out := w (the pushed word) | `(setf %out w)`; `toDefunRet` returns `(values %gas %out)` | the wrapper pushes it |
| `sstoreGas` dispatch | `SstoreSched.ofFork` → `SstoreSched.plan` | `spec-sstore-gas-dispatch` (emitted from `ofFork` and the routine names; the defcfuns too) | each `eita_sstore_gas_<name>` = its `plan` (`SstoreGasSem`); the dispatch is emitted, not assumed |
| `bumpNonce a` | `setAccount a {nonce + 1}` | `journal-nonce!` + `incf nonce-of` | journaled (type 9) |
| `markCreated a` | created := `a :: created` unless in | `journal-created!` + `created-insert!` | the type-10 entry records whether `a` was present; its restore drops code/nonce/storage and the presence it added (§5, latent divergences) |
| `save x s`, `rollback x` | bind x := the state; restore it (keeping gas, result, return data) | `(let ((x <journal count>) (x-facts (observe-mark))) …)`; `revert-journal-to` + `observe-revert!` | `revert-journal-to` restores the view to the save point (JournalSpec for storage; the type-10 precondition: the account had no code, nonce or storage before — the collision rule) |
| `runChild s n w fwd r body` | r := `c.child h fwd` (an oracle; the theorem instantiates it with the spec's `runSub` on the spec's own child frame); on success the state is the child's | `(run-init-frame! s n w init-code fwd)` → `(status gas-left output)` | = `runSub` on `Evm.Frontier.Vm.Create.child`: the native interpreter on the init code, journal absorbed; `:revert` iff REVERT, `:halt` iff exceptional (no output pointer) |
| `childErr`/`childRev`/`childEF`/`childGas`/`childLen` | the result's parts | `(child-status r)` etc. | — |
| `depositCode a r` | `setAccount a {code := r.out}` | `(setf code-of)` (unjournaled: the type-10 entry undoes it) | — |
| `retData r` | rdata := r.out | `(setf %rd …)`; `toDefunChild` returns `(values %gas %out %rd)` | the wrapper installs it as returndata |
| `frameRow …` | identity | `with-observed-frame` around the init frame | observers only |
| `collides a` | `Create.collides` (nonce, code — EIP-684) | two view reads | — |
| `wipeStorage a` | `state.destroyStorage a` | `(storage-wipe-journaled! a)` | = `destroyStorage` on the view (the cold tier's slots through `*cold-storage-map-hook*`); journaled per slot |
| `nonceMax a`, `wlt a b`, `iteG`, `GExp.var/sub/formulaF` | as named (`sub` truncates) | `(= nonce 2^64-1)`, `<`, `(max 0 (- a b))`, `(name arg *fork-ord*)` | — |
| `chainVeto s d w` | `false` (no chain rule: outside the Ethereum theorem) | `(eq :revert (chain-frame-init s d w))` | NIL on Ethereum (no hook installed) |
| `letA x p a b s` | x := if p then a else b | `(let ((x (if p a b))) …)` | — |
| `kindEq n`, `touchedHas a`, `AExp/WExp.lit n` | the `kind` input is n; a ∈ touched; a constant | `(= kind n)`, `(touched-p a)`, `n` | `*touched*` = the touched set |
| `callPlan cold vf na d g a s` | `charge`/`fwd`/`stip` := `Call.plan (Rules.ofOrd fork) …` | `(call-gas-plan …)` → the `_eita_call_gas*` natives by fork | each native = its spec plan (`Evm.CL.ARM64.CallGasSem`); the requested gas is saturated at 2^64 − 1 by the native handler, which no plan's outcome can tell from the u256 (every pool is below 2^64) |
| `pre a` | `(Ctx.pre a).isSome` | `(precompile-address-p a)` | = the fork's table (`Call.precompiles`; OP flags: `*p256verify*`) |
| `runPre a g r body` | r := the fork's precompile at a on `Ctx.input` with gas g (`.err` on failure), the world unchanged | `(precompile-run! a input-ptr input-len g)` → `(status gas-left output)` | `run-precompile` = the spec's table; failure consumes the gas |
| `runCall g r body` | r := `c.child h g` (the theorem: `runSub` on `Call.child`) | `(run-call-frame! kind self to value input-ptr input-len code-addr g)` | = `runSub` on `Call.child`: the native interpreter on the code address's code (the delegate's under EIP-7702), caller/value/static by kind; empty code returns at once with all its gas (a property of the interpreter); journal absorbed |
| `callRow …` | identity | `with-observed-frame` (kind, selector, input length, gas used = charged + stipend − charge) | observers only |
| `chainCall a … rest` | `rest` (no chain precompile) | Arc's `*chain-precompile-hook*` via `chain-precompile-call!` (rolls back to the save point on failure) | outside the Ethereum theorem |
| `chainCallVeto g s d w r veto rest` | `rest` | `(chain-frame-init s d w :emit-log nil)` before the fail-fast | outside the Ethereum theorem |
| `chainLog s d w` | identity | `*chain-value-transfer-log-hook*` (Arc's EIP-7708 log) | outside the Ethereum theorem |
| `warmSys` | accessed ∪= `Ctx.sysSeed`, in order | `(warm-system-seed!)`: `access-addr!` over `*system-seed*` | `*system-seed*` = the chain rule's `System.Rule.seed` (EELS: empty; Arc: `BlockSystem.systemSeed`) |

Emitter: `Stmt.toDefun` (printed by `lake exe emitHostCL` into
`src/generated/host.lisp`); `scripts/verify-host-emit.sh` fails on drift of the
generated file and now also builds `Evm.CL.EffectSelfdestructProof` and rejects a `sorry`
in the three effect modules.

## 4. The first derived callback: `cb-selfdestruct`

`lean/Evm/CL/EffectSelfdestruct.lean` — `term`, one IR term for every fork; emitted as
`spec-selfdestruct-effect`. The hand-written `cb-selfdestruct` is now a wrapper: read the
two addresses, run the chain override (Arc's `*chain-selfdestruct-hook*`, outside the
theorem: `Evm.Arc.Spec.NativeCoin.runSelfdestructCheck`), call the emitted function,
return its gas.

**The callback's part.** The native handler pops the beneficiary, raises EIP-214's
static violation before any gas (Byzantium+), charges the base (`baseGas`: 0 to
Homestead, 5000 from Tangerine Whistle), calls the callback, charges what it returns and
halts. Everything else is the term: EIP-161 touch (SD+), EIP-2929 warm-up and cold
surcharge (Berlin+), the new-account surcharge (none to Homestead; absent beneficiary at
TW; dead beneficiary and value moving from SD), the accounts_to_delete mark and its
24000 refund (first mark; 0 from London; from Cancun only for a same-tx creation —
EIP-6780), the balance move (a self-beneficiary burns before Cancun, keeps it from
Cancun unless created this tx), the pre-Spurious existence of the beneficiary. Deletion
happens at tx end (`finalize-selfdestructs`, EELS `process_transaction`) on every fork.

**Theorem** (`Evm.CL.EffectSelfdestructProof.selfdestruct_refines`): for every fork `f`
and frame with the beneficiary word on the stack, not static, at an existing executing
account (`hself`, the one stated assumption — a frame only runs code at an existing
account):

* if the spec's SELFDESTRUCT (`specSelfdestruct f`) succeeds, its environment `Agree`s with
  the term's state — existence, every account and storage slot (extensionally: the spec's
  association lists differ only in order), the destroyed/touched/warm sets as sets, the
  created set, the refund counter — and the gas it charged is `baseGas + term gas`;
* if it fails, it is out of gas, exactly when the gas left is below `baseGas + term gas`.
  (The CL charges after the effects; on that failure the frame halts exceptionally and the
  journal unwinds every write the term made.)

The proof is one success and one out-of-gas lemma per handler (Frontier, Tangerine Whistle,
Spurious Dragon, Berlin, London, Cancun-family), sharing one tactic script (`sd_inputs`,
`sd_field`, `sd_gas`): unfold the handler, name the inputs, case-split on the conditions
the term and the handler branch on, close each `Agree` field and the gas equation.

`specSelfdestruct f` is the handler the IR trampoline binds, by `rfl`
(`selfdestruct_binding_pre`: `Terminator.handler`; `selfdestruct_binding_<fork>`:
`Terminator.stepHandler` = Cancun's `doSelfdestruct` from Cancun, discharged by
`runYieldOf`).

## 4.2 The fee settlement as deltas (`lean/Evm/CL/EffectSettle.lean`)

`refundTerm` (the sender's `(gas-limit − gas-used) × egp`) and `coinbaseTerm` (the fault,
then `fee = gas-used × (egp − base fee)` as a delta; when the fee is zero: from Spurious
Dragon destroy a dead coinbase, before it bring the coinbase into existence). Emitted as
`spec-gas-refund-effect` and `spec-coinbase-fee-effect`; `run-evm-tx` calls them in order
after `spec-tx-gas-used`; the second is the default `*chain-fee-hook*`, Arc's hook calls
it with base fee 0 (Arc does not burn), OP's vault hook stays a chain hook (its credits
are `balance-delta!` too). The fixture runner's duplicate settlement (and refund cap,
without the EIP-7623 floor) is gone: it calls the same three defuns.

**Burns.** The base fee (London+) and the blob fee (Cancun+, debited upfront with the gas
at `blobs × 131072 × spec-blob-base-fee`) are burned by being credited nowhere: the two
credits are exactly `(gas-limit − gas-used) × egp` and `gas-used × (egp − base fee)`.

**Theorems** (`Evm.CL.EffectSettleProof`):

* `settle_refines`: for every fork ordinal, `refundTerm; coinbaseTerm` leaves a state that
  agrees (existence, every account, every slot) with `specSettle k` — `Frontier.settleFees`
  to Tangerine Whistle, `SpuriousDragon.settleFees` from Spurious Dragon, the functions
  every fork's `processTransaction` calls — with `refundWei = (gl − gu) × egp`, `minerWei =
  gu × (egp − bf)`, and changes nothing else. Assumptions: `gu ≤ gl`, `bf ≤ egp` (EELS
  rejects `max_fee_per_gas < base_fee_per_gas`), the sender exists, only existing accounts
  carry storage (`WF`), and a non-zero fee does not wrap the coinbase balance to 0 (the spec
  tests the wrapped sum; the delta reads nothing).
* `delta_is_rmw`: a non-zero delta is the serial read-modify-write `balance := balance + w`.
* `delta_fold_reads`: deltas folded in index order with the term's meaning leave every
  balance at `Reads.applyDeltas` of the same deltas (mod 2^256) — so `applyDeltas_comm`,
  `applyDeltas_ext` and `deltas_deferred` hold of the emitted credits; `delta_fold_order`:
  any order or grouping with the same per-key sums gives the same balances.

The read stream (§2) now logs the credits as `:delta` events; the checker folds them in
index order (Reads' `Result.apply`) and validates every later read of a delta key against
the folded value (§6).

## 4.3 The end of a tx (`lean/Evm/CL/EffectEndTx.lean`)

`destroyTerm` = `forEach destroyed a (deleteAccount a)` (EELS accounts_to_delete, every
fork; membership — every first SELFDESTRUCT before Cancun, same-tx creations from Cancun —
is `cb-selfdestruct`'s); `sweepTerm` = from Spurious Dragon `forEach touched a (if dead a
then deleteAccount a)`. Emitted as `spec-destroy-effect` / `spec-sweep-effect`; the
hand-written `finalize-selfdestructs` and `sweep-empty-touched!` are deleted. The sweep
moved out of `apply-tx` (where it ran before the gas refund and the coinbase credit) to
the end of the tx, the EELS order. `run-evm-tx`, the fixture runner and OP deposits call
both; system calls and the EIP-4788 call keep only the sweep they always had (EELS system
txs destroy nothing, and from Paris sweep nothing: EIP-7523 leaves nothing to find).

**Theorems** (`Evm.CL.EffectEndTxProof`), through one closed form, `fold_obs` (folding
"destroy `a` if `P`" over a list destroys exactly the members `P` held of at the start,
when deleting `a` never changes what `P` sees of another address):

* `endTx_refines`: `destroyTerm; sweepTerm` agrees with `Frontier.destroyAccounts` (to
  Tangerine Whistle) / `SpuriousDragon.finishTx` (from Spurious Dragon) and changes nothing
  else. Assumption `WF`. The spec sweeps "exists and empty"; the term "dead" — destroying an
  absent account changes nothing in a `WF` state. The zero-fee coinbase rule uses the same
  `dead` test (a storage-only account the Lisp world does not mark present is destroyed, as
  EELS destroys it).
* `destroy_perm`, `sweep_perm`: the result depends on the sets only as sets — the CL's
  `maphash` order is irrelevant.
* `sd_form_closes` — **stage 1's open item (§5.3), closed at the tx boundary.** From
  Spurious Dragon the SELFDESTRUCT handlers credit the beneficiary only a non-zero value and
  touch it always; EELS credits it always (an absent beneficiary comes into existence) and
  touches it only if it is then an existing empty account. For any state, beneficiary,
  value and any other destroyed and touched sets, `finishTx` leaves the same state from
  both. **Residual assumption** (not proved): between the SELFDESTRUCT and the end of the
  tx nothing observes whether an empty beneficiary exists — from Spurious Dragon every gas
  rule asks `is_account_dead` (absent or empty), and EXTCODEHASH answers 0 for both
  (EIP-1052); an account non-empty at the SELFDESTRUCT cannot become empty before the end of
  the tx without being destroyed (nonce never falls, code leaves only by deletion, and
  balance leaves only by executing code or being a sender).

## 4.4 `cb-sstore` (`lean/Evm/CL/EffectSstore.lean`)

**The callback's part.** The native SSTORE handler pops key and value, raises EIP-214's
static violation, applies the EIP-2200/EIP-1706 sentry (Istanbul+: out of gas at gas left
≤ 2300 — `AsmCore.sstoreSentry`, before the callback), calls the callback, charges what it
returns. The term: fault the slot, read it, warm it (Berlin+), record its original at first
touch, run the fork's schedule `sstorePlan` (EIP-1283 at Constantinople, EIP-2200 at
Istanbul/Muir Glacier, EIP-2929 at Berlin, EIP-3529 from London, the legacy schedule
otherwise) — it sets the refund counter and the gas — and write the slot if it changes
(journaled). Emitted as `spec-sstore-effect`; `cb-sstore` is a three-line wrapper (and the
`EITA_TRACE_SSTORE` toggle is gone: the read stream carries every slot read). Since owner note 6
step 6 the term is printed as C only (`Evm.CL.EffectC`, `eita_spec_sstore_effect`, the one
execution path; docs/native-storage.md): the Lisp printing and `cb-sstore` are deleted.

**Theorem** (`Evm.CL.EffectSstoreProof.sstore_refines`): for every fork `f`, with the key
and value on the stack, not static, and (Istanbul+) more than 2300 gas left: if the
handler the IR binds (`Op.handler f .sstore`, `sstore_binding`: Frontier's to Byzantium and
at Petersburg, Constantinople's, Istanbul's, Berlin's `doSstorePure`, London's
`doSstoreLondon` to Amsterdam) succeeds, its environment agrees with the term's — every
slot and account, the refund counter, the accessed slots, the original-value cache from
Berlin, nothing else changed — and charged exactly the term's gas; if it fails it is out of
gas, exactly when the gas left is below that. At Constantinople and Istanbul, whose handlers
read `originalState`, the stated assumption `horig` is the `orig-get!` contract (§3.2).
The gas schedules themselves are the natives already proved (`SstoreGasSem`); the term
uses them through `sstorePlan`, whose dispatch is emitted from the same definition since
stage 3 (§4.5).

## 4.5 `cb-sload`, and the SSTORE dispatch emitted (stage 3, `f137e5d`)

**SSTORE dispatch.** Stage 2 left one assumed seam in `cb-sstore`: `sstore-gas-native`'s
hand-written `cond` choosing the schedule by fork, a copy of `sstorePlan`'s ifs. Now one
copy: `EffectIR.SstoreSched.ofFork`. `sstorePlan` (the term's meaning) reads it, and the
emitter prints from it the dispatch — every fork ordinal listed against its schedule's
routine, London's as the `t` arm (`ofFork_ge`) — and the five `defcfun` bindings
(`eita_sstore_gas_<name>`). The schedules themselves were already proved
(`SstoreGasSem`); nothing hand-written is left between the term and them.

**`cb-sload`** (`lean/Evm/CL/EffectSload.lean`, `spec-sload-effect`): fault the slot, read
it, warm it (Berlin+), record its original at first touch (the cache the SSTORE schedules
read; the spec keeps one from Berlin), return the value (`ret`), charge the fork's price —
the spec's own constants: 50, 200 (EIP-150), 800 (EIP-1884), 2100 cold / 100 warm
(EIP-2929). The access-cost table's SLOAD row is no longer read. Since owner note 6 step 6 printed
as C only (`eita_spec_sload_effect`), with the SSTORE dispatch (`sstoreDispatchC`).

**Theorem** (`Evm.CL.EffectSloadProof.sload_refines`): for every fork, with the key on the
stack and room for the result, the handler the IR binds (`sload_binding`: Frontier's,
Tangerine Whistle's, Istanbul's, Berlin's `doSloadPure`) and the term agree — state
unchanged, accessed slots and (Berlin+) the original cache equal, the pushed word is the
term's, the gas is the term's, out of gas exactly below it.

Deleted with it: `EITA_TRACE_READS_BLOCK` and `trace-read` (3 call sites) and the
`EITA_TRACE_TX`-scoped SLOAD printout — the read stream (§2) logs every read.

## 4.6 One CREATE in the spec (`lean/Evm/Frontier/Vm/Create.lean`, `4a1462e`)

Before this, each fork carried its own `doCreate`/`doCreate2` (ten) and `.createLike` arm or
`resumeCreateOk`/`Err` (fifteen), and they disagreed with EELS and with each other (§5, items 7–11).
Now:

* `Create.native` — the opcode's part before the callback: the static check (Byzantium+),
  the pops (CREATE2's salt), the memory charge, the init code, the address (RLP of the
  creator's nonce; EIP-1014), the charge `baseOf` (GAS_CREATE, EIP-3860's 2/word, CREATE2's
  6/word);
* `Create.start` — EELS `generic_create` to `process_create_message`: out of gas below the
  charge and over EIP-3860's cap; EIP-150's 63/64; the fail-fast (depth, balance, nonce
  2^64−1); EIP-2929's warm-up; the collision rule (code, nonce — EIP-684; EIP-7610's
  storage leg was dropped in stage 4, item 12); the creator's nonce bump; the child's world
  (`childState`: `destroy_storage`, EIP-161 nonce, `touch_account`, `move_ether` of a
  non-zero value);
* `Create.child` — the child frame, marked created (EIP-6780's `mark_account_created`);
* `Create.resume` — `process_create_message`'s end and `incorporate_child_*`: an
  exceptional halt or REVERT keeps nothing of the child (REVERT returns its gas and its
  output as return data), EIP-3541's prefix, the code deposit (Frontier keeps the creation
  without code and the child's gas, later forks fail it), EIP-170's size, the code.

`Rules.ofOrd` switches the clauses by fork ordinal. Every fork's `doCreate`/`doCreate2` is
`Create.opcode` and every `.createLike` arm `Create.resume` (each one line). The Lean replay
harness confirms the fidelity fixes on the legacy Cancun corpus: stCreateTest 907 → 1063 of
1073, stCreate2 1022 → 1184 of 1188, stCodeSizeLimit 37 → 39 of 40, stRevertTest 1906 → 1914
of 1962; the legacy Constantinople corpus (the Frontier..Constantinople networks) passes as
before. (The remaining failures are tx-level creation, the Berlin-only coinbase case and
precompile touches — not the opcode.)

## 4.7 `cb-create` (`lean/Evm/CL/EffectCreate.lean`, `6bf84f2`)

**The callback's part.** The native CREATE/CREATE2 handler does `Create.native` except the
address and the charge: it pops, raises EIP-214, charges the init range's memory and copies
the init code, then calls the callback with the gas left. The wrapper `cb-create` derives
the address (`derive-create-address` / `derive-create2-address`: the seam, = the spec's
`computeContractAddress`/`computeCreate2Address`) and passes `spec-create-gas` and
`spec-create-initcode-oversize` (proved equal to `baseOf` and to the cap `start` reads:
`createGas_eq`, `oversize_eq`). Everything else — 180 hand-written lines before — is the
term, `spec-create-effect`, returning the gas used, the pushed word and the return data:
the charge and the cap; the fail-fast; warm-up, collision, nonce bump (which survive
everything below); on collision the forwarded gas lost; the child's world; the init frame
(`runChild`, inside its observed frame); its end. Two hand-written behaviours went: the
empty-init-code shortcut (the child now always runs; an empty frame halts at once) and
`nonce-clear!` on rollback (the new account's nonce bump is journaled).

**Theorems** (`Evm.CL.EffectCreateProof`):

* `create_refines`: for every fork ordinal `k`, frame, value, init code, address, charge,
  and **every child run `runSub`**, `Refines` between `Create.run (Rules.ofOrd k)` and the
  term. The term runs the child on exactly the spec's frame (`frame_eq`: same message, same
  environment — the term's state operations are the spec's own `setAccount`/
  `touchAccount`/`subBalance`/`addBalance` in the same order, so the states are EQUAL, not
  just extensionally), and given the same child result the outcomes agree: state, the
  destroyed / touched / accessed / created sets, refund counter, accessed slots and
  original cache equal; gas, pushed word and return data the same; out of gas exactly below
  the charge. Assumptions: the child never ends with more gas than it was given; the
  creator's stack has room for the result. Arc's chain veto is outside (meaning "no veto").
* `create_binding`: every fork's CREATE and CREATE2 as the IR binds them
  (`Terminator.stepHandler`, then the yield through the fork's `runYieldOf`) are the
  native part then `Create.run` at that fork's rules — 44 fork × kind cases (CREATE2 is no
  opcode before Constantinople).
* `create_spec_refines`: the two composed — the end-to-end statement per fork.

**Why the oracle is enough.** `runSub` is arbitrary: the theorem does not depend on how the
child runs, only that the callback hands the child the same frame the spec does and treats
its result as the spec does. The child's own effects are whatever `runSub` does — the native
interpreter in the replay, the same callbacks recursively (CALL, SELFDESTRUCT, SSTORE, …,
each with its own theorem or, for `cb-call`, still hand-written).

## 4.8 One CALL family in the spec (`lean/Evm/Frontier/Vm/Call.lean`, `423b863`)

Before this, each fork family carried its own `doCall`/`doCallcode`/`doDelegatecall`/
`doStaticcall` (seventeen), `.callLike` and `.precompile` arms (thirty) and resume helpers,
and they disagreed with EELS and with each other (§5, items 14–18). Now:

* `Call.native` — the opcode's part before the callback: the pops (7, or 6 without a
  value), EIP-214's static check, the memory charge for both ranges, the input;
* `Call.start` — EELS `call`/`callcode`/`delegatecall`/`staticcall` and `generic_call` to
  `process_message`: EIP-2929's warm-up of the target; EIP-7702's `access_delegation` (the
  delegate warmed and charged with the base, precompiles disabled; gated by
  `env.pragueDelegation`); `calculate_message_call_gas` (`Call.plan`: the three existing
  `callGasPlan`s, moved here unchanged, by fork); out of gas; the fail-fast — balance for
  CALL/CALLCODE, then depth; the child's message (`childMsg`: caller and value per kind,
  the code — the delegate's —, the static flag) and world (`touch_account` before EIP-161,
  `move_ether` for a CALL with a value);
* `Call.runChild` — `execute_code`: the fork's precompile at the code address (unless
  disabled) or the child frame (`runSub`); `Call.precompiles k` is each fork's table
  (Frontier; +0x05–0x08; +0x09 and EIP-1108; EIP-2565 MODEXP; +0x0a; +EIP-2537; EIP-7883
  MODEXP and 0x100), read in the caller's environment (the OP-Stack rules are flags there:
  `Cancun.Vm.Effect.opPrecompiles`);
* `Call.resume` — `generic_call`'s end and `incorporate_child_on_*`: an exceptional halt
  keeps nothing (its gas is gone), a REVERT keeps its gas and output, a success merges the
  child; from EIP-161 a success touches its target if existing and empty, a failure keeps
  0x03 touched under the RIPEMD-160 exemption; the output copied into memory (at most
  `retLen` bytes); the flag.

Every fork's call handlers are `Call.opcode` and every `.callLike` arm is `Call.resume` on
`Call.runChild` with the fork's table (one line each). Stated choices (in `Call.lean`):
from Spurious Dragon EELS's `touch_account` also creates an absent target until the sweep,
the spec does not (`sd_form_closes`' residual); the touch and the exemption are kept after
Paris (EIP-7523: nothing to sweep); the exemption's first leg (0x03 in a failed child's
touched set) applies to a REVERTed child only — an exceptionally halting child's
environment is not returned by the spec's child run, and the case needs 0x03 to exist
empty before the child (on mainnet, around block 2,675,119).

The Lean replay harness, legacy Cancun corpus (before → after, of total):
stPreCompiledContracts 3704 → 4851 of 4966, stPreCompiledContracts2 1287 → 1393 of 1655,
stStaticFlagEnabled 168 → 204/204, stStaticCall 2855 → 2871/2871, stRevertTest 1914 →
1962/1962, stReturnDataTest 1238 → 1254/1254, stCreate2 1184 → 1188/1188, stRandom2 1322 →
1326/1326, stSystemOperationsTest 484 → 485/485. Over 103 directories of the Cancun and
Constantinople corpora: 6,813 → 5,435 failures, no new one; the Constantinople corpus
passes as before. (What remains is the MODEXP/BLAKE2F precompile bodies and tx-level
creation/fees, not the call.)

## 4.9 `cb-call` (`lean/Evm/CL/EffectCall.lean`, `14a0e17`)

**The callback's part.** The native CALL-family handler pops the operands (a missing value
is 0), raises EIP-214's static violation, charges the memory expansion of both ranges and
calls the callback with the target, value, input, requested gas (saturated at 2^64 − 1)
and its gas left; afterwards it installs the return data, copies at most `retLen` bytes
into memory, pushes the flag and charges the gas used. The wrapper `cb-call` reads the
operands and resolves EIP-7702's designator (`deleg`, under `*prague-delegation*`).
Everything else — 438 hand-written lines before — is the term, `spec-call-effect`:
warm-ups (target, delegate), the plan, out of gas, the save point, (Arc's veto), the
fail-fast, the child's world, inside its observed call frame (Arc's chain precompile)
the fork's precompile or the child frame, and its end.

**Theorems** (`Evm.CL.EffectCallProof`):

* `call_refines`: for every fork ordinal `k`, opcode hand-over `n`, precompile table and
  **every child run `runSub`**, `Refines` between `Call.run (Rules.ofOrd k)` and the term.
  The term runs the child on exactly the spec's frame (`frame_eq`) and the precompile on
  the same input and gas; given the same result the state, the destroyed / touched /
  accessed / created sets, refund counter, accessed slots and original cache are equal;
  gas, flag, return data and the caller's memory (the native copy-out) the same; out of gas
  exactly below the charge. Assumptions: a child never ends with more gas than it got
  (`hmono`); a precompile never returns more gas than it got (`hpmono`); the caller's stack
  has room for the flag. Arc's chain rules are outside (meaning "none").
* `call_binding`: every fork's CALL, CALLCODE, DELEGATECALL and STATICCALL as the IR binds
  them (`Terminator.stepHandler`, then the fork's `runYieldOf`) are `Call.native` then
  `Call.run` at the fork's rules and table — 88 fork × kind cases (DELEGATECALL from
  Homestead, STATICCALL from Byzantium).
* `call_spec_refines`: the two composed, per fork.

Deleted with it: `HostEmit.newAccountCharged`/`callShouldFail`, their emitted defuns and
the orphan `HostEmitSpec`; the relational CALL layer (§4.8's commit).

## 4.10 One transaction in the spec (`lean/Evm/Frontier/Vm/Tx.lean`, `49aadec`)

Before this, sixteen forks carried their own `processTransaction`, and Prague, Osaka and
Amsterdam ran the Byzantium loop (§5.5): no EIP-1559 split, no base-fee burn, no blob fee,
no EIP-7702, and a tx straight to a precompile never ran the precompile. Now every fork's
`processTransaction` is `Tx.run k` at its ordinal, a port of EELS `process_transaction`,
`check_transaction`, `validate_transaction`, `prepare_message` and `process_message_call`
(EELS master, fetched 2026-10-26; the module header cites the clauses):

* `Tx.rules` / `Tx.invalid` — the validation, rule by rule in EELS order: the type; the
  intrinsic gas and from Prague the EIP-7623 floor within the limit; EIP-3860; EIP-2681;
  EIP-7825 (Osaka); the EIP-1559 fee fields; the EIP-4844 blob fields (the KZG version byte,
  EIP-7594's cap from Osaka, the blob base fee); type 3/4 cannot create; type 4 carries
  authorizations; the nonce; the balance against the maximum cost; EIP-3607 (code, unless a
  delegation designator from Prague);
* the prologue — the nonce, then `gas × effective price + blob gas × blob base fee`; the
  accessed sets (precompiles, sender, target, EIP-3651's coinbase, the access list);
* `Tx.message` — a creation (`Create.collides`, `Create.childState`/`child`, the deposit), or
  a call: from Prague the authorization list (`authorize`: EELS `set_delegation`, the 12,500
  refund for an authority that exists), the target's delegation, then `Call.runChild` with
  the fork's precompile table; the snapshot after the authorizations;
* the end — `GasEmit.txGasUsed` (refund cap, floor), `specSettle`, `destroyAccounts`, the
  sweep; the fee settlement and end-of-tx functions moved to `Evm.Frontier.Vm.Settle`.

Each fork passes its trampoline and precompile table; Prague passes
`Prague.Utils.recoverAuthority`, Osaka and Amsterdam their own trampolines. `Replay.lean`
decodes typed txs into `Tx.Tx` (`RawTransaction.toTx`). Stated choices: Amsterdam's own tx
level (state-gas reservoir, block access list) is not in the Lean Amsterdam spec, it runs
Osaka's; the Paris+ touch and sweep are kept (EIP-7523).

The Lean replay harness over 103 legacy Cancun and Constantinople directories: 5,546 → 5,529
failures, none new (tx-level creation warming at Berlin, the fork's precompile table at the
tx level — `modexpRandomInput` ×10 needs EIP-2565 —, init code and the EF prefix at the tx
level: `CrashingTransaction`, `codesizeInit`, `manualCreate`, `TransactionCreateSuicideInInitcode`,
`CREATE_ContractSuicideDuringInit_WithValueToItself` at Berlin, `CreateTransactionRefundEF`,
`Opcodes_TransactionInit_d131` at Shanghai).

## 4.11 `apply-tx` (`lean/Evm/CL/EffectTx.lean`, `ba77163`)

**The term**, emitted as `spec-tx-effect`: fault the sender and the target; the validation
as one `cond` of rejections (`validateFrom` over `Tx.rules`, the reason index in `%rej`);
the charge (none for a system call); the warm-ups (`warmTx`); from Prague `forAuths` over
the authorization list (`recoverAuth`, `setDelegation`, the refund) and the target's
delegation (`letDeleg`, warmed); the snapshot; in the observed top frame (`txRow`) a creation
or a call — the frame (`runTx`) or the fork's precompile (`runPreTx`), Arc's chain
precompile and veto outside the theorem — and the rollback. New IR: `reject`, `letLt`,
`debit`, `warmTx`, `forAuths`, `recoverAuth`, `setDelegation`, `letDeleg`, `runTx`,
`runPreTx`, `txRow`, the chain arms; `codeEmpty`, `delegated`, `ge`, `nonceIs`; gas `ofWord`,
`nonce`, `mul`.

`apply-tx` (src/evm/) is now the inputs the term reads — the creation address, the
calldata byte counts, the access list's sizes (the seam the emitted intrinsic-gas formulas
read), the blob version check — and one call; `run-evm-tx` is `apply-tx`,
`spec-tx-gas-used`, the derived settlement and the derived end of tx. System calls
(`:system`) and OP deposits (`:checked nil`, `:egp 0`) run the same term.

**Theorems** (`Evm.CL.EffectTxProof`, no `sorry`):

* `validate_run`: the term rejects exactly the txs `Tx.invalid` rejects (the first failing
  rule's index);
* `tx_refines`: for every fork ordinal, block environment, world, sender and tx, **every**
  precompile table `pre`, frame run `runSub` and authority recovery `recover`, a valid tx's
  term leaves the message's world, accounts_to_delete, touched set and refund counter
  (equal), charges the gas the message used and returns its success;
* `apply_tx_refines`: with `settle_refines` and `endTx_refines`, the wrapper's sequence
  leaves the state `Tx.run` leaves (extensionally), its gas used and its success.

Assumptions: `hmono` (a frame never ends with more gas than it got), `hpmono` (the same of a
precompile), the message leaves the sender existing (`hsender`) and only existing accounts
carrying storage (`WF`), the fee does not wrap the coinbase balance (`hnowrap`, as
`settle_refines`). The seams: `run-tx-frame!` and `precompile-run-bytes!` against the frame
and the table, `recover-authority` against `Prague.Utils.recoverAuthority`, the
creation-address derivation, the byte counts.

**The system path** is its own term since stage 6 (§4.14): `apply-tx` no longer takes
`:system`.

## 4.12 The fixture runner on the generic block pipeline (`src/fixtures/runner.lisp`, `5970a9a`)

The BlockchainTests runner had its own block loop with its own copies of the beacon-root
call, the rewards and the withdrawals, and skipped Prague and Osaka (no EIP-2935, no
EIP-7002/7251 pipeline). It now lives in `src/fixtures/runner.lisp` on top of the driver's
code: `ethereum-pre-block-of!` (EIP-4788, EIP-2935), `run-evm-tx` per tx, and
`ethereum-post-block-of!` (rewards, withdrawals, the EIP-7002/7251 request calls) — the
functions the RPC driver's `ethereum-pre-block!`/`ethereum-post-block!` wrap. A fixture
checks the code mainnet runs. "Prague" and "Osaka" are listed networks; `parse-tx` reads the
tx type, `maxFeePerGas` and the authorization list (the authority is recovered by the term,
not read from the fixture). An error in a block fails that test only (it failed the whole
file before). EIP-7702 coverage: EEST v5.4.0 `prague/eip7702_set_code_tx`, 599 pass, 2 fail
(both the missing 0x0a precompile).

`compare-post` also checks presence (`50b466e`): every account of the
expected post-state exists and no other does — what the state root sees and the field
comparison did not (an empty account left behind or destroyed too early). It is skipped for
the fixtures that give only `postStateHash`. It found one family (§5, found not fixed).
Expected failures carry their reason (`#!` lines in `src/fixtures/expected-failures.txt`).

## 4.13 The block's credits (`lean/Evm/CL/EffectBlock.lean`, `3ecd749`)

`Evm.Frontier.Vm.Block` is EELS `pay_rewards` (Frontier..London) and `process_withdrawals`
(Shanghai+) once, keyed on the fork ordinal; every fork's `applyBlock` calls it (eleven
per-fork reward copies, the Shanghai/Cancun/Prague withdrawal folds and the relational
`Shanghai.Spec.WithdrawalsStep` with its `sorry` deleted). The amounts are the emitted
formulas (`GasEmitParis.blockBaseReward_eq_rewardAt` ties the base reward to the fork
schedule). From Paris nothing is paid, so an absent coinbase stays absent; a withdrawal is
`create_ether`, i.e. `modify_state`, which destroys the account if it is left existing and
empty (§5, item 22).

The term `credits` — `pay` the coinbase and each ommer's miner (`forPairs`), then, from
Shanghai, each withdrawal's `pay` and the destroy-if-empty — is emitted as
`spec-block-credits (coinbase number uncles withdrawals)`; `ethereum-post-block-of!` calls
it (the hand-written `pay-block-rewards!` and `apply-withdrawals` are gone). New IR: `pay`
(a credit outside a tx: `block-credit!`, no journal), `forPairs`, gas `formulaK`,
`formulaK2`, `len`.

**Theorem** (`Evm.CL.EffectBlockProof.credits_refines`): for every fork, state, coinbase,
block number, ommer list and withdrawal list, the term changes exactly the world state, to
`Block.postBlock`. No assumptions.

**Still hand-written** in the block pipeline: the EIP-7685 requests hash (deposit-log
parsing, sha256 of the typed payloads; Lean has `Prague.Requests.computeRequestsHash`, not
emitted — §4.14), the header checks. The system calls are derived since stage 6 (§4.14).

## 4.14 The system calls (`lean/Evm/Frontier/Vm/System.lean`, `lean/Evm/CL/EffectSystem.lean`; stage 6)

**Owner decision** (2026-10-26): system calls follow EELS on Ethereum; Arc follows arc-node,
through its chain rule; one rule per chain, the derived term takes it as a parameter.

**The spec**, `Evm.Frontier.Vm.System`, once for every fork (EELS master, fetched
2026-10-26):

* `message` — `process_unchecked_system_transaction` (cancun/fork.py 546-611,
  prague/fork.py 640-707, osaka/fork.py 657-724) and the system message's
  `process_message_call` (prague/vm/interpreter.py 92-160): origin and caller
  `SYSTEM_ADDRESS`, `SYSTEM_TRANSACTION_GAS` (30,000,000) as the message's gas, value 0
  (`should_transfer_value = False`), no validation, nonce, intrinsic gas or fee, and
  **`accessed_addresses = set()`, `accessed_storage_keys = set()`**: nothing starts warm —
  not the caller, the target or the precompiles (EIP-2929's warm-up is `prepare_message`'s,
  which a system transaction does not run); GASPRICE is the block's base fee
  (`gas_price=block_env.base_fee_per_gas`); from Prague the target's delegation (126-133).
  It is `Tx.call` on a tx record (`sysTx`) with no authorizations, so the same `callTail` as a
  user tx, in the environment `env0` builds from a **rule** (`Rule`: the warm seed, the gas
  price; `eels` = none, the base fee).
* `unchecked` — the world after the message (`incorporate_tx_into_block`): the
  accounts_to_delete, the refund counter, the touched set and the logs are dropped (a system
  transaction destroys nothing and sweeps nothing), its success and output (`Out.output`,
  new: the top frame's return data).
* `checked` — `process_checked_system_transaction` (prague/fork.py 581-637, osaka/fork.py
  598-654): a target without code, or a message that fails (an exceptional halt or a REVERT:
  `system_tx_output.error`), is `InvalidBlock`.

The forks use it: Cancun's `applyBlock`/`applyBlockTyped` call `beaconRootCall` (=
`System.unchecked` at Cancun; the hand-made single-frame `processBeaconRootSystemCall` and the
tautological relational `Cancun.Spec.BeaconRoot` are deleted); Prague's (and Osaka's,
Amsterdam's) `applyBlock` runs EIP-4788 and EIP-2935 (`uncheckedCall`) and EIP-7002/7251
(`requestCall`: `System.checked`, a non-empty output is the type's request) — the stubs are
gone; it still runs no transactions (§5, item 23).

**Arc** (`Evm.Arc.Spec.BlockSystem.systemRule`, `systemEnd`; arc-node `6e76402`, read from
the source): Arc's system calls — the EIP-2935 history write (executor.rs:377-378) and
`ProtocolConfig.feeParams()` (executor.rs:229, protocol_config.rs:99-133) — go through
`ArcEvm::transact_system_call` (evm.rs:1557-1597): before Zero7 revm's
`system_call_with_caller` (1572-1574), from Zero7 `ArcEvmHandler::run_system_call` after
loading NativeCoinControl (1576-1589). Both are revm-handler 18.1.0 `run_system_call`
(handler.rs:123-141): `execution` only — no validation, no `pre_execution` (no warm-up of the
caller, the coinbase, an access list), no `post_execution`. The first frame loads (warms) the
target and its delegate (execution.rs:20-35); the value-0 transfer touches the target only
(revm-context 16.0.1 journal/inner.rs:447-449). The precompile addresses a tx's
`pre_execution` warmed persist in the block's journal (inner.rs:160 clears only the coinbase
and the access list), so the post-block `feeParams()` after a block with transactions sees
them warm; the pre-block EIP-2935 call runs on a fresh EVM. GASPRICE is 0 (the system
`TxEnv` has no gas price, system_call.rs:56-68). The EIP-2935 result is committed through
revm's state (selfdestructed accounts destroyed, touched empty accounts cleared: the end of
tx); `feeParams()` is never committed (a view; it writes nothing). **arc-node does not match
EELS** — the warm target, NativeCoinControl from Zero7, the post-block precompiles,
GASPRICE 0 and the end of tx differ —, so Arc keeps its rule: `[target] ++ [NativeCoinControl
if Zero7] ++ [the fork's precompiles if a tx ran]`, GASPRICE 0, the end of tx. None of it
moves state on the contracts Arc calls (they touch only their own storage), and a system
call's gas is charged to no one.

**OP-Stack** (reported, not wired): the L1-info deposit is a deposit tx (`run-deposit-tx`),
not a system call. op-geth (`core/state_processor.go`, `optimism` branch) runs EIP-4788
(`ProcessBeaconBlockRoot`, Ecotone+) and EIP-2935 (`ProcessParentBlockHash`, Isthmus) as
geth does: `AddAddressToAccessList(target)` on the block's state access list — which is not
reset between the two calls, so the history call also finds the beacon-roots address warm —,
no precompiles, GASPRICE 0, `Finalise(true)` after each (EIP-161 deletion, destructs);
EIP-7002/7251 are off from Isthmus (`IsPrague && !IsIsthmus`). Eita's OP drivers run no
system call at all (`chains/op.lisp`: lazy runs read the contracts' storage from the
chain); wiring them is a `:system-rule` like Arc's.

**The term**, emitted as `spec-system-effect (target data checked prague block-ctx)`: the
target loaded; a checked call to a target without code rejected (`reject 1`); the chain
rule's warm-up (`warmSys`, new IR: `Ctx.sysSeed` inserted in order; CL
`(warm-system-seed!)` over `*system-seed*`); from Prague the delegation (`delegS`); the
message — the tx term's for a call (the snapshot, the top `call` row, `callPath`),
unchanged. The defun binds the constants from the
spec: `sender` = `SYSTEM_ADDRESS` (`System.systemAddressNat`), `gas-limit` = `systemGas`, no
value, no creation, no intrinsic gas. The tx term lost its `system` arm (`chargeS` is
unconditional, `apply-tx` has no `:system`); the Lisp `+system-address+` and the 30M literal
are gone.

**The wrapper** (`system-call`, block-system.lisp): the chain's rule
(`*chain-system-rule*`, a new chain-spec slot `system-rule`; default `ethereum-system-rule` =
EELS), the term, a rejection → error, a checked call that fails → error, the end of tx only
when the rule commits one (Arc). Behaviour changes on Ethereum: nothing warm (was: the
precompiles, `SYSTEM_ADDRESS`, the target, the coinbase); GASPRICE the base fee (was 0); no
EIP-161 sweep after a system call (EELS has none; EIP-7523 left nothing for it); EIP-4788
and EIP-2935 run whether or not the contract has code (EELS: unchecked — empty code returns
at once) and a failing EIP-2935 call is no longer an error (EELS ignores the outcome of an
unchecked call). On Arc: the warm set (was the user-tx set), the destroy step added to the
sweep (revm's commit).

**What the replay does with an invalid block**: the checked rule's failures (no code, a
failed EIP-7002/7251 call) are a hard error in the driver — a canonical block cannot carry
one, so our state or the source is wrong; the fixture runner drops blocks marked
`expectException` before running them (§4.12), so EEST's invalid-block cases are not run.

**Theorems** (`Evm.CL.EffectSystemProof`, no `sorry`):

* `system_refines`: for every fork ordinal, block environment, world, **rule**, target and
  data, every precompile table and every frame run `runSub`, the term's world,
  accounts_to_delete, touched set and refund counter are the spec message's (EQUAL), its gas
  plus the message's gas left is `SYSTEM_TRANSACTION_GAS`, its flag is the message's
  success, and it rejects nothing (a checked call's target has code).
* `system_refines_eels`: the EELS rule; the wrapper's world after the call is
  `System.unchecked`'s, its flag the success.
* `checked_refines`: the wrapper with `:checked t` refuses exactly the calls
  `System.checked` invalidates (`system_reject`: no code → `reject 1`, nothing changed) and
  otherwise leaves its world.
* `system_refines_arc`: Arc's rule, then `spec-destroy-effect`, `spec-sweep-effect`: the
  world `systemEnd` describes (extensionally), with `endTx_refines`.

Assumptions: `hmono`, `hpmono` (as the tx); `WF` after the message for Arc's end. Seams:
`warm-system-seed!` (= `Rule.seed` in order), `run-tx-frame!`/`precompile-run-bytes!` as for
the tx (GASPRICE = the block context's `:effective-gas-price` = `Rule.gasPrice`; the output
`*last-tx-output*` = the frame's output), and the chain rule's Lisp (`ethereum-system-rule`,
`arc-system-rule`) = its Lean `Rule`.

**The EIP-7685 requests hash** stays hand-written (`requests-hash`, 6 lines): the effect IR
has no byte-string sort, and adding one (concatenation, sha256, the type byte) for a
function the header gate checks on every Prague block would cost more than it removes.

## 5. Spec bugs found by deriving (spec-fidelity fixes; the CL was right)

1. **Osaka, BPO1/2, Amsterdam SELFDESTRUCT was the Frontier form.** Their
   `handleYield .selfdestruct` arm queued every SELFDESTRUCT for deletion with a 24000
   refund — no EIP-6780, no EIP-3529. Osaka's `step1` reaches it through Cancun's
   `doSelfdestruct` yield. Now the Cancun effect (`selfdestructEIP6780`, made public).
2. **Berlin and London SELFDESTRUCT never touched the beneficiary** and credited it even
   at 0 wei, so a 0-wei SELFDESTRUCT to an absent account left an empty account no sweep
   saw (EELS `berlin/london …/system.py`: `if account_exists_and_is_empty(beneficiary):
   touched_accounts.add`). Now in the Spurious Dragon form the SD and Cancun handlers
   already used: no zero credit to an absent account, touch it.
3. (Convention, not changed) The SD form — skip a zero credit to an absent account and
   touch the beneficiary unconditionally — leaves, after the end-of-tx sweep, the state
   EELS leaves (credit-then-touch-if-empty). **Closed in stage 2** by `sd_form_closes`
   (§4.3), with the residual assumption stated there.

Stage 2:

4. **Constantinople, Berlin and Paris paid the coinbase with a plain `addBalance`** — a
   zero-fee tx created an empty coinbase or kept an existing empty one. EELS
   constantinople/berlin fork.py carry spurious_dragon's rule (balance after the fee
   non-zero: set it; else if the coinbase exists and is empty: destroy it); from Paris EELS
   `create_ether` → `modify_state` destroys an account a write leaves empty (EIP-7523),
   the same rule on the coinbase. Fixed (`e244089`): every fork from Spurious Dragon calls
   `SpuriousDragon.settleFees`. Spec fidelity.
5. **Not fixed, recorded: Prague, Osaka and Amsterdam `processTransaction` run the
   Byzantium tx loop** (`Prague.processTransaction` projects to a Frontier tx and calls
   `Byzantium.processTransaction`): no EIP-1559 fee split, no base-fee burn, no blob fee
   at the tx level of those forks. The settlement theorem is against `settleFees`, which
   they reach, with the EIP-1559 `minerWei` the Cancun/London tx loop computes; wiring the
   Prague tx level through the London/Cancun loop is step 6's (`apply-tx`) work.
6. **Paris+ end of tx keeps the EIP-161 sweep** (EELS replaced it by `modify_state`'s
   destroy-on-empty). Equivalent under EIP-7523 (no empty accounts exist from the Merge);
   documented on `SpuriousDragon.finishTx`, not changed.

Stage 3 (all in `4a1462e`; the Lisp was right on every one, except where noted):

7. **Paris, Shanghai, Cancun, Osaka, Amsterdam CREATE ignored a REVERTing init frame** —
   the revert data was deployed as code — and had **no EIP-170 size limit and no EIP-3541
   prefix rule**; a deposit failure dropped the creator's nonce bump. London had EIP-170
   and EIP-3541 but also ignored REVERT and dropped the nonce bump. Byzantium through
   Berlin had **no EIP-170**.
8. **Homestead and Tangerine Whistle dropped the creator's nonce bump on a failed code
   deposit** (EELS: the snapshot is taken after `increment_nonce`, so the bump survives).
9. **Cancun..Amsterdam marked the new account created only after the init code ran**, so
   a SELFDESTRUCT inside the constructor did not see it as created (EIP-6780: EELS marks it
   in `process_create_message`, before the code runs).
10. **Shanghai+ ignored storage in the collision rule; every fork omitted the nonce
    2^64−1 fail-fast leg** (EELS `generic_create`, all forks).
11. (Unobservable, removed) Spurious Dragon and Byzantium touched the new address in the
    child; EELS does not, and it has nonce 1, so no sweep could see it.
12. **EIP-7610 is not applied (owner decision 2026-10-26, every chain; done in stage 4,
    the final commit).** EELS master dropped the storage leg of the collision rule from
    every fork (execution-specs #3417, merged 2026-08-25, commit 2ce2191562; EIP-7610
    declined per EIP-7773) and a creation over an account holding storage wipes it before
    the init code runs (`process_create_message`'s `destroy_storage`, every fork; #3508,
    merged 2026-09-23, commit faf6637766, ported the wipe into the Cancun..Amsterdam
    trackers, whose reads fell back to the pre-state). Now: `Create.collides` and
    `HostEmit.createCollision` are EIP-684 (nonce, code); `childState` and every fork's
    tx-level creation wipe the storage (`State.destroyStorage`), and the child's
    `originalState` drops it (EELS `get_storage_original` is 0 for a created account); the
    derived cb-create wipes through `storage-wipe-journaled!`, the tx-level creation in
    `apply-tx` too. Clients: geth implemented the check in #28912 (2024-04-08) and removed
    it in #35581 (2026-08-27); revm/reth never had it (revm #3856 closed unmerged; reth
    ignores the hive tests, #23769); op-geth main still has it. The ethereum/tests
    fixtures that expect EIP-7610's abort are listed, by name, in
    `src/fixtures/expected-failures.txt` (reported XFAIL by the fixture runner, XPASS if
    one passes): 107 in the batteries (`InitCollision*`, `create2collisionStorage*`,
    `RevertInCreateInInit*`, `dynamicAccountOverwriteEmpty*`; the older-fork variants that
    expect a post-state both rules produce still pass); the Lean replay harness fails the
    same families (111 tests).
13. (Kept, stated) EELS never rolls back `created_accounts`; the spec (and the replay's
    journal) roll a failed creation's mark back. Unobservable: a failed creation leaves no
    code, so no SELFDESTRUCT runs there before a later creation marks it again.

Stage 4 (all in `423b863`):

14. **EIP-161 touch of a CALL's target.** Constantinople..Amsterdam never touched it;
    Spurious Dragon and Byzantium touched it in the child at entry (EELS: after a
    successful child, if it is existing and empty) and never for STATICCALL.
15. **The RIPEMD-160 exemption** of `incorporate_child_on_error` (block 2,675,119) was in
    no fork (§4.8 for the leg left out).
16. **Berlin and London kept a REVERTed child's warm-ups** (accessed addresses and slots,
    the original cache); EELS merges them on success only.
17. **Precompile tables.** Berlin..Shanghai used Istanbul's (no EIP-2565 MODEXP); from
    Berlin every fork decided "is a precompile" with Istanbul's table at the opcode, so
    Cancun's 0x0a, Prague's BLS12-381 (Prague ran Cancun's table anyway) and Osaka's
    P256VERIFY were unreachable by a CALL, and Osaka's EIP-7883 MODEXP unused.
18. **EIP-7702**: the delegate's access was priced against the warm set before the target
    was warmed (a self-delegated target paid cold twice); precompiles were not disabled for
    a delegated target; Osaka/Amsterdam charged the delegate but ran the designator.
19. (Recorded, not changed) the 7702 gate is `env.pragueDelegation`, which only the OP
    drivers set; the Ethereum Prague+ tx loop is §5.5's gap, wired in step 6.

Stage 5:

20. **Closes item 5.** Prague, Osaka and Amsterdam ran the Byzantium tx loop: no EIP-1559
    split, no base-fee burn, no blob fee, no EIP-7702 (the 7702 gate was set by the OP
    drivers only, item 19), and a tx straight to a precompile never ran it. Now `Tx.run`
    (`49aadec`).
21. **Tx-level fidelity** (`49aadec`; the Lean replay harness, 17 tests): a creation tx did
    not warm the created address at Berlin, the tx level used Istanbul's precompile table
    (`modexpRandomInput`, EIP-2565), init-code and EF-prefix rules were missing at the tx
    level at Berlin/Shanghai (§4.10 lists the tests).
22. **A withdrawal kept an account it left empty** (`3ecd749`). EELS `create_ether` is
    `modify_state`, which destroys an account that exists and is empty afterwards
    (shanghai/state_tracker.py:480-492): a zero withdrawal to an absent or empty account
    leaves none. The Lean folds (`addBalance`) created or kept it; the Lisp too (below).
23. (Recorded, not changed) the Lean `Prague.applyBlock` still stubs its system calls and
    runs no transactions (`Replay.lean` drives Prague txs through `Tx.run` directly).
    **Stage 6:** its system calls are `System` now; it still runs no transactions.

Stage 6:

24. **The EIP-4788 call was a hand-made frame** (`Cancun.processBeaconRootSystemCall`): one
    `applyMessage` in a seed environment the block driver filled by hand (no origin, gas price
    0), skipped when the contract had no code, its failure swallowed; the relational
    `Cancun.Spec.BeaconRoot` was a tautology (`beaconRoot_sound : P → P`). Now
    `System.unchecked` (both deleted).
25. **Prague's four system calls were stubs** (no state change, empty output), so its
    `requestsHash` was always `sha256("")` and the header check was disabled (`pure ()`).
    Now `System.unchecked` / `System.checked`, the requests from the outputs, a mismatch an
    error.

### Latent replay divergences closed (the Lisp, not the spec; never observed)

None reached the gates: segment rows and headers are unchanged, fixtures identical.

* **Pre-Spurious zero-fee coinbase.** A zero-gas-price tx left an absent coinbase absent;
  EELS (and the spec) create it. Visible to a later tx of the same block only (the block
  reward creates it at the end): a CALL to that coinbase would have been charged the 25000
  new-account fee. Now `markPresent`.
* **Spurious-Dragon+ zero-fee coinbase not touched by the tx.** An existing empty coinbase
  survived a zero-fee tx; EELS destroys it. Now the coinbase rule.
* **Sweep before settlement.** The EIP-161 sweep ran inside `apply-tx`, before the refund
  and the fee: a touched empty coinbase with storage lost its storage before the fee made it
  non-empty (EELS keeps it). Now EELS order.
* **OP deposits never destroyed their accounts_to_delete** (`run-deposit-tx` had no
  `finalize-selfdestructs`). Now `spec-destroy-effect`.

Stage 3 (`04ea1f9`):

* **A reverted CREATE deleted an existing empty account** (pre-Spurious Dragon). Undoing a
  CREATE (journal entry 10) dropped the address from the existence set unconditionally. An
  empty account exists once a CALL touches it (EELS `process_message: touch_account`, a
  0-value CALL suffices); if a CREATE then targets that address (no code, nonce or storage,
  so no collision) and the init code or the deposit fails, the rollback made it absent
  where EELS keeps it, and a later CALL to it before Spurious Dragon would pay the 25000
  new-account fee EELS does not. The entry now records the prior presence; the restore keeps
  it. This is what makes `rollback`'s seam contract exact.

Stage 4 (`14a0e17`):

* **The callee's EIP-161 touch was broader than EELS.** `cb-call` touched the current
  target before the charge, journaled below the child's snapshot, so the touch survived a
  fail-fast (depth limit, insufficient balance) and a failed child. EELS touches it only
  when the child succeeds and leaves it existing and empty, and keeps 0x03 by the
  RIPEMD-160 exemption. A CALL with a value to an existing empty account that fails for
  balance (Spurious Dragon to the Merge) made the replay sweep an account EELS keeps. The
  memory note (`project_ripemd_touch_2675119`) is right: the broad rule reproduced block
  2,675,119 by accident. Now the term's rule; gates unchanged (no such case in the
  segment, the fixtures or regress-arc).

Stage 5:

* **EIP-7702's refund went to non-empty authorities** (`ba77163`); EELS `set_delegation`
  (and geth) refund when the authority exists. No type-4 tx in the segment.
* **EIP-3607 and the fee, blob and intrinsic-gas rules were not checked** by the replay
  (`ba77163`): it trusted the block. Now the term's validation; a rejection is an error.
* **The EIP-4788 call ran on the previous tx's per-tx state** and absent block fields left
  stale frame-env slots (`ba77163`).
* **A system call got 30M less the intrinsic gas** (`5970a9a`). EELS
  `process_unchecked_system_transaction` gives the message the whole
  SYSTEM_TRANSACTION_GAS. Observed: EEST v5.4.0
  `test_system_contract_errors[system_contract_reaches_gas_limit]` for EIP-7002 and
  EIP-7251 failed (`request system call … failed`); both pass now. On main since the
  system calls existed.
* **A zero withdrawal to an existing empty account kept it** (`3ecd749`; item 22). Only the
  state root sees it (EIP-161 makes an empty account indistinguishable to the EVM: EXTCODEHASH
  is 0, no new-account fee). Case: a hand-made Shanghai fixture — an empty pre-state account
  E, a zero withdrawal to it in block 1 — fails the presence check on `5970a9a` (`EXTRA E`)
  and passes now.
* (Cosmetic) from Paris the replay credited 0 to the coinbase (fault, observer and MPT
  touch); EELS pays nothing. Now nothing.

Stage 6 (the system calls; Ethereum now follows EELS — none observable on mainnet's system
contracts, which touch only their own storage, and no system call's gas is charged):

* **A system call started with the user-tx warm set**: the precompiles, `SYSTEM_ADDRESS`, the
  target and the coinbase; EELS starts empty. Visible only in the call's own gas (its observed
  `call` row), and only in code that touches one of those addresses.
* **GASPRICE inside a system call was 0**; EELS gives the base fee (geth and revm give 0).
* **An EIP-161 sweep ran after every system call**; EELS has none (EIP-7523 left nothing to
  find).
* **A failing EIP-2935 call was a hard error**; EELS ignores an unchecked call's outcome.
  EIP-4788/2935 were skipped when the contract had no code; EELS runs the message (empty code
  returns at once — the same world, but now an observed frame).

**Found, not fixed** (stage 5):

* **The RIPEMD-160 exemption after an exceptional halt** (§4.8's leg left out) is a real
  state-root difference: the fixture runner's new presence check (`compare-post`: every
  post-state account exists and no other does) fails `RevertPrecompiledTouch` d0/d3 and
  `RevertPrecompiledTouch_storage` d0/d3, Byzantium..London (24 tests): 0x03 exists empty
  in the pre-state, a child touches it and halts; EELS sweeps 0x03, the replay keeps it.
  Not new: the Lisp before stage 4 (`423b863`) fails them the same way. Listed as expected
  failures with that reason; the fix needs the spec's child run to return the halted
  child's touched set.
* **The KZG point-evaluation precompile (0x0a, EIP-4844)** was an explicit error until
  `lean/c/point_evaluation.c` (over vendor/blst, EELS `point_evaluation.py` clause by clause,
  [s]G2 from EELS `crypto/kzg.py`): the 58 battery and 364 EEST v5.4.0 tests that failed on it
  pass. The Lean interpreter's 0x0a calls the same C (it accepted every proof before).

### Presence and storage: `world-account-present-p` vs `mpt-live` (decided with EELS)

EELS: an account exists iff it has an account object; storage lives under an account
(`set_storage` asserts the account exists), so **storage implies existence**, also for an
account whose nonce, balance and code are all zero. `mpt-live` (trie membership:
non-empty ∨ nonzero storage ∨ marked) states exactly that and is right.
`world-account-present-p` (marked ∨ non-empty) ignores storage; it is right on every state
the replay builds, because every path that can leave an empty account with storage marks it
present: a creation marks the address before its init code runs (`markPresent`, kept by
Frontier's failed deposit), the snapshot loader marks every existing empty account
(`exists-empty`), the fixture loader marks every pre-state account, the genesis loader every
empty alloc entry. That invariant (storage ⇒ marked ∨ non-empty) is the Lisp image of the
spec's `WF` (only existing accounts carry storage, §7). Adding a storage probe to the
predicate would cost a scan on every pre-Spurious CALL for a case no path produces; not
changed. The uses that must see storage — the collision rule, the sweep and the zero-fee
coinbase rule (`dead`, which deletes storage with the account) — do.

## 6. Gates (measured)

| gate | before (main `aaf2782`) | seam (`11b9b50`) | derived selfdestruct (`0443c7e`) |
|---|---|---|---|
| perf segment 4,900,001–4,910,000 (2,038,567 txs, Byzantium): observed rows (the private writer) vs main (decoded; file bytes differ by the async commit's group partition) | — | identical, 77 shards | identical, 77 shards (the segment has only 4 value-moving SELFDESTRUCTs: the fixtures carry the fork coverage) |
| header gate on the segment | 0 mismatches | 0 | 0 |
| effect-layer fixtures (legacy Cancun stCreateTest, stCreate2, stCallCreateCallCodeTest, stSystemOperationsTest, stRevertTest, stEIP158Specific, stExtCodeHash, stStaticCall, stInitCodeTest; EEST stCreateTest, stCreate2, stCallCreateCallCodeTest, stExtCodeHash, stInitCodeTest, stRecursiveCreate; bcValidBlockTest, bcRandomBlockhashTest, bcStateTests) | 10,838 PASS / 0 FAIL / 0 ERROR | identical per-test verdicts | identical per-test verdicts |
| regress-arc (14 blocks, header N/N exact) | — | — | 14/14 exact, 0 header mismatches |
| read stream (4,900,001–4,900,300): cross-tx reads equal to the stream's own committed writes | — | 352,862 checked, 0 unfaithful | — |

| µs/tx on the segment (two interleaved rounds, same machine) | 27.7, 27.8 | — | 28.2, 28.1 (+1.4 %) |
| `scripts/test-staticcall`, `-call-family`, `-eita-run`, `-call-memexp-oog`, `-code-buffer` | pass | — | pass |
| `verify-host-emit.sh` (incl. the proof module, no `sorry`); `lake build Evm` | — | — | OK; 1295 jobs OK |

`#print axioms selfdestruct_refines`: `propext`, `Quot.sound` (no `sorryAx`, no
`native_decide`).

**Stage 2** (baseline: main `18ebdf4` = stage 1; each column the commit that derived it):

| gate | settlement (`10764e4`) | end of tx (`c45c6e1`) | `cb-sstore` (`e83c89a`) |
|---|---|---|---|
| segment 4,900,001–4,910,000: decoded fact rows vs main | identical, 77 shards | identical, 77 shards | identical, 77 shards |
| header gate on the segment | 0 mismatches | 0 | 0 |
| effect-layer fixtures (stage-1 set) | 10,838 / 0 / 0, per-test verdicts identical | identical | identical |
| 11 more legacy directories (stTransactionTest, stSpecialTest, stRefundTest, stZeroCallsTest, stZeroCallsRevert, stEIP1559, stEIP150Specific, stSStoreTest, stSelfBalance, stEIP3607, stEIP2930) vs main | — | 7,147 PASS, verdicts identical (stEIP1559's heap exhaustion at the 1 GB default and stSpecialTest's missing 0x0A precompile pre-exist on main) | identical |
| regress-arc 14 blocks | 14/14 N/N exact, 0 header mismatches, rows identical to main's | same | same |
| read stream 4,900,001–4,900,300, deltas folded in index order | 294,717 reads checked (79,071 on delta keys), 0 unfaithful | — | 309,772 checked, 0 unfaithful |
| µs/tx, interleaved rounds (main, this) | 27.7/27.9 vs 27.8/27.8 | 27.3/28.0 vs 27.7/27.7 | 27.6/27.4 vs 27.6/27.6 |
| `scripts/test-*` (5), `verify-host-emit.sh` (4 effect proofs, no `sorry` in `Evm/CL/Effect*.lean`), `lake build Evm` | pass, OK | pass, OK | pass, OK, 1301 jobs |

**Stage 3** (baseline: main `c790b3d` = stage 2):

| gate | dispatch + `cb-sload` (`f137e5d`) | CREATE spec (`4a1462e`) + `cb-create` (`6bf84f2`) | type-10 fix (`04ea1f9`) |
|---|---|---|---|
| segment 4,900,001–4,910,000: decoded fact rows vs main | identical, 77 shards | identical, 77 shards (31,061 CREATE-opcode frames, 28 of them halting) | identical |
| header gate on the segment | 0 mismatches | 0 | 0 |
| effect-layer fixtures (stage-1 set, 10,838) | per-test verdicts identical | identical | identical |
| 11 more legacy directories (stage 2) | identical | identical | identical |
| CREATE family, new (`cfx.sh`): the legacy Constantinople corpus' stCreateTest, stCreate2, stInitCodeTest, stRecursiveCreate, stCodeSizeLimit, stRevertTest, stSystemOperationsTest, stCallCreateCallCodeTest, stEIP158Specific, stReturnDataTest, stTransactionTest (Frontier..Constantinople networks), the Cancun corpus' stCodeSizeLimit, stRecursiveCreate, stReturnDataTest, EEST stCodeSizeLimit | — | 4,907 PASS / 0 FAIL / 0 ERROR, per-test verdicts identical to main | identical |
| regress-arc 14 blocks | 14/14 N/N, 0 header mismatches, rows identical to main's | same | same |
| read stream 4,900,001–4,900,300 | 309,772 checked, 0 unfaithful | 309,772 checked, 0 unfaithful (writes identical; the term reads a little more: +575 balance, +1,725 nonce, +575 presence reads) | — |
| µs/tx, interleaved (main, this) | 29.5/28.8 vs 29.1/28.7 | 28.4/28.7 vs 28.7/28.2 | 28.6 (one run) |
| `scripts/test-*` (5), `verify-host-emit.sh` (6 effect proofs, no `sorry`), `lake build Evm` | pass, OK | pass, OK, 1304 jobs | — |

**Stage 4** (baseline: main `9ffc3f0` = stage 3):

| gate | CALL spec (`423b863`) + `cb-call` (`14a0e17`) |
|---|---|
| segment 4,900,001–4,910,000: decoded fact rows vs main | identical, 77 shards |
| header gate on the segment | 0 mismatches |
| effect-layer fixtures (stage-1 set, 10,838) | per-test verdicts identical |
| 11 more legacy directories (stage 2, 7,148) | identical |
| CREATE family (stage 3, 4,907) | identical |
| CALL family, new (`callfx.sh`, 19,166): legacy Cancun stCallCodes, stCallDelegateCodes*, stDelegatecallTestHomestead, stStaticFlagEnabled, stPreCompiledContracts(2), stEIP150singleCodeGasPrices, stMemExpandingEIP150Calls, stMemoryStressTest, stNonZeroCallsTest; the Constantinople corpus' call directories incl. stStaticCall, stEIP150Specific, stZeroCalls*; the ethereum/tests tgz's 21 call directories (Cancun networks run, Prague skipped by the runner — no EIP-7702 fixture coverage) | per-test verdicts identical to main (19,162 PASS, 4 ERROR on both: precompile 0x0a, pre-existing) |
| regress-arc 14 blocks | 14/14 exact, 0 header mismatches, rows identical to main's run |
| read stream 4,900,001–4,900,300 | 309,851 checked, 0 unfaithful; writes identical (the term reads more: +15,018 presence, +23,158 balance, +14,837 nonce — the success touch's existence test) |
| µs/tx, interleaved (main, this) | 29.3/30.3 vs 28.5/29.7 |
| `scripts/test-*` (5), `verify-host-emit.sh` (7 effect proofs, no `sorry`), `lake build Evm` | pass, OK, 1454 jobs |

**Stage 5** (baseline: main `4f252c7` = stage 4). The segment is Byzantium: it exercises the
pre-London tx level, the Byzantium rewards and ommers; the Cancun/Prague tx level, EIP-7702,
the system calls and the withdrawals are gated by the fixtures only.

| gate | tx spec (`49aadec`) + `apply-tx` (`ba77163`) | fixture runner (`5970a9a`) | block credits (`3ecd749`) |
|---|---|---|---|
| segment 4,900,001–4,910,000: decoded fact rows vs main | identical, 77 shards | identical | identical |
| header gate on the segment | 0 mismatches | 0 | 0 |
| fx (11,323 with Prague), xfx (7,116), cfx (4,905), callfx (23,071) | per-test verdicts identical to main (Prague not run yet) | every pre-Prague verdict identical, except files that errored as a whole on 0x0a now report per test (58 FAIL on 0x0a, 794 PASS); new Prague variants 3,617 PASS, 19 FAIL (0x0a), 6 XFAIL (the EIP-7610 twins) | identical |
| EEST v5.4.0 blockchain_tests frontier..osaka (19,479; `static` not run) | — | 19,075 PASS, 404 FAIL: 364 on 0x0a, 40 EIP-7610 (`paris/eip7610_create_collision`); `frontier/scenarios` (90 MB) exhausts the heap | identical (incl. `prague/eip7702_set_code_tx` 599/2, osaka 911/0) |
| regress-arc 14 blocks | rows identical to main's | identical | identical |
| read stream 4,900,001–4,900,300 | 416,810 checked, 0 unfaithful (the term reads more than the hand-written tx: +nonce/balance/code/presence for the validation; one more `:account` write, the type-10 uncreate) | identical | identical |
| Lean replay harness (103 dirs) | 5,546 → 5,529 failures, none new | — | 5,529, identical list |
| µs/tx, interleaved (main, this) | 36.7 (warm-up)/29.1 vs 29.3/29.3 | — | 27.2/27.5 vs 27.7/28.2 |
| `scripts/test-*`, `verify-host-emit.sh`, `lake build Evm` | pass, OK (8 effect proofs) | pass | OK (9 effect proofs), 1453 jobs |

The presence check (`50b466e`): the four batteries and EEST as `3ecd749` except the 24
`RevertPrecompiledTouch` tests (§5), listed as expected failures.

**Stage 6** (baseline: main `101bb7d` = stage 5, run on a copy of main's tree the same
hour). The segment is Byzantium: it has no system call, so it gates that the user-tx path is
unchanged; the system calls are gated by EEST (EIP-4788, EIP-2935, EIP-7002, EIP-7251,
EIP-7685, EIP-6110), the batteries and regress-arc (Arc's EIP-2935 and `feeParams()` calls on
every block).

| gate | spec (`0ac2c79`) + derived system call (`0859c29`) |
|---|---|
| segment 4,900,001–4,910,000: decoded fact rows vs main | identical, 77 shards |
| header gate on the segment | 0 mismatches |
| EEST v5.4.0 cancun, prague, osaka (8,566 tests) | per-test verdicts identical to main: 8,208 PASS, 358 FAIL (356 on 0x0a, 2 EIP-7702 on 0x0a); the system-call families all PASS before and after — eip4788_beacon_root 126, eip2935_historical_block_hashes_from_state 16, eip7002_el_triggerable_withdrawals 44, eip7251_consolidations 47, eip7685_general_purpose_el_requests 54, eip6110_deposits 76 (blocks marked `expectException` are not run, §4.12) |
| fx, xfx, cfx, callfx (the four batteries: 11,311 / 7,115 / 4,893 / 23,014 PASS) | per-test verdicts identical to main (the same 1 xfx and 57 callfx FAILs, 0x0a; the same XFAILs) |
| regress-arc 14 blocks | 14/14 exact, 0 header mismatches; rows (all kinds, incl. the pre-block EIP-2935 rows) identical to main's run: Arc's new rule moves no state |
| Lean replay harness (103 dirs; the Cancun corpus runs `beaconRootCall` on every block) | 5,529 failures, the identical list to stage 5 (none new, none fixed) |
| read stream 4,900,001–4,900,300 | 416,810 checked, 0 unfaithful; every per-kind count identical to stage 5 |
| µs/tx, interleaved (main, this) | 24.5/24.4 vs 24.7/24.5 (the user-tx path is unchanged) |
| `verify-host-emit.sh` (10 effect proofs, no `sorry`), `lake build Evm` | OK, 1453 jobs |

(regress-arc's own `facts=` column compares against the local copy of the production log,
which differs from main's rows on 10 blocks — a stale reference, identical on main; the
Mac `wc` padding trips its static check. Rows are compared against main's run instead.)

## 7. Migration order and estimates

Each step: an IR term, a theorem against the fork handlers as the trampoline binds them,
the emitted defun replacing the hand-written code, the same gates. The IR grows only by
what the step needs.

| step | what | status / IR additions | estimate |
|---|---|---|---|
| 0 | `cb-selfdestruct` | done, stage 1 | — |
| 1 | fee settlement as deltas | **done** (§4.2): `delta`, `deleteAccount`, word `add/sub/mul` | — |
| 2 | `finalize-selfdestructs`, `sweep-empty-touched!` | **done** (§4.3): `forEach` | — |
| 3 | `cb-sstore`, `cb-sload` | **done** (§4.4, §4.5): slot primitives, `sstoreGas`, `ret`; the SSTORE dispatch emitted | — |
| 4 | `cb-create` | **done** (§4.6, §4.7): one CREATE in the spec first; `runChild`, `save`/`rollback`, `markCreated`, `bumpNonce`, `depositCode`, `retData`, `frameRow` | — |
| 5 | `cb-call` | **done** (§4.8, §4.9): one CALL family in the spec first; `letA`, `callPlan`, `runCall`, `runPre`, `callRow`, the chain primitives | — |
| 6 | `apply-tx` + `run-evm-tx` | **done** (§4.10, §4.11): one tx in the spec first; `reject`, `letLt`, `debit`, `warmTx`, `forAuths`, `recoverAuth`, `setDelegation`, `letDeleg`, `runTx`, `runPreTx`, `txRow` | — |
| 7 | block effects | **rewards and withdrawals done** (§4.13): `pay`, `forPairs`; the fixture runner on the driver's pipeline (§4.12); the system calls are step 8; the EIP-7685 requests hash is hand-written | — |
| 8 | the system calls | **done** (§4.14): one system transaction in the spec (`System`), the Lean Cancun/Prague `applyBlock` on it; `spec-system-effect`, `warmSys`, the chain rule (`system-rule`); the requests hash left hand-written | — |
| 9 | the RIPEMD-160 leg after a halt | the spec's child run returns the halted child's touched set; `Call.ripemdKeep` and the term use it; the 24 expected failures pass | 2–3 days |
| 10 | 0x0a (KZG point evaluation) | a precompile body (c-kzg), outside the effect layer | — |

Open assumptions to discharge along the way: `WF` (only existing accounts carry storage)
as an invariant of the spec's tx step; the original-value cache invariant behind `horig`
and the `orig-get!` contract (no slot write without a prior record); `sd_form_closes`'s
residual (no rule from Spurious Dragon observes an empty account's existence); from
stage 3, `hmono` (a child never ends with more gas than it got — a property of the
interpreter, provable once `runSub` is the trampoline) and the seam contracts of
`run-init-frame!` and the address derivation; from stage 4, `hpmono` (the same of the
precompiles), the seams `run-call-frame!` (incl. its empty-code return), `precompile-run!`
and `precompile-address-p` against `Call.precompiles`, and the RIPEMD-160 exemption's leg
after an exceptional halt (§4.8).

With step 6 the read stream is complete by construction for a tx (every access is emitted IR
over the view) and Block-STM S1 can start; the
settlement deltas already carry `Reads`' delta semantics (`delta_fold_reads`). From stage 5:
`hsender` and `WF` after the message (`apply_tx_refines`), the seams `run-tx-frame!`,
`precompile-run-bytes!`, `recover-authority` and the creation-address derivation. From
stage 6: `warm-system-seed!` against `Rule.seed`, each chain's Lisp rule against its Lean
`Rule` (`ethereum-system-rule` = `System.eels`, `arc-system-rule` = `BlockSystem.systemRule`),
and `WF` after an Arc system call (`system_refines_arc`).

What remains hand-written in the effect layer: the wrappers that read the native frame's
operands and the block's fields; the system call's wrapper (the rule installed, a rejection
or a failed checked call → an error, Arc's end of tx); the EIP-7685 requests hash; the header
checks; Arc's and OP's chain hooks (Arc's system rule among them: its Lean twin is
`BlockSystem.systemRule`).

## 8. Complexity (counted non-blank lines, `scripts/complexity.py` rules)

| commit | delta | classification |
|---|---:|---|
| `11b9b50` storage view (seam) | +15 | seam +120, `EITA_RWSET` and duplicates −105: near zero |
| `45f5488` effect IR | +248 | `complexity exception: spec work` |
| `36c6beb` SELFDESTRUCT spec fixes | +4 | `complexity exception: bug fix (spec)` |
| `0443c7e` derived `cb-selfdestruct` | +711 | proof +727, term +69, hand-written callback and its predicates −94: `complexity exception: spec work` |
| stage-1 document | +≈190 | documentation |
| `e244089` spec: one settlement per fork family, the coinbase rule at Constantinople/Berlin/Paris | −68 | twelve inlined settlements → two definitions |
| `10764e4` derived fee settlement | +380 | proof +299, terms +49, IR +22, Lisp/emitter +10 (`balance-delta!`/`u256` against the fixture runner's duplicate settlement): `complexity exception: spec work` |
| `9062561` spec: `destroyAccounts`, `finishTx` | −1 | refactor |
| `c45c6e1` derived end of tx | +317 | proof +290, terms +31, IR +18, emitter +9, Lisp −31 (the hand-written sweep and deletion): `complexity exception: spec work` |
| `e83c89a` derived `cb-sstore` | +492 | proof +402, IR +72, term +31, emitter +6, Lisp −19 (and one env toggle, `EITA_TRACE_SSTORE`): `complexity exception: spec work` |
| stage-2 document | +≈60 | documentation |
| `f137e5d` SSTORE dispatch emitted, derived `cb-sload` | +198 | proof +149, term +40, IR +50, emitter +10, Lisp −48 and one env toggle (`EITA_TRACE_READS_BLOCK`): `complexity exception: spec work` |
| `4a1462e` spec: one CREATE (`Create.lean`) | −1768 | `Create.lean` +219; the per-fork copies, the Frontier relational CREATE layer and its proofs −1987: a net deletion |
| `6bf84f2` derived `cb-create` | +757 | proof +714, IR +129, term +102, emitter +1, HostEmit −11 (`createShouldFail`), Lisp −179: `complexity exception: spec work` |
| `04ea1f9` type-10 rollback keeps prior presence | +3 | `complexity exception: bug fix` |
| stage 3 net | −810 | |
| `423b863` spec: one CALL family (`Call.lean`) | −2985 | `Call.lean` +405, `IR/Soundness` +68 (`chargeMemory_ok`, moved); the per-fork copies and the relational CALL layer −3458: a net deletion |
| `14a0e17` derived `cb-call` | +567 | proof +687, term +110, IR +84; Lisp −228, HostEmit/HostEmitSpec/emitter −87: `complexity exception: spec work` |
| stage 4 net (CALL) | −2418 | |
| EIP-7610 not applied (final stage-4 commit) | +65 (and the 107-name list, data) | spec: `collides` −1 leg, the wipe in `childState`/`child` and twelve tx-level creations; IR `wipeStorage`; Lisp `storage-wipe-journaled!` against `storage-nonzero-p`/`*cold-storage-p-hook*`; the expected-failure list (data) and the runner's XFAIL: `complexity exception: spec work` |
| this document (stage 3) | see its commit | documentation |
| `49aadec` spec: one transaction (`Tx.lean`) | −1658 | `Tx.lean` +487 lines; sixteen per-fork `processTransaction`s, the relational `IsTxStep` and its `sorry` deleted: a net deletion |
| `ba77163` derived `apply-tx` | +958 | proof +946, term +204, IR +155, spec +10, Lisp −366; two env toggles fewer (`EITA_CAPTURE_ADDR`, `EITA_CAPTURE_BLOCK`): `complexity exception: spec work` |
| `5970a9a` fixture runner on the driver's pipeline | +17 | `fixtures.lisp` +399, `src/evm/` −435, `block-system.lisp` +46 (the `-of!` split): `complexity exception: spec work` |
| `3ecd749` derived block credits | −107 | proof +89, spec +53, term +38, IR +30, emitted +17; per-fork reward copies −213, `WithdrawalsStep` (and its `sorry`) −117, Lisp −17 |
| `50b466e` the presence check | +54 | `fixtures.lisp` +22 (`compare-post`'s presence, reasons per section), the 24 names and their reason (data) +32: `complexity exception: spec work` (a gate) |
| stage 5 net | −736 | |
| `0ac2c79` spec: one system transaction (`System.lean`) | −117 | `System.lean` +93; `Cancun.Spec.BeaconRoot` −95, the hand-made beacon-root frame −69, Prague's system-call stubs −38, `Refinement` −10: a net deletion |
| `0859c29` derived system calls | +351 (and +83 generated) | proof +221, term +41, Arc's rule +40 (spec), IR +7, emitter +8, Lisp +33 (the chain-spec slot, Arc's rule, the wrapper): `complexity exception: spec work` |
| stage 6 document | +149 | documentation |
| stage 6 net (code) | +234 | |
