/-! # CL/HostEmit — emit host-layer decision logic from Lean to CL

The host/control layer (call/create gas flags, account-existence, the
new-account fee, revert dispatch) lived as hand-written CL in
`src/evm/` and drifted from the (correct) Lean spec — the
source of the +25000 new-account overcharge and the revert-ordering bug.

This file is the start of *emitting* that logic from Lean, so the
executable is the spec by construction. The pattern is
a small IR with two interpretations of ONE definition —
`eval` (Lean semantics, used to prove equivalence with the fork spec) and
`toCL` (emitted CL). Because both come from the same IR term, the emitted
CL cannot drift from the proved semantics.

State reads go through the **world-query seam** (`present`/`empty` →
`world-account-present-p` / `world-account-empty-p` in the harness), which
stays hand-written and runtime-pluggable (hashtable today, lazy RPC for the
Base track) — so emitting to CL keeps the researcher flexibility that
emitting to asm would lose. -/

namespace Evm.CL.HostEmit

/-- A boolean decision IR over runtime inputs and the world-query seam.
    `varB` = a runtime boolean argument; `present`/`empty` = world queries. -/
inductive Pred where
  | tru
  | fls
  | and (a b : Pred)
  | or  (a b : Pred)
  | not (a : Pred)
  | varB    (name : String)
  | present (addr : String)
  | empty   (addr : String)
  deriving Inhabited, Repr

/-- A predicate's boolean variables, in order of first appearance: the emitted defun's
    parameter list (derived, so a new leg cannot leave an unbound variable). -/
def Pred.vars : Pred → List String
  | .and a b | .or a b => (a.vars ++ b.vars).eraseDups
  | .not a => a.vars
  | .varB n => [n]
  | _ => []

/-- The runtime environment a `Pred` reads: boolean args + the two world
    queries. This is the Lean mirror of the CL seam. -/
structure Env where
  bvars   : String → Bool
  present : String → Bool
  isEmpty : String → Bool

/-- Lean semantics — the meaning we prove the fork spec against. -/
def Pred.eval (e : Env) : Pred → Bool
  | .tru       => true
  | .fls       => false
  | .and a b   => a.eval e && b.eval e
  | .or a b    => a.eval e || b.eval e
  | .not a     => ! a.eval e
  | .varB n    => e.bvars n
  | .present a => e.present a
  | .empty a   => e.isEmpty a

/-- CL code generation — the SAME term, emitted as Common Lisp calling the
    pluggable world seam. -/
def Pred.toCL : Pred → String
  | .tru       => "t"
  | .fls       => "nil"
  | .and a b   => s!"(and {a.toCL} {b.toCL})"
  | .or a b    => s!"(or {a.toCL} {b.toCL})"
  | .not a     => s!"(not {a.toCL})"
  | .varB n    => n
  | .present a => s!"(world-account-present-p {a})"
  | .empty a   => s!"(world-account-empty-p {a})"

/-! ## CREATE collision guard (EELS `generic_create`)

The CALL family's fail-fast and new-account charge are the derived cb-call's
(`Evm.CL.EffectCall`); CREATE's collision decision is emitted here. -/

/-- CREATE address-collision (EELS `not account_deployable`, EIP-684): the create aborts and
    consumes ALL forwarded gas when the target already has code or a non-zero nonce.
    Checked AFTER the sender nonce bump. Leaf reads are the world seam. No storage leg:
    EIP-7610 is not applied (execution-specs #3417); a creation over storage wipes it. -/
def createCollision : Pred :=
  .or (.varB "has-code") (.varB "nonce-pos")

private def collisionEnv (c n : Bool) : Env :=
  ⟨fun s => if s == "has-code" then c else if s == "nonce-pos" then n else false,
   fun _ => false, fun _ => false⟩

/-- The emitted decision is exactly the spec's three-legged condition (Homestead
    `doCreate`), for every combination of the leaf reads. -/
theorem boolPred_params :
    createCollision.vars = ["has-code", "nonce-pos"] := by native_decide

theorem createCollision_eq_spec (c n : Bool) :
    createCollision.eval (collisionEnv c n) = (n || c) := by
  cases c <;> cases n <;> decide

/-! ## Revert-journal dispatch

The CL-side of `revert-journal-to`: for each journal entry (newest first),
`case` on its `entry_type` (c/tx_arena.h) and restore the recorded value.
The native effect types (refund / warm-addr / warm-slot / tstore) are
reverted by `eita_ts_revert`; only the world-state types live here. Emitting
the dispatch keeps the entry_type→action mapping single-source in Lean. -/

inductive RestoreAction where
  | storageSet     -- world-storage-set world addr slot old
  | balanceSet     -- (setf (gethash addr world-balance) old)
  | sdUnmark       -- unmark-destroyed! addr  (undo selfdestruct mark)
  | existUnmark    -- remhash addr world-accounts    (undo existence insert)
  | nonceSet       -- (setf (gethash addr world-nonce) old)  (undo nonce bump)
  | createdUnmake  -- un-create a CREATE'd account: drop code/nonce/storage, and
                   -- existence unless the entry's old value records it existed before
                   -- (its balance has its own balance entry)
  | untouch        -- untouch! addr  (EIP-161 revert-scoping, #271): a
                   -- touch journaled inside a frame is dropped when the frame
                   -- reverts, so it can't reach the end-of-tx empty-account sweep
  deriving DecidableEq, Repr

/-- Restore semantics over a world seam — one op per action. `eval` and
    `toCL` both consume `revertDispatch`, so the type→action mapping can't
    drift between the Lean meaning and the emitted CL. -/
class RevertOps (m : Type → Type) where
  storageSet    : m Unit
  balanceSet    : m Unit
  sdUnmark      : m Unit
  existUnmark   : m Unit
  nonceSet      : m Unit
  createdUnmake : m Unit
  untouch       : m Unit

def RestoreAction.eval {m : Type → Type} [RevertOps m] : RestoreAction → m Unit
  | .storageSet    => RevertOps.storageSet
  | .balanceSet    => RevertOps.balanceSet
  | .sdUnmark      => RevertOps.sdUnmark
  | .existUnmark   => RevertOps.existUnmark
  | .nonceSet      => RevertOps.nonceSet
  | .createdUnmake => RevertOps.createdUnmake
  | .untouch       => RevertOps.untouch

def RestoreAction.toCL : RestoreAction → String
  -- Every restore goes through the storage view (src/state/world.lisp, "The storage view"), so a
  -- revert is a logged write like any other.
  | .storageSet    => "(setf (storage-of *current-world* addr slot) old)"
  -- old=0 means the account was ABSENT (not present-with-0): clear the entry to keep
  -- the world canonical, exactly as world-storage-set does for a 0 slot. A
  -- 0 nonce/balance is state-root-identical to absent (account-dead-p), so this
  -- is a no-op for mainnet but keeps revert byte-exact (no stray 0 entries that
  -- a re-run / differential tier would see). Presence is tracked separately in
  -- world-accounts (type 11), so removing a 0 entry never changes accountExists.
  | .balanceSet    => "(if (zerop old) (balance-clear! *current-world* addr) (setf (balance-of *current-world* addr) old))"
  | .sdUnmark      => "(unmark-destroyed! addr)"
  | .existUnmark   => "(account-unmark! *current-world* addr)"
  | .nonceSet      => "(if (zerop old) (nonce-clear! *current-world* addr) (setf (nonce-of *current-world* addr) old))"
  | .createdUnmake => "(account-uncreate! *current-world* addr old)"
  | .untouch       => "(untouch! addr)"

/-- The single source: journal `entry_type` code → CL-side restore action.
    Types 1 (tstore) and the warm/refund/created marks are native-side
    (eita_ts_revert) and intentionally absent here. -/
def revertDispatch : List (Nat × RestoreAction) :=
  [(0, .storageSet), (2, .balanceSet), (3, .sdUnmark),
   -- 9/10/11 are CL-side world types. They sit ABOVE the native journal codes
   -- (1/4/5/6/7/8); the native eita_ts_revert's `default` arm skips them, so
   -- there's no double-handling. CRITICAL: existUnmark must NOT be type 4 —
   -- that's the native EITA_J_ACCESS_ADDR (EIP-2929 warm-set insert). A tx that
   -- merely WARMS an empty-but-present account and then reverts would otherwise
   -- have the warm-up's type-4 entry misread as an existence-insert and
   -- remhash the account out of world-accounts (block 637758: a reverting
   -- invalid-jump tx touched 0xf5ed057f, deleting the empty account created at
   -- 637752 → spurious +25000 new-account overcharges across 637785+).
   (9, .nonceSet), (10, .createdUnmake), (11, .existUnmark),
   -- 12: EIP-161 touched-set revert-scoping (#271). Host-only type above the
   -- native codes; eita_ts_revert's `default` arm skips it. Single-sourced here
   -- so the touch-undo can't drift from the world-state restores (it used to be
   -- a hand-written special case in src/evm/journal.lisp's revert-journal-to).
   (12, .untouch)]

/-- Emit the `(case type …)` body from `revertDispatch`. -/
def revertDispatchCL : String :=
  let arm := fun (p : Nat × RestoreAction) => s!"    ({p.1} {p.2.toCL})"
  "(case type\n" ++ String.intercalate "\n" (revertDispatch.map arm) ++ ")"

/-! ## BLOCKHASH validity window (EELS `block_hash`)

EELS `block_hash`: the hash of block `n` is available at current block `cur`
iff `cur - 256 <= n < cur`, i.e. `n < cur` AND `cur <= n + 256`. The OLDEST
valid block is `cur-256`, INCLUSIVE.

The hand-written `cb-block-hash` used `(> n (- cur 256))` (truncated-Nat
subtraction), excluding `cur-256` and returning 0 where mainnet returns the
hash — diverging every contract that used `blockhash(block.number-256)` for
randomness (#265, the dominant Byzantium-era divergence). Emitting the
predicate in EELS's no-subtraction form makes that off-by-one
*unrepresentable*: there is no `cur-256` term to get `<` vs `<=` wrong on. -/

/-- EELS block_hash validity: is block `n` queryable at current block `cur`. -/
def blockhashValid (n cur : Nat) : Bool :=
  decide (n < cur) && decide (cur ≤ n + 256)

-- Kernel-checked boundary. The buggy `(> n (- cur 256))` form makes the FIRST
-- example false, so `by decide` fails to typecheck — the off-by-one cannot
-- survive re-emission.
example : blockhashValid 744 1000  = true  := by decide   -- cur-256: VALID (the #265 bug)
example : blockhashValid 743 1000  = false := by decide   -- cur-257: too old
example : blockhashValid 1000 1000 = false := by decide   -- current block: 0
example : blockhashValid 999 1000  = true  := by decide   -- cur-1: valid

/-- The same predicate emitted as Common Lisp (no subtraction → no off-by-one).
    `n` and `cur` are the emitted CL function's argument names. -/
def blockhashValidCL : String := "(and (< n cur) (<= cur (+ n 256)))"

/-! ## EXTCODEHASH existence (EELS `extcodehash`, EIP-1052)

EELS: `codehash = U256(0) if account == EMPTY_ACCOUNT else keccak256(code)`.
The `EMPTY_ACCOUNT` test is `is_account_dead` — absent OR all-zero (0 nonce,
0 balance, empty code). Note `keccak256("")` IS the empty-code-hash, so a
*live* account with no code returns that constant naturally — EELS has no
special case for it. The hand-written `cb-ext-code-hash` instead duplicated
the dead-account test inline (`code≠∅ ∨ bal>0 ∨ nonce>0`) and special-cased
the empty-code-hash, a second copy of the EIP-161 emptiness logic that the
new-account charge (`EffectCall`'s `dead`) already encodes.

Deriving the "hash is zero" decision reuses the SAME `empty` world-seam query
(`world-account-empty-p`), so the EXTCODEHASH existence test cannot drift from
the dead-account test the rest of the host layer uses. -/

/-- EELS EXTCODEHASH: the returned hash is 0 iff the account is dead. In our
    collapsed world seam `empty` = `is_account_dead` (absent and present-empty
    are indistinguishable, all-zero), so this is exactly `EMPTY_ACCOUNT`. -/
def extcodehashZero : Pred := .empty "addr"

-- Kernel-checked truth table: zero EXACTLY on the dead account. A drift that
-- made a live (non-empty) account hash to 0 — or a dead one hash to a code
-- digest — flips one of these, so `by decide` would fail to typecheck.
example : extcodehashZero.eval ⟨fun _ => false, fun _ => false, fun _ => true⟩  = true  := by decide  -- dead → 0
example : extcodehashZero.eval ⟨fun _ => false, fun _ => true,  fun _ => false⟩ = false := by decide  -- live → keccak256(code)

end Evm.CL.HostEmit
