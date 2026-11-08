import Evm.CL.GasEmit
import Evm.Frontier.Vm
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Berlin.Vm.Instructions.Storage
import Evm.London.Vm.Effect
import Evm.Frontier.Vm.Create
import Evm.Frontier.Vm.Call
import Evm.Frontier.Vm.Tx

/-! # CL/EffectIR — the effect layer as a typed IR (docs/effect-layer-derivation.md)

The host callbacks, `apply-tx`, fee settlement and the sweeps are where state changes:
balances move, accounts appear and disappear, the per-tx sets (touched, destroyed, warm)
grow. `HostEmit.Pred` and `GasEmit.Expr` derive the DECISIONS those callbacks take; this
IR derives the callbacks themselves — the order of reads, writes, journal entries and gas
charges — with the same discipline: ONE term, two meanings.

* `Stmt.run` — the Lean meaning, over the parts of the spec's environment
  (`Frontier.Vm.Environment`) an effect can change: `state`, `selfDestructSet`, `touched`,
  `accessedAddresses`, `createdAccounts`, `refundCounter` (`HState.ofEnv`), plus the gas
  the callback hands back to the native handler and the value-transfer facts. Every
  primitive denotes an operation the fork specs already use (`State.addBalance`,
  `State.touchAccount`, the list-set insert behind `SpuriousDragon.Vm.touchAddr` and
  `Berlin.Vm.Effect.warmAddr`), so a theorem against a fork handler is about the same
  functions, not a re-encoding.
* `Stmt.toCL` — the emitted Common Lisp. Each primitive prints to ONE call into the
  hand-written storage view (src/state/world.lisp "The storage view") or the journal; those
  calls are the trusted seam, and the doc lists each one's contract.

Target-neutral by construction: the expression sorts carry their widths (`Ty.width`), and
every effect is a named primitive — a printer for another target (Rust) needs no semantics
the IR does not state. Structure is `seq`/`ite`/`let` and one bounded loop, `forEach` over
a finite per-tx set (the end-of-tx deletions); word arithmetic wraps mod 2^256.

Journal discipline: a primitive that changes state a frame revert must undo prints its own
journal entry (balance writes, the existence mark, the destroyed mark, the touch). The
Lean meaning has no journal: a reverting frame discards its whole environment, which is
what the journal reproduces in place (`Evm.CL.JournalSpec`). -/

namespace Evm.CL.EffectIR

open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment)

/-- The value sorts at the seam and their machine widths. -/
inductive Ty where
  | bool | addr | word | gas
  deriving DecidableEq, Repr

/-- Bits per sort: addresses are 160, words 256, gas 64 (the native `uint64` the callback
    returns). The CL printer relies on no wider integer than these. -/
def Ty.width : Ty → Nat
  | .bool => 1 | .addr => 160 | .word => 256 | .gas => 64

/-- Address terms (`Ty.addr`): the callback's named inputs. -/
inductive AExp where
  | var (x : String)
  | lit (n : Nat)               -- a constant address (RIPEMD-160's 0x03)
  deriving Repr, Inhabited

/-- Word terms (`Ty.word`). -/
inductive WExp where
  | var (x : String)            -- a `letW`-bound word
  | zero
  | balance (a : AExp)          -- view read: the account's balance
  | add (a b : WExp)            -- U256 arithmetic, wrapping mod 2^256 (as `BitVec 256`)
  | sub (a b : WExp)
  | mul (a b : WExp)
  | sload (a : AExp) (k : WExp) -- view read: a storage slot
  | orig (a : AExp) (k fallback : WExp)  -- the slot's original (tx-start) value, cached at first touch
  | ofAddr (a : AExp)           -- an address as a word (CREATE's result)
  | lit (n : Nat)               -- a constant (the CALL family's success flag)
  deriving Repr, Inhabited

/-- Boolean terms (`Ty.bool`). The world queries are the HostEmit seam's. -/
inductive BExp where
  | lit (b : Bool)
  | var (x : String)            -- a `letB`/`warm`-bound boolean
  | not (p : BExp)
  | and (p q : BExp)
  | or  (p q : BExp)
  | forkGe (n : Nat)            -- the fork's ordinal (`Evm.Fork.ord`) is ≥ n
  | addrEq (a b : AExp)
  | pos (w : WExp)              -- w ≠ 0
  | weq (a b : WExp)            -- a = b
  | present (a : AExp)          -- `State.accountExists`
  | dead (a : AExp)             -- EELS `is_account_dead`: absent, or present and empty
  | created (a : AExp)          -- EIP-6780: created in this tx
  | destroyed (a : AExp)        -- already in the tx's accounts_to_delete
  | wlt (a b : WExp)            -- a < b (as naturals)
  | nonceMax (a : AExp)         -- the account's nonce is 2^64 − 1 (EIP-2681)
  | collides (a : AExp)         -- CREATE's collision rule (`Create.collides`: code, nonce — EIP-684)
  | childErr (r : String)       -- the child run `r` ended in an exceptional halt
  | childRev (r : String)       -- the child run `r` REVERTed
  | childEF (r : String)        -- the child's output starts with 0xEF (EIP-3541)
  /-- A chain's veto of a value-bearing frame (Arc's `chain-frame-init`). Outside the
      Ethereum spec: its meaning is `false` (no chain rule), the theorem is about that. -/
  | chainVeto (s d : AExp) (w : WExp)
  | kindEq (n : Nat)            -- the callback's `kind` input is `n` (CALL 0, CALLCODE 1, DELEGATECALL 2, STATICCALL 3)
  | pre (a : AExp)              -- the fork's precompile table has an entry at `a` (`Ctx.pre`)
  | touchedHas (a : AExp)       -- `a` is in the tx's touched set
  | codeEmpty (a : AExp)        -- the account has no code
  | delegated (a : AExp)        -- its code is an EIP-7702 designator (`parseDelegation`)
  | ge (x : String) (n : Nat)   -- the Nat input `x` is ≥ n (the tx type)
  | nonceIs (a : AExp) (x : String)  -- the account's nonce is the Nat `x` (an authorization's)
  deriving Repr, Inhabited

/-- Gas terms (`Ty.gas`): constants, conditionals and the GasEmit formulas, each printed as
    a call to its emitted `spec-*` defun (so the number has one owner). -/
inductive GExp where
  | lit (n : Nat)
  | ofBool (p : BExp)           -- 1 / 0
  | forkOrd
  | ite (p : BExp) (t e : GExp)
  | add (a b : GExp)
  | formula0 (name : String) (e : GasEmit.Expr)
  | formula1 (name : String) (e : GasEmit.Expr) (param : String) (arg : GExp)
  /-- A GasEmit formula of one argument and the fork (`(name arg *fork-ord*)`). -/
  | formulaF (name : String) (e : GasEmit.Expr) (param : String) (arg : GExp)
  | var (x : String)            -- a gas-valued input
  | sub (a b : GExp)            -- truncated subtraction
  | childGas (r : String)       -- the gas the child run `r` handed back
  | childLen (r : String)       -- the length of its output
  | ofWord (w : WExp)           -- a word as a number (a balance, a value)
  | nonce (a : AExp)            -- view read: the account's nonce
  | mul (a b : GExp)
  /-- A GasEmit formula of the fork alone (`(name *fork-ord*)`). -/
  | formulaK (name : String) (e : GasEmit.Expr)
  /-- A GasEmit formula of the fork and two arguments (`(name *fork-ord* a b)`). -/
  | formulaK2 (name : String) (e : GasEmit.Expr) (x : String) (a : GExp) (y : String) (b : GExp)
  | len (l : String)            -- the length of the input list `l` (`forPairs`)
  deriving Repr, Inhabited

/-- The per-tx address sets a loop ranges over: the accounts_to_delete and the EIP-161
    touched set. -/
inductive TxSet where
  | destroyed | touched
  deriving Repr, Inhabited

/-- Effect statements. -/
inductive Stmt where
  | skip
  | seq (s t : Stmt)
  | ite (p : BExp) (s t : Stmt)
  | letW (x : String) (w : WExp) (s : Stmt)
  | letB (x : String) (p : BExp) (s : Stmt)
  /-- EIP-2929: when `gate`, add `a` to the accessed set and bind `x` := it was cold;
      otherwise `x` := false (pre-Berlin forks have no accessed set). -/
  | warm (gate : BExp) (a : AExp) (x : String) (s : Stmt)
  /-- Load `a` into a lazy world (no meaning on the spec state). -/
  | fault (a : AExp)
  /-- EIP-161 touch (Spurious Dragon+, fork ordinal ≥ 4; a no-op before). Journaled. -/
  | touch (a : AExp)
  /-- `State.touchAccount`: `a` exists from now on (an empty account if it was absent).
      Journaled. -/
  | markPresent (a : AExp)
  /-- Add `a` to the tx's accounts_to_delete (deleted at tx end). Journaled. -/
  | markDestroyed (a : AExp)
  /-- Add to the tx's refund counter. Journaled (natively). -/
  | refund (g : GExp)
  /-- Balance := w. Journaled. -/
  | setBalance (a : AExp) (w : WExp)
  /-- Balance += w. Journaled. -/
  | credit (a : AExp) (w : WExp)
  /-- Balance += w as a commutative DELTA (`Evm.Parallel.Reads`): reads nothing, so a
      parallel executor need not validate it; a later read of `a` is an ordinary read.
      A zero delta has no effect (it does not bring `a` into existence). Not journaled:
      only the tx-level settlement issues it, outside every frame's revert scope. -/
  | delta (a : AExp) (w : WExp)
  /-- EELS `destroy_account`: the account and its storage leave the state. Not journaled
      (tx-level: settlement, the end-of-tx deletions). -/
  | deleteAccount (a : AExp)
  /-- Run `body` once per member of the tx set as it stands at loop entry, bound to `x`
      (the end-of-tx deletions and sweep). The body must not change the set. -/
  | forEach (set : TxSet) (x : String) (body : Stmt)
  /-- Load the slot into a lazy world (no meaning on the spec state). -/
  | faultSlot (a : AExp) (k : WExp)
  /-- EIP-2929: when `gate`, add the slot to the accessed slots and bind `x` := it was
      cold; otherwise `x` := false. -/
  | warmSlot (gate : BExp) (a : AExp) (k : WExp) (x : String) (s : Stmt)
  /-- Cache `w` as the slot's original value unless one is cached (first touch). Not
      journaled: the original value is a tx-level fact. -/
  | origRecord (a : AExp) (k : WExp) (w : WExp)
  /-- The fork's SSTORE schedule (`sstorePlan`) on (original, current, new, cold): sets the
      refund counter to the plan's and charges its cost. The refund change is journaled
      natively. -/
  | sstoreGas (o c n : WExp) (cold : BExp)
  /-- Storage slot := w. Journaled. -/
  | setStorage (a : AExp) (k : WExp) (w : WExp)
  /-- A value transfer of `kind` (an observed transfer; revert-scoped). -/
  | transferFact (kind : Nat) (src dst : AExp) (w : WExp) (child : Bool := false)
  /-- Charge `g` more gas: the callback's return value to the native handler. -/
  | charge (g : GExp)
  /-- The callback's word result (what the native handler pushes: SLOAD's value). -/
  | ret (w : WExp)
  /-- `if a < b then lt else ge` on gas. -/
  | iteG (a b : GExp) (lt ge : Stmt)
  /-- Nonce += 1. Journaled. -/
  | bumpNonce (a : AExp)
  /-- Add `a` to the created set (EIP-6780, `mark_account_created`), and journal the
      creation so a revert un-creates the account (code, nonce, storage, existence).
      Journaled. -/
  | markCreated (a : AExp)
  /-- Bind `x` to the current point of the journal (and the observers' event vector), run `s`. -/
  | save (x : String) (s : Stmt)
  /-- Undo everything since `save x`: the journal unwinds to it (Lean: the state at
      `save x`; the gas, result and return data the callback has built are kept). -/
  | rollback (x : String)
  /-- Run the init code of the account `n` created by `s` with value `w` and gas `fwd`
      as a child frame (the native interpreter; the seam), bind its result to `r`, run
      `body`. The child's effects are in the world afterwards, also when it failed (until
      a rollback). -/
  | runChild (s n : AExp) (w : WExp) (fwd : GExp) (r : String) (body : Stmt)
  /-- Set `a`'s code to the child run `r`'s output (the code deposit). -/
  | depositCode (a : AExp) (r : String)
  /-- The child run `r`'s output becomes the callback's return data (a REVERT's). -/
  | retData (r : String)
  /-- The observed call frame of a child frame from `s` to `n` with value `w`, gas `fwd`,
      around `body`; its gas used is what the callback charges beyond `base`. No meaning
      on the state. -/
  | frameRow (s n : AExp) (w : WExp) (fwd base : GExp) (body : Stmt)
  /-- Bind the address `x` to `a` if `p`, else `b`. -/
  | letA (x : String) (p : BExp) (a b : AExp) (s : Stmt)
  /-- The CALL family's gas plan at the fork (`Call.plan`: EIP-2929 access, value and
      new-account fees, EIP-7702 delegate access, EIP-150's cap), bound to the gas inputs
      `charge`, `fwd`, `stip`. -/
  | callPlan (cold vf na : BExp) (deleg gasArg avail : GExp) (s : Stmt)
  /-- Run the CALL family's child frame with gas `g` (the seam: the native interpreter on
      the code of the code address, as `Call.child` builds it), bind its result to `r`. -/
  | runCall (g : GExp) (r : String) (body : Stmt)
  /-- Run the fork's precompile at `a` (`Ctx.pre`) on the input with gas `g`, bind its result
      to `r` (an exceptional halt on failure; the world unchanged). -/
  | runPre (a : AExp) (g : GExp) (r : String) (body : Stmt)
  /-- The observed call frame of a CALL-family child (from `s` to `n`, value `w`, gas `g`),
      around `body`; its gas used is what the callback charges beyond `base`, plus `stip`. -/
  | callRow (s n : AExp) (w : WExp) (g base stip : GExp) (body : Stmt)
  /-- A chain's native precompile at `a` (Arc's 0x1800…), with gas `g`, rolling back to the
      save point `snap` on failure; otherwise `rest`. Outside the Ethereum spec: its meaning
      is `rest` (no chain precompile). -/
  | chainCall (a : AExp) (g base stip : GExp) (snap : String) (rest : Stmt)
  /-- A chain's frame-init veto of a value-bearing CALL (Arc's blocklist), probed when
      `guard`, before the fail-fast: on a veto `veto` runs with `r` the vetoed child (a
      REVERT with the chain's output). Outside the Ethereum spec: its meaning is `rest`. -/
  | chainCallVeto (guard : BExp) (s d : AExp) (w : WExp) (r : String) (veto rest : Stmt)
  /-- A chain's log of a value transfer (Arc's EIP-7708 log). No meaning on the state. -/
  | chainLog (s d : AExp) (w : WExp)
  /-- EELS `destroy_storage`: the whole storage of `a` goes (a creation over an account
      that holds storage). Journaled (one storage entry per wiped slot). -/
  | wipeStorage (a : AExp)
  /-- The tx is invalid: the first rule it breaks (`n`, from 1; `Tx.invalid`'s order). No
      state meaning beyond the code: the wrapper refuses the tx. -/
  | reject (n : Nat)
  /-- Bind the boolean `x` := `a < b` (on numbers). -/
  | letLt (x : String) (a b : GExp) (s : Stmt)
  /-- Balance −= g (the upfront charge). Journaled. -/
  | debit (a : AExp) (g : GExp)
  /-- EIP-2929/2930/3651: when `gate`, warm the fork's precompiles, the sender, the target,
      from Shanghai the coinbase, and the access list's addresses and slots
      (`Tx.seedAddrs`, `Tx.seedSlots`), in that order. -/
  | warmTx (gate : BExp) (sender target coinbase : AExp)
  /-- A system call's start: warm the chain rule's addresses, in order (`System.Rule.seed`,
      `Ctx.sysSeed`; EELS: none). -/
  | warmSys
  /-- EIP-7702: run `body` once per authorization of the tx, in order, with its fields bound
      (`a-chain`, `a-addr`, `a-nonce`, `a-yp`, `a-r`, `a-s`). -/
  | forAuths (body : Stmt)
  /-- The current authorization's authority (`recover_authority`): bind the address `x` and
      run `found`, or run `miss` when it does not recover. -/
  | recoverAuth (x : String) (miss found : Stmt)
  /-- Set `a`'s code to the delegation designator of `d` (none for the zero address).
      Not journaled (tx level, before the message's snapshot). -/
  | setDelegation (a d : AExp)
  /-- When `gate`, bind the address `x` := the delegate of `a`'s code and `hx` := `a` is
      delegated (EIP-7702 `get_delegated_code_address`); otherwise `x` := 0, `hx` := false. -/
  | letDeleg (x hx : String) (gate : BExp) (a : AExp) (s : Stmt)
  /-- Run the tx's message frame with gas `g` (the seam: the native interpreter on the
      creation's init code, or the target's code — the delegate's under EIP-7702), bind its
      result to `r`. -/
  | runTx (g : GExp) (r : String) (body : Stmt)
  /-- Run the fork's precompile at `a` on the tx's data with gas `g`, bind its result to `r`
      (as `runPre`). -/
  | runPreTx (a : AExp) (g : GExp) (r : String) (body : Stmt)
  /-- The observed call frame of the tx's top frame (gas `g`), around `body`. No meaning on
      the state. -/
  | txRow (g : GExp) (body : Stmt)
  /-- A chain's native precompile at the tx's target (Arc's 0x1800…), with gas `g`, rolling
      back to `snap` on failure; otherwise `rest`. Outside the Ethereum spec: `rest`. -/
  | chainTxCall (a : AExp) (g : GExp) (snap : String) (rest : Stmt)
  /-- A chain's frame-init veto of the tx's value transfer (Arc's blocklist): on a veto
      `veto` runs. Outside the Ethereum spec: `rest`. -/
  | chainTxVeto (s d : AExp) (w : WExp) (veto rest : Stmt)
  /-- A block-level credit of `g` wei to `a` (EELS `create_ether` outside a tx: the
      rewards, a withdrawal) — no journal. -/
  | pay (a : AExp) (g : GExp)
  /-- For each (address, number) of the input list `l`, in order: `body` with them bound
      as `p-addr` / `p-n` (the ommers, the withdrawals). -/
  | forPairs (l : String) (body : Stmt)
  deriving Repr, Inhabited

/-! ## Lean meaning -/

/-- What a callback acts on: the parts of the spec environment (`Frontier.Vm.Environment`)
    an effect can change — the world state and the per-tx sets and counter — plus the gas
    it returns and the facts it emits. (`ofEnv` projects an environment onto it.) -/
structure HState where
  state     : State
  destroyed : List Evm.Address        -- `selfDestructSet` (EELS accounts_to_delete)
  touched   : List Evm.Address        -- EIP-161 touched set
  accessed  : List Evm.Address        -- EIP-2929 `accessedAddresses`
  created   : List Evm.Address        -- EIP-6780 `createdAccounts`
  refund    : Nat                     -- `refundCounter`
  slots     : List (Evm.Address × Evm.U256) := []                  -- `accessedStorageKeys`
  origs     : List ((Evm.Address × Evm.U256) × Evm.U256) := []     -- `storageOriginals`
  gas       : Nat := 0
  out       : Evm.U256 := 0                -- the word result (`ret`)
  rdata     : Evm.Bytes := Evm.Bytes.empty -- the return data the callback hands back (`retData`)
  facts     : List (Nat × Evm.Address × Evm.Address × Evm.U256) := []
  rej       : Nat := 0                     -- a tx's rejection (`reject`; 0: valid)
  deriving Inhabited

/-- The callback's starting point: the environment it runs in, nothing charged yet. -/
def HState.ofEnv (e : Environment) : HState :=
  { state := e.state, destroyed := e.selfDestructSet, touched := e.touched,
    accessed := e.accessedAddresses, created := e.createdAccounts, refund := e.refundCounter,
    slots := e.accessedStorageKeys, origs := e.storageOriginals }

/-- What a child frame hands back: an exceptional halt, or its final world (`h`, the
    child's whole `HState`), the gas it did not use, its output, and whether it REVERTed. -/
inductive ChildRes where
  | err
  | ok (h : HState) (gas : Nat) (out : Evm.Bytes) (reverted : Bool)
  deriving Inhabited

/-- The callback's inputs: the fork, the named addresses, the let-bound values, the gas
    inputs, the saved journal points, the child runs' results, and `child` — what running
    a child frame from a given state with a given gas gives (the native interpreter; the
    theorems instantiate it with the spec's `runSub`). -/
structure Ctx where
  fork : Nat
  addr : String → Evm.Address
  word : String → Evm.U256 := fun _ => 0
  bool : String → Bool := fun _ => false
  nat  : String → Nat := fun _ => 0
  snaps : String → HState := fun _ => default
  res  : String → ChildRes := fun _ => .err
  child : HState → Nat → ChildRes := fun _ _ => .err
  /-- The fork's precompile table (`Call.precompiles`; the CALL family's `runPre`). -/
  pre : Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile := fun _ => none
  /-- The CALL family's input bytes. -/
  input : Evm.Bytes := Evm.Bytes.empty
  /-- A tx's access list (`warmTx`). -/
  accessList : List (Evm.Address × List Evm.U256) := []
  /-- A tx's EIP-7702 authorizations (`forAuths`), the one being processed, and the
      authority of each (`recover_authority`; the theorems take it as an input). -/
  auths : List Evm.Prague.Authorization := []
  cur : Evm.Prague.Authorization := default
  recover : Evm.Prague.Authorization → Option Evm.Address := fun _ => none
  /-- A block's lists of (address, number): the ommers, the withdrawals (`forPairs`). -/
  pairs : String → List (Evm.Address × Nat) := fun _ => []
  /-- The addresses a system call starts warm with (the chain's rule; `warmSys`). -/
  sysSeed : List Evm.Address := []

def TxSet.get (h : HState) : TxSet → List Evm.Address
  | .destroyed => h.destroyed
  | .touched   => h.touched

def AExp.eval (c : Ctx) : AExp → Evm.Address
  | .var x => c.addr x
  | .lit n => Evm.Address.ofNat n

/-- The spec's original-value lookup (`Berlin.Vm.Effect.getOriginal`) on the cache. -/
def getOrig (origs : List ((Evm.Address × Evm.U256) × Evm.U256)) (a : Evm.Address) (k fb : Evm.U256) :
    Evm.U256 :=
  match origs.find? (fun (p, _) => p = (a, k)) with
  | some (_, v) => v
  | none        => fb

/-- The spec's cache insert (`Berlin.Vm.Effect.cacheOriginal`). -/
def putOrig (origs : List ((Evm.Address × Evm.U256) × Evm.U256)) (a : Evm.Address) (k v : Evm.U256) :
    List ((Evm.Address × Evm.U256) × Evm.U256) :=
  if origs.any (fun (p, _) => p = (a, k)) then origs else origs ++ [((a, k), v)]

/-- The SSTORE gas schedules: one emitted native routine each, `eita_sstore_gas_<name>`
    (`Evm.CL.ARM64.SstoreGas`; `SstoreGasSem` proves each equal to its spec function, the
    `plan` below). -/
inductive SstoreSched where
  | legacy | eip1283 | eip2200 | berlin | london
  deriving DecidableEq, Repr

/-- The fork dispatch — THE one copy: the term's meaning (`sstorePlan`) and the emitted C
    dispatch (`Evm.CL.EffectC.sstoreDispatchC`) both read it. EIP-1283 at Constantinople only (Petersburg
    reverts it), EIP-2200 at Istanbul/Muir Glacier, EIP-2929 at Berlin, EIP-3529 from London. -/
def SstoreSched.ofFork (k : Nat) : SstoreSched :=
  if k = 6 then .eip1283 else if k < 8 then .legacy else if k < 10 then .eip2200
  else if k = 10 then .berlin else .london

/-- Each schedule's (cost, new refund counter): the spec function the fork's handler uses. -/
def SstoreSched.plan : SstoreSched → Nat → Evm.U256 → Evm.U256 → Evm.U256 → Bool → Nat × Nat
  | .legacy,  r, _, c, n, _    => Evm.Frontier.Vm.Instructions.sstoreGas r c n
  | .eip1283, r, o, c, n, _    => Evm.Constantinople.Vm.Instructions.sstoreGas r o c n
  | .eip2200, r, o, c, n, _    => Evm.Istanbul.Vm.Instructions.sstoreGas r o c n
  | .berlin,  r, o, c, n, cold => Evm.Berlin.Vm.Instructions.Storage.sstoreGas r cold o c n
  | .london,  r, o, c, n, cold => Evm.London.Vm.Effect.sstoreGas r cold o c n

/-- The native routine's name (`eita_sstore_gas_<name>`, `%sstore-gas-<name>`). -/
def SstoreSched.name : SstoreSched → String
  | .legacy => "legacy" | .eip1283 => "eip1283" | .eip2200 => "eip2200"
  | .berlin => "berlin" | .london => "london"

/-- Each fork's SSTORE (cost, new refund counter): its schedule's plan. -/
def sstorePlan (k refund : Nat) (o c n : Evm.U256) (cold : Bool) : Nat × Nat :=
  (SstoreSched.ofFork k).plan refund o c n cold

/-- From London on the dispatch is constant (so the emitted `t` arm covers every later
    ordinal). -/
theorem SstoreSched.ofFork_ge (k : Nat) (h : k ≥ 11) : SstoreSched.ofFork k = .london := by
  unfold SstoreSched.ofFork; split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | omega

/-- The last fork ordinal (`Evm.Fork.amsterdam`); the emitted dispatch lists every ordinal up
    to it and sends the rest to `ofFork_ge`'s schedule. -/
def maxForkOrd : Nat := 21

def WExp.eval (c : Ctx) (h : HState) : WExp → Evm.U256
  | .var x     => c.word x
  | .zero      => 0
  | .balance a => h.state.getBalance (a.eval c)
  | .add a b   => a.eval c h + b.eval c h
  | .sub a b   => a.eval c h - b.eval c h
  | .mul a b   => a.eval c h * b.eval c h
  | .sload a k => h.state.getStorage (a.eval c) (k.eval c h)
  | .orig a k fb => getOrig h.origs (a.eval c) (k.eval c h) (fb.eval c h)
  | .ofAddr a  => Evm.U256.ofNat (a.eval c).toNat
  | .lit n     => Evm.U256.ofNat n

/-- EELS `is_account_dead` on the spec state (= `SpuriousDragon` `isDead`). -/
def isDead (s : State) (a : Evm.Address) : Bool :=
  if s.accountExists a then (s.getAccount a).isEmpty else true

/-- The child run's parts. -/
def ChildRes.isErr : ChildRes → Bool | .err => true | _ => false
def ChildRes.isRev : ChildRes → Bool | .ok _ _ _ r => r | _ => false
def ChildRes.gas : ChildRes → Nat | .ok _ g _ _ => g | _ => 0
def ChildRes.out : ChildRes → Evm.Bytes | .ok _ _ o _ => o | _ => Evm.Bytes.empty

def BExp.eval (c : Ctx) (h : HState) : BExp → Bool
  | .lit b       => b
  | .var x       => c.bool x
  | .not p       => !(p.eval c h)
  | .and p q     => p.eval c h && q.eval c h
  | .or p q      => p.eval c h || q.eval c h
  | .forkGe n    => decide (c.fork ≥ n)
  | .addrEq a b  => decide (a.eval c = b.eval c)
  | .pos w       => decide (w.eval c h ≠ 0)
  | .weq a b     => decide (a.eval c h = b.eval c h)
  | .present a   => h.state.accountExists (a.eval c)
  | .dead a      => isDead h.state (a.eval c)
  | .created a   => h.created.contains (a.eval c)
  | .destroyed a => h.destroyed.contains (a.eval c)
  | .wlt a b     => decide ((a.eval c h).toNat < (b.eval c h).toNat)
  | .nonceMax a  => decide ((h.state.getAccount (a.eval c)).nonce = Evm.Frontier.Vm.Create.maxNonce)
  | .collides a  => Evm.Frontier.Vm.Create.collides h.state (a.eval c)
  | .childErr r  => (c.res r).isErr
  | .childRev r  => (c.res r).isRev
  | .childEF r   => decide (0 < (c.res r).out.size ∧ (c.res r).out.get! 0 = (0xEF : UInt8))
  | .chainVeto _ _ _ => false
  | .kindEq n    => decide (c.nat "kind" = n)
  | .pre a       => (c.pre (a.eval c)).isSome
  | .touchedHas a => h.touched.contains (a.eval c)
  | .codeEmpty a => decide ((h.state.getAccount (a.eval c)).code.size = 0)
  | .delegated a => (Evm.Prague.State.parseDelegation (h.state.getAccount (a.eval c)).code).isSome
  | .ge x n      => decide (c.nat x ≥ n)
  | .nonceIs a x => decide ((h.state.getAccount (a.eval c)).nonce = c.nat x)

def GExp.eval (c : Ctx) (h : HState) : GExp → Nat
  | .lit n             => n
  | .ofBool p          => if p.eval c h then 1 else 0
  | .forkOrd           => c.fork
  | .ite p t e         => if p.eval c h then t.eval c h else e.eval c h
  | .add a b           => a.eval c h + b.eval c h
  | .formula0 _ e      => e.eval (fun _ => 0)
  | .formula1 _ e x a  => e.eval (fun y => if y = x then a.eval c h else 0)
  | .formulaF _ e x a  => e.eval (fun y => if y = x then a.eval c h else if y = "fork-ord" then c.fork else 0)
  | .var x             => c.nat x
  | .sub a b           => a.eval c h - b.eval c h
  | .childGas r        => (c.res r).gas
  | .childLen r        => (c.res r).out.size
  | .ofWord w          => (w.eval c h).toNat
  | .nonce a           => (h.state.getAccount (a.eval c)).nonce
  | .mul a b           => a.eval c h * b.eval c h
  | .formulaK _ e      => e.eval (fun y => if y = "fork-ord" then c.fork else 0)
  | .formulaK2 _ e x a y b =>
      e.eval (fun z => if z = "fork-ord" then c.fork else if z = x then a.eval c h
                       else if z = y then b.eval c h else 0)
  | .len l             => (c.pairs l).length

/-- Add `a` to an insertion-ordered set (the spec's list sets: `touched`,
    `selfDestructSet`, `accessedAddresses` — `SpuriousDragon.Vm.touchAddr`,
    `Berlin.Vm.Effect.warmAddr` are this on their field). -/
def insertSet (l : List Evm.Address) (a : Evm.Address) : List Evm.Address :=
  if l.contains a then l else l ++ [a]

/-- The context with authorization `a` current and its fields bound (`forAuths`). -/
def Ctx.withAuth (c : Ctx) (a : Evm.Prague.Authorization) : Ctx :=
  { c with cur := a,
           word := fun y => if y = "a-chain" then a.chainId else if y = "a-yp" then a.yParity
                            else if y = "a-r" then a.r else if y = "a-s" then a.s else c.word y,
           addr := fun y => if y = "a-addr" then a.address else c.addr y,
           nat := fun y => if y = "a-nonce" then a.nonce.toNat else c.nat y }

/-- The context with pair `p` of a `forPairs` list bound (`p-addr`, `p-n`). -/
def Ctx.withPair (c : Ctx) (p : Evm.Address × Nat) : Ctx :=
  { c with addr := fun y => if y = "p-addr" then p.1 else c.addr y,
           nat := fun y => if y = "p-n" then p.2 else c.nat y }

def Stmt.run (c : Ctx) : Stmt → HState → HState
  | .skip, h => h
  | .seq s t, h => t.run c (s.run c h)
  | .ite p s t, h => if p.eval c h then s.run c h else t.run c h
  | .letW x w s, h => s.run { c with word := fun y => if y = x then w.eval c h else c.word y } h
  | .letB x p s, h => s.run { c with bool := fun y => if y = x then p.eval c h else c.bool y } h
  | .warm g a x s, h =>
      if g.eval c h then
        s.run { c with bool := fun y => if y = x then !h.accessed.contains (a.eval c) else c.bool y }
              { h with accessed := insertSet h.accessed (a.eval c) }
      else s.run { c with bool := fun y => if y = x then false else c.bool y } h
  | .fault _, h => h
  | .touch a, h => if c.fork ≥ 4 then { h with touched := insertSet h.touched (a.eval c) } else h
  | .markPresent a, h => { h with state := h.state.touchAccount (a.eval c) }
  | .markDestroyed a, h => { h with destroyed := insertSet h.destroyed (a.eval c) }
  | .refund g, h => { h with refund := h.refund + g.eval c h }
  | .setBalance a w, h =>
      let acc : Account := { (h.state.getAccount (a.eval c)) with balance := w.eval c h }
      { h with state := h.state.setAccount (a.eval c) acc }
  | .credit a w, h => { h with state := h.state.addBalance (a.eval c) (w.eval c h) }
  | .delta a w, h =>
      if w.eval c h = 0 then h else { h with state := h.state.addBalance (a.eval c) (w.eval c h) }
  | .deleteAccount a, h => { h with state := h.state.deleteAccount (a.eval c) }
  | .forEach st x body, h =>
      (st.get h).foldl (fun h' a => body.run { c with addr := fun y => if y = x then a else c.addr y } h') h
  | .faultSlot _ _, h => h
  | .warmSlot g a k x s, h =>
      if g.eval c h then
        s.run { c with bool := fun y => if y = x then !h.slots.contains (a.eval c, k.eval c h) else c.bool y }
              { h with slots := if h.slots.contains (a.eval c, k.eval c h) then h.slots
                                else h.slots ++ [(a.eval c, k.eval c h)] }
      else s.run { c with bool := fun y => if y = x then false else c.bool y } h
  | .origRecord a k w, h => { h with origs := putOrig h.origs (a.eval c) (k.eval c h) (w.eval c h) }
  | .sstoreGas o cur n cold, h =>
      let p := sstorePlan c.fork h.refund (o.eval c h) (cur.eval c h) (n.eval c h) (cold.eval c h)
      { h with refund := p.2, gas := h.gas + p.1 }
  | .setStorage a k w, h => { h with state := h.state.setStorage (a.eval c) (k.eval c h) (w.eval c h) }
  | .transferFact k s d w _, h => { h with facts := h.facts ++ [(k, s.eval c, d.eval c, w.eval c h)] }
  | .charge g, h => { h with gas := h.gas + g.eval c h }
  | .ret w, h => { h with out := w.eval c h }
  | .iteG a b lt ge, h => if a.eval c h < b.eval c h then lt.run c h else ge.run c h
  | .bumpNonce a, h =>
      let acc := h.state.getAccount (a.eval c)
      { h with state := h.state.setAccount (a.eval c) { acc with nonce := acc.nonce + 1 } }
  | .markCreated a, h =>
      { h with created := if h.created.contains (a.eval c) then h.created else a.eval c :: h.created }
  | .save x s, h => s.run { c with snaps := fun y => if y = x then h else c.snaps y } h
  | .rollback x, h => { c.snaps x with gas := h.gas, out := h.out, rdata := h.rdata }
  | .runChild _ _ _ fwd r body, h =>
      let res := c.child h (fwd.eval c h)
      let h1 := match res with
        | .err => h
        | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts }
      body.run { c with res := fun y => if y = r then res else c.res y } h1
  | .depositCode a r, h =>
      let acc := h.state.getAccount (a.eval c)
      { h with state := h.state.setAccount (a.eval c) { acc with code := (c.res r).out } }
  | .retData r, h => { h with rdata := (c.res r).out }
  | .frameRow _ _ _ _ _ body, h => body.run c h
  | .letA x p a b s, h =>
      s.run { c with addr := fun y => if y = x then (if p.eval c h then a.eval c else b.eval c) else c.addr y } h
  | .callPlan cold vf na dl ga av s, h =>
      let p := Evm.Frontier.Vm.Call.plan (Evm.Frontier.Vm.Call.Rules.ofOrd c.fork)
        (cold.eval c h) (vf.eval c h) (na.eval c h) (dl.eval c h) (ga.eval c h) (av.eval c h)
      s.run { c with nat := fun y => if y = "charge" then p.charge else if y = "fwd" then p.forward
                                     else if y = "stip" then p.stipend else c.nat y } h
  | .runCall g r body, h =>
      let res := c.child h (g.eval c h)
      let h1 := match res with
        | .err => h
        | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts }
      body.run { c with res := fun y => if y = r then res else c.res y } h1
  | .runPre a g r body, h =>
      let res : ChildRes := match c.pre (a.eval c) with
        | some p => match p c.input (g.eval c h) with
          | .ok (out, g') => .ok h g' out false
          | .error _ => .err
        | none => .err
      body.run { c with res := fun y => if y = r then res else c.res y } h
  | .callRow _ _ _ _ _ _ body, h => body.run c h
  | .chainCall _ _ _ _ _ rest, h => rest.run c h
  | .chainCallVeto _ _ _ _ _ _ rest, h => rest.run c h
  | .chainLog _ _ _, h => h
  | .wipeStorage a, h => { h with state := h.state.destroyStorage (a.eval c) }
  | .reject n, h => { h with rej := n }
  | .letLt x a b s, h =>
      s.run { c with bool := fun y => if y = x then decide (a.eval c h < b.eval c h) else c.bool y } h
  | .debit a g, h =>
      let acc := h.state.getAccount (a.eval c)
      { h with state := h.state.setAccount (a.eval c)
                 { acc with balance := acc.balance - Evm.U256.ofNat (g.eval c h) } }
  | .warmTx g s t cb, h =>
      if g.eval c h then
        { h with accessed := (Evm.Frontier.Vm.Tx.seedAddrs c.fork (s.eval c) (t.eval c) (cb.eval c)
                                c.accessList).foldl insertSet h.accessed,
                 slots := (Evm.Frontier.Vm.Tx.seedSlots c.accessList).foldl
                            Evm.Frontier.Vm.Tx.insSlot h.slots }
      else h
  | .warmSys, h => { h with accessed := c.sysSeed.foldl insertSet h.accessed }
  | .forAuths body, h => c.auths.foldl (fun h' a => body.run (c.withAuth a) h') h
  | .recoverAuth x miss found, h =>
      match c.recover c.cur with
      | Option.none => miss.run c h
      | some au => found.run { c with addr := fun y => if y = x then au else c.addr y } h
  | .setDelegation a d, h =>
      let acc := h.state.getAccount (a.eval c)
      { h with state := h.state.setAccount (a.eval c)
                 { acc with code := if d.eval c = 0 then Evm.Bytes.empty
                                    else Evm.Frontier.Vm.Tx.designator (d.eval c) } }
  | .letDeleg x hx g a s, h =>
      let d := if g.eval c h then Evm.Prague.State.parseDelegation (h.state.getAccount (a.eval c)).code
               else Option.none
      s.run { c with addr := fun y => if y = x then d.getD 0 else c.addr y,
                     bool := fun y => if y = hx then d.isSome else c.bool y } h
  | .runTx g r body, h =>
      let res := c.child h (g.eval c h)
      let h1 := match res with
        | .err => h
        | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts, rej := h.rej }
      body.run { c with res := fun y => if y = r then res else c.res y } h1
  | .runPreTx a g r body, h =>
      let res : ChildRes := match c.pre (a.eval c) with
        | some p => match p c.input (g.eval c h) with
          | .ok (out, g') => .ok h g' out false
          | .error _ => .err
        | Option.none => .err
      body.run { c with res := fun y => if y = r then res else c.res y } h
  | .txRow _ body, h => body.run c h
  | .chainTxCall _ _ _ rest, h => rest.run c h
  | .chainTxVeto _ _ _ _ rest, h => rest.run c h
  | .pay a g, h => { h with state := h.state.addBalance (a.eval c) (Evm.U256.ofNat (g.eval c h)) }
  | .forPairs l body, h => (c.pairs l).foldl (fun h' p => body.run (c.withPair p) h') h

/-! ## CL printer

Each primitive is one call into the storage view / journal (src/evm/). `*fork-ord*`
is the fork's ordinal; the emitted defun binds `%gas`, the charge accumulator it returns. -/

def TxSet.toCL : TxSet → String
  | .destroyed => "*selfdestructed*"
  | .touched   => "*touched*"

def AExp.toCL : AExp → String
  | .var x => x
  | .lit n => toString n

def WExp.toCL : WExp → String
  | .var x     => x
  | .zero      => "0"
  | .balance a => s!"(balance-of *current-world* {a.toCL})"
  | .add a b   => s!"(u256 (+ {a.toCL} {b.toCL}))"
  | .sub a b   => s!"(u256 (- {a.toCL} {b.toCL}))"
  | .mul a b   => s!"(u256 (* {a.toCL} {b.toCL}))"
  | .sload a k => s!"(storage-of *current-world* {a.toCL} {k.toCL})"
  | .orig a k fb => s!"(orig-get! {a.toCL} {k.toCL} {fb.toCL})"
  | .ofAddr a  => a.toCL
  | .lit n     => toString n

def BExp.toCL : BExp → String
  | .lit b       => if b then "t" else "nil"
  | .var x       => x
  | .not p       => s!"(not {p.toCL})"
  | .and p q     => s!"(and {p.toCL} {q.toCL})"
  | .or p q      => s!"(or {p.toCL} {q.toCL})"
  | .forkGe n    => s!"(>= *fork-ord* {n})"
  | .addrEq a b  => s!"(= {a.toCL} {b.toCL})"
  | .pos w       => s!"(plusp {w.toCL})"
  | .weq a b     => s!"(= {a.toCL} {b.toCL})"
  | .present a   => s!"(world-account-present-p {a.toCL})"
  | .dead a      => s!"(world-account-empty-p {a.toCL})"
  | .created a   => s!"(created-p! {a.toCL})"
  | .destroyed a => s!"(destroyed-p {a.toCL})"
  | .wlt a b     => s!"(< {a.toCL} {b.toCL})"
  | .nonceMax a  => s!"(= (nonce-of *current-world* {a.toCL}) {Evm.Frontier.Vm.Create.maxNonce})"
  | .collides a  =>
      s!"(or (plusp (length (code-of *current-world* {a.toCL}))) (plusp (nonce-of *current-world* {a.toCL})))"
  | .childErr r  => s!"(eq (child-status {r}) :halt)"
  | .childRev r  => s!"(eq (child-status {r}) :revert)"
  | .childEF r   => s!"(child-output-ef-p {r})"
  | .chainVeto s d w => s!"(eq :revert (chain-frame-init {s.toCL} {d.toCL} {w.toCL}))"
  | .kindEq n    => s!"(= kind {n})"
  | .pre a       => s!"(precompile-address-p {a.toCL})"
  | .touchedHas a => s!"(touched-p {a.toCL})"
  | .codeEmpty a => s!"(zerop (length (code-of *current-world* {a.toCL})))"
  | .delegated a => s!"(and (delegation-target (code-of *current-world* {a.toCL})) t)"
  | .ge x n      => s!"(>= {x} {n})"
  | .nonceIs a x => s!"(= (nonce-of *current-world* {a.toCL}) {x})"

def GExp.toCL : GExp → String
  | .lit n             => toString n
  | .ofBool p          => s!"(if {p.toCL} 1 0)"
  | .forkOrd           => "*fork-ord*"
  | .ite p t e         => s!"(if {p.toCL} {t.toCL} {e.toCL})"
  | .add a b           => s!"(+ {a.toCL} {b.toCL})"
  | .formula0 n _      => s!"({n})"
  | .formula1 n _ _ a  => s!"({n} {a.toCL})"
  | .formulaF n _ _ a  => s!"({n} {a.toCL} *fork-ord*)"
  | .var x             => x
  | .sub a b           => s!"(max 0 (- {a.toCL} {b.toCL}))"
  | .childGas r        => s!"(child-gas {r})"
  | .childLen r        => s!"(length (child-output {r}))"
  | .ofWord w          => w.toCL
  | .nonce a           => s!"(nonce-of *current-world* {a.toCL})"
  | .mul a b           => s!"(* {a.toCL} {b.toCL})"
  | .formulaK n _      => s!"({n} *fork-ord*)"
  | .formulaK2 n _ _ a _ b => s!"({n} *fork-ord* {a.toCL} {b.toCL})"
  | .len l             => s!"(length {l})"

mutual
/-- The forms of a statement, flattened through `seq` (so a `progn` body stays flat). -/
def Stmt.forms (ind : String) : Stmt → List String
  | .skip => []
  | .seq s t => s.forms ind ++ t.forms ind
  | .ite p (.reject n) t =>
      -- a validation chain (`ite p (reject n) …`) prints flat, as one `cond`
      [s!"(cond ({p.toCL} (setf %rej {n}))\n{Stmt.condArms ind t})"]
  | .ite p s .skip => [s!"(when {p.toCL}\n{Stmt.body (ind ++ "  ") s})"]
  | .ite p s t =>
      [s!"(if {p.toCL}\n{ind}    (progn\n{Stmt.body (ind ++ "      ") s})\n{ind}    (progn\n{Stmt.body (ind ++ "      ") t}))"]
  | .letW x w s => [s!"(let (({x} {w.toCL}))\n{Stmt.body (ind ++ "  ") s})"]
  | .letB x p s => [s!"(let (({x} {p.toCL}))\n{Stmt.body (ind ++ "  ") s})"]
  | .warm g a x s =>
      [s!"(let (({x} (and {g.toCL} (access-addr! {a.toCL}))))\n{ind}  (declare (ignorable {x}))\n{Stmt.body (ind ++ "  ") s})"]
  | .fault a => [s!"(fault-account! {a.toCL})"]
  | .touch a => [s!"(touch! {a.toCL})"]
  | .markPresent a => [s!"(mark-account-present! (current-arena) {a.toCL})"]
  | .markDestroyed a =>
      [s!"(mark-destroyed! {a.toCL})"]
  | .refund g => [s!"(refund-add! {g.toCL})"]
  | .setBalance a w =>
      [s!"(journal-balance! (current-arena) {a.toCL})", s!"(setf (balance-of *current-world* {a.toCL}) {w.toCL})"]
  | .credit a w =>
      [s!"(journal-balance! (current-arena) {a.toCL})", s!"(incf (balance-of *current-world* {a.toCL}) {w.toCL})"]
  | .delta a w => [s!"(balance-delta! *current-world* {a.toCL} {w.toCL})"]
  | .deleteAccount a => [s!"(account-delete! *current-world* {a.toCL})"]
  | .forEach st x body =>
      [s!"(dolist ({x} (tx-set-addrs {st.toCL}))\n{Stmt.body (ind ++ "  ") body})"]
  | .faultSlot a k => [s!"(fault-slot! {a.toCL} {k.toCL})"]
  | .warmSlot g a k x s =>
      [s!"(let (({x} (and {g.toCL} (access-slot! {a.toCL} {k.toCL}))))\n{Stmt.body (ind ++ "  ") s})"]
  | .origRecord a k w => [s!"(orig-record! {a.toCL} {k.toCL} {w.toCL})"]
  | .sstoreGas o cur n cold =>
      [s!"(multiple-value-bind (%cost %refund) (sstore-gas-native (ts-refund) {o.toCL} {cur.toCL} {n.toCL} {cold.toCL})",
       s!"  (let ((%d (- %refund (ts-refund)))) (unless (zerop %d) (refund-add! %d)))",
       s!"  (incf %gas %cost))"]
  | .setStorage a k w =>
      [s!"(journal-push! (current-arena) 0 {a.toCL} {k.toCL} (storage-of *current-world* {a.toCL} {k.toCL}))",
       s!"(setf (storage-of *current-world* {a.toCL} {k.toCL}) {w.toCL})"]
  | .transferFact k s d w ch =>
      [s!"(observe-transfer! {k} {if ch then "(1+ *call-depth*)" else "*call-depth*"} {s.toCL} {d.toCL} {w.toCL})"]
  | .charge g => [s!"(incf %gas {g.toCL})"]
  | .ret w => [s!"(setf %out {w.toCL})"]
  | .iteG a b lt .skip => [s!"(when (< {a.toCL} {b.toCL})\n{Stmt.body (ind ++ "  ") lt})"]
  | .iteG a b lt ge =>
      [s!"(if (< {a.toCL} {b.toCL})\n{ind}    (progn\n{Stmt.body (ind ++ "      ") lt})\n{ind}    (progn\n{Stmt.body (ind ++ "      ") ge}))"]
  | .bumpNonce a =>
      [s!"(journal-nonce! (current-arena) {a.toCL})", s!"(incf (nonce-of *current-world* {a.toCL}))"]
  | .markCreated a => [s!"(journal-created! (current-arena) {a.toCL})", s!"(created-insert! {a.toCL})"]
  | .save x s =>
      [s!"(let (({x} (mem-ref (current-arena) :uint64 0)) ({x}-facts (observe-mark)))\n{Stmt.body (ind ++ "  ") s})"]
  | .rollback x => [s!"(revert-journal-to (current-arena) {x})", s!"(observe-revert! {x}-facts)"]
  | .runChild sa n w fwd r body =>
      [s!"(let (({r} (run-init-frame! {sa.toCL} {n.toCL} {w.toCL} init-code {fwd.toCL})))\n{ind}  (setf %child {r})\n{Stmt.body (ind ++ "  ") body})"]
  | .depositCode a r => [s!"(setf (code-of *current-world* {a.toCL}) (child-output {r}))"]
  | .retData r => [s!"(setf %rd (child-output {r}))"]
  | .frameRow sa n w fwd base body =>
      [s!"(with-observed-frame (:kind kind :depth (1+ *call-depth*) :from {sa.toCL} :to {n.toCL} :value {w.toCL} :selector -1 :input-len (length init-code) :gas {fwd.toCL} :gas-used (- %gas {base.toCL}) :status (child-frame-status %child %out))\n{Stmt.body (ind ++ "  ") body})"]
  | .letA x p a b s => [s!"(let (({x} (if {p.toCL} {a.toCL} {b.toCL})))\n{Stmt.body (ind ++ "  ") s})"]
  | .callPlan cold vf na dl ga av s =>
      [s!"(multiple-value-bind (charge fwd stip) (call-gas-plan {cold.toCL} {vf.toCL} {na.toCL} {dl.toCL} {ga.toCL} {av.toCL})\n{ind}  (declare (ignorable charge fwd stip))\n{Stmt.body (ind ++ "  ") s})"]
  | .runCall g r body =>
      [s!"(let (({r} (run-call-frame! kind self to value input-ptr input-len (or deleg to) {g.toCL})))\n{Stmt.body (ind ++ "  ") body})"]
  | .runPre a g r body =>
      [s!"(let (({r} (precompile-run! {a.toCL} input-ptr input-len {g.toCL})))\n{Stmt.body (ind ++ "  ") body})"]
  | .callRow sa n w g base stip body =>
      [s!"(with-observed-frame (:kind kind :depth (1+ *call-depth*) :from {sa.toCL} :to {n.toCL} :value (if (< kind 2) {w.toCL} 0) :selector (input-selector input-ptr input-len) :input-len input-len :gas {g.toCL} :gas-used (- (+ %gas {stip.toCL}) {base.toCL}) :status *last-sub-outcome*)\n{Stmt.body (ind ++ "  ") body})"]
  | .chainCall a g base stip snap rest =>
      [s!"(if (and *chain-precompile-p* (funcall *chain-precompile-p* {a.toCL}))\n{ind}    (multiple-value-bind (%ok %used %o) (chain-precompile-call! {a.toCL} kind self input-ptr input-len {g.toCL} static value {snap} {snap}-facts)\n{ind}      (incf %gas (max 0 (+ {base.toCL} %used (- {stip.toCL}))))\n{ind}      (setf %out (if %ok 1 0) %rd %o))\n{ind}    (progn\n{Stmt.body (ind ++ "      ") rest}))"]
  | .chainCallVeto gd s d w r veto rest =>
      [s!"(multiple-value-bind (%verdict %vout) (and {gd.toCL} (chain-frame-init {s.toCL} {d.toCL} {w.toCL} :emit-log nil))\n{ind}  (if (eq %verdict :revert)\n{ind}      (let (({r} (list :revert 0 %vout)))\n{ind}        (setf *last-sub-outcome* :revert)\n{Stmt.body (ind ++ "        ") veto})\n{ind}      (progn\n{Stmt.body (ind ++ "        ") rest})))"]
  | .chainLog s d w =>
      [s!"(when *chain-value-transfer-log-hook* (funcall *chain-value-transfer-log-hook* {s.toCL} {d.toCL} {w.toCL}))"]
  | .wipeStorage a => [s!"(storage-wipe-journaled! {a.toCL})"]
  | .reject n => [s!"(setf %rej {n})"]
  | .letLt x a b s => [s!"(let (({x} (< {a.toCL} {b.toCL})))\n{ind}  (declare (ignorable {x}))\n{Stmt.body (ind ++ "  ") s})"]
  | .debit a g =>
      [s!"(journal-balance! (current-arena) {a.toCL})", s!"(decf (balance-of *current-world* {a.toCL}) {g.toCL})"]
  | .warmTx g s t cb => [s!"(when {g.toCL} (warm-tx-seed! {s.toCL} {t.toCL} {cb.toCL} access-list))"]
  | .warmSys => ["(warm-system-seed!)"]
  | .forAuths body =>
      [s!"(dolist (%auth auth-list)\n{ind}  (let ((a-chain (getf %auth :chain-id)) (a-addr (getf %auth :address)) (a-nonce (getf %auth :nonce))\n{ind}        (a-yp (getf %auth :y-parity)) (a-r (getf %auth :r)) (a-s (getf %auth :s)))\n{ind}    (declare (ignorable a-chain a-addr a-nonce a-yp a-r a-s))\n{Stmt.body (ind ++ "    ") body}))"]
  | .recoverAuth x miss found =>
      [s!"(let (({x} (recover-authority a-chain a-addr a-nonce a-yp a-r a-s)))\n{ind}  (if {x}\n{ind}      (progn\n{Stmt.body (ind ++ "        ") found})\n{ind}      (progn\n{Stmt.body (ind ++ "        ") miss})))"]
  | .setDelegation a d =>
      [s!"(if (zerop {d.toCL}) (code-clear! *current-world* {a.toCL}) (setf (code-of *current-world* {a.toCL}) (designator-bytes {d.toCL})))"]
  | .letDeleg x hx g a s =>
      [s!"(let* (({x} (and {g.toCL} (delegation-target (code-of *current-world* {a.toCL})))) ({hx} (and {x} t)) ({x} (or {x} 0)))\n{ind}  (declare (ignorable {x} {hx}))\n{Stmt.body (ind ++ "  ") s})"]
  | .runTx g r body =>
      [s!"(let (({r} (run-tx-frame! create sender target (if hasdeleg deleg target) value data block-ctx {g.toCL})))\n{ind}  (setf %child {r})\n{Stmt.body (ind ++ "  ") body})"]
  | .runPreTx a g r body =>
      [s!"(let (({r} (precompile-run-bytes! {a.toCL} data {g.toCL})))\n{ind}  (setf %child {r})\n{Stmt.body (ind ++ "  ") body})"]
  | .txRow g body =>
      [s!"(with-observed-frame (:kind (if create 4 0) :depth 0 :from sender :to target :value value :selector (if create -1 (input-selector data (length data))) :input-len (length data) :gas {g.toCL} :gas-used %gas :status (tx-frame-status %child %out))\n{Stmt.body (ind ++ "  ") body})"]
  | .chainTxCall a g snap rest =>
      [s!"(if (and *chain-precompile-p* (funcall *chain-precompile-p* {a.toCL}))\n{ind}    (multiple-value-bind (%ok %used) (chain-tx-precompile! {a.toCL} sender data {g.toCL} value {snap} {snap}-facts)\n{ind}      (incf %gas %used)\n{ind}      (setf %out (if %ok 1 0) %child (list (cond (%ok :return) ((< %used {g.toCL}) :revert) (t :halt)) 0 nil)))\n{ind}    (progn\n{Stmt.body (ind ++ "      ") rest}))"]
  | .pay a g => [s!"(block-credit! {a.toCL} {g.toCL})"]
  | .forPairs l body =>
      [s!"(loop for (p-addr . p-n) in {l}\n{ind}      do (progn\n{Stmt.body (ind ++ "            ") body}))"]
  | .chainTxVeto sa d w veto rest =>
      [s!"(if (and (plusp {w.toCL}) (eq :revert (chain-frame-init {sa.toCL} {d.toCL} {w.toCL})))\n{ind}    (progn (setf %child (list :revert 0 nil))\n{Stmt.body (ind ++ "      ") veto})\n{ind}    (progn\n{Stmt.body (ind ++ "      ") rest}))"]

/-- The remaining arms of a validation chain, then its `t` arm. -/
def Stmt.condArms (ind : String) : Stmt → String
  | .ite p (.reject n) t => s!"{ind}      ({p.toCL} (setf %rej {n}))\n{Stmt.condArms ind t}"
  | s => s!"{ind}      (t\n{Stmt.body (ind ++ "        ") s})"

/-- The forms of `s`, one per line at indentation `i`. -/
def Stmt.body (i : String) (s : Stmt) : String :=
  match s.forms i with
  | [] => i ++ "nil"
  | fs => String.intercalate "\n" (fs.map (i ++ ·))
end

/-- A callback as an emitted defun: inputs, body, the charged gas as its value. -/
def Stmt.toDefun (name : String) (params : List String) (s : Stmt) : String :=
  s!"(defun {name} ({" ".intercalate params})\n  (let ((%gas 0))\n{Stmt.body "    " s}\n    %gas))"

/-- A callback that runs a child frame: binds the child (`%child`) and the return data
    (`%rd`), returns `(values gas out rd)`. -/
def Stmt.toDefunChild (name : String) (params : List String) (s : Stmt) : String :=
  s!"(defun {name} ({" ".intercalate params})\n  (let ((%gas 0) (%out 0) (%rd nil) (%child nil))\n{Stmt.body "    " s}\n    (values %gas %out %rd)))"

/-- The tx's effect: binds the gas the message used (`%gas`), the success flag (`%out`), the
    rejection (`%rej`) and the top frame's result (`%child`); returns `(values gas out rej)`. -/
def Stmt.toDefunTx (name : String) (params : List String) (s : Stmt) : String :=
  s!"(defun {name} ({" ".intercalate params})\n  (let ((%gas 0) (%out 0) (%rej 0) (%child nil) (%rd nil))\n    (declare (ignorable %child %rd))\n{Stmt.body "    " s}\n    (values %gas %out %rej)))"

end Evm.CL.EffectIR
