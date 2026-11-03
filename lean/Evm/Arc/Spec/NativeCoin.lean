/-
  Evm.Arc.Spec.NativeCoin — Circle Arc's native-USDC precompiles.

  Source of truth: `circlefin/arc-node` (Apache-2.0, reth/revm fork), HEAD
  6e76402 (2026-09-25):
    crates/precompiles/src/precompile_provider.rs       registration (L43-70)
    crates/precompiles/src/native_coin_authority.rs     NativeCoinAuthority 0x1800…0000
    crates/precompiles/src/native_coin_control.rs       NativeCoinControl   0x1800…0001
    crates/precompiles/src/helpers.rs                   metering, guards, transfer
    crates/precompiles/src/macros.rs                    selector dispatch (L95-135)
    crates/execution-config/src/native_coin_control.rs  blocklist slot (L23-46)
    crates/execution-config/src/hardforks.rs            Zero8 activation (L410-411)

  On Arc, USDC is the native coin. The ERC-20 surface at 0x3600…0000 is Circle's
  `FiatTokenProxy` → `NativeFiatTokenV2_2`, whose balances ARE native balances:
  `_balanceOf` is the BALANCE opcode and `_transfer` CALLs
  0x1800…0000 `transfer(from, to, amount)` — a stateful precompile. Genesis
  gives every 0x1800…00xx a one-byte placeholder code `0x01`; a stock EVM that
  executes it (ADD on an empty stack) burns all forwarded gas and reverts — the
  exact Eita↔Arc delta this module closes (blocks 56284998–56285001, every
  divergent tx routed through 0x1800…0000/0001).

  Gas is metered INSIDE the precompile against the forwarded gas (revm `Gas`),
  step by step, with EIP-2929 warm/cold prices shared with the EVM's access
  set (the precompile address itself is NOT pre-warmed: the CALL pays its own
  2600/100). Early reverts charge gas-so-far + a flat 200 penalty
  (`PRECOMPILE_EARLY_REVERT_GAS_PENALTY`, helpers.rs:82); OOG halts consume all
  forwarded gas (revm); reverts carry `Error(string)` data (helpers.rs:66).

  Shape: `runTransfer` / `runIsBlocklisted` are the executable semantics over a
  *view* — the world observations the host seam makes, in the order the source
  makes them. The success-path gas is ALSO given as a `GasEmit.Expr`
  (`transferGas`, `isBlocklistedGas`), emitted to `src/generated/host.lisp`
  as `spec-arc-*` and consumed by the CL seam (`src/chains/arc-precompiles.lisp`);
  the examples below kernel-check that the two agree on the canonical cases.
-/
import Evm.BaseTypes
import Evm.CL.GasEmit

namespace Evm.Arc.Spec.NativeCoin

open Evm.CL.GasEmit (Expr mkEnv)

/-! ## Addresses & selectors -/

def nativeCoinAuthorityAddress : Evm.Address :=
  Evm.Address.ofNat 0x1800000000000000000000000000000000000000
def nativeCoinControlAddress : Evm.Address :=
  Evm.Address.ofNat 0x1800000000000000000000000000000000000001
/-- The only caller allowed to move native coin: Circle's FiatToken proxy
    (`ALLOWED_CALLER_ADDRESS = NATIVE_FIAT_TOKEN_ADDRESS`, helpers.rs:31). -/
def nativeFiatTokenAddress : Evm.Address :=
  Evm.Address.ofNat 0x3600000000000000000000000000000000000000
/-- EIP-7708 log emitter (revm `SYSTEM_ADDRESS`). -/
def systemAddress : Evm.Address :=
  Evm.Address.ofNat 0xfffffffffffffffffffffffffffffffffffffffe

def selTransfer      : Nat := 0xbeabacc8   -- transfer(address,address,uint256)
def selMint          : Nat := 0x40c10f19   -- mint(address,uint256)
def selBurn          : Nat := 0x9dc29fac   -- burn(address,uint256)
def selBlocklist     : Nat := 0xe5c7160b   -- blocklist(address)
def selUnBlocklist   : Nat := 0x31b23020   -- unBlocklist(address)
def selTotalSupply   : Nat := 0x18160ddd   -- totalSupply()
def selIsBlocklisted : Nat := 0x8e204c43   -- isBlocklisted(address)

/-- Solidity mapping slot index of NativeCoinControl `isBlocklisted`
    (execution-config native_coin_control.rs:23); slot = keccak256(pad32(addr) ++ pad32(2)). -/
def blocklistMappingSlot : Nat := 2

/-! ## Gas constants (helpers.rs:38-46, :82; revm `gas::*`) -/

def precompileSstoreGas : Nat := 2900    -- PRECOMPILE_SSTORE_GAS_COST
def coldSloadGas        : Nat := 2100    -- PRECOMPILE_SLOAD_GAS_COST = COLD_SLOAD_COST
def warmReadGas         : Nat := 100     -- WARM_STORAGE_READ_COST
def coldAccountGas      : Nat := 2600    -- COLD_ACCOUNT_ACCESS_COST
def emptyAccountGas     : Nat := 25000   -- PRECOMPILE_EMPTY_ACCOUNT_GAS_COST
def earlyRevertPenalty  : Nat := 200     -- PRECOMPILE_EARLY_REVERT_GAS_PENALTY
def logBaseGas  : Nat := 375
def logTopicGas : Nat := 375
def logDataGas  : Nat := 8
/-- `emit_event` (helpers.rs:631): 375 + 375·topics + 8·data. `Transfer(address
    indexed, address indexed, uint256)` encodes as 3 topics (signature + 2
    indexed) and 32 data bytes: 375 + 1125 + 256 = 1756. -/
def transferLogGas : Nat := logBaseGas + 3 * logTopicGas + 32 * logDataGas

theorem transferLogGas_eq : transferLogGas = 1756 := rfl

/-! ## Outcome and metering -/

inductive Outcome where
  | success (gasUsed : Nat) (ret : Bool)     -- ABI-encoded bool output
  | revert  (gasUsed : Nat) (msg : String)   -- Error(string) revert data
  | oog                                      -- halt: all forwarded gas consumed
  deriving DecidableEq, Repr

/-- Metered step over (used, remaining): `none` = out of gas
    (`record_cost_or_out_of_gas`, helpers.rs:176). -/
def step (s : Nat × Nat) (c : Nat) : Option (Nat × Nat) :=
  if c ≤ s.2 then some (s.1 + c, s.2 - c) else none

/-- Early-path revert: gas-so-far + 200 penalty, OOG if the penalty itself
    does not fit (`new_reverted_with_penalty`, helpers.rs:109). -/
def earlyRevert (s : Nat × Nat) (msg : String) : Outcome :=
  match step s earlyRevertPenalty with
  | some s' => .revert s'.1 msg
  | none    => .oog

def accountLoadGas (cold : Bool) : Nat := if cold then coldAccountGas else warmReadGas
def slotReadGas    (cold : Bool) : Nat := if cold then coldSloadGas else warmReadGas

/-! ## `transfer(from, to, amount)` — native_coin_authority.rs:281-349 -/

/-- What the host observes, in source order. Warmth flags are *as observed at
    that step* (e.g. `blToCold` is false when `to = from` because the first
    read warmed the slot). -/
structure TransferView where
  gas           : Nat      -- forwarded gas
  isStatic      : Bool     -- static context (check_staticcall, helpers.rs:548)
  argsOk        : Bool     -- validated ABI decode (100 bytes, canonical addresses)
  callerIsToken : Bool     -- caller == 0x3600…0000
  isDelegate    : Bool     -- target/bytecode address ≠ precompile (check_delegatecall)
  fromAddr      : Nat
  toAddr        : Nat
  amount        : Nat
  blFromCold    : Bool     -- blocklist slot of `from`, cold at read
  blFrom        : Bool     -- blocklisted
  blToCold      : Bool
  blTo          : Bool
  fromCold      : Bool     -- account `from`, cold at load
  fromBalance   : Nat
  fromNonceZero : Bool     -- pre-Zero8 drain-to-empty check
  fromCodeEmpty : Bool
  toCold        : Bool
  toEmpty       : Bool     -- revm `is_empty` BEFORE the credit
  toSelfdestructed : Bool
  zero8         : Bool     -- ArcHardfork::Zero8 active (hardforks.rs:410)
  deriving Repr

/-- The precompile, clause by clause. Line refs are native_coin_authority.rs
    unless noted. -/
def runTransfer (v : TransferView) : Outcome :=
  let s0 : Nat × Nat := (0, v.gas)
  -- check_staticcall: spend all, revert (helpers.rs:548-562)
  if v.isStatic then .revert v.gas "State change during static call"
  -- abi_decode_raw_validated failure → +200 (L292-297)
  else if !v.argsOk then earlyRevert s0 "Execution reverted"
  -- caller gate (L300-306)
  else if !v.callerIsToken then earlyRevert s0 "Not enabled for native coin transfers"
  -- check_delegatecall (helpers.rs:565-592): penalty only under Zero8
  else if v.isDelegate then
    (if v.zero8 then earlyRevert s0 "Delegate call not allowed"
     else .revert 0 "Delegate call not allowed")
  -- zero addresses (L316-318)
  else if v.fromAddr = 0 ∨ v.toAddr = 0 then earlyRevert s0 "Zero address not allowed"
  else
  -- is_blocklisted(from) (L82-99 → helpers.rs read, 2100 cold / 100 warm)
  match step s0 (slotReadGas v.blFromCold) with
  | none => .oog
  | some s1 =>
  if v.blFrom then earlyRevert s1 "Blocked address" else
  match step s1 (slotReadGas v.blToCold) with
  | none => .oog
  | some s2 =>
  if v.blTo then earlyRevert s2 "Blocked address" else
  -- zero amount: allowed, no transfer, no log (L329)
  if v.amount = 0 then .success s2.1 true else
  -- helpers.rs transfer (L381-457): load from
  match step s2 (accountLoadGas v.fromCold) with
  | none => .oog
  | some s3 =>
  -- check_can_decr_account (helpers.rs:595-628)
  if v.fromBalance < v.amount then .revert s3.1 "Insufficient funds" else
  if !v.zero8 && (v.fromBalance == v.amount) && v.fromNonceZero && v.fromCodeEmpty then
    (match step s3 precompileSstoreGas with
     | none => .oog
     | some s3' => .revert s3'.1 "Cannot clear balance of empty account")
  else
  match step s3 precompileSstoreGas with
  | none => .oog
  | some s4 =>
  match step s4 (accountLoadGas v.toCold) with
  | none => .oog
  | some s5 =>
  match step s5 precompileSstoreGas with
  | none => .oog
  | some s6 =>
  if v.toSelfdestructed then .revert s6.1 "Cannot increase the balance of selfdestructed account" else
  -- record_empty_account_creation_cost (helpers.rs:164): amount ≠ 0 here
  match (if v.toEmpty then step s6 emptyAccountGas else some s6) with
  | none => .oog
  | some s7 =>
  -- journal transfer; EIP-7708 log unless self-transfer (L336-346)
  if v.fromAddr = v.toAddr then .success s7.1 true else
  match step s7 transferLogGas with
  | none => .oog
  | some s8 => .success s8.1 true

/-! ## `mint(to, amount)` / `burn(from, amount)` — native_coin_authority.rs:100-280

Both touch the authority's TOTAL_SUPPLY slot (slot 2, native_coin_authority.rs:47-49): a metered `read`
(2100 cold / 100 warm) then a metered `write` (helpers.rs:320-378) — EIP-2200
sentry (remaining ≤ 2300 → OOG), then `sstore_base_cost(original, present, new)`
(helpers.rs:289): 100 if new = present; else 20000 if original = present = 0,
2900 if original = present ≠ 0; else 100 (the slot is warm from the read; no
refund counter in the precompile). `mint` credits via `balance_incr`
(helpers.rs:459), `burn` debits via `balance_decr` (helpers.rs:503). -/

def sstoreSetGas   : Nat := 20000   -- SSTORE_SET
def callStipend    : Nat := 2300    -- EIP-2200 sentry (write refuses when remaining ≤ 2300)

/-- `sstore_base_cost` over the observed (original, present, new) relation. -/
def writeGas (sameAsPresent originalIsPresent originalZero : Bool) : Nat :=
  if sameAsPresent then warmReadGas
  else if originalIsPresent then (if originalZero then sstoreSetGas else precompileSstoreGas)
  else warmReadGas

structure MintView where
  gas : Nat
  isStatic : Bool
  argsOk : Bool
  callerIsToken : Bool
  isDelegate : Bool
  toAddr : Nat
  amount : Nat
  blToCold : Bool
  blTo : Bool
  tsCold : Bool                       -- TOTAL_SUPPLY slot cold at read
  tsOverflow : Bool                   -- supply + amount overflows u256
  tsSame : Bool                       -- write relation (see writeGas)
  tsOrigPresent : Bool
  tsOrigZero : Bool
  toCold : Bool
  toSelfdestructed : Bool
  toOverflow : Bool
  toEmpty : Bool
  zero8 : Bool
  deriving Repr

def runMint (v : MintView) : Outcome :=
  let s0 : Nat × Nat := (0, v.gas)
  if v.isStatic then .revert v.gas "State change during static call"
  else if !v.argsOk then earlyRevert s0 "Execution reverted"
  else if !v.callerIsToken then earlyRevert s0 "Not enabled native coin minter"
  else if v.isDelegate then
    (if v.zero8 then earlyRevert s0 "Delegate call not allowed" else .revert 0 "Delegate call not allowed")
  else if v.toAddr = 0 then earlyRevert s0 "Zero address not allowed"
  else match step s0 (slotReadGas v.blToCold) with
  | none => .oog
  | some s1 =>
  if v.blTo then earlyRevert s1 "Blocked address" else
  if v.amount = 0 then earlyRevert s1 "Zero amount invalid" else
  match step s1 (slotReadGas v.tsCold) with
  | none => .oog
  | some s2 =>
  if v.tsOverflow then earlyRevert s2 "Arithmetic overflow" else
  if s2.2 ≤ callStipend then .oog else
  match step s2 (writeGas v.tsSame v.tsOrigPresent v.tsOrigZero) with
  | none => .oog
  | some s3 =>
  -- balance_incr(to)
  match step s3 (accountLoadGas v.toCold) with
  | none => .oog
  | some s4 =>
  if v.toSelfdestructed then .revert s4.1 "Cannot increase the balance of selfdestructed account" else
  if v.toOverflow then .revert s4.1 "Arithmetic overflow" else
  match step s4 precompileSstoreGas with
  | none => .oog
  | some s5 =>
  match (if v.toEmpty then step s5 emptyAccountGas else some s5) with
  | none => .oog
  | some s6 =>
  match step s6 transferLogGas with       -- Transfer(0 → to), always emitted
  | none => .oog
  | some s7 => .success s7.1 true

structure BurnView where
  gas : Nat
  isStatic : Bool
  argsOk : Bool
  callerIsToken : Bool
  isDelegate : Bool
  fromAddr : Nat
  amount : Nat
  blFromCold : Bool
  blFrom : Bool
  fromCold : Bool
  fromBalance : Nat
  fromNonceZero : Bool
  fromCodeEmpty : Bool
  tsCold : Bool
  tsSame : Bool
  tsOrigPresent : Bool
  tsOrigZero : Bool
  zero8 : Bool
  deriving Repr

def runBurn (v : BurnView) : Outcome :=
  let s0 : Nat × Nat := (0, v.gas)
  if v.isStatic then .revert v.gas "State change during static call"
  else if !v.argsOk then earlyRevert s0 "Execution reverted"
  else if !v.callerIsToken then earlyRevert s0 "Not enabled native coin burner"
  else if v.isDelegate then
    (if v.zero8 then earlyRevert s0 "Delegate call not allowed" else .revert 0 "Delegate call not allowed")
  else if v.fromAddr = 0 then earlyRevert s0 "Zero address not allowed"
  else match step s0 (slotReadGas v.blFromCold) with
  | none => .oog
  | some s1 =>
  if v.blFrom then earlyRevert s1 "Blocked address" else
  if v.amount = 0 then earlyRevert s1 "Zero amount invalid" else
  -- balance_decr(from)
  match step s1 (accountLoadGas v.fromCold) with
  | none => .oog
  | some s2 =>
  if v.fromBalance < v.amount then .revert s2.1 "Insufficient funds" else
  if !v.zero8 && (v.fromBalance == v.amount) && v.fromNonceZero && v.fromCodeEmpty then
    (match step s2 precompileSstoreGas with
     | none => .oog
     | some s2' => .revert s2'.1 "Cannot clear balance of empty account")
  else
  match step s2 precompileSstoreGas with
  | none => .oog
  | some s3 =>
  match step s3 (slotReadGas v.tsCold) with
  | none => .oog
  | some s4 =>
  if s4.2 ≤ callStipend then .oog else
  match step s4 (writeGas v.tsSame v.tsOrigPresent v.tsOrigZero) with
  | none => .oog
  | some s5 =>
  match step s5 transferLogGas with       -- Transfer(from → 0), always emitted
  | none => .oog
  | some s6 => .success s6.1 true

/-- Typical mint: fresh tx (blocklist + supply slots cold), supply already
    nonzero and unchanged this tx (reset 2900), warm non-empty recipient. -/
def typicalMint : MintView :=
  { gas := 60000, isStatic := false, argsOk := true, callerIsToken := true, isDelegate := false
    toAddr := 2, amount := 5, blToCold := true, blTo := false, tsCold := true, tsOverflow := false
    tsSame := false, tsOrigPresent := true, tsOrigZero := false
    toCold := false, toSelfdestructed := false, toOverflow := false, toEmpty := false, zero8 := true }
example : runMint typicalMint = .success (2100 + 2100 + 2900 + 100 + 2900 + 1756) true := by decide
example : runMint { typicalMint with toEmpty := true } = .success (11856 + 25000) true := by decide
example : runMint { typicalMint with amount := 0 } = .revert 2300 "Zero amount invalid" := by decide

def typicalBurn : BurnView :=
  { gas := 60000, isStatic := false, argsOk := true, callerIsToken := true, isDelegate := false
    fromAddr := 1, amount := 5, blFromCold := true, blFrom := false
    fromCold := false, fromBalance := 100, fromNonceZero := false, fromCodeEmpty := true
    tsCold := true, tsSame := false, tsOrigPresent := true, tsOrigZero := false, zero8 := true }
example : runBurn typicalBurn = .success (2100 + 100 + 2900 + 2100 + 2900 + 1756) true := by decide
example : runBurn { typicalBurn with fromBalance := 3 } = .revert 2200 "Insufficient funds" := by decide

/-! ## `callFrom(sender, target, data)` — 0x1800…0003 CallFrom, the subcall precompile

Sources: crates/precompiles/src/call_from.rs (decode/encode gas L54-70, init L147,
complete L166), crates/evm/src/evm.rs (`init_subcall` L884-1100, `complete_subcall`
L1106-1180, rejection helpers L132-175, registry L1665: allowed callers = MEMO and
MULTICALL3_FROM, Zero7+). A frame-spawning precompile: it runs a CALL to `target`
with `msg.sender = sender` (which must be the caller itself or `tx.origin`), value 0,
and returns `abi(bool success, bytes returnData)` — the precompile itself succeeds
whenever it is not out of gas; the caller inspects the bool.

Gas: rejections (caller not allowed, non-CALL scheme, value attached, decode error,
spoof rule) charge a flat `SUBCALL_DISPATCH_COST` 100 (all gas if less remains) and
revert with `Error(string)`; a static context spends everything. Success path: ABI
decode overhead `100 + 3·⌈len(data)/32⌉`, the target's account access (2600/100,
plus an EIP-7702 delegate load if any), then the child with limit `rem − rem/64`,
then encode overhead `100 + 3·⌈len(out)/32⌉`. A child that HALTS (OOG etc., not a
REVERT) makes the precompile consume its whole gas limit and return `(false, "")`. -/

def subcallDispatchCost : Nat := 100
/-- ABI decode/encode overhead: base 100 + COPY (3) per 32-byte word (call_from.rs:57,67). -/
def abiCopyGas (words : Nat) : Nat := 100 + 3 * words

structure CallFromView where
  gas : Nat
  callerAllowed : Bool
  isCallScheme : Bool
  isStatic : Bool
  hasValue : Bool
  argsOk : Bool
  dataWords : Nat
  spoofOk : Bool
  targetCold : Bool
  delegateCold : Option Bool
  childSpent : Nat
  childHalted : Bool
  outWords : Nat
  deriving Repr

def runCallFrom (v : CallFromView) : Outcome :=
  let dispatch (msg : String) : Outcome :=
    match step (0, v.gas) subcallDispatchCost with
    | some s => .revert s.1 msg
    | none   => .revert v.gas msg
  if !v.callerAllowed then dispatch "unauthorized caller"
  else if !v.isCallScheme then dispatch "subcall precompiles only support CALL scheme"
  else if v.isStatic then .revert v.gas "subcall precompiles cannot be invoked in static context"
  else if v.hasValue then dispatch "subcall precompiles do not support value transfers"
  else if !v.argsOk then dispatch "ABI decode error: callFrom: buffer overrun while deserializing"
  else if v.gas < abiCopyGas v.dataWords then dispatch "insufficient gas: gas limit below ABI decode overhead"
  else if !v.spoofOk then dispatch "sender spoofing requires tx.origin as sender"
  else
  match step (0, v.gas) (abiCopyGas v.dataWords) with
  | none => .oog
  | some s1 =>
  match step s1 (accountLoadGas v.targetCold) with
  | none => .oog
  | some s2 =>
  match (match v.delegateCold with | some c => step s2 (accountLoadGas c) | none => some s2) with
  | none => .oog
  | some s3 =>
  if v.childHalted then .success v.gas true       -- all gas, output (false, "")
  else match step s3 v.childSpent with
  | none => .oog
  | some s4 =>
  match step s4 (abiCopyGas v.outWords) with
  | none => .oog
  | some s5 => .success s5.1 true

def typicalCallFrom : CallFromView :=
  { gas := 100000, callerAllowed := true, isCallScheme := true, isStatic := false, hasValue := false
    argsOk := true, dataWords := 3, spoofOk := true, targetCold := true, delegateCold := none
    childSpent := 20000, childHalted := false, outWords := 1 }
example : runCallFrom typicalCallFrom = .success (109 + 2600 + 20000 + 103) true := by decide
example : runCallFrom { typicalCallFrom with callerAllowed := false }
    = .revert 100 "unauthorized caller" := by decide
example : runCallFrom { typicalCallFrom with isStatic := true }
    = .revert 100000 "subcall precompiles cannot be invoked in static context" := by decide
example : runCallFrom { typicalCallFrom with childHalted := true } = .success 100000 true := by decide

def abiCopyGasExpr : Expr := .add (.lit 100) (.mul (.lit 3) (.var "words"))
def subcallDispatchCostExpr : Expr := .lit subcallDispatchCost
example : abiCopyGasExpr.eval (mkEnv [("words", 3)]) = 109 := by decide

/-! ## `blocklist(account)` / `unBlocklist(account)` — native_coin_control.rs:100-178, 216-296

Both are the same program up to the stored value (1 / 0), the revert string and
the event. Order (the file's own comments explain it): static check (spend all),
ABI decode (+200), caller must be the fiat token (+200), delegate check — which
moved from after to before the gas floor at Zero8, so the +200 penalty is reachable
regardless of remaining gas — then `check_gas_remaining(BLOCKLIST_GAS_COST −
PRECOMPILE_SLOAD_GAS_COST)` = 2900 + 1125 = 4025, then `write` (EIP-2200 sentry;
sload probe charges 2100 only when the slot is COLD, nothing when warm;
`sstore_base_cost`), then `emit_event` (375 + 2·375, no data). -/

/-- `Blocklisted(address indexed)` / `UnBlocklisted(address indexed)`: LOG_BASE_COST +
    2 · LOG_TOPIC_COST (helpers.rs:44-45, 631-648), no data bytes. -/
def blocklistEventGas : Nat := 375 + 2 * 375
/-- `write`'s warmth probe (helpers.rs:342-358): COLD_SLOAD_COST when cold, else free. -/
def writeProbeGas (cold : Bool) : Nat := if cold then coldSloadGas else 0
/-- `check_gas_remaining` floor for both ops: BLOCKLIST_GAS_COST − PRECOMPILE_SLOAD_GAS_COST. -/
def blocklistGasFloor : Nat := precompileSstoreGas + blocklistEventGas

structure BlocklistView where
  gas : Nat
  unblock : Bool          -- unBlocklist (store 0) vs blocklist (store 1)
  isStatic : Bool
  argsOk : Bool
  callerIsToken : Bool
  isDelegate : Bool
  slotCold : Bool
  sameAsPresent : Bool    -- new value == present (a no-op write)
  origIsPresent : Bool
  origZero : Bool
  zero8 : Bool
  deriving Repr

def runBlocklist (v : BlocklistView) : Outcome :=
  let s0 : Nat × Nat := (0, v.gas)
  if v.isStatic then .revert v.gas "State change during static call"
  else if !v.argsOk then earlyRevert s0 "Execution reverted"
  else if !v.callerIsToken then
    earlyRevert s0 (if v.unblock then "Not enabled for unblocklisting" else "Not enabled for blocklisting")
  else if v.zero8 && v.isDelegate then earlyRevert s0 "Delegate call not allowed"
  else if v.gas < blocklistGasFloor then .oog
  else if v.isDelegate then .revert 0 "Delegate call not allowed"
  else if v.gas ≤ callStipend then .oog
  else match step s0 (writeProbeGas v.slotCold) with
  | none => .oog
  | some s1 =>
  match step s1 (writeGas v.sameAsPresent v.origIsPresent v.origZero) with
  | none => .oog
  | some s2 =>
  match step s2 blocklistEventGas with
  | none => .oog
  | some s3 => .success s3.1 true

/-- The canonical first blocklisting of a fresh address: cold slot, 0 → 1. -/
def typicalBlocklist : BlocklistView :=
  { gas := 100000, unblock := false, isStatic := false, argsOk := true, callerIsToken := true
    isDelegate := false, slotCold := true, sameAsPresent := false, origIsPresent := true
    origZero := true, zero8 := true }
example : runBlocklist typicalBlocklist = .success (2100 + 20000 + 1125) true := by decide
/-- The arc-node unit test "blocklist() basic functionality": gas_used 23225 (native_coin_control.rs:448-462). -/
example : runBlocklist typicalBlocklist = .success 23225 true := by decide
/-- Un-blocklisting a blocklisted address in the same tx that set it: warm slot, 1 → 0, original 0. -/
example : runBlocklist { typicalBlocklist with unblock := true, slotCold := false, origIsPresent := false }
    = .success (0 + 100 + 1125) true := by decide
example : runBlocklist { typicalBlocklist with callerIsToken := false }
    = .revert 200 "Not enabled for blocklisting" := by decide
/-- The unit test "insufficient gas errors with OOG": gas_limit = BLOCKLIST_GAS_COST − 2100 − 1. -/
example : runBlocklist { typicalBlocklist with gas := 4024 } = .oog := by decide
example : runBlocklist { typicalBlocklist with isDelegate := true } = .revert 200 "Delegate call not allowed" := by decide
example : runBlocklist { typicalBlocklist with isDelegate := true, zero8 := false } = .revert 0 "Delegate call not allowed" := by decide

/-! ## SELFDESTRUCT override — crates/evm/src/opcode.rs `arc_network_selfdestruct_impl` (L64-175)

Arc forks revm's SELFDESTRUCT: when the destructing account's balance is non-zero,
before the standard destruct it (1) reverts on a zero-address target with a message,
(2) reverts (bare) when target = source, (3) reads both parties' blocklist slots
UNMETERED (fail-open before Zero7, fail-closed after) and reverts "Blocked address"
on a hit (target first), (4) from Zero8 reverts when the target is already
destructed, and (5) otherwise emits the EIP-7708 Transfer log. The opcode's own
gas (5000 + cold/topup) is charged as in revm; every revert keeps the remaining gas.
Block 2 405 747 (init code `30 ff` with a 1-wei endowment) is case (2): status 0,
same gas as a success. -/

structure SelfdestructView where
  balancePos : Bool
  targetZero : Bool
  selfTarget : Bool
  targetBlocked : Bool
  sourceBlocked : Bool
  targetDestructed : Bool
  zero8 : Bool
  deriving Repr

inductive SelfdestructVerdict where
  | proceed (emitsLog : Bool)
  | revert (message : Option String)
  deriving Repr, DecidableEq

def runSelfdestructCheck (v : SelfdestructView) : SelfdestructVerdict :=
  if !v.balancePos then .proceed false
  else if v.targetZero then .revert (some "Zero address not allowed")
  else if v.selfTarget then .revert none
  else if v.targetBlocked then .revert (some "Blocked address")
  else if v.sourceBlocked then .revert (some "Blocked address")
  else if v.targetDestructed then       -- every warmth policy loads the target and checks it (opcode.rs:331, :370)
    .revert (some "Cannot increase the balance of selfdestructed account")
  else .proceed true

/-! ### Frame init of a value-bearing CALL/CREATE — evm.rs `check_blocklist_and_create_log` (L497-590)

Before the sub-frame runs: zero address on either side → revert (no reads);
`from` then `to` blocklist slots read unmetered → "Blocked address"; destructed
target → "Cannot increase the balance of selfdestructed account"; self-transfer
→ no log; else the EIP-7708 Transfer log. A revert here spends 0 gas of the
forwarded pool (`metered_revert` with `meter_sloads = false`); the CALL's own
charges were already taken by the opcode. -/
structure FrameInitView where
  fromZero : Bool
  toZero : Bool
  fromBlocked : Bool
  toBlocked : Bool
  toDestructed : Bool
  selfTransfer : Bool
  deriving Repr

def runFrameInitCheck (v : FrameInitView) : SelfdestructVerdict :=
  if v.fromZero || v.toZero then .revert (some "Zero address not allowed")
  else if v.fromBlocked then .revert (some "Blocked address")
  else if v.toBlocked then .revert (some "Blocked address")
  else if v.toDestructed then .revert (some "Cannot increase the balance of selfdestructed account")
  else .proceed (!v.selfTransfer)

def frameInitDestructed : FrameInitView :=
  { fromZero := false
    toZero := false
    fromBlocked := false
    toBlocked := false
    toDestructed := true
    selfTransfer := false }
example : runFrameInitCheck frameInitDestructed
    = .revert (some "Cannot increase the balance of selfdestructed account") := by decide
example : runFrameInitCheck { frameInitDestructed with toDestructed := false, selfTransfer := true }
    = .proceed false := by decide
example : runFrameInitCheck { frameInitDestructed with toDestructed := false, toZero := true }
    = .revert (some "Zero address not allowed") := by decide

example : runSelfdestructCheck
    { balancePos := true, targetZero := false, selfTarget := true, targetBlocked := false,
      sourceBlocked := false, targetDestructed := false, zero8 := false } = .revert none := by decide
example : runSelfdestructCheck
    { balancePos := false, targetZero := false, selfTarget := true, targetBlocked := false,
      sourceBlocked := false, targetDestructed := false, zero8 := false } = .proceed false := by decide
/-- Block 2 456 071: parent self-destructs to a child destructed earlier in the tx. -/
example : runSelfdestructCheck
    { balancePos := true, targetZero := false, selfTarget := false, targetBlocked := false,
      sourceBlocked := false, targetDestructed := true, zero8 := false }
    = .revert (some "Cannot increase the balance of selfdestructed account") := by decide

/-! ## `isBlocklisted(account)` — native_coin_control.rs:180-215 -/

structure IsBlocklistedView where
  gas      : Nat
  argsOk   : Bool
  slotCold : Bool
  blocked  : Bool
  deriving Repr

/-- View function: no static/caller/delegate checks. Note the gas floor is the
    COLD read (2100) even when the slot is warm (`check_gas_remaining`). -/
def runIsBlocklisted (v : IsBlocklistedView) : Outcome :=
  if !v.argsOk then earlyRevert (0, v.gas) "Execution reverted"
  else if v.gas < coldSloadGas then .oog
  else match step (0, v.gas) (slotReadGas v.slotCold) with
  | none => .oog
  | some s => .success s.1 v.blocked

/-- Dispatcher-level failures (macros.rs:108-127): input shorter than a
    selector, or an unknown selector → +200 revert. -/
def runUnknownSelector (gas : Nat) (tooShort : Bool) : Outcome :=
  earlyRevert (0, gas) (if tooShort then "Input too short" else "Invalid selector")

/-! ## Unmetered warming outside the precompiles (arc-node crates/evm)

Two client-side reads leave keys WARM without charging gas, which the precompile
and later CALLs then observe (this is where the residual −2500 / −2000 deltas came
from before the host modelled them):

* `handler.rs check_blocklist` (L157-178): pre-execution `journal.sload` of the
  blocklist slot of `tx.from`, and of `tx.to` when the tx carries value. The sload
  loads NativeCoinControl 0x1800…0001 (account warm) and warms those slots.
* `evm.rs check_blocklist_and_create_log` (L499-590): every value-bearing CALL/CREATE
  frame-init reads both parties' blocklist slots the same way (`meter_sloads = false`).
  Its Zero7+ selfdestructed-target probe is checkpoint-reverted (target stays cold).

Host seam: `arc-tx-prewarm!` / `arc-value-transfer-prewarm!` (src/chains/arc-precompiles.lisp).
That frame-init also reverts value moves to the zero address or a selfdestructed target:
`runFrameInitCheck` (above) models it. -/

/-- Keys warmed before a tx executes (handler.rs check_blocklist). -/
def txPrewarmSlots (txFrom : Nat) (txTo : Option Nat) (txValue : Nat) : List Nat :=
  [txFrom] ++ (match txTo with | some t => if txValue ≠ 0 then [t] else [] | none => [])

/-! ## Emitted success-path gas (host.lisp `spec-arc-*`)

Inputs are 0/1 flags; `Expr.ite lo hi t e` is `if lo < hi`. -/

private def flag (x : String) : Expr := .var x
private def coldWarm (x : String) (cold warm : Nat) : Expr :=
  .ite (.lit 0) (flag x) (.lit cold) (.lit warm)

/-- Success-path gas of `transfer` = the `runTransfer` success branch. -/
def transferGas : Expr :=
  .add (coldWarm "bl-from-cold" coldSloadGas warmReadGas)
  (.add (coldWarm "bl-to-cold" coldSloadGas warmReadGas)
    (.ite (.lit 0) (flag "amount-pos")
      (.add (coldWarm "from-cold" coldAccountGas warmReadGas)
      (.add (.lit precompileSstoreGas)
      (.add (coldWarm "to-cold" coldAccountGas warmReadGas)
      (.add (.lit precompileSstoreGas)
      (.add (.ite (.lit 0) (flag "to-empty") (.lit emptyAccountGas) (.lit 0))
            (.ite (.lit 0) (flag "self") (.lit 0) (.lit transferLogGas)))))))
      (.lit 0)))

/-- Success-path gas of `isBlocklisted`. -/
def isBlocklistedGas : Expr := coldWarm "slot-cold" coldSloadGas warmReadGas

-- Constants emitted for the CL seam's revert paths (same numbers, one source).
def earlyRevertPenaltyExpr  : Expr := .lit earlyRevertPenalty
def precompileSstoreGasExpr : Expr := .lit precompileSstoreGas
def emptyAccountGasExpr     : Expr := .lit emptyAccountGas
def transferLogGasExpr      : Expr := .lit transferLogGas
def accountLoadGasExpr      : Expr := coldWarm "cold" coldAccountGas warmReadGas
/-- `sstore_base_cost` as an emitted formula over 0/1 flags (helpers.rs:289). -/
def writeGasExpr : Expr :=
  .ite (.lit 0) (flag "same-as-present") (.lit warmReadGas)
    (.ite (.lit 0) (flag "original-is-present")
       (.ite (.lit 0) (flag "original-zero") (.lit sstoreSetGas) (.lit precompileSstoreGas))
       (.lit warmReadGas))
def callStipendExpr : Expr := .lit callStipend
example : writeGasExpr.eval (mkEnv [("same-as-present",0),("original-is-present",1),("original-zero",0)]) = 2900 := by decide
example : writeGasExpr.eval (mkEnv [("same-as-present",0),("original-is-present",1),("original-zero",1)]) = 20000 := by decide
example : writeGasExpr.eval (mkEnv [("same-as-present",1),("original-is-present",1),("original-zero",1)]) = 100 := by decide
def slotReadGasExpr         : Expr := coldWarm "cold" coldSloadGas warmReadGas
def blocklistEventGasExpr   : Expr := .lit blocklistEventGas
/-- `write`'s sload probe: cold → 2100, warm → 0 (NOT the 100 of a metered read). -/
def writeProbeGasExpr       : Expr := coldWarm "cold" coldSloadGas 0
example : writeProbeGasExpr.eval (mkEnv [("cold", 1)]) = 2100 := by decide
example : writeProbeGasExpr.eval (mkEnv [("cold", 0)]) = 0 := by decide

/-! ## Kernel-checked agreement on the canonical cases -/

/-- The common Arc transfer: caller 0x3600, `from` = tx sender (warm), `to`
    cold + non-empty, both blocklist slots cold. -/
def typical : TransferView :=
  { gas := 60000, isStatic := false, argsOk := true, callerIsToken := true, isDelegate := false
    fromAddr := 1, toAddr := 2, amount := 5, blFromCold := true, blFrom := false
    blToCold := true, blTo := false, fromCold := false, fromBalance := 100
    fromNonceZero := false, fromCodeEmpty := true, toCold := true, toEmpty := false
    toSelfdestructed := false, zero8 := false }

example : runTransfer typical = .success 14456 true := by decide
example : transferGas.eval (mkEnv
  [("bl-from-cold", 1), ("bl-to-cold", 1), ("amount-pos", 1), ("from-cold", 0),
   ("to-cold", 1), ("to-empty", 0), ("self", 0)]) = 14456 := by decide

/-- Self-transfer: second blocklist read and `to` load are warm, no log. -/
example : runTransfer { typical with toAddr := 1, blToCold := false, toCold := false }
    = .success (2100 + 100 + 100 + 2900 + 100 + 2900) true := by decide
example : transferGas.eval (mkEnv
  [("bl-from-cold", 1), ("bl-to-cold", 0), ("amount-pos", 1), ("from-cold", 0),
   ("to-cold", 0), ("to-empty", 0), ("self", 1)]) = 8200 := by decide

/-- Fresh recipient pays the 25000 new-account surcharge. -/
example : runTransfer { typical with toEmpty := true } = .success 39456 true := by decide

/-- Zero amount: only the blocklist reads, no log, success. -/
example : runTransfer { typical with amount := 0 } = .success 4200 true := by decide

/-- Wrong caller: nothing metered, +200 penalty revert. -/
example : runTransfer { typical with callerIsToken := false }
    = .revert 200 "Not enabled for native coin transfers" := by decide

/-- Blocklisted recipient: both reads metered, then +200. -/
example : runTransfer { typical with blTo := true } = .revert 4400 "Blocked address" := by decide

/-- Pre-Zero8 drain-to-empty: reads + from-load + 2900, revert; Zero8 allows it. -/
example : runTransfer { typical with fromBalance := 5, fromNonceZero := true }
    = .revert (4200 + 100 + 2900) "Cannot clear balance of empty account" := by decide
example : runTransfer { typical with fromBalance := 5, fromNonceZero := true, zero8 := true }
    = .success 14456 true := by decide

/-- Static context spends everything. -/
example : runTransfer { typical with isStatic := true }
    = .revert 60000 "State change during static call" := by decide

/-- isBlocklisted: cold read 2100; warm read 100 but still needs 2100 available. -/
example : runIsBlocklisted { gas := 5000, argsOk := true, slotCold := true, blocked := false }
    = .success 2100 false := by decide
example : runIsBlocklisted { gas := 5000, argsOk := true, slotCold := false, blocked := true }
    = .success 100 true := by decide
example : runIsBlocklisted { gas := 1000, argsOk := true, slotCold := false, blocked := true }
    = .oog := by decide
example : isBlocklistedGas.eval (mkEnv [("slot-cold", 1)]) = 2100 := by decide

end Evm.Arc.Spec.NativeCoin
