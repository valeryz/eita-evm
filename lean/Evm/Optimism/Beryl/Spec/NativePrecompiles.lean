/-
  Evm.Optimism.Beryl.Spec.NativePrecompiles — Base's stateful native precompiles: which
  addresses they are at each fork, which are warm from the start of a tx, the boundary of a
  call into one, and the price of every operation one performs on the world.

  Source: base/base @ v1.5.6 (a9f6cc9d, the release Base mainnet runs),
  `crates/common/precompiles`:

    provider.rs:209-245   install_with_observer: from Beryl the B-20 factory, the B-20 token
                          lookup, the policy registry and the activation registry; from
                          Cobalt also the transaction-context and nonce-manager precompiles
    lookup.rs             BerylLookup: an address B20Variant::from_address decodes is a token
    b20_factory/variant.rs:66-73
                          from_address: byte 0 = 0xb2, bytes 1..9 zero, byte 10 the variant
                          (0 asset, 1 stablecoin; variant.rs:10-13)
    macros.rs:8-35        base_precompile!: a call that is not direct (DELEGATECALL,
                          CALLCODE: target ≠ code address) reverts with
                          DelegateCallNotAllowed at no gas; else the body runs over a storage
                          provider with GasParams::default() (revm SpecId::default() = OSAKA)
    precompile-storage/src/evm.rs:113-317
                          the provider's operations and their prices (`hostGas` below)

  What a native precompile DOES (the B-20 token, factory, policy and activation logic, three
  frozen versions of each) is not restated here: it is base/base's code, linked unchanged at
  the pinned release (rust/base), and it reaches the world only through the operations this
  file prices. That linked logic is a trusted component of the replay, named as such in
  docs/trusted-surface.md. Every number it charges for touching the world is the engine's,
  from the functions below, each proved equal to the EVM opcode's own spec term.

  Warmth (alloy-evm 0.38 precompiles.rs:597-602, `warm_addresses`): the addresses installed
  into the precompile map (factory, registries; from Cobalt the two Cobalt precompiles) are in
  the tx's warm set from its start, like Ethereum's precompiles; the token addresses resolved
  by the lookup are not (a first call to one pays the cold account access).

  Result (revm-handler 42.0.1 precompile_provider.rs:86-116): a success keeps its unspent gas
  and its refund; a revert keeps its unspent gas, drops its refund and its state changes; a
  halt (out of gas, or a claim above the limit) spends the whole limit and returns nothing.
-/

import Evm.CL.GasEmit
import Evm.Optimism.Forks
import Evm.London.Vm.Effect

namespace Evm.Optimism.Beryl.Spec

open Evm.CL.GasEmit (Expr Env mkEnv)
open Evm.Optimism (OpFork)

/-! ## The native precompile at an address -/

/-- base/base b20_factory/storage.rs:20. -/
def factoryAddr    : Nat := 0xB20F000000000000000000000000000000000000
/-- policy/storage.rs:81. -/
def policyAddr     : Nat := 0x8453000000000000000000000000000000000002
/-- activation/storage.rs:87. -/
def activationAddr : Nat := 0x8453000000000000000000000000000000000001
/-- tx_context/storage.rs:30 (Cobalt). -/
def txContextAddr  : Nat := 0x813000000000000000000000000000000000aa02
/-- nonce/storage.rs:53 = eip8130 nonce.rs:25 (Cobalt). -/
def nonceAddr      : Nat := 0x813000000000000000000000000000000000aa01

/-- An address's bytes 0..10 (its top 88 bits) for a B-20 token of variant `d`: 0xb2, nine
    zero bytes, `d` (variant.rs:66-73). -/
def b20Prefix (d : Nat) : Nat := 0xb2 * 2 ^ 80 + d

/-- The native-precompile kind at `addr` at OP fork `f` (the shim's `kind_of`, which must
    agree): 1 factory, 2 policy registry, 3 activation registry, 4 asset token, 5 stablecoin
    token, 6 transaction context, 7 nonce manager; 0 none. -/
def nativeKind (f : OpFork) (addr : Nat) : Nat :=
  if ¬ f.atLeast .beryl then 0
  else if addr = factoryAddr then 1
  else if addr = policyAddr then 2
  else if addr = activationAddr then 3
  else if f.atLeast .cobalt ∧ addr = txContextAddr then 6
  else if f.atLeast .cobalt ∧ addr = nonceAddr then 7
  else if addr / 2 ^ 72 = b20Prefix 0 then 4
  else if addr / 2 ^ 72 = b20Prefix 1 then 5
  else 0

/-- Warm from the start of every tx: the kinds installed into the precompile map (not the
    looked-up tokens). -/
def warmAtTxStart (f : OpFork) (addr : Nat) : Bool :=
  let k := nativeKind f addr
  k ≠ 0 ∧ k ≠ 4 ∧ k ≠ 5

example : nativeKind .denim 0xb200000000000000000000ce42a5c4d1e3d1883d = 4 := by decide
example : nativeKind .denim 0xb200000000000000000001000000000000000007 = 5 := by decide
example : nativeKind .denim 0xb2cc000000000000000000000000000000000000 = 0 := by decide
example : nativeKind .azul factoryAddr = 0 := by decide
example : nativeKind .beryl txContextAddr = 0 := by decide
example : nativeKind .cobalt nonceAddr = 7 := by decide
example : warmAtTxStart .denim policyAddr = true := by decide
example : warmAtTxStart .denim 0xb200000000000000000000ce42a5c4d1e3d1883d = false := by decide

/-! ## The price of each host operation (precompile-storage/src/evm.rs, Osaka GasParams)

  Each is the EVM opcode's own spec term: the provider meters an operation exactly as the
  opcode it stands for. -/

/-- `sload` (evm.rs:214-238): warm read + the cold surcharge = Berlin's SLOAD. Like
    `sstore`, it loads the slot's account first, which puts the account in the tx's warm set
    at no charge of its own (alloy-evm traits.rs:317-326, `load_account_mut`). -/
def sloadGas (cold : Bool) : Nat :=
  Evm.Berlin.Vm.Gas.warmAccess + if cold then Evm.Berlin.Vm.Gas.coldSload - Evm.Berlin.Vm.Gas.warmAccess else 0

/-- `with_account_info` / `with_account_code` (evm.rs:144-191): Berlin's account access. -/
def accountGas (cold : Bool) : Nat :=
  Evm.Berlin.Vm.Gas.warmAccess + if cold then Evm.Berlin.Vm.Gas.coldAccountAccess - Evm.Berlin.Vm.Gas.warmAccess else 0

/-- `sstore` (evm.rs:249-282): static + dynamic = London's SSTORE cost. -/
def sstoreGas (cold : Bool) (original current new_ : Evm.U256) : Nat :=
  (Evm.London.Vm.Effect.sstoreGas 0 cold original current new_).1

/-- `sstore`'s refund delta (EIP-3529, `sstore_refund`): London's additions and
    subtractions; the shim adds `add - sub` to the call's refund. -/
def sstoreRefundAdd (original current new_ : Evm.U256) : Nat :=
  (Evm.London.Vm.Effect.eip2200London original current new_).2.1
def sstoreRefundSub (original current new_ : Evm.U256) : Nat :=
  (Evm.London.Vm.Effect.eip2200London original current new_).2.2

/-- `sstore` refuses (out of gas) with no more than the stipend left (evm.rs:254-256). -/
def sstoreSentry : Nat := Evm.Istanbul.Vm.Gas.sstoreSentryGas

/-- `tload` / `tstore` (evm.rs:240-247, 284-291): the warm read cost (the TLOAD/TSTORE
    opcode price). -/
def transientGas : Nat := Evm.Berlin.Vm.Gas.warmAccess

/-- `emit_event` (evm.rs:293-302): LOG's base, per topic, per data byte. -/
def logGas (topics len : Nat) : Nat :=
  Evm.Frontier.Vm.Gas.log + Evm.Frontier.Vm.Gas.logTopic * topics + Evm.Frontier.Vm.Gas.logData * len

/-- `metered_keccak256` (evm.rs:368-377): KECCAK256's base and per-word price. -/
def keccakGas (len : Nat) : Nat := 30 + 6 * ((len + 31) / 32)

/-- `set_code` (evm.rs:108-137): the code deposit always; then, for an account without code,
    CREATE's base cost and the keccak of the code hash. -/
def codeDepositGas (len : Nat) : Nat := 200 * len
def newCodeGas (len : Nat) : Nat := 32000 + keccakGas len

/-! ## Emitted forms (src/generated/host.lisp via EmitHostCL), each proved = the spec -/

private def v (x : String) : Expr := .var x
private def n (k : Nat) : Expr := .lit k

/-- `if x = k then t else e` in the Expr IR, each branch once: `x ≠ k` iff the truncated
    differences do not both vanish. -/
def eqThen (x : Expr) (k : Nat) (t e : Expr) : Expr :=
  .ite (n 0) (.add (.sub x (n k)) (.sub (n k) x)) e t

theorem eqThen_eval (ρ : Env) (x : Expr) (k : Nat) (t e : Expr) :
    (eqThen x k t e).eval ρ = if x.eval ρ = k then t.eval ρ else e.eval ρ := by
  simp only [eqThen, Expr.eval, n]
  by_cases h : x.eval ρ = k
  · simp [h]
  · have : 0 < x.eval ρ - k + (k - x.eval ρ) := by omega
    simp [h, this]

/-- `nativeKind` over `op-fork` (the OpFork ordinal) and `addr`. -/
def nativeKindExpr : Expr :=
  let q : Expr := .fdiv (v "addr") (n (2 ^ 72))
  let tokens : Expr := eqThen q (b20Prefix 0) (n 4) (eqThen q (b20Prefix 1) (n 5) (n 0))
  let cobalt : Expr := eqThen (v "addr") txContextAddr (n 6) (eqThen (v "addr") nonceAddr (n 7) tokens)
  .ite (v "op-fork") (n 9) (n 0) <|
  eqThen (v "addr") factoryAddr (n 1) <|
  eqThen (v "addr") policyAddr (n 2) <|
  eqThen (v "addr") activationAddr (n 3) <|
  .ite (v "op-fork") (n 10) tokens cobalt

set_option maxRecDepth 4000 in
theorem nativeKindExpr_eq_spec (f : OpFork) (addr : Nat) :
    nativeKindExpr.eval (mkEnv [("op-fork", f.ord), ("addr", addr)]) = nativeKind f addr := by
  simp only [nativeKindExpr, eqThen_eval, Expr.eval, nativeKind, mkEnv, List.find?, v, n]
  cases f <;> simp [OpFork.ord, OpFork.atLeast, factoryAddr, policyAddr, activationAddr,
    txContextAddr, nonceAddr, b20Prefix] <;> (repeat' split) <;> first | rfl | simp_all | omega

/-- `sloadGas` / `accountGas` over the 0/1 flag `cold`. -/
def sloadGasExpr : Expr := .ite (n 0) (v "cold") (n 2100) (n 100)
def accountGasExpr : Expr := .ite (n 0) (v "cold") (n 2600) (n 100)

theorem sloadGasExpr_eq_spec (cold : Bool) :
    sloadGasExpr.eval (mkEnv [("cold", if cold then 1 else 0)]) = sloadGas cold := by
  cases cold <;> decide

theorem accountGasExpr_eq_spec (cold : Bool) :
    accountGasExpr.eval (mkEnv [("cold", if cold then 1 else 0)]) = accountGas cold := by
  cases cold <;> decide

/-- `sstoreGas` and its refund over 0/1 flags the host reads off the slot: `cold`,
    `new-eq-cur`, `cur-eq-orig`, `orig-zero`, `cur-zero`, `new-zero`, `new-eq-orig`. -/
private def flag (x : String) (t e : Expr) : Expr := .ite (n 0) (v x) t e

def sstoreGasExpr : Expr :=
  .add (flag "cold" (n 2100) (n 0))
    (flag "new-eq-cur" (n 100)
      (flag "cur-eq-orig" (flag "orig-zero" (n 20000) (n 2900)) (n 100)))

def sstoreRefundAddExpr : Expr :=
  flag "new-eq-cur" (n 0) <|
  flag "cur-eq-orig" (flag "orig-zero" (n 0) (flag "new-zero" (n 4800) (n 0))) <|
  .add (flag "orig-zero" (n 0) (flag "cur-zero" (n 0) (flag "new-zero" (n 4800) (n 0))))
       (flag "new-eq-orig" (flag "orig-zero" (n 19900) (n 2800)) (n 0))

def sstoreRefundSubExpr : Expr :=
  flag "new-eq-cur" (n 0) <|
  flag "cur-eq-orig" (n 0) <|
  flag "orig-zero" (n 0) (flag "cur-zero" (n 4800) (n 0))

/-- The flag environment of a write of `new_` over `current` (tx-start value `original`). -/
def sstoreEnv (cold : Bool) (original current new_ : Evm.U256) : Env :=
  let b (p : Bool) : Nat := if p then 1 else 0
  mkEnv [("cold", b cold), ("new-eq-cur", b (decide (new_ = current))),
         ("cur-eq-orig", b (decide (current = original))), ("orig-zero", b (decide (original = 0))),
         ("cur-zero", b (decide (current = 0))), ("new-zero", b (decide (new_ = 0))),
         ("new-eq-orig", b (decide (new_ = original)))]

theorem sstoreGasExpr_eq_spec (cold : Bool) (original current new_ : Evm.U256) :
    sstoreGasExpr.eval (sstoreEnv cold original current new_) = sstoreGas cold original current new_ := by
  unfold sstoreGasExpr sstoreGas sstoreEnv Evm.London.Vm.Effect.sstoreGas
    Evm.London.Vm.Effect.eip2200London
  by_cases h1 : new_ = current <;> by_cases h2 : current = original <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h6 : new_ = original <;>
    cases cold <;>
    simp_all [flag, Expr.eval, mkEnv, List.find?, v, n, Evm.Berlin.Vm.Gas.warmAccess,
      Evm.Berlin.Vm.Instructions.Storage.sstoreSet, Evm.Berlin.Vm.Instructions.Storage.sstoreReset,
      Evm.Berlin.Vm.Gas.sstoreColdSurcharge, Evm.Berlin.Vm.Gas.coldSload]

theorem sstoreRefundExpr_eq_spec (cold : Bool) (original current new_ : Evm.U256) :
    sstoreRefundAddExpr.eval (sstoreEnv cold original current new_) = sstoreRefundAdd original current new_ ∧
    sstoreRefundSubExpr.eval (sstoreEnv cold original current new_) = sstoreRefundSub original current new_ := by
  unfold sstoreRefundAddExpr sstoreRefundSubExpr sstoreRefundAdd sstoreRefundSub sstoreEnv
    Evm.London.Vm.Effect.eip2200London
  by_cases h1 : new_ = current <;> by_cases h2 : current = original <;>
    by_cases h3 : original = 0 <;> by_cases h4 : current = 0 <;> by_cases h5 : new_ = 0 <;>
    by_cases h6 : new_ = original <;>
    simp_all [flag, Expr.eval, mkEnv, List.find?, v, n, Evm.Berlin.Vm.Gas.warmAccess,
      Evm.Berlin.Vm.Instructions.Storage.sstoreSet, Evm.Berlin.Vm.Instructions.Storage.sstoreReset,
      Evm.London.Vm.Gas.sStoreClearRefund, Evm.Berlin.Vm.Gas.coldSload]

def sstoreSentryExpr : Expr := n sstoreSentry
def transientGasExpr : Expr := n transientGas
def logGasExpr : Expr := .add (n 375) (.add (.mul (n 375) (v "topics")) (.mul (n 8) (v "len")))
def keccakGasExpr : Expr := .add (n 30) (.mul (n 6) (.fdiv (.add (v "len") (n 31)) (n 32)))
def codeDepositGasExpr : Expr := .mul (n 200) (v "len")
def newCodeGasExpr : Expr := .add (n 32000) keccakGasExpr

theorem sstoreSentryExpr_eq : sstoreSentryExpr.eval (mkEnv []) = 2300 := by decide
theorem transientGasExpr_eq : transientGasExpr.eval (mkEnv []) = transientGas := by decide
theorem logGasExpr_eq_spec (topics len : Nat) :
    logGasExpr.eval (mkEnv [("topics", topics), ("len", len)]) = logGas topics len := by
  simp [logGasExpr, logGas, Expr.eval, mkEnv, List.find?, v, n, Evm.Frontier.Vm.Gas.log,
    Evm.Frontier.Vm.Gas.logTopic, Evm.Frontier.Vm.Gas.logData]
  omega
theorem keccakGasExpr_eq_spec (len : Nat) :
    keccakGasExpr.eval (mkEnv [("len", len)]) = keccakGas len := by
  simp [keccakGasExpr, keccakGas, Expr.eval, mkEnv, List.find?, v, n]
theorem codeDepositGasExpr_eq_spec (len : Nat) :
    codeDepositGasExpr.eval (mkEnv [("len", len)]) = codeDepositGas len := by
  simp [codeDepositGasExpr, codeDepositGas, Expr.eval, mkEnv, List.find?, v, n]
theorem newCodeGasExpr_eq_spec (len : Nat) :
    newCodeGasExpr.eval (mkEnv [("len", len)]) = newCodeGas len := by
  simp [newCodeGasExpr, keccakGasExpr, newCodeGas, keccakGas, Expr.eval, mkEnv, List.find?, v, n]

end Evm.Optimism.Beryl.Spec
