/-
  Evm.Optimism.Denim.Spec.BaseTime — Denim's 200 ms blocks: the timestamp schedule, the
  BaseTime metadata deposit every block carries at tx[1], and the BaseTime predeploy the
  activation installs.

  Source: base/base @ v1.5.6 (a9f6cc9d):

    genesis/src/schedule.rs:23-66   DenimTimestampSchedule: activation at the first legacy
                                    slot at or after the configured time; then +200 ms a block
    genesis/src/rollup.rs:428-436   the schedule from the rollup config (Base mainnet:
                                    genesis block 0 at 1686789347, 2 s blocks,
                                    chains/src/config.rs:455-478)
    execution/consensus/src/lib.rs:206-218
                                    a Denim header's timestamp is the schedule's seconds
    execution/consensus/src/lib.rs:252-266
                                    a child's timestamp may equal its parent's only when both
                                    are Denim; never smaller
    consensus/src/base_time.rs      BaseTimeUpdateTx: the deposit's form and calldata; the
                                    block's millisecond part must be the schedule's
    consensus/src/source.rs:105-125 its source hash (domain 3, the block number)
    evm/src/base_time.rs:40-160     BaseTime::ensure_predeploy, run before every block's
                                    transactions (executor/block_executor.rs:186-193)

  The header itself is unchanged: `timestamp` stays in seconds (several Denim blocks share
  one), and fork activation compares it with the activation times as before. The
  millisecond time exists only as BaseTime's storage, written by tx[1].
-/

import Evm.CL.GasEmit
import Evm.Optimism.Forks

namespace Evm.Optimism.Denim.Spec

open Evm.CL.GasEmit (Expr Env mkEnv)

/-! ## The schedule (schedule.rs) -/

/-- A legacy-to-Denim schedule (schedule.rs:11-21). -/
structure Schedule where
  genesisBlock : Nat
  genesisTime  : Nat
  legacyInterval : Nat
  denimTime    : Nat

/-- Base mainnet (config.rs: genesis_l2_number 0, genesis_l2_time 1_686_789_347,
    block_time 2, denim_timestamp 1_793_901_600). -/
def baseMainnet : Schedule := ⟨0, 1686789347, 2, 1793901600⟩

/-- schedule.rs:30-34: the block offset Denim activates at (`div_ceil`). -/
def Schedule.activationOffset (s : Schedule) : Nat :=
  (s.denimTime - s.genesisTime + s.legacyInterval - 1) / s.legacyInterval

/-- schedule.rs:36-40. -/
def Schedule.isDenimAt (s : Schedule) (number : Nat) : Bool :=
  decide (number - s.genesisBlock ≥ s.activationOffset)

/-- The interval after Denim, in ms (schedule.rs:25). -/
def blockIntervalMs : Nat := 200

/-- schedule.rs:43-60: a block's timestamp in milliseconds. -/
def Schedule.blockMs (s : Schedule) (number : Nat) : Nat :=
  let k := number - s.genesisBlock
  let a := s.activationOffset
  if k < a then (s.genesisTime + k * s.legacyInterval) * 1000
  else (s.genesisTime + a * s.legacyInterval) * 1000 + (k - a) * blockIntervalMs

/-- Base mainnet's Denim activation block (measured: 53,556,127 is the first block whose
    header carries the Denim extraData and whose tx[1] is a BaseTime deposit). -/
theorem baseMainnet_activation : baseMainnet.activationOffset = 53556127 := by decide

example : baseMainnet.blockMs 53556126 = 1793901599000 := by decide
example : baseMainnet.blockMs 53556127 = 1793901601000 := by decide
example : baseMainnet.blockMs 53556128 = 1793901601200 := by decide
example : baseMainnet.blockMs 53556131 = 1793901601800 := by decide
example : baseMainnet.blockMs 53556132 = 1793901602000 := by decide

/-- consensus lib.rs:206-218 + base_time.rs: a Denim block's header seconds and its
    BaseTime millisecond part. -/
def Schedule.seconds (s : Schedule) (number : Nat) : Nat := s.blockMs number / 1000
def Schedule.millisPart (s : Schedule) (number : Nat) : Nat := s.blockMs number % 1000

/-- consensus lib.rs:252-266: `timestamp` against the parent's. -/
def timestampOk (parentDenim denim : Bool) (parentTs ts : Nat) : Bool :=
  decide (parentTs < ts) || (decide (parentTs = ts) && parentDenim && denim)

/-! ## The BaseTime metadata deposit (base_time.rs) -/

/-- predeploys.rs:144. -/
def baseTimeAddr : Nat := 0x4200000000000000000000000000000000000030
/-- `setTimestampMillisPart(uint16)` (base_time.rs:39). -/
def setMillisSelector : Nat := 0x86bdf394
/-- SystemAddresses::DEPOSITOR_ACCOUNT (predeploys.rs:155). -/
def depositorAddr : Nat := 0xDeaDDEaDDeAdDeAdDEAdDEaddeAddEAdDEAd0001
/-- REGOLITH_SYSTEM_TX_GAS (consensus lib.rs:14): the deposit's gas limit. -/
def depositGas : Nat := 1000000
/-- source.rs:7-19: the BaseTime deposit source domain. -/
def sourceDomain : Nat := 3

/-- base_time.rs:46-50: a millisecond part is a 200 ms slot of the second. -/
def validMillis (ms : Nat) : Bool := decide (ms < 1000 ∧ ms % blockIntervalMs = 0)

/-- base_time.rs:70-94: the calldata's millisecond part — 36 bytes, the selector, 30 zero
    bytes, the uint16 — or none. -/
def decodeCalldata (data : List UInt8) : Option Nat :=
  if data.length ≠ 36 then none
  else
    let sel := data.take 4 |>.foldl (fun a b => a * 256 + b.toNat) 0
    if sel ≠ setMillisSelector then none
    else if (data.drop 4 |>.take 30).any (· ≠ 0) then none
    else
      let ms := (data.getD 34 0).toNat * 256 + (data.getD 35 0).toNat
      if validMillis ms then some ms else none

example : decodeCalldata ([0x86, 0xbd, 0xf3, 0x94] ++ List.replicate 30 0 ++ [0x03, 0x20]) = some 800 := by decide
example : decodeCalldata ([0x86, 0xbd, 0xf3, 0x94] ++ List.replicate 30 0 ++ [0x03, 0x21]) = none := by decide

/-- base_time.rs:166-198 (validate_deposit) and :148-164 (the schedule): tx[1] is a deposit
    from the depositor to BaseTime, no mint, no value, the system gas, not a system tx, with
    the domain-3 source hash of the block number (checked by the host, which hashes), and its
    millisecond part is the schedule's. -/
def metadataOk (s : Schedule) (number : Nat) (from_ to mint value gas : Nat) (isSystem : Bool)
    (data : List UInt8) : Bool :=
  decide (from_ = depositorAddr) && decide (to = baseTimeAddr) && decide (mint = 0) && decide (value = 0) && decide (gas = depositGas)
    && !isSystem && decodeCalldata data == some (s.millisPart number)

/-! ## The predeploy (evm/src/base_time.rs:40-160) -/

/-- The implementation's code address (base_time.rs:43). -/
def implementationAddr : Nat := 0xc0D3C0d3C0d3C0D3c0d3C0d3c0D3C0d3c0d30030
/-- The runtime's code hash (base_time.rs:47; chains/op/base-time.hex hashes to it). -/
def implementationCodeHash : Nat := 0x9c4c8a497a69d0b8f2ba67be0bee7a1373186055978c3be6ec3068e0ec27f32a
/-- EIP-1967 slots (base_time.rs:55-60). -/
def implementationSlot : Nat := 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc
def adminSlot : Nat := 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103
/-- Predeploys::PROXY_ADMIN (predeploys.rs:112). -/
def proxyAdmin : Nat := 0x4200000000000000000000000000000000000018

/-- `ensure_predeploy` before a Denim block's txs: when the proxy's implementation slot is
    still zero, the proxy must be a coded account administered by ProxyAdmin (else the block
    is invalid), and the implementation's code is installed and linked; once linked, nothing
    (the slot is the migration marker, kept across later upgrades). -/
inductive Install | none | link | invalid
  deriving DecidableEq, Repr

def ensurePredeploy (denim : Bool) (implSlot : Nat) (proxyHasCode : Bool) (adminWord : Nat) : Install :=
  if !denim then .none
  else if implSlot ≠ 0 then .none
  else if !proxyHasCode then .invalid
  else if adminWord ≠ proxyAdmin then .invalid
  else .link

/-! ## Emitted forms (EmitHostCL), proved = the spec -/

private def v (x : String) : Expr := .var x
private def n (k : Nat) : Expr := .lit k

/-- `baseMainnet.blockMs` over `number`. -/
def blockMsExpr : Expr :=
  .ite (v "number") (n 53556127)
    (.mul (.add (n 1686789347) (.mul (v "number") (n 2))) (n 1000))
    (.add (n 1793901601000) (.mul (.sub (v "number") (n 53556127)) (n 200)))

theorem blockMsExpr_eq_spec (number : Nat) :
    blockMsExpr.eval (mkEnv [("number", number)]) = baseMainnet.blockMs number := by
  have ha : baseMainnet.activationOffset = 53556127 := baseMainnet_activation
  simp only [Schedule.blockMs, ha]
  simp only [blockMsExpr, Expr.eval, mkEnv, List.find?, v, n, baseMainnet, blockIntervalMs]
  by_cases h : number < 53556127 <;> simp [h] <;> omega

/-- `baseMainnet.isDenimAt` over `number` (1/0). -/
def isDenimExpr : Expr := .ite (v "number") (n 53556127) (n 0) (n 1)

theorem isDenimExpr_eq_spec (number : Nat) :
    isDenimExpr.eval (mkEnv [("number", number)]) = if baseMainnet.isDenimAt number then 1 else 0 := by
  have ha : baseMainnet.activationOffset = 53556127 := baseMainnet_activation
  simp only [Schedule.isDenimAt, ha]
  simp only [isDenimExpr, Expr.eval, mkEnv, List.find?, v, n, baseMainnet]
  by_cases h : number < 53556127 <;> simp [h] <;> omega

/-- A Denim block's milliseconds on Base mainnet, in closed form. -/
theorem blockMs_denim (number : Nat) (h : 53556127 ≤ number) :
    baseMainnet.blockMs number = 1793901601000 + (number - 53556127) * 200 := by
  rw [← blockMsExpr_eq_spec]
  have h' : ¬ number < 53556127 := by omega
  simp [blockMsExpr, Expr.eval, mkEnv, List.find?, v, n, h']

/-- The schedule meets the parent rule: a Denim block's seconds are at least its Denim
    parent's (equal for five blocks in each second), so the schedule gate subsumes
    `timestampOk` from the activation on. -/
theorem schedule_timestampOk (number : Nat) (h : 53556127 ≤ number) :
    timestampOk true true (baseMainnet.seconds number) (baseMainnet.seconds (number + 1)) = true := by
  simp only [timestampOk, Schedule.seconds, blockMs_denim number h, blockMs_denim (number + 1) (by omega)]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_true]
  omega

end Evm.Optimism.Denim.Spec
