/-
  Evm.IR.Dispatch — per-IR.Op handler dispatch.

  Given an `IR.Op` tag (and the active fork), returns the canonical
  `Handler = Evm → Except Exception Evm` that runs the opcode.

  The handler IS the corresponding `Fork.Instructions.X` Effect
  handler — no new semantics here, just dispatch. Per-op soundness
  theorems are correspondingly trivial (definitional). This is
  intentional: there's exactly one definition of what `IR.Op.add`
  means (Frontier.Instructions.add), and the JIT/interp emitters
  both refine that single definition.

  Status: pure ops + state-touching ops wired; SLOAD/SSTORE/BALANCE/
  EXTCODE* carry per-fork repricing ladders, complete through Berlin/
  London (EIP-150/1283/1884/2200/2929/3529). PUSH-family needs a
  small hypothesis about the bytecode's immediate matching the
  IR.Op's carried `imm`.
-/

import Evm.IR.Types
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Instructions.Comparison
import Evm.Frontier.Vm.Instructions.Bitwise
import Evm.Frontier.Vm.Instructions.Stack
import Evm.Frontier.Vm.Instructions.ControlFlow
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Vm.Instructions.Keccak
import Evm.Frontier.Vm.Instructions.Environment
import Evm.Frontier.Vm.Instructions.Block
import Evm.Frontier.Vm.Instructions.Storage
import Evm.Frontier.Vm.Instructions.Log
import Evm.TangerineWhistle.Vm.Instructions
import Evm.SpuriousDragon.Vm.Instructions
import Evm.Constantinople.Vm.Instructions.Bitwise
import Evm.Constantinople.Vm.Instructions.Environment
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Byzantium.Vm.Instructions.Memory
import Evm.Istanbul.Vm.Instructions.Block
import Evm.Istanbul.Vm.Instructions.Environment
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Effect
import Evm.Berlin.Vm.Effect
import Evm.London.Vm.Effect
import Evm.London.Vm.Instructions.Block
import Evm.Cancun.Vm.Instructions

namespace Evm.IR.Dispatch

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-- Per-IR.Op handler dispatch, parametric in `Fork`.
    Returns `none` for ops we haven't classified yet (the chunk
    runner treats `none` as "invalid op for this fork"). -/
def Op.handler (fork : Evm.Fork) (op : Op) : Option Handler := Id.run do
  let _ := fork  -- per-fork dispatch arrives as opcodes that vary get added
  match op with
  -- 0x01..0x0b: pure arithmetic
  | .add        => some Instructions.add
  | .mul        => some Instructions.mul
  | .sub        => some Instructions.sub
  | .div        => some Instructions.div
  | .sdiv       => some Instructions.sdiv
  | .addmod     => some Instructions.addmod
  | .mulmod     => some Instructions.mulmod
  -- EXP: EIP-160 (Spurious Dragon) reprices the per-byte cost 10 → 50;
  -- semantics (powMod) never changed.
  | .exp        =>
    if fork.atLeast .spuriousDragon
    then some Evm.SpuriousDragon.Vm.Instructions.exp
    else some Instructions.exp
  | .signextend => some Instructions.signextend
  -- 0x10..0x15: pure comparison
  | .lt         => some Instructions.lt
  | .gt         => some Instructions.gt
  | .slt        => some Instructions.slt
  | .sgt        => some Instructions.sgt
  | .eq         => some Instructions.eq
  | .iszero     => some Instructions.iszero
  -- 0x06..0x07: mod / smod (Frontier's defs are mod_ / smod_ since `mod`
  -- is a Lean keyword in the Std namespace).
  | .mod        => some Instructions.mod_
  | .smod       => some Instructions.smod_
  -- 0x16..0x19: pure bitwise (NOT/BYTE + AND/OR/XOR)
  | .and_       => some Instructions.and_
  | .or_        => some Instructions.or_
  | .xor_       => some Instructions.xor_
  | .not_       => some Instructions.not_
  | .byte       => some Instructions.byte
  -- 0x20: KECCAK256 (memory-touching, gas includes per-word)
  | .keccak256  => some Instructions.keccak256
  -- 0x30..0x3a: environment readers (most are pre-Berlin and fork-
  -- agnostic at the handler level; balance/extcode* gain cold/warm
  -- surcharges in Berlin — see per-fork branch below).
  | .address       => some Instructions.address
  | .origin        => some Instructions.origin
  | .caller        => some Instructions.caller
  | .callvalue     => some Instructions.callvalue
  | .calldataload  => some Instructions.calldataload
  | .calldatasize  => some Instructions.calldatasize
  | .calldatacopy  => some Instructions.calldatacopy
  | .codesize      => some Instructions.codesize
  | .codecopy      => some Instructions.codecopy
  | .gasprice      => some Instructions.gasprice
  -- 0x40..0x46: block-context readers
  | .blockhash  => some Instructions.blockhash
  | .coinbase   => some Instructions.coinbase
  | .timestamp  => some Instructions.timestamp
  | .number     => some Instructions.number
  | .gaslimit   => some Instructions.gaslimit
  -- 0x44 is DIFFICULTY pre-Paris and PREVRANDAO after; both read the
  -- same env field (the importer stores mixHash there post-Merge), so
  -- the Frontier handler is the binding for every fork.
  | .prevrandao => some Instructions.difficulty
  -- 0x50: POP; 0x51..0x53 memory; 0x59 MSIZE
  | .pop        => some Instructions.pop
  | .mload      => some Instructions.mload
  | .mstore     => some Instructions.mstore
  | .mstore8    => some Instructions.mstore8
  | .msize      => some Instructions.msize
  -- 0x58, 0x5a, 0x5b: PC, GAS, JUMPDEST. The IR carries compile-time
  -- literals (pc position / suffix static gas); the canonical handler
  -- reads the live frame. They agree because the compiler only emits
  -- `.pc v` at bytecode position v (resp. `.gas rem` with the chunk's
  -- residual static gas) — the chunk soundness theorems carry that
  -- correspondence.
  | .pc _       => some Instructions.pc
  | .gas _      => some Instructions.gas
  | .jumpdest   => some Instructions.jumpdest
  -- 0x60..0x7f: PUSH-N. The IR carries `imm` for compile-time analysis;
  -- the canonical handler reads the immediate from bytecode at runtime.
  -- The Phase 2a compiler must guarantee bytecode[pc+1..pc+1+n] = imm
  -- (proven by the compile-loop's correctness — Phase 4 obligation).
  | .push n _   => some (Instructions.push n)
  -- 0x80..0x8f, 0x90..0x9f, 0xa0..0xa4: parametric stack/log ops
  | .dup n      => some (Instructions.dup n)
  | .swap n     => some (Instructions.swap n)
  | .log n      => some (Instructions.log n)
  -- Storage / external-account ops, repriced across forks. Each arm
  -- binds the repricing fork's own tested handler (the same definition
  -- that fork's Effect step1 / interpreter uses). Berlin's EIP-2929
  -- warm/cold handlers are Handler-shaped because the accessed-
  -- address/-slot sets live in `evm.env` (#206); every fork ≥ berlin
  -- falls through its step1 chain to Berlin's `do*Pure` (London
  -- overrides only SSTORE — EIP-3529 refund).
  | .sload =>
    if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doSloadPure            -- EIP-2929: 100/2100
    else if fork.atLeast .istanbul
    then some Evm.Istanbul.Vm.Instructions.sload          -- EIP-1884: 800
    else if fork.atLeast .tangerineWhistle
    then some Evm.TangerineWhistle.Vm.Instructions.sload  -- EIP-150: 200
    else some Instructions.sload                          -- 50
  | .sstore =>
    if fork.atLeast .london
    then some Evm.London.Vm.Effect.doSstoreLondon         -- EIP-3529 refund cut
    else if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doSstorePure           -- EIP-2929 + EIP-2200
    else if fork.atLeast .istanbul
    then some Evm.Istanbul.Vm.Instructions.sstore         -- EIP-2200 net metering
    else
      match fork with
      -- EIP-1283 net metering: Constantinople ONLY (Petersburg reverts
      -- it back to the Frontier 5000/20000 + clear-refund schedule).
      | .constantinople => some Evm.Constantinople.Vm.Instructions.sstore
      | _ => some Instructions.sstore
  | .balance =>
    if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doBalancePure          -- EIP-2929: 100/2600
    else if fork.atLeast .istanbul
    -- Istanbul implements the EIP-1884 reprice (700) inline at the
    -- Effect layer; `doBalance` IS that handler.
    then some Evm.Istanbul.Vm.Effect.doBalance
    else if fork.atLeast .tangerineWhistle
    then some Evm.TangerineWhistle.Vm.Instructions.balance -- EIP-150: 400
    else some Instructions.balance                         -- 20
  -- EXTCODESIZE/EXTCODECOPY: repriced at EIP-150 (20 → 700 base), then
  -- EIP-2929 (warm/cold); EIP-1884 left them alone, so the TW binding
  -- holds through Muir Glacier.
  | .extcodesize =>
    if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doExtcodesizePure
    else if fork.atLeast .tangerineWhistle
    then some Evm.TangerineWhistle.Vm.Instructions.extcodesize
    else some Instructions.extcodesize
  | .extcodecopy =>
    if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doExtcodecopyPure
    else if fork.atLeast .tangerineWhistle
    then some Evm.TangerineWhistle.Vm.Instructions.extcodecopy
    else some Instructions.extcodecopy
  -- Post-Frontier additions, gated on their INTRODUCING fork and
  -- bound to that fork's handler. Per-fork repricings are #223.
  | .shl =>
    if fork.atLeast .constantinople
    then some Evm.Constantinople.Vm.Instructions.shl else none
  | .shr =>
    if fork.atLeast .constantinople
    then some Evm.Constantinople.Vm.Instructions.shr else none
  | .sar =>
    if fork.atLeast .constantinople
    then some Evm.Constantinople.Vm.Instructions.sar else none
  | .extcodehash =>
    if fork.atLeast .berlin
    then some Evm.Berlin.Vm.Effect.doExtcodehashPure        -- EIP-2929
    else if fork.atLeast .istanbul
    then some Evm.Istanbul.Vm.Instructions.extcodehash      -- EIP-1884: 700
    else if fork.atLeast .constantinople
    then some Evm.Constantinople.Vm.Instructions.extcodehash -- EIP-1052: 400
    else none
  | .returndatasize =>
    if fork.atLeast .byzantium
    then some Evm.Byzantium.Vm.Instructions.returndatasize else none
  | .returndatacopy =>
    if fork.atLeast .byzantium
    then some Evm.Byzantium.Vm.Instructions.returndatacopy else none
  | .chainid =>
    if fork.atLeast .istanbul
    then some Evm.Istanbul.Vm.Instructions.chainid else none
  | .selfbalance =>
    if fork.atLeast .istanbul
    then some Evm.Istanbul.Vm.Instructions.selfbalance else none
  | .basefee =>
    if fork.atLeast .london
    then some Evm.London.Vm.Instructions.baseFee else none
  -- PUSH0 (Shanghai, EIP-3855) has no standalone `Handler`: the
  -- Shanghai Effect layer wires it inline as `doPush0` (StepResult-
  -- valued), which doesn't fit `Option Handler`. The IR semantics
  -- lives in `execOp .push0`; a Handler-shaped binding can land if
  -- Shanghai ever factors one out. Left `none` so the gap is visible.
  | .push0 => none
  -- Cancun additions: only legal on Cancun and later forks.
  -- EIP-1153 (TLOAD/TSTORE), EIP-5656 (MCOPY), EIP-4844 (BLOBHASH),
  -- EIP-7516 (BLOBBASEFEE).
  | .tload      =>
    match fork with
    | .cancun | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam =>
      some Evm.Cancun.Vm.Instructions.tload
    | _ => none
  | .tstore     =>
    match fork with
    | .cancun | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam =>
      some Evm.Cancun.Vm.Instructions.tstore
    | _ => none
  | .mcopy      =>
    match fork with
    | .cancun | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam =>
      some Evm.Cancun.Vm.Instructions.mcopy
    | _ => none
  | .blobhash   =>
    match fork with
    | .cancun | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam =>
      some Evm.Cancun.Vm.Instructions.blobhash
    | _ => none
  | .blobbasefee =>
    match fork with
    | .cancun | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam =>
      some Evm.Cancun.Vm.Instructions.blobbasefee
    | _ => none
  -- All other ops: not yet wired (currently only the Osaka
  -- placeholder CLZ).
  | _           => none

/-! ## Per-op soundness theorems

    For each wired op, `Op.handler fork .X = some Frontier.Instructions.X`.
    These are trivial (`rfl`) by construction — the dispatch table IS
    the handler binding. The audit value is in the name being
    discoverable: a grep for `_dispatch_sound` lists every op that has
    a verified dispatch entry.

    State-touching and per-fork-varying ops will get more substantive
    soundness theorems once their dispatch entries differ across forks. -/

theorem add_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .add = some Instructions.add := rfl

theorem mul_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mul = some Instructions.mul := rfl

theorem sub_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .sub = some Instructions.sub := rfl

theorem div_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .div = some Instructions.div := rfl

theorem sdiv_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .sdiv = some Instructions.sdiv := rfl

theorem addmod_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .addmod = some Instructions.addmod := rfl

theorem mulmod_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mulmod = some Instructions.mulmod := rfl

/-- EXP repricing boundary (EIP-160): Frontier 10/byte through
    Tangerine Whistle, 50/byte from Spurious Dragon on. -/
theorem exp_dispatch_sound_frontier :
    Op.handler .frontier .exp = some Instructions.exp := rfl
theorem exp_dispatch_sound_tangerine :
    Op.handler .tangerineWhistle .exp = some Instructions.exp := rfl
theorem exp_dispatch_sound_spurious :
    Op.handler .spuriousDragon .exp
      = some Evm.SpuriousDragon.Vm.Instructions.exp := rfl
theorem exp_dispatch_sound_london :
    Op.handler .london .exp
      = some Evm.SpuriousDragon.Vm.Instructions.exp := rfl

theorem signextend_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .signextend = some Instructions.signextend := rfl

theorem lt_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .lt = some Instructions.lt := rfl

theorem gt_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .gt = some Instructions.gt := rfl

theorem slt_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .slt = some Instructions.slt := rfl

theorem sgt_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .sgt = some Instructions.sgt := rfl

theorem eq_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .eq = some Instructions.eq := rfl

theorem iszero_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .iszero = some Instructions.iszero := rfl

theorem and_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .and_ = some Instructions.and_ := rfl

theorem or_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .or_ = some Instructions.or_ := rfl

theorem xor_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .xor_ = some Instructions.xor_ := rfl

theorem byte_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .byte = some Instructions.byte := rfl

theorem pop_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .pop = some Instructions.pop := rfl

theorem mod_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mod = some Instructions.mod_ := rfl

theorem smod_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .smod = some Instructions.smod_ := rfl

theorem not_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .not_ = some Instructions.not_ := rfl

theorem keccak256_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .keccak256 = some Instructions.keccak256 := rfl

-- Environment readers
theorem address_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .address = some Instructions.address := rfl

theorem origin_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .origin = some Instructions.origin := rfl

theorem caller_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .caller = some Instructions.caller := rfl

theorem callvalue_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .callvalue = some Instructions.callvalue := rfl

theorem calldataload_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .calldataload = some Instructions.calldataload := rfl

theorem calldatasize_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .calldatasize = some Instructions.calldatasize := rfl

theorem calldatacopy_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .calldatacopy = some Instructions.calldatacopy := rfl

theorem codesize_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .codesize = some Instructions.codesize := rfl

theorem codecopy_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .codecopy = some Instructions.codecopy := rfl

theorem gasprice_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .gasprice = some Instructions.gasprice := rfl

-- Block context
theorem blockhash_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .blockhash = some Instructions.blockhash := rfl

theorem coinbase_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .coinbase = some Instructions.coinbase := rfl

theorem timestamp_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .timestamp = some Instructions.timestamp := rfl

theorem number_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .number = some Instructions.number := rfl

theorem gaslimit_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .gaslimit = some Instructions.gaslimit := rfl

-- Memory + frame state
theorem mload_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mload = some Instructions.mload := rfl

theorem mstore_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mstore = some Instructions.mstore := rfl

theorem mstore8_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .mstore8 = some Instructions.mstore8 := rfl

theorem msize_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .msize = some Instructions.msize := rfl

theorem pc_dispatch_sound (fork : Evm.Fork) (v : Nat) :
    Op.handler fork (.pc v) = some Instructions.pc := rfl

theorem gas_dispatch_sound (fork : Evm.Fork) (rem : Nat) :
    Op.handler fork (.gas rem) = some Instructions.gas := rfl

theorem jumpdest_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .jumpdest = some Instructions.jumpdest := rfl

-- Parametric ops: IR carries `n`, handler is `Instructions.X n`.
theorem push_dispatch_sound (fork : Evm.Fork) (n : Nat) (imm : Evm.U256) :
    Op.handler fork (.push n imm) = some (Instructions.push n) := rfl

theorem dup_dispatch_sound (fork : Evm.Fork) (n : Nat) :
    Op.handler fork (.dup n) = some (Instructions.dup n) := rfl

theorem swap_dispatch_sound (fork : Evm.Fork) (n : Nat) :
    Op.handler fork (.swap n) = some (Instructions.swap n) := rfl

theorem log_dispatch_sound (fork : Evm.Fork) (n : Nat) :
    Op.handler fork (.log n) = some (Instructions.log n) := rfl

/-! ### Storage / external-account dispatch ladder

    These ops keep their semantics but get repriced across forks, so
    the theorems are per-fork spot checks at each repricing boundary
    (plus delegation checks for the forks that inherit a predecessor's
    binding). -/

-- Frontier flat costs (≤ DAO fork).
theorem sload_dispatch_sound_frontier :
    Op.handler .frontier .sload = some Instructions.sload := rfl
theorem sstore_dispatch_sound_frontier :
    Op.handler .frontier .sstore = some Instructions.sstore := rfl
theorem balance_dispatch_sound_homestead :
    Op.handler .homestead .balance = some Instructions.balance := rfl
theorem extcodesize_dispatch_sound_daoFork :
    Op.handler .daoFork .extcodesize = some Instructions.extcodesize := rfl
theorem extcodecopy_dispatch_sound_frontier :
    Op.handler .frontier .extcodecopy = some Instructions.extcodecopy := rfl

-- EIP-150 (Tangerine Whistle) repricings. sload/balance hold through
-- Petersburg; extcodesize/extcodecopy hold through Muir Glacier
-- (EIP-1884 didn't touch them).
theorem sload_dispatch_sound_tangerine :
    Op.handler .tangerineWhistle .sload
      = some Evm.TangerineWhistle.Vm.Instructions.sload := rfl
theorem sload_dispatch_sound_petersburg :
    Op.handler .petersburg .sload
      = some Evm.TangerineWhistle.Vm.Instructions.sload := rfl
theorem balance_dispatch_sound_byzantium :
    Op.handler .byzantium .balance
      = some Evm.TangerineWhistle.Vm.Instructions.balance := rfl
theorem extcodesize_dispatch_sound_tangerine :
    Op.handler .tangerineWhistle .extcodesize
      = some Evm.TangerineWhistle.Vm.Instructions.extcodesize := rfl
theorem extcodecopy_dispatch_sound_muirGlacier :
    Op.handler .muirGlacier .extcodecopy
      = some Evm.TangerineWhistle.Vm.Instructions.extcodecopy := rfl

-- EIP-1283 net metering: Constantinople ONLY; Petersburg reverts to
-- the Frontier schedule.
theorem sstore_dispatch_sound_constantinople :
    Op.handler .constantinople .sstore
      = some Evm.Constantinople.Vm.Instructions.sstore := rfl
theorem sstore_dispatch_sound_petersburg_reverts_eip1283 :
    Op.handler .petersburg .sstore = some Instructions.sstore := rfl

-- EIP-1884 + EIP-2200 (Istanbul), inherited by Muir Glacier.
theorem sload_dispatch_sound_istanbul :
    Op.handler .istanbul .sload
      = some Evm.Istanbul.Vm.Instructions.sload := rfl
theorem sload_dispatch_sound_muirGlacier :
    Op.handler .muirGlacier .sload
      = some Evm.Istanbul.Vm.Instructions.sload := rfl
theorem sstore_dispatch_sound_istanbul :
    Op.handler .istanbul .sstore
      = some Evm.Istanbul.Vm.Instructions.sstore := rfl
theorem balance_dispatch_sound_istanbul :
    Op.handler .istanbul .balance
      = some Evm.Istanbul.Vm.Effect.doBalance := rfl
theorem extcodehash_dispatch_sound_istanbul :
    Op.handler .istanbul .extcodehash
      = some Evm.Istanbul.Vm.Instructions.extcodehash := rfl

-- EIP-2929 (Berlin): warm/cold via the env-carried accessed sets;
-- the `do*Pure` handlers are what Berlin's step1 lifts. Later forks
-- fall through their step1 chain to the same bindings, except SSTORE,
-- which London overrides (EIP-3529 refund cut) — spot-check both the
-- Berlin bindings and the deep-fork delegation.
theorem sload_dispatch_sound_berlin :
    Op.handler .berlin .sload
      = some Evm.Berlin.Vm.Effect.doSloadPure := rfl
theorem sload_dispatch_sound_cancun :
    Op.handler .cancun .sload
      = some Evm.Berlin.Vm.Effect.doSloadPure := rfl
theorem sstore_dispatch_sound_berlin :
    Op.handler .berlin .sstore
      = some Evm.Berlin.Vm.Effect.doSstorePure := rfl
theorem sstore_dispatch_sound_london :
    Op.handler .london .sstore
      = some Evm.London.Vm.Effect.doSstoreLondon := rfl
theorem sstore_dispatch_sound_amsterdam :
    Op.handler .amsterdam .sstore
      = some Evm.London.Vm.Effect.doSstoreLondon := rfl
theorem balance_dispatch_sound_berlin :
    Op.handler .berlin .balance
      = some Evm.Berlin.Vm.Effect.doBalancePure := rfl
theorem extcodesize_dispatch_sound_berlin :
    Op.handler .berlin .extcodesize
      = some Evm.Berlin.Vm.Effect.doExtcodesizePure := rfl
theorem extcodecopy_dispatch_sound_berlin :
    Op.handler .berlin .extcodecopy
      = some Evm.Berlin.Vm.Effect.doExtcodecopyPure := rfl
theorem extcodehash_dispatch_sound_berlin :
    Op.handler .berlin .extcodehash
      = some Evm.Berlin.Vm.Effect.doExtcodehashPure := rfl
theorem extcodehash_dispatch_sound_prague :
    Op.handler .prague .extcodehash
      = some Evm.Berlin.Vm.Effect.doExtcodehashPure := rfl

theorem prevrandao_dispatch_sound (fork : Evm.Fork) :
    Op.handler fork .prevrandao = some Instructions.difficulty := rfl

-- Post-Frontier additions: sound at their introducing fork,
-- `none` (invalid) below it.
theorem shl_dispatch_sound_constantinople :
    Op.handler .constantinople .shl
      = some Evm.Constantinople.Vm.Instructions.shl := rfl
theorem shr_dispatch_sound_constantinople :
    Op.handler .constantinople .shr
      = some Evm.Constantinople.Vm.Instructions.shr := rfl
theorem sar_dispatch_sound_constantinople :
    Op.handler .constantinople .sar
      = some Evm.Constantinople.Vm.Instructions.sar := rfl
theorem extcodehash_dispatch_sound_constantinople :
    Op.handler .constantinople .extcodehash
      = some Evm.Constantinople.Vm.Instructions.extcodehash := rfl
theorem returndatasize_dispatch_sound_byzantium :
    Op.handler .byzantium .returndatasize
      = some Evm.Byzantium.Vm.Instructions.returndatasize := rfl
theorem returndatacopy_dispatch_sound_byzantium :
    Op.handler .byzantium .returndatacopy
      = some Evm.Byzantium.Vm.Instructions.returndatacopy := rfl
theorem chainid_dispatch_sound_istanbul :
    Op.handler .istanbul .chainid
      = some Evm.Istanbul.Vm.Instructions.chainid := rfl
theorem selfbalance_dispatch_sound_istanbul :
    Op.handler .istanbul .selfbalance
      = some Evm.Istanbul.Vm.Instructions.selfbalance := rfl
theorem basefee_dispatch_sound_london :
    Op.handler .london .basefee
      = some Evm.London.Vm.Instructions.baseFee := rfl

theorem shl_invalid_pre_constantinople :
    Op.handler .byzantium .shl = none := rfl
theorem returndatasize_invalid_pre_byzantium :
    Op.handler .frontier .returndatasize = none := rfl
theorem chainid_invalid_pre_istanbul :
    Op.handler .constantinople .chainid = none := rfl
theorem basefee_invalid_pre_london :
    Op.handler .istanbul .basefee = none := rfl

-- Cancun additions: each gates on Fork ≥ Cancun. Theorem shape is
-- per-fork — pre-Cancun forks dispatch to `none` (op invalid for fork).
theorem tload_dispatch_sound_cancun :
    Op.handler .cancun .tload = some Evm.Cancun.Vm.Instructions.tload := rfl
theorem tstore_dispatch_sound_cancun :
    Op.handler .cancun .tstore = some Evm.Cancun.Vm.Instructions.tstore := rfl
theorem mcopy_dispatch_sound_cancun :
    Op.handler .cancun .mcopy = some Evm.Cancun.Vm.Instructions.mcopy := rfl
theorem blobhash_dispatch_sound_cancun :
    Op.handler .cancun .blobhash = some Evm.Cancun.Vm.Instructions.blobhash := rfl
theorem blobbasefee_dispatch_sound_cancun :
    Op.handler .cancun .blobbasefee =
      some Evm.Cancun.Vm.Instructions.blobbasefee := rfl

-- Invalidity: Cancun additions are NOT legal pre-Cancun. Spot check.
theorem tload_invalid_pre_cancun :
    Op.handler .frontier .tload = none := rfl
theorem blobhash_invalid_pre_cancun :
    Op.handler .istanbul .blobhash = none := rfl

end Evm.IR.Dispatch
