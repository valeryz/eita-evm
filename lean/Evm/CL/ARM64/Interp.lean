/-
  Evm.CL.ARM64.Interp — per-op handler registry for the threaded
  interpreter (Phase 5).

  Instantiates the shape emitters in `Evm.CL.ARM64` with static gas
  costs drawn from `IR.Op.metadata` / `IR.Terminator.metadata` — the
  same tables the verified IR pipeline (`Evm.IR.Compile`) is contracted
  to use. No handler redeclares a gas constant: the cost an emitted
  handler charges IS `(metadata interpFork op).staticCost`, so the
  Phase 2 per-op soundness theorems pin the schedule in one place.

  Dynamic-gas *coefficients* (6/word KECCAK, 50/byte EXP, 8/byte LOG,
  3/word copy, memory-expansion 3w + w²/512) remain inline in the
  shape emitters: `DynamicGasShape` declares the shape, not the
  multiplier, and those formulas are what the JIT (Phase 6) will share.

  Emit via:  lake exe emitARM64 > c/handlers.S
-/

import Evm.CL.ARM64
import Evm.CL.ARM64.CallGas
import Evm.CL.ARM64.SstoreGas
import Evm.CL.ARM64.RunProgram
import Evm.IR.Types
import Evm.Frontier.Vm.Gas
import Evm.SpuriousDragon.Vm.Gas
import Evm.Istanbul.Vm.Gas

namespace Evm.CL.ARM64.Interp

open Evm.IR

/-- The fork whose cost schedule the threaded interpreter implements.
    The hand-written handlers this module replaced used Cancun-era
    constants (warm EIP-2929 access costs, PUSH0, TLOAD/MCOPY/BLOBHASH
    present), so the registry is pinned there. -/
def interpFork : Evm.Fork := .cancun

/-- Static cost of an op per the IR metadata table on fork `f`. Panics
    (at emit time, not at run time) if the op has no metadata row —
    a registry/metadata mismatch must never emit. -/
def opCostOn (f : Evm.Fork) (op : Op) : Nat :=
  match Op.metadata f op with
  | some m => m.staticCost
  | none   => panic! s!"ARM64.Interp: no metadata for {repr op} on {repr f}"

/-- Static cost of an op on `interpFork` (the registry's charging fork). -/
def opCost (op : Op) : Nat :=
  match Op.metadata interpFork op with
  | some m => m.staticCost
  -- ops introduced after the registry fork (CLZ, Osaka): priced on their first fork;
  -- the per-fork dispatch tables keep them absent before it.
  | none   => opCostOn .osaka op

/-- Static cost of a terminator per the IR metadata table on fork `f`. -/
def termCostOn (f : Evm.Fork) (t : Terminator) : Nat :=
  match Terminator.metadata f t with
  | some m => m.staticCost
  | none   => panic! s!"ARM64.Interp: no metadata for {repr t} on {repr f}"

/-- Static cost of a terminator on `interpFork`. -/
def termCost (t : Terminator) : Nat := termCostOn interpFork t

/-- EXP's per-exponent-byte coefficient: 10 until EIP-160 (Spurious
    Dragon) repriced it to 50. Sourced from the fork Gas tables, not
    restated here. -/
def expByteCost (f : Evm.Fork) : Nat :=
  if f.atLeast .spuriousDragon then Evm.SpuriousDragon.Vm.Gas.expByte
  else Evm.Frontier.Vm.Gas.expByte

/-- The handler registry: (dispatch name, emitted asm) for every
    opcode the threaded interpreter implements. Ops use the supplied
    `oc` (the interp tier passes `opCost`; the JIT flat set passes 0),
    frame-ending / control-flow opcodes use `termCost`; handlers whose
    gas flows entirely through a host callback or the sub-frame's
    `gas_used` (SLOAD/SSTORE/TLOAD/TSTORE/BALANCE/EXTCODE*/CALL-family/
    CREATE*) take no cost parameter — see `chargedCost`. -/
def handlersWith (oc : Op → Nat) : List (String × String) := [
  ("add", binArithHandler "add" (oc .add) "adds" "adcs" "adc"),
  ("sub", binArithHandler "sub" (oc .sub) "subs" "sbcs" "sbc"),
  ("and", bitwiseHandler "and" (oc .and_) "and"),
  ("or",  bitwiseHandler "or"  (oc .or_) "orr"),
  ("xor", bitwiseHandler "xor" (oc .xor_) "eor"),
  ("lt", cmpHandler "lt" (oc .lt) "lo"),
  ("gt", cmpHandlerSwapped "gt" (oc .gt) "lo"),
  ("eq", eqHandler (oc .eq)),
  ("iszero", iszeroHandler (oc .iszero)),
  ("clz", clzHandler (oc .clz)),
  ("not", notHandler (oc .not_)),
  ("pop", popHandler (oc .pop)),
  ("stop", stopHandler),
  ("jumpdest", jumpdestHandler (oc .jumpdest)),
  ("invalid", invalidHandler),
  ("address",   pushU256FromField "address"   (oc .address) Offset.address),
  ("origin",    pushU256FromField "origin"    (oc .origin) Offset.origin),
  ("caller",    pushU256FromField "caller"    (oc .caller) Offset.caller),
  ("coinbase",  pushU256FromField "coinbase"  (oc .coinbase) Offset.coinbase),
  ("callvalue", pushU256FromField "callvalue" (oc .callvalue) Offset.callvalue),
  ("gasprice",  pushU256FromField "gasprice"  (oc .gasprice) Offset.gasprice),
  ("chainid",   pushU256FromField "chainid"   (oc .chainid) Offset.chainid),
  ("timestamp", pushU256FromField "timestamp" (oc .timestamp) Offset.timestamp),
  ("number",    pushU256FromField "number"    (oc .number) Offset.blockNumber),
  ("gaslimit",  pushU256FromField "gaslimit"  (oc .gaslimit) Offset.gaslimit),
  ("basefee",   pushU256FromField "basefee"   (oc .basefee) Offset.basefee),
  ("prevrandao", prevrandaoHandler (oc .prevrandao)),
  ("blobhash",    blobhashHandler (oc .blobhash)),
  ("blobbasefee", blobbasefeeHandler (oc .blobbasefee)),
  ("pc",        pcHandler (oc (.pc 0))),
  ("msize",     msizeHandler (oc .msize)),
  ("gas",       gasHandler (oc (.gas 0))),
  ("calldatasize",   pushU64FromField "calldatasize"   (oc .calldatasize) 88),  -- calldata_size offset
  ("codesize",       pushU64FromField "codesize"       (oc .codesize) Offset.codeSize),
  ("returndatasize", pushU64FromField "returndatasize" (oc .returndatasize) 104), -- returndata_size offset
  ("sstore", sstoreHandler Evm.Istanbul.Vm.Gas.sstoreSentryGas),
  -- Signed comparison
  ("slt", signedCmpHandler "slt" (oc .slt) "lt"),
  ("sgt", cmpHandlerSwapped "sgt" (oc .sgt) "lt"),
  -- Hard compute (C helpers)
  ("mul",        binComputeHandler "mul"        (oc .mul) "_eita_helper_mul"),
  ("div",        binComputeHandler "div"        (oc .div) "_eita_helper_div"),
  ("sdiv",       binComputeHandler "sdiv"       (oc .sdiv) "_eita_helper_sdiv"),
  ("mod",        binComputeHandler "mod"        (oc .mod) "_eita_helper_mod"),
  ("smod",       binComputeHandler "smod"       (oc .smod) "_eita_helper_smod"),
  ("exp",        expHandler (oc .exp) (expByteCost interpFork)),
  ("shl",        binComputeHandler "shl"        (oc .shl) "_eita_helper_shl"),
  ("shr",        binComputeHandler "shr"        (oc .shr) "_eita_helper_shr"),
  ("sar",        binComputeHandler "sar"        (oc .sar) "_eita_helper_sar"),
  ("byte",       binComputeHandler "byte"       (oc .byte) "_eita_helper_byte"),
  ("signextend", binComputeHandler "signextend" (oc .signextend) "_eita_helper_signextend"),
  ("addmod",     ternaryComputeHandler "addmod" (oc .addmod) "_eita_helper_addmod"),
  ("mulmod",     ternaryComputeHandler "mulmod" (oc .mulmod) "_eita_helper_mulmod"),
  -- Buffer ops (C helpers, state-aware)
  ("calldataload",   calldataloadHandler (oc .calldataload)),
  ("calldatacopy",   stateTernaryHandler "calldatacopy"   (oc .calldatacopy) "_eita_helper_calldatacopy"),
  ("codecopy",       stateTernaryHandler "codecopy"       (oc .codecopy) "_eita_helper_codecopy"),
  ("returndatacopy", returndatacopyHandler (oc .returndatacopy)),
  ("mcopy",          mcopyHandler        "mcopy"          (oc .mcopy) "_eita_helper_mcopy"),
  -- KECCAK256 (variable gas + state-aware)
  ("keccak256", keccak256Handler (oc .keccak256)),
  -- Callbacks (gas comes back from the host in x0; no static charge here)
  ("sload",       sloadHandler),
  ("tload",       tloadHandler),
  ("balance",     balanceHandler),
  ("selfbalance", selfbalanceHandler (oc .selfbalance)),
  ("extcodesize", extcodesizeHandler),
  ("extcodehash", extcodehashHandler),
  ("blockhash",   blockhashHandler (oc .blockhash)),
  ("extcodecopy", extcodecopyHandler),
  -- Sub-calls (host-callback recursive). All four use the parametric
  -- callFamilyHandler so they share gas accounting, returndata-to-memory
  -- copy, and EIP-3 invariants.
  ("staticcall",   callFamilyHandler "staticcall" 3 1 false),
  ("call",         callOp),
  ("callcode",     callcodeOp),
  ("delegatecall", delegatecallOp),
  ("create",       createHandler),
  ("create2",      create2Handler),
  ("selfdestruct", selfdestructHandler (termCost .selfdestruct)),
  -- Memory
  ("mload",   mloadHandler (oc .mload)),
  ("mstore",  mstoreHandler (oc .mstore)),
  ("mstore8", mstore8Handler (oc .mstore8)),
  -- Halt with output
  ("return", returnHandler),
  ("revert", revertHandler),
  -- Control (runtime-resolved destinations → the Dynamic terminators)
  ("jump",  jumpHandler (termCost .jumpDynamic)),
  ("jumpi", jumpiHandler (termCost .jumpiDynamic)),
  -- Transient storage
  ("tstore", tstoreHandler),
  -- PUSH-N: full range 0..32 via unified pushHandler (multi-limb shift via EXTR)
  ("push0", pushHandler 0 (oc .push0))
] ++ (List.range 32 |>.map (fun i => (s!"push{i+1}", pushHandler (i+1) (oc (.push (i+1) 0)))))
  ++ (List.range 5 |>.map (fun i => (s!"log{i}", logHandler i (oc (.log i)))))
  ++ (List.range 16 |>.map (fun i => (s!"dup{i+1}",  dupHandler  (i+1) (oc (.dup (i+1))))))
  ++ (List.range 16 |>.map (fun i => (s!"swap{i+1}", swapHandler (i+1) (oc (.swap (i+1))))))

/-- The interp-tier registry: every op charges its own static cost. -/
def allHandlers : List (String × String) := handlersWith opCost

/-- Ops whose gas flows entirely through the host callback: the emitted
    body takes no cost parameter, so it is fork-invariant even where the
    metadata cost varies (SLOAD 50/200/800/100, BALANCE 20/400/700/100,
    EXTCODE* 20/700/100, …) — the HOST must charge the fork's cost. -/
def cbDriven : Op → Bool
  | .sload | .sstore | .tload | .tstore | .balance
  | .extcodesize | .extcodehash | .extcodecopy => true
  | _ => false

/-- The static gas an emitted handler actually charges. This is `opCost`
    except for the cb-driven entries, where it is 0. The JIT's chunk-head
    pre-charge must sum THIS, not raw `opCost`, or the cb-driven ops
    would be double-charged. -/
def chargedCost (op : Op) : Nat :=
  if cbDriven op then 0 else opCost op

/-- Handlers that end a chunk: the JIT keeps branching to the interp-tier
    bodies for these (they exit via sync_and_ret and charge `termCost`
    themselves), so no flat variant is emitted. -/
def termHandlerNames : List String :=
  ["stop", "invalid", "return", "revert", "jump", "jumpi",
   "staticcall", "call", "callcode", "delegatecall",
   "create", "create2", "selfdestruct"]

/-- Flat (cost-0) handler variants for the JIT tier: same audited bodies
    with every static charge removed (the JIT pre-charges the whole
    chunk's static gas at the head). All labels the body defines are
    suffixed `_f` so both variants link into one image. -/
def flatOpHandlers : List (String × String) :=
  ((handlersWith (fun _ => 0)).filter (fun (n, _) => !termHandlerNames.contains n)
   |>.map (fun (n, b) => (n ++ "_f", suffixDefinedLabels b "_f"))) ++
  -- Flat twins of the fork-variant bodies, so `handlerSymbol f nm ++ "_f"`
  -- resolves for every fork the JIT compiles at (sentry/byte-cost are
  -- body concerns, not static charges, so they survive flattening).
  [("sstore_nosentry_f",
    suffixDefinedLabels (sstoreHandler 0) "_nosentry_f"),
   ("exp_pre160_f",
    suffixDefinedLabels (expHandler 0 (expByteCost .frontier)) "_pre160_f")]

/-! ## Per-fork dispatch (Stage A of fork-parametric emission)

    The registry bodies are pinned to `interpFork` (Cancun) constants,
    but almost nothing in them actually varies by fork:
      - presence varies (PUSH0 Shanghai+, REVERT Byzantium+, …) — a
        dispatch-TABLE concern: absent ops route to the invalid handler;
      - cb-driven costs vary (SLOAD/BALANCE/EXTCODE*…) — a HOST concern;
      - exactly two statically-charged constants vary in a body:
        EXP's per-byte 10→50 (EIP-160) and SELFDESTRUCT's 0→5000
        (EIP-150). Those get variant bodies.
    So per-fork dispatch = one table per fork over the same bodies, two
    variant bodies, and a mutable `_eita_dispatch_ptr` that
    `_eita_set_fork` repoints. Any OTHER cost drift the metadata tables
    introduce later panics at emit time — no silent gaps.

    Known Stage-A limitation: CALL-family terminators still branch to
    the Berlin-pinned `_eita_call_gas` plans, so pre-Berlin tables carry
    wrong call gas until Stage B emits per-fork call-gas plans. -/

/-- What the registry name keys into the metadata tables. -/
inductive RegKey where
  | op   (o : Op)
  | term (t : Terminator)

/-- Registry name → metadata key, parallel to `handlersWith`. -/
def regKeys : List (String × RegKey) := [
  ("add", .op .add), ("sub", .op .sub), ("and", .op .and_),
  ("or", .op .or_), ("xor", .op .xor_), ("lt", .op .lt),
  ("gt", .op .gt), ("eq", .op .eq), ("iszero", .op .iszero), ("clz", .op .clz),
  ("not", .op .not_), ("pop", .op .pop), ("stop", .term .stop),
  ("jumpdest", .op .jumpdest), ("invalid", .term .invalid),
  ("address", .op .address), ("origin", .op .origin),
  ("caller", .op .caller), ("coinbase", .op .coinbase),
  ("callvalue", .op .callvalue), ("gasprice", .op .gasprice),
  ("chainid", .op .chainid), ("timestamp", .op .timestamp),
  ("number", .op .number), ("gaslimit", .op .gaslimit),
  ("basefee", .op .basefee), ("prevrandao", .op .prevrandao),
  ("blobhash", .op .blobhash), ("blobbasefee", .op .blobbasefee),
  ("pc", .op (.pc 0)), ("msize", .op .msize), ("gas", .op (.gas 0)),
  ("calldatasize", .op .calldatasize), ("codesize", .op .codesize),
  ("returndatasize", .op .returndatasize), ("sstore", .op .sstore),
  ("slt", .op .slt), ("sgt", .op .sgt), ("mul", .op .mul),
  ("div", .op .div), ("sdiv", .op .sdiv), ("mod", .op .mod),
  ("smod", .op .smod), ("exp", .op .exp), ("shl", .op .shl),
  ("shr", .op .shr), ("sar", .op .sar), ("byte", .op .byte),
  ("signextend", .op .signextend), ("addmod", .op .addmod),
  ("mulmod", .op .mulmod), ("calldataload", .op .calldataload),
  ("calldatacopy", .op .calldatacopy), ("codecopy", .op .codecopy),
  ("returndatacopy", .op .returndatacopy), ("mcopy", .op .mcopy),
  ("keccak256", .op .keccak256), ("sload", .op .sload),
  ("tload", .op .tload), ("balance", .op .balance),
  ("selfbalance", .op .selfbalance), ("extcodesize", .op .extcodesize),
  ("extcodehash", .op .extcodehash), ("blockhash", .op .blockhash),
  ("extcodecopy", .op .extcodecopy),
  ("staticcall", .term (.call .staticcall)),
  ("call", .term (.call .call)),
  ("callcode", .term (.call .callcode)),
  ("delegatecall", .term (.call .delegatecall)),
  ("create", .term (.create .create)),
  ("create2", .term (.create .create2)),
  ("selfdestruct", .term .selfdestruct),
  ("mload", .op .mload), ("mstore", .op .mstore),
  ("mstore8", .op .mstore8), ("return", .term .ret),
  ("revert", .term .revert), ("jump", .term .jumpDynamic),
  ("jumpi", .term .jumpiDynamic), ("tstore", .op .tstore),
  ("push0", .op .push0)
] ++ (List.range 32 |>.map (fun i => (s!"push{i+1}", RegKey.op (.push (i+1) 0))))
  ++ (List.range 5  |>.map (fun i => (s!"log{i}",    RegKey.op (.log i))))
  ++ (List.range 16 |>.map (fun i => (s!"dup{i+1}",  RegKey.op (.dup (i+1)))))
  ++ (List.range 16 |>.map (fun i => (s!"swap{i+1}", RegKey.op (.swap (i+1)))))

/-- Resolve a registry name to the handler symbol fork `f`'s dispatch
    table should hold. Absent ops route to the invalid handler;
    cb-driven ops always use the base body (the host owns their cost);
    the two known repricings select variant bodies; any other static-
    cost drift vs `interpFork` panics at emit time. -/
def handlerSymbol (f : Evm.Fork) (nm : String) : String :=
  match regKeys.find? (fun (n, _) => n == nm) with
  | none => panic! s!"ARM64.Interp: registry name {nm} missing from regKeys"
  | some (_, .op o) =>
    match Op.metadata f o with
    | none   => "_eita_handler_invalid"
    | some m =>
      -- SSTORE is cb-driven for gas, but the EIP-1706/EIP-2200 sentry
      -- (gasLeft ≤ 2300 → OOG) is a handler-body concern: it ships at
      -- Istanbul and must be ABSENT before (EIP-1283 had no sentry).
      if o == .sstore then
        if f.atLeast .istanbul then s!"_eita_handler_{nm}"
        else "_eita_handler_sstore_nosentry"
      else if cbDriven o then s!"_eita_handler_{nm}"
      else if o == .exp then
        if m.staticCost != opCost .exp then
          panic! s!"ARM64.Interp: EXP static-cost drift on {repr f} has no variant body"
        else if expByteCost f != expByteCost interpFork then
          "_eita_handler_exp_pre160"
        else "_eita_handler_exp"
      else if m.staticCost == opCost o then s!"_eita_handler_{nm}"
      else panic! s!"ARM64.Interp: {nm} costs {m.staticCost} on {repr f} but {opCost o} on {repr interpFork}; emit a variant body"
  | some (_, .term t) =>
    match Terminator.metadata f t with
    | none   => "_eita_handler_invalid"
    | some m =>
      if t == .selfdestruct then
        if m.staticCost == termCost .selfdestruct then
          "_eita_handler_selfdestruct"
        else if m.staticCost == termCostOn .frontier .selfdestruct then
          "_eita_handler_selfdestruct_pre150"
        else
          panic! s!"ARM64.Interp: SELFDESTRUCT costs {m.staticCost} on {repr f}; no variant body"
      else if m.staticCost == termCost t then s!"_eita_handler_{nm}"
      else panic! s!"ARM64.Interp: {nm} costs {m.staticCost} on {repr f} but {termCost t} on {repr interpFork}; emit a variant body"

/-- The two fork-variant bodies (labels suffixed so they link alongside
    the base bodies): EXP with the pre-EIP-160 byte coefficient and
    SELFDESTRUCT with the pre-EIP-150 (zero) static charge. Costs come
    from the same metadata/Gas tables as everything else. -/
def variantHandlers : List (String × String) := [
  ("exp_pre160",
   suffixDefinedLabels (expHandler (opCost .exp) (expByteCost .frontier)) "_pre160"),
  ("selfdestruct_pre150",
   suffixDefinedLabels (selfdestructHandler (termCostOn .frontier .selfdestruct)) "_pre150"),
  -- SSTORE without the EIP-1706/EIP-2200 gasLeft ≤ 2300 trip-wire:
  -- pre-Istanbul forks (Constantinople's EIP-1283 shipped without
  -- EIP-1706). Gas itself still comes from the host cb.
  ("sstore_nosentry",
   suffixDefinedLabels (sstoreHandler 0) "_nosentry")
]

/-! ## The registry as programs (stage 4v)

`handlersWith` above is the registry as STRINGS: each entry is a shape
emitter that prints `hdr name ++ body.emitDerived` for one `AsmCore` body.
This is the same registry as `Prog`s — name → body — which is what a second
target lowers (`X86Interp` takes each body through `Op.instrsX86?`). The
ARM64 strings are derived from it below (`allHandlersP`, …) and
`registry_from_progs` is the identity with the string registry, so the
handlers file cannot change. -/

open Evm.CL.AsmCore in
/-- Name → body, in the file's order. The costs are the registry's (`oc`). -/
def handlerProgs (oc : IR.Op → Nat) : List (String × AsmCore.Prog) := [
  ("add", arithBody .add (oc .add)),
  ("sub", arithBody .sub (oc .sub)),
  ("and", bitwiseBody .and (oc .and_)),
  ("or",  bitwiseBody .orr (oc .or_)),
  ("xor", bitwiseBody .eor (oc .xor_)),
  ("lt", cmpBody false .lo (oc .lt)),
  ("gt", cmpBody true .lo (oc .gt)),
  ("eq", eqBody (oc .eq)),
  ("iszero", iszeroBody (oc .iszero)),
  ("clz", clzBody (oc .clz)),
  ("not", notBody (oc .not_)),
  ("pop", popBody (oc .pop)),
  ("stop", stopBody),
  ("jumpdest", jumpdestBody (oc .jumpdest)),
  ("invalid", invalidBody),
  ("address",   envU256Body Offset.address   (oc .address)),
  ("origin",    envU256Body Offset.origin    (oc .origin)),
  ("caller",    envU256Body Offset.caller    (oc .caller)),
  ("coinbase",  envU256Body Offset.coinbase  (oc .coinbase)),
  ("callvalue", envU256Body Offset.callvalue (oc .callvalue)),
  ("gasprice",  envU256Body Offset.gasprice  (oc .gasprice)),
  ("chainid",   envU256Body Offset.chainid   (oc .chainid)),
  ("timestamp", envU256Body Offset.timestamp (oc .timestamp)),
  ("number",    envU256Body Offset.blockNumber (oc .number)),
  ("gaslimit",  envU256Body Offset.gaslimit  (oc .gaslimit)),
  ("basefee",   envU256Body Offset.basefee   (oc .basefee)),
  ("prevrandao", envU256Body 512 (oc .prevrandao)),
  ("blobhash",    blobhashBody (oc .blobhash)),
  ("blobbasefee", envU256Body Offset.blobBaseFee (oc .blobbasefee)),
  ("pc",        pcBody (oc (.pc 0))),
  ("msize",     msizeBody (oc .msize)),
  ("gas",       gasBody (oc (.gas 0))),
  ("calldatasize",   envU64Body 88 (oc .calldatasize)),
  ("codesize",       envU64Body Offset.codeSize (oc .codesize)),
  ("returndatasize", envU64Body 104 (oc .returndatasize)),
  ("sstore", sstoreBody Evm.Istanbul.Vm.Gas.sstoreSentryGas),
  ("slt", cmpBody false .lt (oc .slt)),
  ("sgt", cmpBody true .lt (oc .sgt)),
  ("mul",        binComputeBody "_eita_helper_mul"        (oc .mul)),
  ("div",        binComputeBody "_eita_helper_div"        (oc .div)),
  ("sdiv",       binComputeBody "_eita_helper_sdiv"       (oc .sdiv)),
  ("mod",        binComputeBody "_eita_helper_mod"        (oc .mod)),
  ("smod",       binComputeBody "_eita_helper_smod"       (oc .smod)),
  ("exp",        expBody (oc .exp) (expByteCost interpFork)),
  ("shl",        binComputeBody "_eita_helper_shl"        (oc .shl)),
  ("shr",        binComputeBody "_eita_helper_shr"        (oc .shr)),
  ("sar",        binComputeBody "_eita_helper_sar"        (oc .sar)),
  ("byte",       binComputeBody "_eita_helper_byte"       (oc .byte)),
  ("signextend", binComputeBody "_eita_helper_signextend" (oc .signextend)),
  ("addmod",     ternaryComputeBody "_eita_helper_addmod" (oc .addmod)),
  ("mulmod",     ternaryComputeBody "_eita_helper_mulmod" (oc .mulmod)),
  ("calldataload",   calldataloadBody (oc .calldataload)),
  ("calldatacopy",   copyBody "_eita_helper_calldatacopy"   (oc .calldatacopy)),
  ("codecopy",       copyBody "_eita_helper_codecopy"       (oc .codecopy)),
  ("returndatacopy", returndatacopyBody (oc .returndatacopy)),
  ("mcopy",          mcopyBody "_eita_helper_mcopy"         (oc .mcopy)),
  ("keccak256", keccak256Body (oc .keccak256)),
  ("sload",       sloadBody),
  ("tload",       tloadBody),
  ("balance",     balanceBody),
  ("selfbalance", selfbalanceBody (oc .selfbalance)),
  ("extcodesize", extcodesizeBody),
  ("extcodehash", extcodehashBody),
  ("blockhash",   blockhashBody (oc .blockhash)),
  ("extcodecopy", extcodecopyBody),
  ("staticcall",   callFamilyBody "staticcall"   3 1 false),
  ("call",         callFamilyBody "call"         0 0 true),
  ("callcode",     callFamilyBody "callcode"     1 0 true),
  ("delegatecall", callFamilyBody "delegatecall" 2 0 false),
  ("create",       createBody),
  ("create2",      create2Body),
  ("selfdestruct", selfdestructBody (termCost .selfdestruct)),
  ("mload",   mloadBody (oc .mload)),
  ("mstore",  mstoreBody (oc .mstore)),
  ("mstore8", mstore8Body (oc .mstore8)),
  ("return", returnBody),
  ("revert", revertBody),
  ("jump",  jumpBody (termCost .jumpDynamic)),
  ("jumpi", jumpiBody (termCost .jumpiDynamic)),
  ("tstore", tstoreBody),
  ("push0", pushBody 0 (oc .push0))
] ++ (List.range 32 |>.map (fun i => (s!"push{i+1}", pushBody (i+1) (oc (.push (i+1) 0)))))
  ++ (List.range 5 |>.map (fun i => (s!"log{i}", logBody i (oc (.log i)))))
  ++ (List.range 16 |>.map (fun i => (s!"dup{i+1}",  dupBody  (i+1) (oc (.dup (i+1))))))
  ++ (List.range 16 |>.map (fun i => (s!"swap{i+1}", swapBody (i+1) (oc (.swap (i+1))))))

open Evm.CL.AsmCore in
/-- The fork-variant bodies, with the label suffix each links under. -/
def variantProgs : List (String × String × AsmCore.Prog) := [
  ("exp_pre160", "_pre160", expBody (opCost .exp) (expByteCost .frontier)),
  ("selfdestruct_pre150", "_pre150", selfdestructBody (termCostOn .frontier .selfdestruct)),
  ("sstore_nosentry", "_nosentry", sstoreBody 0)
]

open Evm.CL.AsmCore in
/-- The flat (cost-0) twins for the JIT tier, name, suffix and body. -/
def flatProgs : List (String × String × AsmCore.Prog) :=
  ((handlerProgs (fun _ => 0)).filter (fun (n, _) => !termHandlerNames.contains n)
   |>.map (fun (n, p) => (n ++ "_f", "_f", p))) ++
  [("sstore_nosentry_f", "_nosentry_f", sstoreBody 0),
   ("exp_pre160_f", "_pre160_f", expBody 0 (expByteCost .frontier))]

/-- A body's ARM64 text under a header, with its named labels suffixed. -/
def progText (name suf : String) (p : AsmCore.Prog) : String :=
  hdr name ++ Frame.text ((Evm.CL.OpInstrs.bodyInstrs p).map (Evm.CL.OpInstrs.suffixLabels suf))

def allHandlersP : List (String × String) :=
  (handlerProgs opCost).map (fun (n, p) => (n, progText n "" p))
def flatOpHandlersP : List (String × String) :=
  flatProgs.map (fun (n, suf, p) => (n, progText n suf p))
def variantHandlersP : List (String × String) :=
  variantProgs.map (fun (n, suf, p) => (n, progText n suf p))

/-- **The string registry is the program registry printed.** -/
theorem registry_from_progs :
    allHandlers = allHandlersP ∧ flatOpHandlers = flatOpHandlersP ∧
    variantHandlers = variantHandlersP := by
  native_decide

/-- **Every body checks the stack its op needs** (pops from the Osaka IR metadata; an
    overflow check when it grows the stack). ADDMOD/MULMOD/BLOBHASH once had none. -/
theorem handler_stack_guards :
    (handlerProgs (fun _ => 0)).all (fun (nm, p) =>
      let guard := (p.findSome? fun | .underflow n => some n | _ => none).getD 0
      match (regKeys.find? (·.1 == nm)).map (·.2) with
      | some (RegKey.op o) => (Op.metadata .osaka o).all fun m => let e := m.stackEffect
          e.popCount ≤ guard && (e.pushCount ≤ e.popCount || p.contains .ovfGuard)
      | some (RegKey.term t) => (Terminator.metadata .osaka t).all (·.popCount ≤ guard)
      | none => false) = true := by
  native_decide

open Evm.CL.AsmCore in
/-- Every start of the memory-expansion gadget in IS is fed by a guarded end: an
    overflow-checked add (`b.cs` → OOG) and a high-limb guard (`cbnz` → OOG) precede
    it, and no unchecked `add x0` follows the last overflow check. -/
def memexpGuarded (is : List AInstr) : Bool :=
  (List.range is.length).all fun i =>
    !(memExpandInstrs.isPrefixOf (is.drop i)) ||
      (let pre := is.take i
       let afterCheck := (pre.reverse.takeWhile (· != .bcsOog))
       pre.contains .bcsOog && pre.any (fun x => match x with | .cbnzOog _ => true | _ => false) &&
         !afterCheck.any (fun x => match x with | .addReg .x0 _ _ => true | _ => false))

/-- **Every handler bounds its memory operands over the full 256 bits** before memory
    expansion: an offset or length with a nonzero high limb, or an end past 2^64, is OOG
    (EELS: the expansion gas alone exceeds any gas limit). LOG0-4 (low limbs only, the
    end added unchecked, on BOTH backends — x86 has its own LOG list) and EXTCODECOPY
    (no high-limb guard) once violated it; checked on the ARM64 and x86 bodies. The
    CALL family (#260) and CODECOPY (u256 src) were earlier instances of the class. -/
theorem handler_memory_operands_guarded :
    (handlerProgs (fun _ => 0)).all (fun (_, p) =>
      memexpGuarded (Evm.CL.OpInstrs.bodyInstrs p) &&
      memexpGuarded (p.flatMap (fun o => (Evm.CL.OpInstrs.Op.instrsX86? o).getD []))) = true := by
  native_decide

open Evm.CL.AsmCore in
/-- **Every RETURNDATACOPY bounds its source first** (EIP-211): any body (base or fork
    variant) that calls the return-buffer copy helper runs `returndataBounds` before
    it, so a read past the buffer halts instead of zero-padding as CALLDATACOPY does.
    It once copied with zero padding (ethereum/tests stReturnDataTest, Byzantium+). -/
theorem handler_returndata_bounded :
    ((handlerProgs (fun _ => 0)).map (·.2) ++ variantProgs.map (·.2.2)).all (fun (p : AsmCore.Prog) =>
      match p.findIdx? (· == Op.copyCbPop3 "_eita_helper_returndatacopy") with
      | none => true
      | some i => (p.take i).contains Op.returndataBounds) = true := by
  native_decide

open Evm.CL.AsmCore in
/-- **EIP-214 over every handler body** (base and fork variants, derived from the
    programs): every op that writes state (SSTORE, TSTORE, LOG, CREATE, CREATE2,
    SELFDESTRUCT) is preceded by the static guard, and every value-carrying CALL by the
    value-conditional one. -/
theorem handler_static_writes_guarded :
    ((handlerProgs (fun _ => 0)).map (·.2) ++ variantProgs.map (·.2.2)).all (fun (p : AsmCore.Prog) =>
      (List.range p.length).all fun i =>
        let pre := p.take i
        match p[i]? with
        | some .sstoreCb | some .tstoreCb | some (.logEmit _ _) | some .createCore
        | some .create2Core | some .selfdestructCb => pre.contains Op.staticGuard
        | some (.callFamilyCore _ 0 _ true) => pre.contains Op.staticValueGuard
        | _ => true) = true := by
  native_decide

open Evm.CL.AsmCore Evm.CL.OpInstrs in
/-- **Every callback argument is written by the call's own op** (or the argument-
    marshalling ops right before it), from the frame's live-in roles, on every path,
    and not clobbered by an intervening call — on both backends, for every base and
    fork-variant body, with the callee's arity from the vtable (`cbArity`) or the C
    helper table (`helperArity`); an unknown callee fails. EXTCODECOPY's ARM64 cb op
    passed `len` in x4 without writing it: the gas gadget before it used to leave
    len.l0 there, f812945 rebuilt that gadget on `memRangeInstrs`, and the host read a
    stale x4 (mainnet 4,972,698 tx 17: an 8·10^18-byte memset past the memory arena;
    x86-64 loads len itself and was unaffected). `Op.denote` is coarse at callbacks,
    which is how it slipped past `extcodecopyBody`'s proofs — the #260 family. -/
theorem handler_callback_args_defined :
    ((handlerProgs (fun _ => 0)).map (·.2) ++ variantProgs.map (·.2.2)).all callArgsDefined = true := by
  native_decide

open Evm.CL.AsmCore Evm.CL.OpInstrs in
/-- …and it rejects the bug: without the one `ldr x4, [x14]` the fix added, the
    EXTCODECOPY body passes len from whatever x4 held. -/
theorem callback_args_rejects_inherited_len :
    (callArgsBad false
      ((taggedBody Op.instrs? extcodecopyBody).filter (·.2 != .ldrBase .x4 .x14))).isEmpty = false := by
  native_decide

open Evm.CL.AsmCore Evm.CL.OpInstrs in
/-- **Every body keeps the register-cached stack coherent** (ARM64): entered with
    x6-x9 = stack[sp-1] and x10-x13 = stack[sp-2], every `br x27` leaves them so for the
    sp it leaves (`cacheCoherent`, a value numbering over the instructions). CLZ
    computed in x10-x13 and broke it: `clz(x) & ~1` read a clobbered NOS (mainnet
    26,042,126 tx 135). `Op.denote` keeps `nos` apart from the registers, so
    `clz_correct` could not see it. -/
theorem handler_stack_cache_coherent :
    ((handlerProgs (fun _ => 0)).map (·.2) ++ variantProgs.map (·.2.2)).all cacheCoherent = true := by
  native_decide

open Evm.CL.AsmCore Evm.CL.OpInstrs in
/-- …and it rejects the bug: the CLZ body on the former x10-x13 temporaries. -/
theorem cache_coherence_rejects_clz_on_nos :
    (cacheIncoherent ((clzBody 5).flatMap fun o =>
      if o == .clzReduce then
        [ .clzReg .x10 .x9, .clzReg .x11 .x8, .clzReg .x12 .x7, .clzReg .x13 .x6,
          .addImm .x11 .x11 64, .addImm .x12 .x12 128, .addImm .x13 .x13 192,
          .cmpImm .x7 0, .cselNe .x12 .x12 .x13, .cmpImm .x8 0, .cselNe .x11 .x11 .x12,
          .cmpImm .x9 0, .cselNe .x6 .x10 .x11, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ]
      else (Op.instrs? o).getD [])).isEmpty = false := by
  native_decide

/-- The forks that get their own dispatch table, in `Fork.ord` order
    (ords 0..15). Cancun and later reuse the default
    `_eita_dispatch_table` — the registry is pinned there. -/
def tableForks : List (Evm.Fork × String) :=
  [(.frontier, "frontier"), (.homestead, "homestead"),
   (.daoFork, "dao_fork"), (.tangerineWhistle, "tangerine_whistle"),
   (.spuriousDragon, "spurious_dragon"), (.byzantium, "byzantium"),
   (.constantinople, "constantinople"), (.petersburg, "petersburg"),
   (.istanbul, "istanbul"), (.muirGlacier, "muir_glacier"),
   (.berlin, "berlin"), (.london, "london"),
   (.arrowGlacier, "arrow_glacier"), (.grayGlacier, "gray_glacier"),
   (.paris, "paris"), (.shanghai, "shanghai")]

/-- `_eita_set_fork(uint64 ord)`: repoint `_eita_dispatch_ptr` at the
    `Fork.ord`-indexed table. Ordinals past amsterdam (21) clamp; ords
    16..17 (cancun, prague) hold the default Cancun table, 18..21
    (osaka, bpo1, bpo2, amsterdam) the Osaka table (+CLZ, EIP-7939): a
    BPO fork (EIP-7892) changes the blob schedule, not the opcode table. -/
def setForkCodeSpec : String :=
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  ".global _eita_set_fork\n" ++
  ".p2align 2\n" ++
  "_eita_set_fork:\n" ++
  "    mov   x1, #21\n" ++
  "    cmp   x0, x1\n" ++
  "    csel  x0, x0, x1, ls\n" ++
  "    adrp  x1, _eita_fork_tables@PAGE\n" ++
  "    add   x1, x1, _eita_fork_tables@PAGEOFF\n" ++
  "    ldr   x1, [x1, x0, lsl #3]\n" ++
  "    adrp  x2, _eita_dispatch_ptr@PAGE\n" ++
  "    add   x2, x2, _eita_dispatch_ptr@PAGEOFF\n" ++
  "    str   x1, [x2]\n" ++
  "    ret\n"

-- `_eita_set_fork` as instructions (stage 4t).
open Evm.CL.AsmCore in
def setForkInstrs : List AInstr :=
  ([.textSection] : List AInstr) ++ Frame.header "_eita_set_fork" ++
  [ .movImm .x1 21, .cmpReg .x0 .x1, .csel .x0 .x0 .x1 .ls,
    .loadSymAddr .x1 "_eita_fork_tables", .ldrLsl3 .x1 .x1 .x0,
    .loadSymAddr .x2 "_eita_dispatch_ptr", .strBase .x1 .x2, .ret ]

def setForkCode : String := Frame.text setForkInstrs

theorem setFork_derived : setForkCode = setForkCodeSpec := by native_decide

-- The `Fork.ord`-indexed table of tables, as directives.
open Evm.CL.AsmCore in
def forkTablesInstrs : List AInstr :=
  ([ .dataSection, .global "_eita_fork_tables", .p2align3, .symLabel "_eita_fork_tables" ] : List AInstr) ++
  tableForks.map (fun (_, nm) => AInstr.quadSym s!"_eita_dispatch_table_{nm}") ++
  [ .quadSym "_eita_dispatch_table",        -- 16 cancun
    .quadSym "_eita_dispatch_table",        -- 17 prague
    .quadSym "_eita_dispatch_table_osaka",  -- 18 osaka
    .quadSym "_eita_dispatch_table_osaka",  -- 19 bpo1 (EIP-7892: blob schedule only)
    .quadSym "_eita_dispatch_table_osaka",  -- 20 bpo2
    .quadSym "_eita_dispatch_table_osaka" ] -- 21 amsterdam

/-- All per-fork dispatch machinery: one named table per pre-Cancun
    fork, the `Fork.ord`-indexed table-of-tables, and `_eita_set_fork`. -/
def forkDispatch : String :=
  String.join (tableForks.map fun (f, nm) =>
    dispatchTableNamed s!"_eita_dispatch_table_{nm}" (handlerSymbol f)) ++
  -- Osaka (+CLZ): the default table is the Cancun registry; ops absent before
  -- Osaka stay routed to `invalid` there and resolve only in this table.
  dispatchTableNamed "_eita_dispatch_table_osaka" (handlerSymbol .osaka) ++
  Frame.text forkTablesInstrs ++
  setForkCode

theorem forkTables_derived :
    Frame.text forkTablesInstrs =
      ".data\n.global _eita_fork_tables\n.p2align 3\n_eita_fork_tables:\n" ++
      String.join (tableForks.map fun (_, nm) => s!"    .quad   _eita_dispatch_table_{nm}\n") ++
      "    .quad   _eita_dispatch_table\n    .quad   _eita_dispatch_table\n" ++
      "    .quad   _eita_dispatch_table_osaka\n    .quad   _eita_dispatch_table_osaka\n" ++
      "    .quad   _eita_dispatch_table_osaka\n    .quad   _eita_dispatch_table_osaka\n" := by
  native_decide

/-- The full handlers.S text: runtime scaffolding (trampoline, next,
    sync_and_ret, fault stubs) + every handler (interp-tier charging
    variants + JIT flat variants + fork-variant bodies) + the default
    dispatch table + per-fork dispatch + call-gas + sstore-gas/access
    table + the program loop. -/
def emit : String :=
  -- the default table is the Cancun registry: ops that only exist later (CLZ, Osaka) are absent there
  -- (printed from the PROGRAM registry; `registry_from_progs` is the identity with the strings)
  emitWith (allHandlersP ++ flatOpHandlersP ++ variantHandlersP)
           (fun nm => handlerSymbol interpFork nm != "_eita_handler_invalid") ++ "\n"
    ++ forkDispatch ++ "\n" ++ CallGas.code ++ "\n" ++ SstoreGas.code
    ++ "\n" ++ RunProgram.code

end Evm.CL.ARM64.Interp
