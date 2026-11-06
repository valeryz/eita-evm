/-
  Evm.CL.OpInstrs — `Op` lowered to `AInstr`, gated by text identity.

  `AsmCore.Op` is the handler-level vocabulary: every constructor has a
  denotation (`Op.denote`), and every constructor lowers to ARM64 text directly
  (`Op.emit`). That text is the only form the ops have, so an x86-64 handler
  cannot be derived from them — the gadgets inside them are `AInstr`, the ops
  around the gadgets are strings.

  `Op.instrs?` gives the ops an `AInstr` form. It is partial by design — ops
  are added as handlers need them — and it is GATED: `instrs_reproduce_emit`
  checks, for every op in the MLOAD and MSTORE bodies, that printing the
  `AInstr` form through `emitARM64` gives `Op.emit`'s text character for
  character. So the ARM64 output of a handler assembled from `Op.instrs?` is
  the handler assembled from `Op.emit`, and `handlers.S` cannot move when the
  emitters switch over.

  The first two handlers: MLOAD (9 ops) and MSTORE (9 ops), 18 ops, 14
  distinct constructors.
-/

import Evm.CL.AsmCore
import Evm.CL.Lowering

namespace Evm.CL.OpInstrs

open Evm.CL.AsmCore

/-- The ARM64 argument register `x{i}` for i < 4. -/
def argReg : Nat → Option Reg
  | 0 => some .x0 | 1 => some .x1 | 2 => some .x2 | 3 => some .x3 | _ => none

/-- The ARM register name whose x86 HOME is SysV argument register i
    (rdi, rsi, rdx, rcx) — x3, x2, x1, x14 under the forced colouring. -/
def sysvReg : Nat → Option Reg
  | 0 => some .x3 | 1 => some .x2 | 2 => some .x1 | 3 => some .x14
  -- argument 4 is r8 — TOS limb 0's home. Usable only when TOS has been synced
  -- to the stack and is reloaded after the call, which every caller of a
  -- five-argument callback does (`tstoreCb`).
  | 4 => some .x6
  -- argument 5 is r9 — TOS limb 1's home; same condition (LOG's `len`)
  | 5 => some .x7 | _ => none

/-- `createMemExpandEmit offP lenP name`, as instructions. -/
def createMemExpandInstrs (offP lenP : Nat) (name : String) : List AInstr :=
  memRangeInstrs lenP offP .x0 s!".Lcrin0_{name}" s!".Lcrin1_{name}" ++
  [.movImm .x17 0, .cbzLbl .x0 "4f"] ++ memExpandInstrs ++
  [.subsReg .x22 .x22 .x17, .bloOog, .label "4", .strOff .x22 .x20 8]

/-- `callMemExpandEmit inOffP inLenP outOffP outLenP name`, as instructions. -/
def callMemExpandInstrs (inOffP inLenP outOffP outLenP : Nat) (name : String) : List AInstr :=
  memRangeInstrs inLenP inOffP .x0 s!".Lcfin0_{name}" s!".Lcfin1_{name}" ++
  memRangeInstrs outLenP outOffP .x14 s!".Lcfout0_{name}" s!".Lcfout1_{name}" ++
  [.cmpReg .x0 .x14, .cselHi .x0 .x0 .x14, .movImm .x17 0, .cbzLbl .x0 "4f"] ++ memExpandInstrs ++
  [.subsReg .x22 .x22 .x17, .bloOog, .label "4"]

/-- The ARM64 cache sync of both words, and the TOS reload, as used by every
    frame body. -/
def syncTosNos : List AInstr :=
  [ .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
    .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .stpOff .x10 .x11 .x14 0, .stpOff .x12 .x13 .x14 16 ]
def reloadTos : List AInstr :=
  [ .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
def reloadNosIf2 (target lbl : String) : List AInstr :=
  [ .cmpImm .x23 2, .bcLbl .lt target, .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
    .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label lbl ]

def Op.instrs? : Op → Option (List AInstr)
  | .ovfGuard         => some [.cmpImm .x23 1024, .bSym .hs "_eita_stack_overflow"]
  | .underflow n      => some [.cmpImm .x23 n, .bSym .lo "_eita_stack_underflow"]
  | .boundCheckHiTos  => some [.orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzOog .x14]
  | .newEndTos add    => some [.addsImm .x0 .x6 add, .bcsOog]
  | .setAcc base      => some [.movImm .x17 base]
  | .memExpand        => some memExpandInstrs
  | .chargeAcc        => some [.subsReg .x22 .x22 .x17, .bloOog]
  | .mstoreTail       => some
      [ .addImm .x15 .x6 32, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16,
        .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24,
        .ldrOff .x14 .x20 40, .addReg .x14 .x14 .x6,
        .rev .x0 .x13, .rev .x1 .x12, .rev .x2 .x11, .rev .x3 .x10,
        .strOff .x0 .x14 0, .strOff .x1 .x14 8, .strOff .x2 .x14 16, .strOff .x3 .x14 24,
        .subImm .x23 .x23 2, .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .mloadTail        => some
      [ .ldrOff .x14 .x20 40, .addImm .x15 .x6 32, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16,
        .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24,
        .addReg .x14 .x14 .x6,
        .ldrOff .x6 .x14 0, .ldrOff .x7 .x14 8, .ldrOff .x8 .x14 16, .ldrOff .x9 .x14 24,
        .rev .x6 .x6, .rev .x7 .x7, .rev .x8 .x8, .rev .x9 .x9,
        .movReg .x14 .x6, .movReg .x6 .x9, .movReg .x9 .x14,
        .movReg .x14 .x7, .movReg .x7 .x8, .movReg .x8 .x14 ]
  | .reloadNos        => some
      [ .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16 ]
  | .storeTos         => some
      [ .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
        .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16 ]
  | .brCont           => some [.brCont]
  -- the C-ABI call family (stage 4m). ARM64 AAPCS: a 32-byte scratch below a
  -- saved fp/lr, result pointer in x0, stack-word pointers in x1-x3.
  | .binHelper h      => some
      [ .spSub 32, .stpFpLr, .addSp .x0 16,
        .subImm .x14 .x23 1, .addLsl5 .x1 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x2 .x24 .x14,
        .blSym h,
        .addSp .x14 16, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .ldpFpLr, .spAdd 32 ]
  | .ternaryHelper h  => some
      [ .spSub 32, .stpFpLr, .addSp .x0 16,
        .subImm .x14 .x23 1, .addLsl5 .x1 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x2 .x24 .x14,
        .subImm .x14 .x23 3, .addLsl5 .x3 .x24 .x14,
        .blSym h,
        .addSp .x14 16, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .ldpFpLr, .spAdd 32 ]
  | .cbEnter s        => some [.spSub s, .stpFpLr]
  | .cbExit s         => some [.ldpFpLr, .spAdd s]
  | .loadScratchTos   => some [.addSp .x14 16, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16]
  | .loadScratchU64Tos => some [.ldrSp .x6 16, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .chargeGasX0      => some [.subsReg .x22 .x22 .x0, .bloOog]
  -- environment loads (stage 4n)
  | .loadFieldTos f   => some [.ldrOff .x6 .x20 f.offset, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .loadU64Off off   => some [.ldrOff .x6 .x20 off, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .loadU256Off off  => some
      (if off + 16 ≤ 504 then [.ldpOff .x6 .x7 .x20 off, .ldpOff .x8 .x9 .x20 (off + 16)]
       else [.addImm .x14 .x20 off, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16])
  | .pcMinus1Tos      => some [.subImm .x6 .x21 1, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .chargeGasPushTos c => some
      [.subsImm .x22 .x22 c, .bloOog, .movReg .x6 .x22, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .chargeFixed n    => some [.movImm .x14 n, .subsReg .x22 .x22 .x14, .bloOog]
  | .chargeGasX0Via14 => some [.movReg .x14 .x0, .subsReg .x22 .x22 .x14, .bloOog]
  -- host callbacks: ARM64 passes args in x0-x3 (`argReg`)
  | .argStateBase r   => (argReg r).map (fun a => [.movReg a .x20])
  | .argStateField r off => (argReg r).map (fun a => [.addImm a .x20 off])
  | .argStackPtr r n  => (argReg r).map (fun a => [.subImm .x14 .x23 n, .addLsl5 a .x24 .x14])
  | .argScratch r     => (argReg r).map (fun a => [.addSp a 16])
  | .loadCtx r        => (argReg r).map (fun a => [.ldrOff a .x20 504])
  | .loadCtxVia14 r   => (argReg r).map (fun a => [.ldrOff .x14 .x20 504, .movReg a .x14])
  | .loadTxStateCtx r => (argReg r).map (fun a => [.ldrOff .x14 .x20 504, .ldrOff a .x14 64])
  | .cbDirect name    => some [.blSym name]
  | .cbSlot slot      => some [.ldrOff .x14 .x20 496, .ldrOff .x14 .x14 slot, .blr .x14]
  -- the gas gadgets, already AInstr (stage 4o)
  | .copyGasCharge c  => some (copyGasInstrs c)
  | .returndataBounds => some returndataBoundsInstrs
  | .staticValueGuard => some staticValueGuardInstrs
  | .keccakGasCharge c => some (keccakGasInstrs c)
  | .mcopyGasCharge c => some (mcopyGasInstrs c)
  | .extcodecopyGasMem => some extcodecopyGasInstrs
  | .expGasCharge c b => some (expGasInstrs c b)
  | .blobhashLookup   => some blobHashInstrs
  -- control flow, halting, output
  | .pcDec            => some [.subImm .x21 .x21 1]
  | .branchOOG        => some [.bSymU "_eita_oog"]
  | .staticGuard      => some [.ldrbOff .x14 .x20 130, .cbnzSymW .x14 "_eita_static_violation"]
  | .setHalted        => some [.movImmW .x14 1, .strbOff .x14 .x20 128]
  | .setReverted      => some [.strbOff .x14 .x20 129]
  | .setOutput        => some
      [ .strOff .x10 .x20 120, .ldrOff .x14 .x20 40, .addReg .x14 .x14 .x6, .strOff .x14 .x20 112,
        .addReg .x15 .x6 .x10, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16, .cselHi .x16 .x15 .x16,
        .strOff .x16 .x20 24 ]
  | .jumpSyncRet      => some [.loadSymAddr .x27 "_eita_sync_and_ret", .brReg .x27]
  -- The destination is looked up in the host's valid-JUMPDEST map (EvmState #136), not
  -- in the code: a 0x5b byte inside a PUSH immediate is not a JUMPDEST (EELS
  -- `get_valid_jump_destinations`). See `jumpDestInstrs`.
  | .jumpValidate     => some
      ([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
        .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++
      jumpDestInstrs ++ [ .movReg .x21 .x6 ])
  | .jumpiCheck       => some
      ([ .orr3 .x14 .x10 .x11, .orr3 .x15 .x12 .x13, .orr3 .x14 .x14 .x15, .cbzLbl .x14 "_eita_jumpi_fallthrough",
        .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
        .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++
      jumpDestInstrs ++ [ .movReg .x21 .x6, .label "_eita_jumpi_pop" ])
  | .jumpiTailGas c   => some
      [ .subsImm .x22 .x22 c, .bloOog, .brCont, .label "_eita_jumpi_fallthrough", .bLbl "_eita_jumpi_pop" ]
  -- `movImmStr` prints a single movz when the value fits 16 bits (2300 does)
  | .sstoreSentry n   => if n < 65536 then some [.movzImm .x14 n, .cmpReg .x22 .x14, .bSym .ls "_eita_oog"] else none
  | .mstore8Tail      => some
      [ .ldrOff .x14 .x20 40, .addImm .x15 .x6 1, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16,
        .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24, .strbReg .x10 .x14 .x6,
        .subImm .x23 .x23 2, .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .memExpandIfLen tag => some
      (memRangeInstrs 2 1 .x0 s!".Lro{tag}0" s!".Lro{tag}1" ++
       [.movImm .x17 0, .cbzLbl .x0 "4f"] ++ memExpandInstrs ++
       [.subsReg .x22 .x22 .x17, .bloOog, .label "4"])
  | .copyCbPop3 h     => some
      [ .stpFpLr, .movReg .x0 .x20,
        .subImm .x14 .x23 1, .addLsl5 .x1 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x2 .x24 .x14,
        .subImm .x14 .x23 3, .addLsl5 .x3 .x24 .x14,
        .blSym h, .ldpFpLr,
        .subImm .x23 .x23 3, .cmpImm .x23 1, .bcLbl .lt "7f",
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .label "7", .cmpImm .x23 2, .bcLbl .lt "8f",
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16,
        .label "8" ]
  | .keccakCbPop1     => some
      [ .spSub 32, .stpFpLr, .movReg .x0 .x20,
        .subImm .x14 .x23 1, .addLsl5 .x1 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x2 .x24 .x14,
        .addSp .x3 16, .blSym "_eita_helper_keccak256",
        .addSp .x14 16, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .ldpFpLr, .spAdd 32, .subImm .x23 .x23 1 ]
  -- the write-side callbacks (stage 4p): sync the caches to the stack, call
  -- the host with pointers, charge the returned gas
  | .selfdestructCb   => some
      [ .stpFpLr,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .ldrOff .x0 .x20 504, .addImm .x1 .x20 144, .movReg .x2 .x14,
        .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 104, .blr .x14,
        .subsReg .x22 .x22 .x0, .bloOog, .ldpFpLr ]
  | .tstoreCb         => some
      [ .stpFpLr,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .stpOff .x10 .x11 .x14 0, .stpOff .x12 .x13 .x14 16,
        .ldrOff .x1 .x20 504, .ldrOff .x0 .x1 64, .addImm .x2 .x20 144,
        .subImm .x14 .x23 1, .addLsl5 .x3 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x4 .x24 .x14,
        .blSym "_eita_ts_tstore", .ldpFpLr,
        .subImm .x23 .x23 2,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16 ]
  | .sstoreCb         => some
      [ .stpFpLr,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .stpOff .x10 .x11 .x14 0, .stpOff .x12 .x13 .x14 16,
        .ldrOff .x0 .x20 504, .addImm .x1 .x20 144,
        .subImm .x14 .x23 1, .addLsl5 .x2 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x3 .x24 .x14,
        .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 8, .blr .x14,
        .subsReg .x22 .x22 .x0, .bloOog, .ldpFpLr,
        .ldrOff .x14 .x20 504, .ldrOff .x15 .x14 0, .ldrOff .x16 .x14 16, .movImm .x17 104, .madd .x0 .x15 .x17 .x16,
        .strZr .x0 0, .ldpOff .x1 .x2 .x20 144, .ldpOff .x3 .x4 .x20 160, .stpOff .x1 .x2 .x0 8, .stpOff .x3 .x4 .x0 24,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16,
        .stpOff .x6 .x7 .x0 40, .stpOff .x8 .x9 .x0 56, .stpOff .x10 .x11 .x0 72, .stpOff .x12 .x13 .x0 88,
        .ldrOff .x14 .x20 504, .addImm .x15 .x15 1, .strOff .x15 .x14 0,
        .subImm .x23 .x23 2,
        .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .extcodecopyCb    => some
      [ .stpFpLr, .ldrOff .x0 .x20 504,
        .subImm .x14 .x23 1, .addLsl5 .x1 .x24 .x14,
        .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14,
        .ldrOff .x16 .x20 40, .addReg .x2 .x16 .x15,
        .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14, .ldrBase .x3 .x14,
        .ldrOff .x15 .x14 8, .ldrOff .x16 .x14 16, .orr3 .x15 .x15 .x16,
        .ldrOff .x16 .x14 24, .orr3 .x15 .x15 .x16, .cbzLbl .x15 "94f",
        .movImm .x3 0, .subImm .x3 .x3 1, .label "94",
        -- len (fifth argument) loaded by this op, never inherited from the gas gadget
        .subImm .x14 .x23 4, .addLsl5 .x14 .x24 .x14, .ldrBase .x4 .x14,
        .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 56, .blr .x14,
        .subsReg .x22 .x22 .x0, .bloOog, .ldpFpLr,
        .subImm .x23 .x23 4,
        .cmpImm .x23 1, .bcLbl .lt "91f", .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "91",
        .cmpImm .x23 2, .bcLbl .lt "92f", .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
        .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label "92" ]
  -- the frame bodies (stage 4q): LOG, CREATE, CREATE2, the CALL family
  | .logEmit n cost   => some
      (syncTosNos ++
       [ .orr3 .x14 .x11 .x12, .orr3 .x14 .x14 .x13, .cbnzOog .x14,
         .movImm .x17 cost, .addLsl .x17 .x17 .x10 3, .cbzLbl .x10 "4f",
         .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzOog .x14,
         .adds .x0 .x6 .x10, .bcsOog ] ++
       memExpandInstrs ++
       [ .label "4",
         .ldrOff .x14 .x20 504, .ldrOff .x15 .x14 8, .addImm .x15 .x15 1, .strOff .x15 .x14 8,
         .addReg .x15 .x6 .x10, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16, .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24,
         .subImm .x23 .x23 (2 + n),
         .subsReg .x22 .x22 .x17, .bloOog,
         .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 72, .cbzLbl .x14 "7f",
         .stpFpLr,
         .ldrOff .x0 .x20 504, .addImm .x1 .x20 144,
         .movImm .x2 n,
         .addLsl5 .x3 .x24 .x23,
         .addImm .x15 .x23 (n + 1),
         .addLsl5 .x15 .x24 .x15, .ldrBase .x15 .x15, .ldrOff .x4 .x20 40, .addReg .x4 .x4 .x15,
         .addImm .x15 .x23 n,
         .addLsl5 .x15 .x24 .x15, .ldrBase .x5 .x15,
         .blr .x14, .ldpFpLr,
         .label "7",
         .cmpImm .x23 1, .bcLbl .lt "5f" ] ++ reloadTos ++ [ .label "5" ] ++
       reloadNosIf2 "6f" "6" ++ [ .brCont ])
  | .createCore       => some
      ([ .spSub 192, .stpFpLr, .strOff .x21 .x20 0, .strOff .x22 .x20 8, .strOff .x23 .x20 16 ] ++ syncTosNos ++
       createMemExpandInstrs 2 3 "create" ++
       [ .movImmW .x0 4, .strWSp .x0 16, .strWzrSp 20, .stpZrSp 24, .stpZrSp 40,
         .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 56, .stpSp .x2 .x3 72,
         .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 88,
         .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 96,
         .strSp .x22 104, .stpZrSp 112, .stpZrSp 128,
         .ldrOff .x0 .x20 504, .addSp .x1 16, .addSp .x2 144, .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 96, .blr .x14,
         .ldrSp .x14 152, .strOff .x14 .x20 96, .ldrSp .x14 160, .strOff .x14 .x20 104,
         .ldrWSp .x15 144, .cbzWLbl .x15 "L_create_fail",
         .addSp .x14 176, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .bLbl "L_create_done",
         .label "L_create_fail", .movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
         .label "L_create_done", .ldrSp .x0 168, .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog,
         .subImm .x23 .x23 2, .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16 ] ++
       reloadNosIf2 "L_create_done2" "L_create_done2" ++ [ .ldpFpLr, .spAdd 192, .brCont ])
  | .create2Core      => some
      ([ .spSub 192, .stpFpLr, .strOff .x21 .x20 0, .strOff .x22 .x20 8, .strOff .x23 .x20 16 ] ++ syncTosNos ++
       createMemExpandInstrs 2 3 "create2" ++
       [ .movImmW .x0 5, .strWSp .x0 16, .strWzrSp 20, .stpZrSp 24, .stpZrSp 40,
         .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 56, .stpSp .x2 .x3 72,
         .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 88,
         .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 96,
         .strSp .x22 104,
         .subImm .x14 .x23 4, .addLsl5 .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 112, .stpSp .x2 .x3 128,
         .ldrOff .x0 .x20 504, .addSp .x1 16, .addSp .x2 144, .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 96, .blr .x14,
         .ldrSp .x14 152, .strOff .x14 .x20 96, .ldrSp .x14 160, .strOff .x14 .x20 104,
         .ldrWSp .x15 144, .cbzWLbl .x15 "L_create2_fail",
         .addSp .x14 176, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .bLbl "L_create2_done",
         .label "L_create2_fail", .movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
         .label "L_create2_done", .ldrSp .x0 168, .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog,
         .subImm .x23 .x23 3, .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16 ] ++
       reloadNosIf2 "L_create2_done2" "L_create2_done2" ++ [ .ldpFpLr, .spAdd 192, .brCont ])
  | .callFamilyCore name kind staticpFlag withValue =>
      let argsCount : Nat := if withValue then 7 else 6
      let inOff : Nat := if withValue then 4 else 3
      let inLen : Nat := if withValue then 5 else 4
      let outOff : Nat := if withValue then 6 else 5
      let outLen : Nat := if withValue then 7 else 6
      some
      (callMemExpandInstrs inOff inLen outOff outLen name ++
       [ .spSub 192, .stpFpLr, .strOff .x21 .x20 0, .strOff .x22 .x20 8, .strOff .x23 .x20 16 ] ++ syncTosNos ++
       [ .movImmW .x0 kind, .strWSp .x0 16, .movImmW .x0 staticpFlag, .strWSp .x0 20,
         .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 24, .stpSp .x2 .x3 40 ] ++
       (if withValue then
          [ .subImm .x14 .x23 3, .addLsl5 .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 56, .stpSp .x2 .x3 72 ]
        else [ .stpZrSp 56, .stpZrSp 72 ]) ++
       [ .subImm .x14 .x23 inOff, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 88,
         .subImm .x14 .x23 inLen, .addLsl5 .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 96,
         .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .ldpOff .x15 .x16 .x14 0, .ldpOff .x0 .x1 .x14 16,
         .orr3 .x16 .x16 .x0, .orr3 .x16 .x16 .x1, .cmpImm .x16 0, .csinvEqZr .x15 .x15, .strSp .x15 104,
         .stpZrSp 112, .stpZrSp 128,
         .ldrOff .x0 .x20 504, .addSp .x1 16, .addSp .x2 144, .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 88, .blr .x14,
         .ldrSp .x0 152, .strOff .x0 .x20 96, .ldrSp .x0 160, .strOff .x0 .x20 104,
         .subImm .x14 .x23 outOff, .addLsl5 .x14 .x24 .x14, .ldrBase .x1 .x14,
         .subImm .x14 .x23 outLen, .addLsl5 .x14 .x24 .x14, .ldrBase .x2 .x14, .movReg .x0 .x20, .blSym "_eita_helper_returndata_to_mem",
         .ldrWSp .x15 144, .ldrSp .x0 168,
         .subImm .x23 .x23 (argsCount - 1),
         .movReg .x6 .x15, .andImmHex .x6 .x6 0xff, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
         .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16 ] ++
       reloadNosIf2 s!"L_callret_{name}" s!"L_callret_{name}" ++
       [ .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog, .ldpFpLr, .spAdd 192, .brCont ])
  | .clzReduce        => some clzReduceInstrs
  -- the stack family (stage 4l). On x86-64 `tosToNos` vanishes (spScale drops
  -- NOS writes: the old TOS is already in memory by the invariant that every
  -- TOS-producing handler ends with storeTos) and `nosToTos` becomes four
  -- loads from stack[sp-2], which is exactly the per-instruction lowering of
  -- `mov x6, x10` with a NOS source.
  | .tosToNos         => some [.movReg .x10 .x6, .movReg .x11 .x7, .movReg .x12 .x8, .movReg .x13 .x9]
  | .nosToTos         => some [.movReg .x6 .x10, .movReg .x7 .x11, .movReg .x8 .x12, .movReg .x9 .x13]
  | .spInc            => some [.addImm .x23 .x23 1]
  | .spDec2           => some [.subImm .x23 .x23 2]
  | .loadZeroTos      => some [.movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .dupLoad n        => some
      [ .subImm .x14 .x23 n, .addLsl5 .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .swapPartner n    => some
      [ .subImm .x14 .x23 (n + 1), .addLsl5 .x14 .x24 .x14,
        .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16,
        .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .movReg .x6 .x0, .movReg .x7 .x1, .movReg .x8 .x2, .movReg .x9 .x3 ]
  | .pushImm n        => some (pushWideInstrs n)
  | .spDec            => some [.subImm .x23 .x23 1]
  | .exitGas c        => some [.subsImm .x22 .x22 c, .bloOog, .brCont]
  | .notLimbs         => some [.mvn .x6 .x6, .mvn .x7 .x7, .mvn .x8 .x8, .mvn .x9 .x9]
  | .eqReduce         => some
      [ .eor3 .x14 .x6 .x10, .eor3 .x15 .x7 .x11, .orr3 .x14 .x14 .x15,
        .eor3 .x15 .x8 .x12, .orr3 .x14 .x14 .x15, .eor3 .x15 .x9 .x13, .orr3 .x14 .x14 .x15,
        .cmpImm .x14 0, .cset .x6 .eq, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ]
  | .iszeroReduce     => some
      [ .orr3 .x14 .x6 .x7, .orr3 .x15 .x8 .x9, .orr3 .x14 .x14 .x15,
        .cmpImm .x14 0, .cset .x6 .eq, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ]
  | .cmpChain swapped cond => some
      ((if swapped then
          [ .subsZr .x10 .x6, .sbcsZr .x11 .x7, .sbcsZr .x12 .x8, .sbcsZr .x13 .x9 ]
        else
          [ .subsZr .x6 .x10, .sbcsZr .x7 .x11, .sbcsZr .x8 .x12, .sbcsZr .x9 .x13 ]) ++
       [ .cset .x6 (match cond with | .lo => .lo | .lt => .lt),
         .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ])
  | .arith .add       => some
      [ .adds .x10 .x6 .x10, .adcs .x11 .x7 .x11, .adcs .x12 .x8 .x12, .adc .x13 .x9 .x13,
        .movReg .x6 .x10, .movReg .x7 .x11, .movReg .x8 .x12, .movReg .x9 .x13 ]
  | .arith .sub       => some
      [ .subsReg .x10 .x6 .x10, .sbcs .x11 .x7 .x11, .sbcs .x12 .x8 .x12, .sbc .x13 .x9 .x13,
        .movReg .x6 .x10, .movReg .x7 .x11, .movReg .x8 .x12, .movReg .x9 .x13 ]
  | .bitwise op       => some
      (let f : Reg → Reg → Reg → AInstr := match op with
         | .and => .and3 | .orr => .orr3 | .eor => .eor3
       [ f .x10 .x10 .x6, f .x11 .x11 .x7, f .x12 .x12 .x8, f .x13 .x13 .x9,
         .movReg .x6 .x10, .movReg .x7 .x11, .movReg .x8 .x12, .movReg .x9 .x13 ])

/-! ## The x86-64 program for an op

x86-64 keeps no NOS cache, so an ARM64 body that computes INTO the NOS
registers and copies down (`adds x10, x6, x10 … mov x6, x10`) has no literal
lowering. Its natural x86-64 form is better anyway: compute into TOS with NOS
as a memory operand — `add r8, [nos]; adc r9, [nos+8]; …` — half the
instructions and no copies. So the arithmetic family gets a per-target
`AInstr` program, while everything else is the ARM64 program with the sp
representation change applied (`spScale`, below). -/

def isNos : Reg → Bool
  | .x10 | .x11 | .x12 | .x13 => true
  | _ => false

/-- The register an instruction writes, if any. -/
def dest? : AInstr → Option Reg
  | .subImm d _ _ | .addImm d _ _ | .movImm d _ | .ldrOff d _ _ | .ldrBase d _ | .clzReg d _
  | .lsrImm d _ _ | .lslImm d _ _ | .addLsl5 d _ _ | .orr3 d _ _ | .adds d _ _ | .cselHi d _ _
  | .subsReg d _ _ | .subReg d _ _ | .addReg d _ _ | .mulReg d _ _ | .addLsr d _ _ _
  | .addLsl d _ _ _ | .addsImm d _ _ | .rev d _ | .movReg d _
  | .adcs d _ _ | .adc d _ _ | .sbcs d _ _ | .sbc d _ _ | .and3 d _ _ | .eor3 d _ _
  | .subsImm d _ _ | .mvn d _ | .cset d _ | .ldrbReg d _ _ | .movImmW d _
  | .addSp d _ | .ldrSp d _ | .ldrbOff d _ _ | .loadSymAddr d _ | .cselNe d _ _ | .movzImm d _
  | .madd d _ _ _ | .ldrWSp d _ | .andImmHex d _ _ | .csinvEqZr d _ => some d
  | .ldpOff r1 _ _ _ => some r1
  | _ => none

/-- Word counts on sp become byte counts; the stack-address idiom becomes an
    add; NOS writes disappear. -/
def spScale : AInstr → List AInstr
  | .subImm .x23 .x23 k => [.subImm .x23 .x23 (32 * k)]
  | .addImm .x23 .x23 k => [.addImm .x23 .x23 (32 * k)]
  | .cmpImm .x23 k      => [.cmpImm .x23 (32 * k)]
  | .subImm d .x23 k    => [.subImm d .x23 (32 * k)]
  | .addImm d .x23 k    => [.addImm d .x23 (32 * k)]
  -- the stack-address idiom, whatever register it lands in: the index is a
  -- (scaled) sp-derived byte count, so the `lsl #5` goes. The `d == e` guard
  -- that used to be here left `copyGasInstrs`' `add x15, x24, x14, lsl #5` in
  -- word form — CODECOPY read its length from the wrong slot (depth 3 hid it:
  -- slot 0 is offset 0 either way); the x86-64 Linux ValidBlocks run found it.
  | .addLsl5 d .x24 e   => [.addReg d .x24 e]
  | i => match dest? i with
         | some d => if isNos d then [] else [i]
         | none => [i]

/-! ### The x86-64 call sequence

SysV: arguments in rdi, rsi, rdx, rcx; no frame pointer or link register to
save (the return address is already on the stack); the 32-byte result scratch
at [rsp] after `sub rsp, 32`. The ARM64 program names its argument registers
x0-x3; on x86-64 the SysV registers are reached through the ARM names whose
x86 HOMES are rdi/rsi/rdx/rcx — x3, x2, x1, x14 under the forced colouring —
which `sysv_arg_homes` pins so the correspondence cannot drift silently.
Stack-word addresses are byte offsets off r12 (sp is a byte offset on x86-64,
stage 4d): &top = r12 + r13 − 32, &nos = r12 + r13 − 64, &third = −96.

Alignment: a SysV callee expects rsp ≡ 8 (mod 16) at entry. A handler body
is entered by `call` from a frame that pushed six registers after its own
entry, so the body starts at rsp ≡ 0; `sub rsp, 32` keeps that, and the
`call` then makes it 8 — `helper_calls_are_aligned` walks the body to check. -/

def argRegs : List (Reg × String) := [(.x3, "rdi"), (.x2, "rsi"), (.x1, "rdx"), (.x14, "rcx")]

def x86BinHelper (h : String) : List AInstr :=
  [ .spSub 32, .addSp .x3 0,
    .subImm .x2 .x23 32, .addReg .x2 .x24 .x2,
    .subImm .x1 .x23 64, .addReg .x1 .x24 .x1,
    .blSym h,
    .addSp .x14 0, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
    .spAdd 32 ]

def x86TernaryHelper (h : String) : List AInstr :=
  [ .spSub 32, .addSp .x3 0,
    .subImm .x2 .x23 32, .addReg .x2 .x24 .x2,
    .subImm .x1 .x23 64, .addReg .x1 .x24 .x1,
    .subImm .x14 .x23 96, .addReg .x14 .x24 .x14,
    .blSym h,
    .addSp .x14 0, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
    .spAdd 32 ]

/-- The frame bodies' x86-64 building blocks. `x86SaveState` stores the
    pc/gas/sp fields for the host — sp as a WORD count (r13 is bytes). -/
def x86SaveState : List AInstr :=
  [ .strOff .x21 .x20 0, .strOff .x22 .x20 8, .movReg .x14 .x23, .lsrImm .x14 .x14 5, .strOff .x14 .x20 16 ]
def x86SyncTos : List AInstr :=
  [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16 ]
def x86ReloadTos : List AInstr :=
  [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
def x86StoreTos : List AInstr := x86SyncTos

/-- An op's x86-64 program: the arithmetic family computed into TOS, the call
    family in SysV shape, every other op the scaled ARM64 program. -/
def Op.instrsX86? : Op → Option (List AInstr)
  | .binHelper h     => some (x86BinHelper h)
  | .ternaryHelper h => some (x86TernaryHelper h)
  -- host callbacks, SysV shape: argument i through `sysvReg i`; the scratch is
  -- at [rsp] (no fp/lr save); the indirect call target goes through rax (x0's
  -- home) because rcx — x14's home, the ARM scratch — is argument 3
  | .argStateBase r   => (sysvReg r).map (fun a => [.movReg a .x20])
  | .argStateField r off => (sysvReg r).map (fun a => [.addImm a .x20 off])
  | .argStackPtr r n  => (sysvReg r).map (fun a => [.subImm a .x23 (32 * n), .addReg a .x24 a])
  | .argScratch r     => (sysvReg r).map (fun a => [.addSp a 0])
  | .loadCtx r        => (sysvReg r).map (fun a => [.ldrOff a .x20 504])
  | .loadCtxVia14 r   => (sysvReg r).map (fun a => [.ldrOff a .x20 504])
  | .loadTxStateCtx r => (sysvReg r).map (fun a => [.ldrOff a .x20 504, .ldrOff a a 64])
  | .cbSlot slot      => some [.ldrOff .x0 .x20 496, .ldrOff .x0 .x0 slot, .blr .x0]
  -- the write-side callbacks in SysV shape. TOS is synced to the stack before
  -- the call (r8-r11 are caller-saved) and reloaded after; NOS is already
  -- memory, so its syncs vanish. Argument i goes through `sysvReg i`; the
  -- indirect target through rax; the ARM pair x3/x4 (both rdi on x86-64) in the
  -- journal copy becomes two sequential pairs through distinct temporaries.
  | .selfdestructCb   => some
      [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .ldrOff .x3 .x20 504, .addImm .x2 .x20 144, .movReg .x1 .x14,
        .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 104, .blr .x0,
        .subsReg .x22 .x22 .x0, .bloOog ]
  | .tstoreCb         => some
      [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .ldrOff .x2 .x20 504, .ldrOff .x3 .x2 64, .addImm .x1 .x20 144,
        .subImm .x14 .x23 32, .addReg .x14 .x24 .x14,
        .subImm .x6 .x23 64, .addReg .x6 .x24 .x6,
        .blSym "_eita_ts_tstore",
        .subImm .x23 .x23 64,
        .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .sstoreCb         => some
      [ .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16,
        .ldrOff .x3 .x20 504, .addImm .x2 .x20 144,
        .subImm .x1 .x23 32, .addReg .x1 .x24 .x1,
        .subImm .x14 .x23 64, .addReg .x14 .x24 .x14,
        .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 8, .blr .x0,
        .subsReg .x22 .x22 .x0, .bloOog,
        .ldrOff .x14 .x20 504, .ldrOff .x15 .x14 0, .ldrOff .x16 .x14 16, .movImm .x17 104, .madd .x0 .x15 .x17 .x16,
        -- the journal count is bumped HERE, while x15 (rdx) still holds it: the
        -- entry's address limbs below go through x1/x2 and x16/x17, whose x86-64
        -- homes are x15's and x17's (`X86Alias.no_alias_hazards`)
        .addImm .x15 .x15 1, .strOff .x15 .x14 0,
        .strZr .x0 0,
        .ldpOff .x1 .x2 .x20 144, .stpOff .x1 .x2 .x0 8,
        .ldpOff .x16 .x17 .x20 160, .stpOff .x16 .x17 .x0 24,
        .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .stpOff .x6 .x7 .x0 40, .stpOff .x8 .x9 .x0 56, .stpOff .x10 .x11 .x0 72, .stpOff .x12 .x13 .x0 88,
        .subImm .x23 .x23 64,
        .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16 ]
  | .extcodecopyCb    => some
      [ .ldrOff .x3 .x20 504,
        .subImm .x2 .x23 32, .addReg .x2 .x24 .x2,
        -- dst = memory base + destOffset, staged in x8/x9 (TOS is synced, so they
        -- are free): x16's home is x3's (rdi, the ctx argument) and x15's is x1's
        -- (rdx, the destination) — `add x1, x8, x15` lowered to `add rdx, rdx`
        .subImm .x14 .x23 64, .addReg .x14 .x24 .x14, .ldrBase .x9 .x14,
        .ldrOff .x8 .x20 40, .addReg .x1 .x8 .x9,
        .subImm .x14 .x23 96, .addReg .x14 .x24 .x14,
        -- src is a u256: any high limb ⇒ 2^64-1 (past any code; the host zero-fills)
        .ldrOff .x9 .x14 8, .ldrOff .x8 .x14 16, .orr3 .x9 .x9 .x8,
        .ldrOff .x8 .x14 24, .orr3 .x9 .x9 .x8, .ldrBase .x14 .x14,
        .cbzLbl .x9 "94f", .movImm .x14 0, .subImm .x14 .x14 1, .label "94",
        -- len is the FIFTH argument (r8 = x6), loaded from the stack by this op, as
        -- on ARM64 (x4) — never a value a previous gadget happened to leave behind
        .subImm .x6 .x23 128, .addReg .x6 .x24 .x6, .ldrBase .x6 .x6,
        .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 56, .blr .x0,
        .subsReg .x22 .x22 .x0, .bloOog,
        .subImm .x23 .x23 128,
        .cmpImm .x23 32, .bcLbl .lt "91f", .subImm .x14 .x23 32, .addReg .x14 .x24 .x14,
        .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "91" ]
  -- the frame bodies on x86-64: SysV args, scratch at [rsp] (offsets −16), the
  -- state's sp FIELD is a word count so r13 (bytes) is stored shifted, the
  -- NOS sync is absent, the callee address goes through rax
  | .logEmit n cost   => some
      (x86SyncTos ++
       [ .orr3 .x14 .x11 .x12, .orr3 .x14 .x14 .x13, .cbnzOog .x14,
         .movImm .x17 cost, .movReg .x0 .x10, .lslImm .x0 .x0 3, .addReg .x17 .x17 .x0,
         .cbzLbl .x10 "4f",
         .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzOog .x14,
         .adds .x0 .x6 .x10, .bcsOog ] ++ memExpandInstrs ++
       [ .label "4",
         .ldrOff .x14 .x20 504, .ldrOff .x15 .x14 8, .addImm .x15 .x15 1, .strOff .x15 .x14 8,
         .addReg .x15 .x6 .x10, .ldrOff .x16 .x20 24, .cmpReg .x15 .x16, .cselHi .x16 .x15 .x16, .strOff .x16 .x20 24,
         .subImm .x23 .x23 (32 * (2 + n)),
         .subsReg .x22 .x22 .x17, .bloOog,
         .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 72, .cbzLbl .x0 "7f",
         .ldrOff .x3 .x20 504, .addImm .x2 .x20 144,
         .addReg .x14 .x24 .x23,
         .addImm .x15 .x23 (32 * (n + 1)), .addReg .x15 .x24 .x15, .ldrBase .x15 .x15, .ldrOff .x6 .x20 40, .addReg .x6 .x6 .x15,
         .addImm .x15 .x23 (32 * n), .addReg .x15 .x24 .x15, .ldrBase .x7 .x15,
         -- the topic count goes in LAST: x1's home is x15's (rdx), the address temporary above
         .movImm .x1 n,
         .blr .x0,
         .label "7",
         .cmpImm .x23 32, .bcLbl .lt "5f" ] ++ x86ReloadTos ++ [ .label "5", .brCont ])
  | .createCore       => some
      ([ .spSub 192 ] ++ x86SaveState ++ x86SyncTos ++
       (createMemExpandInstrs 2 3 "create").flatMap spScale ++
       [ .movImmW .x0 4, .strWSp .x0 0, .strWzrSp 4, .stpZrSp 8, .stpZrSp 24,
         .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 40, .stpSp .x2 .x3 56,
         .subImm .x14 .x23 64, .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 72,
         .subImm .x14 .x23 96, .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 80,
         .strSp .x22 88, .stpZrSp 96, .stpZrSp 112,
         .ldrOff .x3 .x20 504, .addSp .x2 0, .addSp .x1 128, .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 96, .blr .x0,
         .ldrSp .x14 136, .strOff .x14 .x20 96, .ldrSp .x14 144, .strOff .x14 .x20 104,
         .ldrWSp .x15 128, .cbzWLbl .x15 "L_create_fail",
         .addSp .x14 160, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .bLbl "L_create_done",
         .label "L_create_fail", .movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
         .label "L_create_done", .ldrSp .x0 152, .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog,
         .subImm .x23 .x23 64 ] ++ x86StoreTos ++ [ .spAdd 192, .brCont ])
  | .create2Core      => some
      ([ .spSub 192 ] ++ x86SaveState ++ x86SyncTos ++
       (createMemExpandInstrs 2 3 "create2").flatMap spScale ++
       [ .movImmW .x0 5, .strWSp .x0 0, .strWzrSp 4, .stpZrSp 8, .stpZrSp 24,
         .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 40, .stpSp .x2 .x3 56,
         .subImm .x14 .x23 64, .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 72,
         .subImm .x14 .x23 96, .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 80,
         .strSp .x22 88,
         .subImm .x14 .x23 128, .addReg .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 96, .stpSp .x2 .x3 112,
         .ldrOff .x3 .x20 504, .addSp .x2 0, .addSp .x1 128, .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 96, .blr .x0,
         .ldrSp .x14 136, .strOff .x14 .x20 96, .ldrSp .x14 144, .strOff .x14 .x20 104,
         .ldrWSp .x15 128, .cbzWLbl .x15 "L_create2_fail",
         .addSp .x14 160, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .bLbl "L_create2_done",
         .label "L_create2_fail", .movImm .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0,
         .label "L_create2_done", .ldrSp .x0 152, .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog,
         .subImm .x23 .x23 96 ] ++ x86StoreTos ++ [ .spAdd 192, .brCont ])
  | .callFamilyCore name kind staticpFlag withValue =>
      let argsCount : Nat := if withValue then 7 else 6
      let inOff : Nat := if withValue then 4 else 3
      let inLen : Nat := if withValue then 5 else 4
      let outOff : Nat := if withValue then 6 else 5
      let outLen : Nat := if withValue then 7 else 6
      some
      ((callMemExpandInstrs inOff inLen outOff outLen name).flatMap spScale ++
       [ .spSub 192 ] ++ x86SaveState ++ x86SyncTos ++
       [ .movImmW .x0 kind, .strWSp .x0 0, .movImmW .x0 staticpFlag, .strWSp .x0 4,
         .subImm .x14 .x23 64, .addReg .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 8, .stpSp .x2 .x3 24 ] ++
       (if withValue then
          [ .subImm .x14 .x23 96, .addReg .x14 .x24 .x14, .ldpOff .x0 .x1 .x14 0, .ldpOff .x2 .x3 .x14 16, .stpSp .x0 .x1 40, .stpSp .x2 .x3 56 ]
        else [ .stpZrSp 40, .stpZrSp 56 ]) ++
       [ .subImm .x14 .x23 (32 * inOff), .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .ldrOff .x16 .x20 40, .addReg .x15 .x16 .x15, .strSp .x15 72,
         .subImm .x14 .x23 (32 * inLen), .addReg .x14 .x24 .x14, .ldrBase .x15 .x14, .strSp .x15 80,
         -- the gas word's high limbs go through x8/x9 (TOS is synced, so they are
         -- free): x1's x86-64 home is x15's (rdx), and loading limb 3 into x1 while
         -- limb 0 sits in x15 zeroed the forwarded gas — the first x86-64 Linux ValidBlocks
         -- run's sub-frames all started at gas 0 (`no_alias_overlap` now forbids it)
         .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x15 .x16 .x14 0, .ldpOff .x8 .x9 .x14 16,
         .orr3 .x16 .x16 .x8, .orr3 .x16 .x16 .x9, .cmpImm .x16 0, .csinvEqZr .x15 .x15, .strSp .x15 88,
         .stpZrSp 96, .stpZrSp 112,
         .ldrOff .x3 .x20 504, .addSp .x2 0, .addSp .x1 128, .ldrOff .x0 .x20 496, .ldrOff .x0 .x0 88, .blr .x0,
         .ldrSp .x0 136, .strOff .x0 .x20 96, .ldrSp .x0 144, .strOff .x0 .x20 104,
         .subImm .x14 .x23 (32 * outOff), .addReg .x14 .x24 .x14, .ldrBase .x2 .x14,
         .subImm .x14 .x23 (32 * outLen), .addReg .x14 .x24 .x14, .ldrBase .x1 .x14, .movReg .x3 .x20, .blSym "_eita_helper_returndata_to_mem",
         .ldrWSp .x15 128, .ldrSp .x0 152,
         .subImm .x23 .x23 (32 * (argsCount - 1)),
         .movReg .x6 .x15, .andImmHex .x6 .x6 0xff, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0 ] ++
       x86StoreTos ++
       [ .ldrOff .x22 .x20 8, .subsReg .x22 .x22 .x0, .bloOog, .spAdd 192, .brCont ])
  -- x86-64: the continuation is the return address, so "sync and return to
  -- the host" is `ret` — the dispatcher continues from pc (rbp)
  | .jumpSyncRet      => some [.bSymU "_eita_sync_and_ret"]   -- an EXIT, not a continue: the frame tells them apart
  | .clzReduce        => some clzReduceInstrs   -- scratch only, as on ARM64
  | .copyCbPop3 h     => some
      [ .movReg .x3 .x20,
        .subImm .x2 .x23 32, .addReg .x2 .x24 .x2,
        .subImm .x1 .x23 64, .addReg .x1 .x24 .x1,
        .subImm .x14 .x23 96, .addReg .x14 .x24 .x14,
        .blSym h,
        .subImm .x23 .x23 96, .cmpImm .x23 32, .bcLbl .lt "7f",
        .subImm .x14 .x23 32, .addReg .x14 .x24 .x14, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .label "7" ]
  | .keccakCbPop1     => some
      [ .spSub 32, .movReg .x3 .x20,
        .subImm .x2 .x23 32, .addReg .x2 .x24 .x2,
        .subImm .x1 .x23 64, .addReg .x1 .x24 .x1,
        .addSp .x14 0, .blSym "_eita_helper_keccak256",
        .addSp .x14 0, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16,
        .spAdd 32, .subImm .x23 .x23 32 ]
  | .loadScratchTos   => some [.addSp .x14 0, .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16]
  | .loadScratchU64Tos => some [.ldrSp .x6 0, .movImm .x7 0, .movImm .x8 0, .movImm .x9 0]
  | .arith .add => some [.adds .x6 .x6 .x10, .adcs .x7 .x7 .x11, .adcs .x8 .x8 .x12, .adc .x9 .x9 .x13]
  | .arith .sub => some [.subsReg .x6 .x6 .x10, .sbcs .x7 .x7 .x11, .sbcs .x8 .x8 .x12, .sbc .x9 .x9 .x13]
  | .bitwise op => some
      (let f : Reg → Reg → Reg → AInstr := match op with
         | .and => .and3 | .orr => .orr3 | .eor => .eor3
       [ f .x6 .x6 .x10, f .x7 .x7 .x11, f .x8 .x8 .x12, f .x9 .x9 .x13 ])
  | o => (Op.instrs? o).map (fun is => is.flatMap spScale)

/-- The x86-64 arithmetic forms compute the same limb-wise result the ARM64
    forms do: both are `TOS ← TOS ∘ NOS`; ARM64 lands it in x10-x13 first and
    copies, x86-64 lands it in x6-x9 directly. Checked structurally: the
    x86-64 program is the ARM64 program's first four instructions with the
    destination renamed to the TOS limb and the copies removed. -/
def tosOf : Reg → Reg
  | .x10 => .x6 | .x11 => .x7 | .x12 => .x8 | .x13 => .x9 | r => r

def renameDest : AInstr → AInstr
  | .adds d a b => .adds (tosOf d) a b | .adcs d a b => .adcs (tosOf d) a b | .adc d a b => .adc (tosOf d) a b
  | .subsReg d a b => .subsReg (tosOf d) a b | .sbcs d a b => .sbcs (tosOf d) a b | .sbc d a b => .sbc (tosOf d) a b
  | .and3 d a b => .and3 (tosOf d) a (tosOf b) | .orr3 d a b => .orr3 (tosOf d) a (tosOf b)
  | .eor3 d a b => .eor3 (tosOf d) a (tosOf b)
  | i => i

theorem x86_arith_is_arm_arith_into_tos :
    [Op.arith .add, .arith .sub].all (fun o =>
      (Op.instrsX86? o).map (·.length) == some 4 &&
      ((Op.instrs? o).map (fun is => (is.take 4).map renameDest)) == Op.instrsX86? o) = true := by
  native_decide

/-- The handlers that are fully covered so far. -/
def covered : List Prog :=
  [mloadBody 3, mstoreBody 3,
   arithBody .add 3, arithBody .sub 3,
   bitwiseBody .and 3, bitwiseBody .orr 3, bitwiseBody .eor 3,
   notBody 3,
   eqBody 3, iszeroBody 3,
   cmpBody false .lo 3, cmpBody true .lo 3, cmpBody false .lt 3, cmpBody true .lt 3,
   popBody 2, pushBody 0 2, pushBody 1 3, pushBody 2 3, pushBody 8 3, pushBody 9 3, pushBody 32 3,
   dupBody 1 3, dupBody 2 3, swapBody 1 3, swapBody 2 3,
   binComputeBody "_eita_helper_mul" 5, binComputeBody "_eita_helper_div" 5,
   binComputeBody "_eita_helper_sdiv" 5, binComputeBody "_eita_helper_mod" 5,
   binComputeBody "_eita_helper_smod" 5, binComputeBody "_eita_helper_shl" 3,
   binComputeBody "_eita_helper_shr" 3, binComputeBody "_eita_helper_sar" 3,
   binComputeBody "_eita_helper_byte" 3, binComputeBody "_eita_helper_signextend" 5,
   ternaryComputeBody "_eita_helper_addmod" 8, ternaryComputeBody "_eita_helper_mulmod" 8,
   pcBody 2, gasBody 2, envU64Body 8 2, envU256Body 320 2, sloadBody,
   stopBody, jumpdestBody 1, invalidBody, returnBody, revertBody, jumpBody 8, jumpiBody 10,
   mstore8Body 3, keccak256Body 30, copyBody "_eita_helper_calldatacopy" 3,
   mcopyBody "_eita_helper_mcopy" 3, clzBody 5, envU256Body 568 2, msizeBody 2, tloadBody,
   blobhashBody 3,
   expBody 10 50,
   sstoreBody 2300, tstoreBody, selfdestructBody 5000, extcodecopyBody,
   logBody 0 375, logBody 2 1125, logBody 4 1875, createBody, create2Body,
   callFamilyBody "call" 0 0 true, callFamilyBody "callcode" 1 0 true,
   callFamilyBody "delegatecall" 2 0 false, callFamilyBody "staticcall" 3 1 false]

/-- Every op of the covered handlers has an `AInstr` form. -/
theorem covered_ops_lower :
    covered.all (fun p => p.all (fun o => (Op.instrs? o).isSome)) = true := by native_decide

/-- Ops that only appear in bodies not yet covered are checked standalone, so
    a printing slip cannot hide behind the body list — handlers.S found both
    of these the first time (`cbnz w14` is the 32-bit form; the sentry is a
    `movz`). -/
def standaloneOps : List Op := [.staticGuard, .sstoreSentry 2300, .chargeFixed 100, .cbDirect "_eita_ts_tload"]

theorem standalone_ops_reproduce_emit :
    standaloneOps.all (fun o =>
      match Op.instrs? o with
      | some is => String.join (is.map AInstr.emitARM64) == o.emit
      | none => false) = true := by native_decide

theorem sysv_arg4_is_tos_limb0 :
    (sysvReg 4).bind Evm.CL.Lowering.x86Reg? = some "r8" := by native_decide

/-- **Text identity.** Printing the `AInstr` form through `emitARM64` is
    `Op.emit`, character for character, for every covered op — so switching
    the handler emitters to `Op.instrs?` cannot change `handlers.S`. -/
theorem instrs_reproduce_emit :
    covered.all (fun p => p.all (fun o =>
      match Op.instrs? o with
      | some is => String.join (is.map AInstr.emitARM64) == o.emit
      | none => false)) = true := by native_decide

/-- The emitter the handler files use from now on: an op with an `AInstr` form
    is printed through `emitARM64`; one without falls back to `Op.emit`. For
    covered ops the two are character-identical (`instrs_reproduce_emit`), for
    uncovered ops the fallback IS `Op.emit` — so switching every call site is
    byte-neutral by construction, and `handlers.S` is the gate that says so. -/
def _root_.Evm.CL.AsmCore.Op.emitDerived (o : Op) : String :=
  match Op.instrs? o with
  | some is => String.join (is.map AInstr.emitARM64)
  | none => o.emit

def _root_.Evm.CL.AsmCore.Prog.emitDerived (p : Prog) : String := String.join (p.map Op.emitDerived)

theorem emitDerived_eq_emit_covered :
    covered.all (fun p => p.emitDerived == p.emit) = true := by native_decide

/-- Append `suf` to every NAMED label a body defines and every reference to
    one — the `AInstr` form of `ARM64.suffixDefinedLabels`. Numeric labels
    (`1:`, `5f`) are assembler-local and stay; symbol references (`blSym`,
    `bSym`) are not labels and stay. Lets one body link twice into an image
    (the interp-tier body and its flat `_f` twin; a fork variant). -/
def suffixLabels (suf : String) : AInstr → AInstr
  | .label l      => .label (ren l)
  | .bLbl l       => .bLbl (ren l)
  | .cbzLbl r l   => .cbzLbl r (ren l)
  | .cbnzLbl r l  => .cbnzLbl r (ren l)
  | .bcLbl c l    => .bcLbl c (ren l)
  | .blsLbl l     => .blsLbl (ren l)
  | .cbzWLbl r l  => .cbzWLbl r (ren l)
  | .cbnzWLbl r l => .cbnzWLbl r (ren l)
  | .adrLbl r l   => .adrLbl r (ren l)
  | i             => i
where
  ren (l : String) : String :=
    if l.length > 0 && !l.front.isDigit then l ++ suf else l

/-- A handler body as one `AInstr` list. -/
def bodyInstrs (p : Prog) : List AInstr := p.flatMap (fun o => (Op.instrs? o).getD [])

/-- The two bodies as `AInstr`, for the pressure analysis and the x86 pipeline. -/
def handlerBodies : List (List AInstr) := covered.map bodyInstrs

/-- The covered handlers' sizes as `AInstr`. -/
theorem handler_sizes :
    handlerBodies.map List.length =
      [58, 57, 22, 22, 22, 22, 22, 13, 26, 17, 22, 22, 22, 22,
       14, 18, 23, 23, 22, 26, 28, 20, 20, 23, 19,
       27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 29, 29,
       18, 18, 18, 16, 29,
       5, 3, 1, 69, 70, 25, 32, 49, 67, 74, 116, 25, 17, 18, 28, 26, 60,
       63, 35, 27, 100,
       92, 92, 92, 135, 139, 187, 174, 170, 170] := by
  native_decide

/-- **Totality over the handlers.** `Op.instrs?` has an arm for every
    constructor (the compiler rejects a fallback as redundant); the only `none`s
    left are out-of-range parameters that no handler uses (`argReg r` for r ≥ 4,
    `sstoreSentry n` for n ≥ 2^16). So every op of every handler body has an
    `AInstr` form, and `Op.emit` is a specification the derived text is checked
    against, not an emitter any handler file reaches. -/
theorem instrs_total_over_handlers :
    (covered.flatten ++ standaloneOps).all (fun o => (Op.instrs? o).isSome) = true := by
  native_decide

/-- The ARM register names the x86-64 call programs use for arguments have
    exactly the SysV argument registers as their x86 homes. -/
theorem sysv_arg_homes :
    argRegs.all (fun (r, h) => Evm.CL.Lowering.x86Reg? r == some h) = true ∧
    [0, 1, 2, 3].all (fun i => (sysvReg i).bind Evm.CL.Lowering.x86Reg? ==
      some (["rdi", "rsi", "rdx", "rcx"].getD i "")) = true := by native_decide

/-- rsp (mod 16) along a body entered at ≡ 0, counting only the stack-moving
    forms; every `blSym` must sit at ≡ 0 so the callee sees ≡ 8. -/
def helperCallsAligned (p : List AInstr) : Bool :=
  (p.foldl (fun (acc : Nat × Bool) i =>
    let (sp, ok) := acc
    match i with
    | .spSub n => ((sp + 16 - n % 16) % 16, ok)
    | .spAdd n => ((sp + n) % 16, ok)
    | .blSym _ | .blr _ => (sp, ok && sp == 0)
    | _ => (sp, ok)) (0, true)).2

/-! ## Callback arguments are defined by the op that passes them

EXTCODECOPY's ARM64 cb op passed `len` (the fifth argument, x4) without loading it:
the gas gadget before it happened to leave len.l0 there, until f812945 rebuilt that
gadget on `memRangeInstrs` and x4 reached the host stale — a copy length of
8·10^18, a memset past the memory arena (mainnet 4,972,698 tx 17). `Op.denote`
models a callback coarsely (sp −= 4, gas/memory host effects), so no theorem saw
the argument. This is the instruction-level check that does.

A must-analysis over the flattened body, per path: `D` is the set of registers
holding a value computed from the frame's live-in roles (an instruction defines
its destinations iff every register it reads is in `D`; a call kills the
caller-saved registers and defines x0), and `W` ⊆ `D` is what the CURRENT CALL
GROUP has written — the call's own op plus the dedicated argument-marshalling ops
right before it; `W` is emptied at the start of every other op. At every call
(`blr` through a vtable slot, `bl` to a C helper) the callee must have a known
arity and all its argument registers, and the `blr` target, must be in `W`. So
an argument cannot be inherited from a previous gadget (the pre-f812945 design,
correct but fragile) and cannot be left unset (the post-f812945 bug). -/

/-- Registers an instruction writes. -/
def defs : AInstr → List Reg
  | .subImm d _ _ | .addLsl5 d _ _ | .ldrOff d _ _ | .ldrBase d _ | .movImm d _ | .orr3 d _ _
  | .adds d _ _ | .cselHi d _ _ | .subsReg d _ _ | .addImm d _ _ | .subReg d _ _ | .addReg d _ _
  | .mulReg d _ _ | .clzReg d _ | .lsrImm d _ _ | .lslImm d _ _ | .addLsr d _ _ _ | .addLsl d _ _ _
  | .addsImm d _ _ | .rev d _ | .movReg d _ | .adcs d _ _ | .adc d _ _ | .sbcs d _ _ | .sbc d _ _
  | .and3 d _ _ | .eor3 d _ _ | .subsImm d _ _ | .mvn d _ | .cset d _ | .ldrbReg d _ _
  | .movImmW d _ | .addSp d _ | .ldrSp d _ | .ldrbOff d _ _ | .loadSymAddr d _
  | .cselNe d _ _ | .movzImm d _ | .madd d _ _ _ | .ldrWSp d _ | .andImmHex d _ _ | .csinvEqZr d _
  | .movFromSp d | .ldrLsl3 d _ _ | .loadSymValue d _ | .loadSymGotValue d _ | .movkImm d _ _
  | .addSpReg d | .adrLbl d _ | .csel d _ _ _ | .cselZrA d _ _ | .cselZrB d _ _ | .eorImm1 d _ => [d]
  | .ldpOff a b _ _ | .ldpPostSp a b _ | .ldpSp a b _ => [a, b]
  | .ldpFpLr => [.x29, .x30]
  | _ => []

/-- Registers an instruction reads (flags, sp and memory are not registers). -/
def uses : AInstr → List Reg
  | .subImm _ a _ | .addImm _ a _ | .clzReg _ a | .lsrImm _ a _ | .lslImm _ a _ | .addsImm _ a _
  | .rev _ a | .movReg _ a | .subsImm _ a _ | .mvn _ a | .andImmHex _ a _ | .csinvEqZr _ a
  | .cselZrA _ a _ | .cselZrB _ a _ | .eorImm1 _ a | .ldrOff _ a _ | .ldrBase _ a | .ldrbOff _ a _
  | .ldpOff _ _ a _ | .cmpImm a _ | .cbnzOog a | .cbzLbl a _ | .cbnzLbl a _ | .cbzWLbl a _
  | .cbnzWLbl a _ | .cbnzSym a _ | .cbnzSymW a _ | .cmpImmWHex a _ | .brReg a | .blr a
  | .strZr a _ | .strWSp a _ | .strSp a _ | .movToSp a | .movkImm a _ _ | .addSpReg a
  | .spAddReg a | .spSubReg a | .tstImm a _ => [a]
  | .addLsl5 _ a b | .orr3 _ a b | .adds _ a b | .cmpReg a b | .cselHi _ a b | .subsReg _ a b
  | .subReg _ a b | .addReg _ a b | .mulReg _ a b | .addLsr _ a b _ | .addLsl _ a b _
  | .strOff a b _ | .adcs _ a b | .adc _ a b | .sbcs _ a b | .sbc _ a b | .and3 _ a b
  | .eor3 _ a b | .subsZr a b | .sbcsZr a b | .ldrbReg _ a b | .strbOff a b _
  | .cselNe _ a b | .stpSp a b _ | .stpPreSp a b _ | .ldrLsl3 _ a b | .strBase a b
  | .strbBase a b | .csel _ a b _ => [a, b]
  | .stpOff a b c _ | .strbReg a b c | .madd _ a b c => [a, b, c]
  | .stpFpLr => [.x29, .x30]
  | _ => []

/-- Live at handler entry: the frame's roles (state, pc, gas, sp, stack and code
    bases, continuation, TOS/NOS caches, callee-saved pairs). Never x0-x5, x14-x17. -/
def liveIn : List Reg :=
  [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x20, .x21, .x22, .x23, .x24, .x26, .x27,
   .x19, .x25, .x28, .x29, .x30]

/-- Killed by a call: x0-x17 (AAPCS64); on x86-64 the NOS names are memory and survive. -/
def callerSaved (x86 : Bool) : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17] ++
  (if x86 then [] else [.x10, .x11, .x12, .x13])

/-- Argument register i: AAPCS64 x0-x5, SysV through `sysvReg`. -/
def argRegOn (x86 : Bool) (i : Nat) : Option Reg :=
  if x86 then sysvReg i else [Reg.x0, .x1, .x2, .x3, .x4, .x5][i]?

/-- Arity by vtable slot — `EvmCallbacks` in c/evm_state.h, eight bytes a slot. -/
def cbArity : Nat → Option Nat
  | 0 => some 4 | 8 => some 4 | 16 => some 3 | 24 => some 3 | 32 => some 3 | 40 => some 3
  | 48 => some 3 | 56 => some 5 | 64 => some 3 | 72 => some 6 | 80 => some 3 | 88 => some 3
  | 96 => some 3 | 104 => some 3 | 112 => some 5 | _ => none

/-- Arity of the C helpers the bodies `bl` (c/eita_compute.c, c/tx_state.c). -/
def helperArity (h : String) : Option Nat :=
  if ["_eita_helper_mul", "_eita_helper_div", "_eita_helper_sdiv", "_eita_helper_mod",
      "_eita_helper_smod", "_eita_helper_shl", "_eita_helper_shr", "_eita_helper_sar",
      "_eita_helper_byte", "_eita_helper_signextend", "_eita_helper_exp",
      "_eita_helper_calldataload", "_eita_helper_returndata_to_mem"].contains h then some 3
  else if ["_eita_helper_addmod", "_eita_helper_mulmod", "_eita_helper_keccak256",
           "_eita_helper_calldatacopy", "_eita_helper_codecopy", "_eita_helper_returndatacopy",
           "_eita_helper_mcopy", "_eita_ts_tload"].contains h then some 4
  else if h == "_eita_ts_tstore" then some 5 else none

/-- The ops that only stage a callback's arguments (or open its frame), and the
    call ops they feed: a call group is a run of these ending in the call. -/
def inCallGroup : Op → Bool
  | .loadCtx _ | .loadCtxVia14 _ | .loadTxStateCtx _ | .argStateField _ _ | .argStackPtr _ _
  | .argScratch _ | .argStateBase _ | .cbEnter _ | .cbSlot _ | .cbDirect _ => true
  | _ => false

/-- A body flattened, each instruction tagged `true` when it opens an op that
    starts a new call group (emptying `W`). -/
def taggedBody (lower : Op → Option (List AInstr)) (p : Prog) : List (Bool × AInstr) :=
  p.flatMap fun o => match (lower o).getD [] with
    | [] => []
    | i :: is => (!inCallGroup o, i) :: is.map ((false, ·))

/-- The local label a branch goes to, if any. -/
def localBranch : AInstr → Option String
  | .bLbl l | .cbzLbl _ l | .cbnzLbl _ l | .bcLbl _ l | .blsLbl l | .cbzWLbl _ l | .cbnzWLbl _ l => some l
  | _ => none

def noFallthrough : AInstr → Bool
  | .bLbl _ | .bSymU _ | .brCont | .brReg _ | .ret | .bFar _ | .bTramp _ => true
  | _ => false

/-- Where a branch at `j` to local label `l` lands: `7f`/`7b` is the next/previous
    `7:`, a named label its definition. -/
def labelTarget (is : List AInstr) (j : Nat) (l : String) : Option Nat :=
  let cs := l.toList
  let numeric := cs.length > 1 && cs.dropLast.all Char.isDigit &&
    (cs.getLast? == some 'f' || cs.getLast? == some 'b')
  let name := if numeric then String.ofList cs.dropLast else l
  let ds := (List.range is.length).filter (fun k => is[k]? == some (.label name))
  if numeric && cs.getLast? == some 'b' then (ds.filter (· < j)).getLast?
  else (ds.filter (fun k => !numeric || j < k)).head?

/-- `(D, W)`, or `none` where no path has reached yet. -/
abbrev DefState := Option (List Reg × List Reg)

def meet : DefState → DefState → DefState
  | none, s | s, none => s
  | some (d, w), some (d', w') => some (d.filter d'.contains, w.filter w'.contains)

/-- One instruction's transfer: define the destinations iff every source is
    defined, else undefine them; a call kills the caller-saved set and yields x0. -/
def step (x86 : Bool) (reset : Bool) (i : AInstr) : List Reg × List Reg → List Reg × List Reg
  | (d, w) =>
    let w := if reset then [] else w
    let ok := (uses i).all d.contains
    let upd (s : List Reg) : List Reg :=
      if ok then s ++ (defs i).filter (fun r => !s.contains r) else s.filter (fun r => !(defs i).contains r)
    let kill (s : List Reg) : List Reg := .x0 :: s.filter (fun r => !(callerSaved x86).contains r)
    match i with
    | .blSym _ | .blr _ | .blFar _ => (kill (upd d), kill (upd w))
    | _ => (upd d, upd w)

/-- The state before each instruction, iterated to a fixpoint (fuel-bounded;
    `meet` only shrinks, so a pass without change is the answer). -/
def reach (x86 : Bool) (tb : List (Bool × AInstr)) : Array DefState :=
  let is : List AInstr := tb.map (·.2)
  let n := is.length
  let pass (st : Array DefState) : Array DefState := Id.run do
    let mut st := st
    for j in [0:n] do
      match st[j]!, tb[j]? with
      | some s, some (reset, i) =>
        let out : DefState := some (step x86 reset i s)
        if !noFallthrough i then st := st.set! (j + 1) (meet st[j + 1]! out)
        match (localBranch i).bind (labelTarget is j) with
        | some k => st := st.set! k (meet st[k]! out)
        | none => pure ()
      | _, _ => pure ()
    return st
  let rec fix : Nat → Array DefState → Array DefState
    | 0, st => st
    | fuel + 1, st => let st' := pass st; if st' == st then st else fix fuel st'
  fix (n + 1) (((List.replicate (n + 1) (none : DefState)).toArray).set! 0 (some (liveIn, [])))

/-- The vtable slot a `blr r` at `j` calls through: r's last write before `j` is
    `ldr r, [r, #slot]` right after `ldr r, [x20, #496]`. -/
def slotOf (is : List AInstr) (j : Nat) (r : Reg) : Option Nat :=
  match (List.range j).reverse.find? (fun k => ((is[k]?.map defs).getD []).contains r) with
  | some (k + 1) =>
    match is[k + 1]?, is[k]? with
    | some (.ldrOff d b slot), some (.ldrOff d' .x20 496) =>
      if d == r && b == r && d' == r then some slot else none
    | _, _ => none
  | _ => none

/-- The calls in a tagged body whose callee is unknown or whose arguments (or
    `blr` target) are not all written by their own call group — empty when sound. -/
def callArgsBad (x86 : Bool) (tb : List (Bool × AInstr)) : List Nat :=
  let is : List AInstr := tb.map (·.2)
  let st := reach x86 tb
  let argsOk (w : List Reg) (a : Nat) : Bool :=
    (List.range a).all (fun i => (argRegOn x86 i).any w.contains)
  (List.range is.length).filter fun j =>
    match is[j]?, st[j]! with
    | some (.blr r), some (_, w) =>
      !(match (slotOf is j r).bind cbArity with
        | some a => w.contains r && argsOk w a
        | none => false)
    | some (.blSym h), some (_, w) =>
      !(match helperArity h with | some a => argsOk w a | none => false)
    | _, _ => false

/-- Both backends' lists of a body, tagged (`Op.instrs?` / `Op.instrsX86?`). -/
def callArgsDefined (p : Prog) : Bool :=
  p.all (fun o => (Op.instrs? o).isSome && (Op.instrsX86? o).isSome) &&
  (callArgsBad false (taggedBody Op.instrs? p)).isEmpty &&
  (callArgsBad true (taggedBody Op.instrsX86? p)).isEmpty

/-! ## The register-cached stack stays coherent

On ARM64 the top two stack words are cached in registers — x6-x9 (TOS) and x10-x13
(NOS) — and the stack memory holds every word as well. A body is entered with x6-x9 =
stack[sp-1] and x10-x13 = stack[sp-2] (`_eita_run` loads them, every body keeps them)
and must leave by `br x27` the same way for the sp it leaves (TOS only if sp ≥ 1, NOS
only if sp ≥ 2). CLZ broke it: it computed in x10-x13 ("free in a unary op") and kept
no NOS, so the next AND read the clobbered x10 (mainnet 26,042,126 tx 135; x86-64
caches no NOS and was right). `Op.denote` keeps `nos` as a field of its own, so
`clz_correct` held — the emit/denote gap of the #260 family.

The check is a value numbering over the flattened body, per path: a register or stack
limb holds a symbolic value (`CV`) — an entry stack limb, an sp-relative index or stack
address (`sub x14, x23, #k` / `add x14, x24, x14, lsl #5`), or the opaque result of one
instruction; a join of two different values is a `phi` keyed by both, so a register
and a limb that were equal on both sides stay equal. A store to a stack address moves
the stored value into the limb, a load reads it; a call kills the caller-saved
registers (x10-x13 among them on ARM64) and, by the ABI of the C helpers and host
callbacks, writes no word of the frame's stack; stores through any other base are not
the stack (state fields, EVM memory, the C scratch frame). `cmp x23, #k ; b.lt` is the
guarded reload: on its taken edge sp < k, so the words below are not owed. At every
`br x27` the cached registers must equal the limbs they cache.

With `x86 := true` the same analysis reads the x86-64 bodies (`Op.instrsX86?`): sp is a
byte offset (an immediate is whole words, or the path is `bad`), a stack address is
`sub d, x23, #32k` / `add d, x24, d`, a call kills the SysV caller-saved homes, and
only the TOS (x6-x9, r8-r11) is register-cached, so only it is checked. -/

inductive CV where
  | cell (c : Int) (l : Nat)       -- limb l of stack word sp₀+c as it was at entry
  | idx (c : Int)                  -- the integer sp₀+c
  | addr (c : Int)                 -- the address of stack word sp₀+c
  | fresh (j : Nat) (r : Reg)      -- what instruction j wrote into r
  | phi (j : Nat) (a b : CV)       -- a at one predecessor of j, b at the other
  deriving DecidableEq, Repr, Inhabited

/-- One path's state: sp − sp₀, the known register values, the stack limbs written so
    far (the rest hold their entry value), the known bound sp < `lt`, and `bad` when the
    body moved sp in a way the analysis does not follow. -/
structure CS where
  off  : Int
  regs : List (Reg × CV)
  mem  : List ((Int × Nat) × CV)
  lt   : Option Int
  bad  : Bool
  deriving DecidableEq, Repr, Inhabited

def tosRegs : List Reg := [.x6, .x7, .x8, .x9]
def nosRegs : List Reg := [.x10, .x11, .x12, .x13]

def CS.rv (s : CS) (r : Reg) : Option CV :=
  if r == .x23 then some (.idx s.off) else (s.regs.find? (·.1 == r)).map (·.2)
def CS.mv (s : CS) (c : Int) (l : Nat) : CV :=
  ((s.mem.find? (·.1 == (c, l))).map (·.2)).getD (.cell c l)
def CS.setR (s : CS) (r : Reg) (v : Option CV) : CS :=
  { s with regs := (match v with | some v => [(r, v)] | none => []) ++ s.regs.filter (·.1 != r) }
def CS.setM (s : CS) (c : Int) (l : Nat) (v : CV) : CS :=
  { s with mem := ((c, l), v) :: s.mem.filter (·.1 != (c, l)) }

def CS.entry : CS :=
  { off := 0, mem := [], lt := none, bad := false,
    regs := (tosRegs.zipIdx.map fun (r, l) => (r, CV.cell (-1) l)) ++
            (nosRegs.zipIdx.map fun (r, l) => (r, CV.cell (-2) l)) }

/-- The stack word a base register addresses, if it is one. -/
def CS.word (s : CS) (b : Reg) : Option Int :=
  match s.rv b with | some (.addr c) => some c | _ => none

/-- Store `r` into limb l of word c (an unknown register gets a name first). -/
def CS.store (j : Nat) (s : CS) (c : Int) (l : Nat) (r : Reg) : CS :=
  match s.rv r with
  | some v => s.setM c l v
  | none => (s.setR r (some (.fresh j r))).setM c l (.fresh j r)

/-- An sp immediate in words: as is on ARM64; on x86-64 (bytes) only a whole word. -/
def spWords (x86 : Bool) (k : Int) : Option Int :=
  if !x86 then some k else if k % 32 == 0 then some (k / 32) else none

/-- The transfer of instruction j. -/
def cstep (j : Nat) (i : AInstr) (s : CS) (x86 : Bool := false) : CS :=
  let writeAll (s : CS) : CS := (defs i).foldl (fun s d => s.setR d (some (.fresh j d))) s
  let other (s : CS) : CS := if (defs i).contains .x23 then { s with bad := true } else writeAll s
  match i with
  | .subImm .x23 .x23 k => match spWords x86 k with
      | some k => { s with off := s.off - k, lt := s.lt.map (· - k) } | none => { s with bad := true }
  | .addImm .x23 .x23 k => match spWords x86 k with
      | some k => { s with off := s.off + k, lt := s.lt.map (· + k) } | none => { s with bad := true }
  | .subImm d .x23 k => s.setR d ((spWords x86 k).map (fun k => .idx (s.off - k)) <|> some (.fresh j d))
  | .addImm d .x23 k => s.setR d ((spWords x86 k).map (fun k => .idx (s.off + k)) <|> some (.fresh j d))
  | .addReg d .x24 a =>
      if !x86 then other s else
      s.setR d (match s.rv a with | some (.idx c) => some (.addr c) | _ => some (.fresh j d))
  | .addLsl5 d .x24 a =>
      s.setR d (match s.rv a with | some (.idx c) => some (.addr c) | _ => some (.fresh j d))
  | .movReg d a => s.setR d (s.rv a)
  | .ldpOff a b base o =>
      match s.word base with
      | some c => if o == 0 || o == 16 then (s.setR a (some (s.mv c (o / 8)))).setR b (some (s.mv c (o / 8 + 1)))
                  else writeAll s
      | none => writeAll s
  | .ldrOff d base o =>
      match s.word base with
      | some c => if o % 8 == 0 && o < 32 then s.setR d (some (s.mv c (o / 8))) else writeAll s
      | none => writeAll s
  | .ldrBase d base =>
      match s.word base with | some c => s.setR d (some (s.mv c 0)) | none => writeAll s
  | .stpOff a b base o =>
      match s.word base with
      | some c => if o == 0 || o == 16 then (CS.store j (CS.store j s c (o / 8) a) c (o / 8 + 1) b)
                  else { s with bad := true }
      | none => s
  | .strOff r base o =>
      match s.word base with
      | some c => if o % 8 == 0 && o < 32 then CS.store j s c (o / 8) r else { s with bad := true }
      | none => s
  | .strBase r base => match s.word base with | some c => CS.store j s c 0 r | none => s
  | .blSym _ | .blr _ | .blFar _ =>
      let s := (callerSaved x86).foldl (fun s r => s.setR r none) s
      s.setR .x0 (some (.fresh j .x0))
  | _ => other s

/-- Join at j: equal values stay, different ones become `phi j`; a side on which the TOS
    (sp < 1) or NOS (sp < 2) word is not owed takes the other side's registers and limb. -/
def cmeet (j : Nat) (a b : CS) : CS :=
  if a.bad || b.bad || a.off != b.off then { a with bad := true } else
  let vac (s : CS) (k : Int) : Bool := s.lt.any (· ≤ k)
  let grp (r : Reg) : Int := if tosRegs.contains r then 1 else if nosRegs.contains r then 2 else 0
  let pick (k : Int) (va vb : Option CV) : Option CV :=
    if k > 0 && vac a k then vb else if k > 0 && vac b k then va else
    match va, vb with
    | some x, some y => some (if x == y then x else .phi j x y)
    | _, _ => none
  let rs := (a.regs.map (·.1) ++ b.regs.map (·.1)).eraseDups
  let ms := (a.mem.map (·.1) ++ b.mem.map (·.1)).eraseDups
  { off := a.off, bad := false,
    lt := match a.lt, b.lt with | some x, some y => some (max x y) | _, _ => none,
    regs := rs.filterMap fun r => (pick (grp r) (a.rv r) (b.rv r)).map (r, ·),
    mem := ms.filterMap fun (c, l) =>
      let k : Int := if c == a.off - 1 then 1 else if c == a.off - 2 then 2 else 0
      (pick k (some (a.mv c l)) (some (b.mv c l))).map ((c, l), ·) }

/-- The out-edges of instruction j: (target, state on that edge). -/
def cedges (is : List AInstr) (j : Nat) (i : AInstr) (s : CS) (x86 : Bool := false) : List (Nat × CS) :=
  let out := cstep j i s x86
  let taken : CS :=
    match i, (if j = 0 then none else is[j - 1]?) with
    | .bcLbl .lt _, some (.cmpImm .x23 k) =>
        match spWords x86 k with
        | some k => { out with lt := some (match out.lt with | some x => min x k | none => k) }
        | none => out
    | _, _ => out
  (if noFallthrough i then [] else [(j + 1, out)]) ++
  (match (localBranch i).bind (labelTarget is j) with | some k => [(k, taken)] | none => [])

/-- The state before each instruction (Jacobi iteration over the predecessors, so a
    join is recomputed, never re-joined; the bodies are acyclic). -/
def creach (is : List AInstr) (x86 : Bool := false) : Array (Option CS) :=
  let n := is.length
  let pass (st : Array (Option CS)) : Array (Option CS) := Id.run do
    let mut nxt : Array (Option CS) := (List.replicate (n + 1) none).toArray
    nxt := nxt.set! 0 (some CS.entry)
    for j in [0:n] do
      match st[j]!, is[j]? with
      | some s, some i =>
        for (k, e) in cedges is j i s x86 do
          if k ≤ n then nxt := nxt.set! k (match nxt[k]! with | none => some e | some x => some (cmeet k x e))
      | _, _ => pure ()
    return nxt
  let rec fix : Nat → Array (Option CS) → Array (Option CS)
    | 0, st => st
    | fuel + 1, st => let st' := pass st; if st' == st then st else fix fuel st'
  fix (n + 2) (((List.replicate (n + 1) (none : Option CS)).toArray).set! 0 (some CS.entry))

/-- Indices of the `br x27` exits where a cached register is not the limb it caches
    (or the analysis lost sp) — empty when the body keeps the cache coherent. -/
def cacheIncoherent (is : List AInstr) (x86 : Bool := false) : List Nat :=
  let st := creach is x86
  let ok (s : CS) (rs : List Reg) (c : Int) : Bool :=
    rs.zipIdx.all fun (r, l) => s.rv r == some (s.mv c l)
  (List.range is.length).filter fun j =>
    match is[j]?, st[j]! with
    | some .brCont, some s =>
        s.bad || !((s.lt.any (· ≤ 1) || ok s tosRegs (s.off - 1)) &&
                   (x86 || s.lt.any (· ≤ 2) || ok s nosRegs (s.off - 2)))
    | _, _ => false

/-- Every op lowers, and the ARM64 body keeps the stack cache coherent. -/
def cacheCoherent (p : Prog) : Bool :=
  p.all (fun o => (Op.instrs? o).isSome) && (cacheIncoherent (bodyInstrs p)).isEmpty

end Evm.CL.OpInstrs
