/-
  Evm.CL.RV32.Items — the lowering's arithmetic core as INSTRUCTIONS.

  `Lower` prints text; `Sem` gives meaning to `RvInsn`. This module is the
  bridge: the same sequences built as data, so they can be executed by the
  machine and proved — with a gate (`items_match_the_emitted_text`) saying that
  for every instruction the interpreter actually emits, the structured form
  prints exactly the text the production path prints.

  That gate is the point. `AsmItems` records what happens without one: "every
  gadget that appears in both paths was written twice, and the two copies could
  disagree — which is not hypothetical". Here the two copies are checked against
  each other over the real programs, so a proof about `items` is a proof about
  the file that ships. The eventual shape is for `Lower` to print FROM this
  type; until each form is converted, this is the subset that is proved.
-/

import Evm.CL.RV32.Sem
import Evm.CL.RV32.Lower

namespace Evm.CL.RV32.Items

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.RV32 Evm.CL.RV32.Asm

/-- A register by its ABI name — the bridge to `Lower`'s string tables, which
    `Asm.regOfName_regName` shows loses nothing. -/
def rv (s : String) : RvReg := (regOfName s).getD 0

def loR (r : Reg) : RvReg := rv (lo r)
def hiR (r : Reg) : RvReg := rv (hi r)
def carryR : RvReg := rv carry
def stateR : RvReg := rv state
def nosLoR : RvReg := rv nos.lo
def nosHiR : RvReg := rv nos.hi

/-- `Lower.addc32`, as items. -/
def addc32I (n : Nat) (D P Q : RvReg) (cin cout : Bool) : List RvItem :=
  if D == P && D == Q then
    (if cout then [RvItem.insn (.srli carryR P 31)] else []) ++
    [RvItem.insn (.add D P P)] ++
    (if cin then [RvItem.insn (.add D D carryR)] else [])
  else
    let A := if D == Q then Q else P
    let B := if D == Q then P else Q
    if !cin then
      [RvItem.insn (.add D A B)] ++
      (if cout then [RvItem.insn (.sltu carryR D B)] else [])
    else if !cout then
      [RvItem.insn (.add D A carryR), RvItem.insn (.add D D B)]
    else
      [ RvItem.insn (.add D A carryR), RvItem.insn (.sltu carryR D carryR),
        RvItem.insn (.add D D B), RvItem.insn (.bgeu D B s!".Lk{n}"),
        RvItem.insn (.addi carryR carryR 1), RvItem.label s!".Lk{n}" ]

/-- `Lower.subb32`, as items (the aliased case spills a second victim). -/
def subb32I (D P Q : RvReg) (bin bout : Bool) : List RvItem :=
  if !bin then
    (if bout then [RvItem.insn (.sltu carryR P Q)] else []) ++
    [RvItem.insn (.sub D P Q)]
  else if !bout then
    [RvItem.insn (.sub D P Q), RvItem.insn (.sub D D carryR)]
  else
    let v := rv (pickFree [regName D, regName P, regName Q, carry])
    if D == Q then
      let v2 := rv (pickFree [regName D, regName P, regName Q, carry, regName v])
      [ RvItem.insn (.sw v 608 stateR), RvItem.insn (.sw v2 612 stateR),
        RvItem.insn (.mv v2 Q),
        RvItem.insn (.sltu v P carryR), RvItem.insn (.sub D P carryR),
        RvItem.insn (.sltu carryR D v2), RvItem.insn (.sub D D v2),
        RvItem.insn (.orr carryR carryR v),
        RvItem.insn (.lw v 608 stateR), RvItem.insn (.lw v2 612 stateR) ]
    else
      [ RvItem.insn (.sw v 608 stateR),
        RvItem.insn (.sltu v P carryR), RvItem.insn (.sub D P carryR),
        RvItem.insn (.sltu carryR D Q), RvItem.insn (.sub D D Q),
        RvItem.insn (.orr carryR carryR v),
        RvItem.insn (.lw v 608 stateR) ]

/-- The 64-bit pair operations: the low half always produces the carry the high
    half consumes; `cin`/`cout` are the external ones. -/
def add64I (n : Nat) (d a b : Reg) (cin cout : Bool) : List RvItem :=
  addc32I (2 * n) (loR d) (loR a) (loR b) cin true ++
  addc32I (2 * n + 1) (hiR d) (hiR a) (hiR b) true cout

def sub64I (d a b : Reg) (bin bout : Bool) : List RvItem :=
  subb32I (loR d) (loR a) (loR b) bin true ++
  subb32I (hiR d) (hiR a) (hiR b) true bout

/-- `Lower.nosLoad`. -/
def nosLoadI (limb : Nat) : List RvItem :=
  [ RvItem.insn (.add nosHiR (rv stackBase) (rv spReg)),
    RvItem.insn (.lw nosLoR (nosOff limb) nosHiR),
    RvItem.insn (.lw nosHiR (nosOff limb + 4) nosHiR) ]

/-- `Lower.loadWords`, structurally: a multi-word load off one base, with the
    base's own slot loaded LAST, so that `ldr d, [d]` does not destroy its own
    address between the two halves. -/
def loadWordsI (b : RvReg) (slots : List (RvReg × Nat)) : List RvItem :=
  let deferred := slots.filter (fun s => s.1 == b)
  let first := slots.filter (fun s => s.1 != b)
  (first ++ deferred).map (fun s => RvItem.insn (.lw s.1 s.2 b))

/-- The forms converted so far. `none` is "still string-only", not "unlowered":
    `Lower` handles many more, they are simply not yet provable. -/

def itemsBody (n : Nat) : AInstr → Option (List RvItem)
  | .addReg d a b  => some (add64I n d a b false false)
  | .adds d a b    => some (add64I n d a b false true)
  | .adcs d a b    => some (add64I n d a b true true)
  | .adc d a b     => some (add64I n d a b true false)
  | .subReg d a b  => some (sub64I d a b false false)
  | .subsReg d a b => some (sub64I d a b false true)
  | .sbcs d a b    => some (sub64I d a b true true)
  | .sbc d a b     => some (sub64I d a b true false)
  | .movReg d a    => some [.insn (.mv (loR d) (loR a)), .insn (.mv (hiR d) (hiR a))]
  | .mvn d a       => some [.insn (.notr (loR d) (loR a)), .insn (.notr (hiR d) (hiR a))]
  | .orr3 d a b    => some [.insn (.orr (loR d) (loR a) (loR b)),
                            .insn (.orr (hiR d) (hiR a) (hiR b))]
  | .and3 d a b    => some [.insn (.andr (loR d) (loR a) (loR b)),
                            .insn (.andr (hiR d) (hiR a) (hiR b))]
  | .eor3 d a b    => some [.insn (.xorr (loR d) (loR a) (loR b)),
                            .insn (.xorr (hiR d) (hiR a) (hiR b))]
  | .ldrOff d b o  => some (loadWordsI (loR b) [(loR d, o), (hiR d, o + 4)])
  | .ldrBase d b   => some (loadWordsI (loR b) [(loR d, 0), (hiR d, 4)])
  | .strOff s b o  => some [.insn (.sw (loR s) o (loR b)), .insn (.sw (hiR s) (o + 4) (loR b))]
  | _ => none

/-- …with the NOS load in front, as `Lower.emitOne` does. -/
def items (n : Nat) (it : AInstr) : Option (List RvItem) :=
  match nosLimbsOf it with
  | []  => itemsBody n it
  | [l] => (itemsBody n it).map (fun b => nosLoadI l ++ b)
  | _   => none

/-! ## The gate -/

/-- Every `AInstr` the interpreter's handlers and the structured gadgets
    contain. -/
def allEmitted : List AInstr :=
  ((rv32Streams.flatMap (fun (_, is) => is)) ++ gadgetSet.flatten).eraseDups

/-- **Where a form is converted, the structured version prints exactly the text
    the production path prints** — over every instruction the interpreter
    emits, at a fixed label index. So a theorem about `items` is a theorem
    about the emitted file. -/
theorem items_match_the_emitted_text :
    allEmitted.all (fun it =>
      match items 7 it with
      | some is => Asm.emitProg is == emitOne 7 it
      | none => true) = true := by
  native_decide

/-- How much of the emitted instruction stream is structured (and so provable)
    so far — a ratchet, like the handler coverage. -/
def convertedCount : Nat :=
  (allEmitted.filter (fun it => (items 7 it).isSome)).length

example : 0 < convertedCount := by native_decide

end Evm.CL.RV32.Items
