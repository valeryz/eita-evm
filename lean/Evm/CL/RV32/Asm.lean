/-
  Evm.CL.RV32.Asm — rv32 instructions as DATA, so they can be given a meaning.

  `Evm.CL.RV32.Lower` prints text, and a string has no denotation — the gap
  `AsmItems` names for ARM64 ("nothing can be derived for a string") and the
  reason x86-64's chain is `XInsn` → `X86Print` → `X86Sem`. This module is the
  rv32 instruction type, with a printer that reproduces the lowering's text
  exactly, so `Lower` can be re-expressed over it one form at a time and
  `RV32.Sem` can say what each one does.

  The vocabulary is what the lowering actually emits — measured from the
  emitted file, 28 mnemonics — not the ISA. An instruction the lowering never
  produces is one the semantics never has to model.
-/

import Std.Tactic.BVDecide

namespace Evm.CL.RV32.Asm

/-- A register, by number. `x0` reads as zero and discards writes, which the
    lowering relies on: it is the high half of every 32-bit role. -/
abbrev RvReg := Fin 32

/-- The ABI names, which is how the lowering and the assembler spell them. -/
def regName (r : RvReg) : String :=
  match r.val with
  | 0 => "zero" | 1 => "ra" | 2 => "sp" | 3 => "gp" | 4 => "tp"
  | 5 => "t0" | 6 => "t1" | 7 => "t2"
  | 8 => "s0" | 9 => "s1"
  | 10 => "a0" | 11 => "a1" | 12 => "a2" | 13 => "a3"
  | 14 => "a4" | 15 => "a5" | 16 => "a6" | 17 => "a7"
  | 18 => "s2" | 19 => "s3" | 20 => "s4" | 21 => "s5" | 22 => "s6" | 23 => "s7"
  | 24 => "s8" | 25 => "s9" | 26 => "s10" | 27 => "s11"
  | 28 => "t3" | 29 => "t4" | 30 => "t5" | _ => "t6"

/-- The ABI name back to a number, so the lowering's existing string tables can
    be read as registers while it is converted form by form. -/
def regOfName (s : String) : Option RvReg :=
  (List.finRange 32).find? (fun r => regName r == s)

/-- The instruction subset the lowering emits. Branch targets are names (a local
    label or an external symbol); `Sem` resolves them within a fragment. -/
inductive RvInsn where
  -- three-register arithmetic and logic
  | add   (d a b : RvReg)
  | sub   (d a b : RvReg)
  | orr   (d a b : RvReg)
  | andr  (d a b : RvReg)
  | xorr  (d a b : RvReg)
  | sltu  (d a b : RvReg)
  | mul   (d a b : RvReg)
  | mulhu (d a b : RvReg)
  -- register / immediate
  | addi  (d a : RvReg) (imm : Int)
  | sltiu (d a : RvReg) (imm : Nat)
  | slli  (d a : RvReg) (sh : Nat)
  | srli  (d a : RvReg) (sh : Nat)
  | li    (d : RvReg) (imm : Int)
  | mv    (d a : RvReg)
  | notr  (d a : RvReg)
  -- memory (word and unsigned byte)
  | lw    (d : RvReg) (off : Int) (base : RvReg)
  | sw    (s : RvReg) (off : Int) (base : RvReg)
  | lbu   (d : RvReg) (off : Int) (base : RvReg)
  | sb    (s : RvReg) (off : Int) (base : RvReg)
  -- branches and jumps
  | beqz  (a : RvReg) (target : String)
  | bnez  (a : RvReg) (target : String)
  | beq   (a b : RvReg) (target : String)
  | bne   (a b : RvReg) (target : String)
  | bltu  (a b : RvReg) (target : String)
  | bgeu  (a b : RvReg) (target : String)
  | blt   (a b : RvReg) (target : String)
  | bge   (a b : RvReg) (target : String)
  | j     (target : String)
  | call  (target : String)
  | jalr  (a : RvReg)
  | jr    (a : RvReg)
  | ret
  deriving DecidableEq, Repr

/-- A line of the emitted file. -/
inductive RvItem where
  | insn  (i : RvInsn)
  | label (l : String)
  /-- A form the lowering cannot handle: the loud marker, carried as data. -/
  | unlowered (why : String)
  deriving DecidableEq, Repr

/-- The mnemonic column the lowering uses: four spaces, then a padded mnemonic. -/
def pad (m : String) : String :=
  m ++ (if m.length < 4 then "".pushn ' ' (5 - m.length) else " ")

private def r3 (m : String) (d a b : RvReg) : String :=
  s!"    {pad m}{regName d}, {regName a}, {regName b}\n"

private def mem (m : String) (x : RvReg) (off : Int) (base : RvReg) : String :=
  s!"    {pad m}{regName x}, {off}({regName base})\n"

/-- The printer: byte-for-byte the text `Lower` emits today. -/
def RvInsn.emit : RvInsn → String
  | .add d a b   => r3 "add" d a b
  | .sub d a b   => r3 "sub" d a b
  | .orr d a b   => r3 "or" d a b
  | .andr d a b  => r3 "and" d a b
  | .xorr d a b  => r3 "xor" d a b
  | .sltu d a b  => r3 "sltu" d a b
  | .mul d a b   => r3 "mul" d a b
  | .mulhu d a b => r3 "mulhu" d a b
  | .addi d a i  => s!"    {pad "addi"}{regName d}, {regName a}, {i}\n"
  | .sltiu d a i => s!"    {pad "sltiu"}{regName d}, {regName a}, {i}\n"
  | .slli d a sh => s!"    {pad "slli"}{regName d}, {regName a}, {sh}\n"
  | .srli d a sh => s!"    {pad "srli"}{regName d}, {regName a}, {sh}\n"
  | .li d i      => s!"    {pad "li"}{regName d}, {i}\n"
  | .mv d a      => s!"    {pad "mv"}{regName d}, {regName a}\n"
  | .notr d a    => s!"    {pad "not"}{regName d}, {regName a}\n"
  | .lw d o b    => mem "lw" d o b
  | .sw s o b    => mem "sw" s o b
  | .lbu d o b   => mem "lbu" d o b
  | .sb s o b    => mem "sb" s o b
  | .beqz a t    => s!"    {pad "beqz"}{regName a}, {t}\n"
  | .bnez a t    => s!"    {pad "bnez"}{regName a}, {t}\n"
  | .beq a b t   => s!"    {pad "beq"}{regName a}, {regName b}, {t}\n"
  | .bne a b t   => s!"    {pad "bne"}{regName a}, {regName b}, {t}\n"
  | .bltu a b t  => s!"    {pad "bltu"}{regName a}, {regName b}, {t}\n"
  | .bgeu a b t  => s!"    {pad "bgeu"}{regName a}, {regName b}, {t}\n"
  | .blt a b t   => s!"    {pad "blt"}{regName a}, {regName b}, {t}\n"
  | .bge a b t   => s!"    {pad "bge"}{regName a}, {regName b}, {t}\n"
  | .j t         => s!"    {pad "j"}{t}\n"
  | .call t      => s!"    {pad "call"}{t}\n"
  | .jalr a      => s!"    {pad "jalr"}{regName a}\n"
  | .jr a        => s!"    {pad "jr"}{regName a}\n"
  | .ret         => "    ret\n"

def RvItem.emit : RvItem → String
  | .insn i      => i.emit
  | .label l     => s!"{l}:\n"
  | .unlowered w => s!"    /* «unlowered: {w}» */\n"

def emitProg (p : List RvItem) : String := String.join (p.map RvItem.emit)

/-- Name lookup is a bijection on the 32 registers, so reading the lowering's
    string tables back as registers loses nothing. -/
theorem regOfName_regName : ∀ r : RvReg, regOfName (regName r) = some r := by
  native_decide

end Evm.CL.RV32.Asm
