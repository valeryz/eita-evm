/-
  Evm.CL.X86Print — Intel-syntax text for `XInsn`/`XItem`.

  Stage 4 of #238. The x86-64 FRAME (`X86Run`, `X86Dispatch`, `X86Interp`) is
  written as `XItem`s, because its instructions (push/pop, `shl r13, 5`,
  RIP-relative loads, `call [rax + rcx*8]`) have no ARM64 twin in `AInstr`.
  Those items already encode to bytes (`X86Encode`); this is their text, in
  exactly the style `Lowering` prints for `AInstr` (`pad`, `qword ptr [r12 +
  r13 - 32]`), so an assembly file can carry both side by side and the system
  assembler can be the oracle for the frame too (`verify-x86-interp.sh`:
  bytes of `X86Asm.assemble` == bytes of clang on this text).
-/

import Evm.CL.X86Items

namespace Evm.CL.X86Print

open Evm.CL.X86Encode Evm.CL.X86Items

def XReg.s : XReg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The 32-bit name. -/
def XReg.s32 : XReg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | r => XReg.s r ++ "d"

/-- The low-byte name. -/
def XReg.s8 : XReg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | r => XReg.s r ++ "b"

def XCond.s : XCond → String
  | .o => "o" | .no => "no" | .b => "b" | .ae => "ae" | .e => "e" | .ne => "ne"
  | .be => "be" | .a => "a" | .s => "s" | .ns => "ns" | .p => "p" | .np => "np"
  | .l => "l" | .ge => "ge" | .le => "le" | .g => "g"

def AluOp.s : AluOp → String
  | .add => "add" | .or_ => "or" | .adc => "adc" | .sbb => "sbb"
  | .and_ => "and" | .sub => "sub" | .xor_ => "xor" | .cmp => "cmp"

def ShiftOp.s : ShiftOp → String
  | .shl => "shl" | .shr => "shr" | .sar => "sar"

/-- `[base + index*scale + disp]`, with the sign of the displacement spelled
    out and the unit scale left implicit — `Lowering.nosMem`'s style. -/
def Mem.s (m : Mem) : String :=
  let idx := match m.index with
    | some i => " + " ++ XReg.s i ++ (if m.scale == 1 then "" else s!"*{m.scale}")
    | none => ""
  let d := if m.disp == 0 then "" else if m.disp > 0 then s!" + {m.disp}" else s!" - {-m.disp}"
  "[" ++ XReg.s m.base ++ idx ++ d ++ "]"

/-- Pad a mnemonic to the column `Lowering.pad` uses. -/
def pad (m : String) : String :=
  m ++ ("".pushn ' ' (if m.length < 5 then 5 - m.length else 1))

def line (m ops : String) : String := s!"    {pad m} {ops}\n"

def XInsn.s : XInsn → String
  | .movRR d s    => line "mov" s!"{XReg.s d}, {XReg.s s}"
  | .movRM d m    => line "mov" s!"{XReg.s d}, qword ptr {Mem.s m}"
  | .movMR m s    => line "mov" s!"qword ptr {Mem.s m}, {XReg.s s}"
  | .movRI d i    => line "mov" s!"{XReg.s d}, {i}"
  | .aluRR o d s  => line (AluOp.s o) s!"{XReg.s d}, {XReg.s s}"
  | .aluRM o d m  => line (AluOp.s o) s!"{XReg.s d}, qword ptr {Mem.s m}"
  | .aluMR o m s  => line (AluOp.s o) s!"qword ptr {Mem.s m}, {XReg.s s}"
  | .aluRI o d i  => line (AluOp.s o) s!"{XReg.s d}, {i}"
  | .aluMI o m i  => line (AluOp.s o) s!"qword ptr {Mem.s m}, {i}"
  | .shiftRI o d n => line (ShiftOp.s o) s!"{XReg.s d}, {n}"
  | .imulRR d s   => line "imul" s!"{XReg.s d}, {XReg.s s}"
  | .lea d m      => line "lea" s!"{XReg.s d}, {Mem.s m}"
  | .cmovRR c d s => line ("cmov" ++ XCond.s c) s!"{XReg.s d}, {XReg.s s}"
  | .lzcnt d s    => line "lzcnt" s!"{XReg.s d}, {XReg.s s}"
  | .lzcntRM d m  => line "lzcnt" s!"{XReg.s d}, qword ptr {Mem.s m}"
  | .push r       => line "push" (XReg.s r)
  | .pop r        => line "pop" (XReg.s r)
  | .jmpReg r     => line "jmp" (XReg.s r)
  | .callReg r    => line "call" (XReg.s r)
  | .jmpMem m     => line "jmp" s!"qword ptr {Mem.s m}"
  | .bswap r      => line "bswap" (XReg.s r)
  | .notR r       => line "not" (XReg.s r)
  | .setcc c r    => line ("set" ++ XCond.s c) (XReg.s8 r)
  | .movzxB d s   => line "movzx" s!"{XReg.s d}, {XReg.s8 s}"
  | .movzxBM d m  => line "movzx" s!"{XReg.s d}, byte ptr {Mem.s m}"
  | .movMR8 m s   => line "mov" s!"byte ptr {Mem.s m}, {XReg.s8 s}"
  | .movMI m i    => line "mov" s!"qword ptr {Mem.s m}, {i}"
  | .movMI32 m i  => line "mov" s!"dword ptr {Mem.s m}, {i}"
  | .movMR32 m s  => line "mov" s!"dword ptr {Mem.s m}, {XReg.s32 s}"
  | .movRM32 d m  => line "mov" s!"{XReg.s32 d}, dword ptr {Mem.s m}"
  | .cmpRI32 r i  => line "cmp" s!"{XReg.s32 r}, {i}"
  | .testRI r i   => line "test" s!"{XReg.s r}, {i}"
  | .ret          => "    ret\n"

/-- Items. `QuadOff` has no standalone text (its value is relative to an image
    start the item does not name); the frame does not use it. -/
def XItem.s : XItem → String
  | .I i          => XInsn.s i
  | .L n          => n ++ ":\n"
  | .Jcc c t      => line ("j" ++ XCond.s c) t
  | .Jmp t        => line "jmp" t
  | .JccSym c t   => line ("j" ++ XCond.s c) t
  | .JmpSym t     => line "jmp" t
  | .LeaRip d t   => line "lea" s!"{XReg.s d}, [rip + {t}]"
  | .LeaRipSym d t => line "lea" s!"{XReg.s d}, [rip + {t}]"
  | .QuadOff t    => s!"    «no text: QuadOff {t}»\n"
  | .Call t       => line "call" t
  | .CallRip s    => line "call" s!"qword ptr [rip + {s}]"
  | .QuadSym s    => s!"    .quad   {s}\n"
  | .unlowered w  => s!"    «unlowered: {w}»\n"

def text (its : List XItem) : String := String.join (its.map XItem.s)

end Evm.CL.X86Print
