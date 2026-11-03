/-
  X86EncodeVectors.lean — `lake exe x86EncodeVectors` prints
  `<hex bytes>\t<asm text>` for a battery of x86-64 instructions, covering every
  encoder path: both ALU directions, immediate widths, shifts, cmov, lzcnt, lea,
  and each addressing-mode special case (SIB-forcing base, displacement-forcing
  base, every legal scale, high registers needing REX bits).

  `scripts/verify-x86-encode.sh` assembles the text column with clang and
  requires the bytes to match — the same differential gate as
  verify-asm-encode.sh for ARM64.
-/

import Evm.CL.X86Encode

open Evm.CL.X86Encode

/-- The registers worth covering: a low one, the two with awkward low bits, and
    high ones that need REX. -/
def regs : List XReg := [.rax, .rcx, .rbx, .rsp, .rbp, .rdi, .r12, .r13, .r15]

def alus : List AluOp := [.add, .or_, .adc, .sbb, .and_, .sub, .xor_, .cmp]

def mems : List Mem :=
  [ { base := .rbx, disp := 56 },
    { base := .rbx },                                    -- no displacement
    { base := .r12, disp := 48 },                        -- SIB forced by base
    { base := .r12 },                                    -- SIB, no displacement
    { base := .r13 },                                    -- displacement forced
    { base := .r13, disp := -8 },
    { base := .r12, index := some .r13, disp := -48 },    -- the NOS access
    { base := .r12, index := some .r13 },
    { base := .rdi, index := some .rcx, scale := 2 },
    { base := .rdi, index := some .rcx, scale := 4 },
    { base := .rbx, index := some .r15, scale := 8, disp := 4096 },  -- disp32
    { base := .rbp, index := some .rax, disp := -4000 } ]

def vectors : List XInsn :=
  -- register-register, both ALU ops and both directions
  (alus.flatMap (fun o => [XInsn.aluRR o .rcx .rdx, XInsn.aluRR o .r15 .rax,
                           XInsn.aluRR o .rax .r12]))
  ++ (alus.flatMap (fun o => mems.map (fun m => XInsn.aluRM o .rcx m)))
  ++ (alus.flatMap (fun o => mems.map (fun m => XInsn.aluMR o m .r15)))
  -- immediates: one-byte, four-byte, negative
  ++ (alus.flatMap (fun o => [XInsn.aluRI o .rcx 100, XInsn.aluRI o .r15 100,
                              XInsn.aluRI o .rcx 100000, XInsn.aluRI o .rcx (-5)]))
  ++ (mems.map (fun m => XInsn.aluMI .cmp m 0))
  ++ (mems.map (fun m => XInsn.aluMI .add m 1000))
  -- moves
  ++ (mems.map (fun m => XInsn.movRM .rcx m))
  ++ (mems.map (fun m => XInsn.movMR m .rcx))
  ++ (regs.map (fun r => XInsn.movRR r .rcx))
  ++ (regs.map (fun r => XInsn.movRR .rcx r))
  ++ [XInsn.movRI .rcx 0, XInsn.movRI .rcx 1000000, XInsn.movRI .r15 (-1),
      XInsn.movRI .rcx 2147483647, XInsn.movRI .rcx 2147483648,
      XInsn.movRI .rcx 4294967295, XInsn.movRI .r15 4294967295,
      XInsn.movRI .rcx 4294967296, XInsn.movRI .r15 1099511627776]
  -- shifts, at every amount the gadgets use and the boundaries
  ++ ([0, 1, 5, 9, 31, 63].flatMap (fun n =>
        [XInsn.shiftRI .shl .rcx n, XInsn.shiftRI .shr .rcx n,
         XInsn.shiftRI .sar .r15 n]))
  -- lea over every addressing mode
  ++ (mems.map (fun m => XInsn.lea .rdi m))
  -- imul, cmov (every condition), lzcnt, ret
  ++ [XInsn.imulRR .rdi .rcx, XInsn.imulRR .r15 .rax, XInsn.imulRR .rax .r12]
  ++ ([XCond.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .p, .np, .l, .ge, .le, .g].flatMap
        (fun c => [XInsn.cmovRR c .rax .rcx, XInsn.cmovRR c .r15 .r12]))
  ++ [XInsn.lzcnt .rcx .rdx, XInsn.lzcnt .r15 .r12]
  ++ (mems.map (fun m => XInsn.lzcntRM .rdx m)) ++ [XInsn.lzcntRM .r9 { base := .r12, index := some .r13, disp := -56 }]
  ++ (regs.flatMap (fun r => [XInsn.push r, XInsn.pop r, XInsn.jmpReg r, XInsn.callReg r]))
  ++ (mems.map (fun m => XInsn.jmpMem m))
  ++ (regs.map (fun r => XInsn.bswap r))
  ++ (regs.map (fun r => XInsn.notR r))
  ++ ([XCond.e, .b, .l, .ne, .a].flatMap (fun c => regs.map (fun r => XInsn.setcc c r)))
  ++ (regs.map (fun r => XInsn.movzxB r r)) ++ [XInsn.movzxB .rax .r8, XInsn.movzxB .r8 .rsi]
  ++ (mems.map (fun m => XInsn.movzxBM .rdi m)) ++ [XInsn.movzxBM .rdi { base := .r14, index := some .rdx }]
  ++ (mems.map (fun m => XInsn.movMR8 m .rcx)) ++ (regs.map (fun r => XInsn.movMR8 { base := .rbx, disp := 128 } r))
  ++ [XInsn.movMR8 { base := .rcx, index := some .r8 } .rax]
  ++ (mems.map (fun m => XInsn.movMI m 0)) ++ [XInsn.movMI { base := .rax } (-1), XInsn.movMI { base := .r13, disp := 8 } 100000]
  ++ [XInsn.movMI32 { base := .rsp, disp := 4 } 0, XInsn.movMI32 { base := .rsp, disp := 20 } 7, XInsn.movMI32 { base := .r12, disp := 4 } 1]
  ++ (regs.map (fun r => XInsn.movMR32 { base := .rsp, disp := 0 } r)) ++ (regs.map (fun r => XInsn.movRM32 r { base := .rsp, disp := 128 }))
  ++ (regs.map (fun r => XInsn.cmpRI32 r 0)) ++ [XInsn.cmpRI32 .rdx 1000]
  ++ [XInsn.jmpMem { base := .rcx, index := some .rdi, scale := 8 }]
  ++ (regs.flatMap (fun r => [XInsn.testRI r 1, XInsn.testRI r 4, XInsn.testRI r 65536]))
  ++ [XInsn.ret]

def hex2 (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def main : IO Unit := do
  for i in vectors do
    IO.println s!"{String.join ((encode i).map hex2)}\t{asm i}"
