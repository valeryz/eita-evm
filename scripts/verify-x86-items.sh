#!/usr/bin/env bash
# verify-x86-items.sh — the two x86-64 lowerings of AsmCore.AInstr must agree.
#
# `Lowering.emitX86` produces TEXT; `X86Items.x86Items` produces the structured
# instructions `X86Encode.encode` turns into BYTES. For every instruction in
# the structured gadget set, encode(x86Items i) must equal clang(emitX86 i).
# The pairing is one to one by `X86Items.lowerings_align`.
#
# Counterpart of verify-asm-items.sh (ARM64). Together with verify-x86-encode.sh
# (encoder vs clang over a battery) and verify-x86-emit.sh (the text assembles),
# this closes the loop: text and bytes come from one vocabulary and are checked
# against each other through the assembler.
set -euo pipefail
# Portable across macOS (Rosetta oracle) and Linux x86-64 (native): the
# assembler, the object's text-section name and the runner differ.
case "$(uname -s)" in
  Darwin) CLANG_X86="clang -arch x86_64"; TEXTSEC="__text"; RUNX86="arch -x86_64" ;;
  *)      CLANG_X86="clang";              TEXTSEC=".text";  RUNX86="" ;;
esac
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-items"
mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe x86ItemsVectors ) > "$OUT/vec.tsv" 2>/dev/null
{ echo ".text"; echo ".intel_syntax noprefix"; echo ".globl _t"; echo "_t:";
  cut -f2 "$OUT/vec.tsv"; } > "$OUT/vec.s"
$CLANG_X86 -c -x assembler "$OUT/vec.s" -o "$OUT/vec.o"
# whole text section, split back by the encoder's own lengths (portable: no
# listing format to parse, and no wrapped 10-byte instructions)
objdump -s -j "$TEXTSEC" "$OUT/vec.o" \
  | sed -nE 's/^ *[0-9a-f]+ (([0-9a-f]{2,8} ?)+).*/\1/p' | tr -d ' \n' > "$OUT/clang.hex"
VEC="$OUT/vec.tsv" CLANG="$OUT/clang.hex" python3 -c '
import os,sys
exp=[];asm=[]
for l in open(os.environ["VEC"]):
    h,a=l.rstrip("\n").split("\t");exp.append(h);asm.append(a.strip())
clang=open(os.environ["CLANG"]).read().strip()
pos=0;bad=[]
for i,(e,a) in enumerate(zip(exp,asm)):
    got=clang[pos:pos+len(e)]
    if got!=e: bad.append((i,a,e,got))
    pos+=len(e)
if pos!=len(clang): print(f"LENGTH MISMATCH: clang {len(clang)//2}B vs items {pos//2}B")
for i,s,e,a in bad[:12]: print(f"  [{i}] {s}: items={e} clang={a}")
ok = not bad and pos==len(clang)
print(f"{len(exp)-len(bad)}/{len(exp)} x86-64 AInstr lowerings agree (bytes == clang(text))"+(" OK" if ok else ""))
print("  (label and branch items are layout-dependent; Relax decides their width)")
sys.exit(0 if ok else 1)
'
