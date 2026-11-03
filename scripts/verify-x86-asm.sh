#!/usr/bin/env bash
# verify-x86-asm.sh — whole-gadget differential gate for the x86-64 assembler.
#
# X86Asm.assemble turns an XItem list into bytes, choosing rel8/rel32 for each
# local branch by relaxation (Evm.CL.Relax). For every structured gadget this
# assembles the TEXT lowering with clang as a standalone function — no local
# _eita_oog, so symbol branches are rel32 + relocation on both sides — and
# requires the whole function's bytes to match ours.
#
# Covers what the per-instruction gates cannot: label offsets, branch
# displacements, and the relaxation choice itself (clang's MC layer runs the
# same start-short-and-widen algorithm; a disagreement shows as a byte diff).
# x86-64 analogue of verify-jit-emit.sh.
#
# The oracle is clang targeting ELF (x86_64-linux-gnu), not Mach-O: on Darwin
# only `L`-prefixed labels are assembler-temporaries, so `.Lzero` / `.Lmcd0`
# start new ATOMS and a branch between atoms is forced to rel32 with a linker
# relocation — even inside one function. Our assembler has no atoms, and
# neither does the x86-64 deployment target (stage 4 is ELF/mmap), so ELF is
# the format whose behaviour we are matching.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-x86-asm"
rm -rf "$OUT"; mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe x86AsmVectors ) > "$OUT/blocks.txt" 2>/dev/null
OUT="$OUT" python3 - <<'PY'
import os,re,subprocess,sys
out=os.environ["OUT"]
blocks=[];cur=None
for line in open(f"{out}/blocks.txt"):
    line=line.rstrip("\n")
    if line.startswith("=== "):
        cur={"name":line[4:],"hex":None,"text":[]}; blocks.append(cur)
    elif cur and cur["hex"] is None:
        cur["hex"]=line.strip()
    elif cur:
        cur["text"].append(line)
bad=0
for b in blocks:
    s=f'{out}/{b["name"]}.s'
    with open(s,"w") as f:
        f.write(".text\n.intel_syntax noprefix\n.globl g\ng:\n")
        f.write("\n".join(b["text"])+"\n")
    o=f'{out}/{b["name"]}.o'
    r=subprocess.run(["clang","-target","x86_64-linux-gnu","-c","-x","assembler",s,"-o",o],capture_output=True,text=True)
    if r.returncode!=0:
        print(f"  {b['name']}: clang FAILED\n{r.stderr}"); bad+=1; continue
    # the whole .text section (ELF), portable across GNU and LLVM objdump
    d=subprocess.run(["objdump","-s","-j",".text",o],capture_output=True,text=True).stdout
    hexs=[]
    for l in d.splitlines():
        m=re.match(r"^ *[0-9a-f]+ ((?:[0-9a-f]{2,8} ?)+)",l)
        if m: hexs.append(m.group(1).replace(" ",""))
    clang="".join(hexs)
    if clang!=b["hex"]:
        bad+=1
        # first differing byte, for the report
        i=next((k for k in range(min(len(clang),len(b["hex"]))) if clang[k]!=b["hex"][k]),min(len(clang),len(b["hex"])))
        print(f"  {b['name']}: MISMATCH at byte {i//2}  ours={len(b['hex'])//2}B clang={len(clang)//2}B")
        print(f"    ours : …{b['hex'][max(0,i-16):i+24]}")
        print(f"    clang: …{clang[max(0,i-16):i+24]}")
    else:
        print(f"  {b['name']}: {len(clang)//2} bytes OK")
print(f"{len(blocks)-bad}/{len(blocks)} x86-64 gadgets assemble byte-exact vs clang"+(" OK" if not bad else ""))
sys.exit(1 if bad else 0)
PY
