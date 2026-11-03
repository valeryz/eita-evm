#!/usr/bin/env bash
# verify-asm-gadgets.sh — whole-gadget differential gate for the ARM64 byte
# lowering (AsmItems.assembleGadget = resolveLocals + AsmEncode.assemble).
#
# verify-asm-items.sh pairs instructions one to one and skips branch items, so
# it never checked a branch's TARGET — which is how the gadgets' numeric local
# labels (`7f` = "the next `7:`") were silently unresolved in the byte lowering.
# This assembles each gadget whole with clang (labels, branches, relocations)
# and compares the function's bytes. Twin of verify-x86-asm.sh; ELF target for
# the same reason (Mach-O atoms force cross-label relocations).
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-asm-gadgets"
rm -rf "$OUT"; mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe asmGadgetVectors ) > "$OUT/blocks.txt" 2>/dev/null
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
        f.write(".text\n.globl g\ng:\n")
        f.write("\n".join(b["text"])+"\n")
    o=f'{out}/{b["name"]}.o'
    r=subprocess.run(["clang","-target","aarch64-linux-gnu","-c","-x","assembler",s,"-o",o],capture_output=True,text=True)
    if r.returncode!=0:
        print(f"  {b['name']}: clang FAILED\n{r.stderr}"); bad+=1; continue
    # the whole .text section (ELF): bytes in memory order, portable across objdumps
    d=subprocess.run(["objdump","-s","-j",".text",o],capture_output=True,text=True).stdout
    hexs=[]
    for l in d.splitlines():
        m=re.match(r"^ *[0-9a-f]+ ((?:[0-9a-f]{2,8} ?)+)",l)
        if m: hexs.append(m.group(1).replace(" ",""))
    clang="".join(hexs)
    if clang!=b["hex"]:
        bad+=1
        i=next((k for k in range(min(len(clang),len(b["hex"]))) if clang[k]!=b["hex"][k]),min(len(clang),len(b["hex"])))
        print(f"  {b['name']}: MISMATCH at byte {i//2}  ours={len(b['hex'])//2}B clang={len(clang)//2}B")
        print(f"    ours : …{b['hex'][max(0,i-16):i+24]}")
        print(f"    clang: …{clang[max(0,i-16):i+24]}")
    else:
        print(f"  {b['name']}: {len(clang)//2} bytes OK")
print(f"{len(blocks)-bad}/{len(blocks)} ARM64 gadgets assemble byte-exact vs clang"+(" OK" if not bad else ""))
sys.exit(1 if bad else 0)
PY
