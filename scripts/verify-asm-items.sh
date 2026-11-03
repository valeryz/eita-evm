#!/usr/bin/env bash
# verify-asm-items.sh — the two ARM64 lowerings of AsmCore.AInstr must agree.
#
# `AInstr.emitARM64` produces the TEXT that clang assembles into c/handlers.S at
# build time; `AsmItems.items` produces the Items the in-process encoder turns
# into BYTES at run time. Until these were one vocabulary, every gadget in both
# paths was hand-written twice — which is how ChunkGas's `retake` ended up with
# a bare `sub` and no borrow check on the Item side only.
#
# This gate drives the comparison off the vocabulary: for every instruction in
# the structured gadget set, encode(items i) must equal clang(emitARM64 i).
# Companion to verify-asm-encode.sh (which checks the encoder against a battery
# of 100 instructions) and verify-jit-emit.sh (the JIT leaf cores).
set -euo pipefail
# Portable: on macOS clang assembles arm64 natively; on Linux x86-64 it
# cross-assembles with -target (nothing is executed — this is a byte check).
case "$(uname -s)" in
  Darwin) CLANG_ARM="clang -arch arm64" ;;
  *)      CLANG_ARM="clang -target aarch64-linux-gnu" ;;
esac
case "$(uname -s)" in Darwin) SECTION="__text" ;; *) SECTION=".text" ;; esac
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/eita-asm-items"
mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe asmItemsVectors ) > "$OUT/vec.tsv" 2>/dev/null
{ echo ".text"; echo ".global _t"; echo "_t:"; cut -f2 "$OUT/vec.tsv"; } > "$OUT/vec.s"
$CLANG_ARM -c "$OUT/vec.s" -o "$OUT/vec.o"
objdump -s -j "$SECTION" "$OUT/vec.o" | VEC="$OUT/vec.tsv" python3 -c '
import re,sys
hexs="".join(m.group(1).replace(" ","") for l in sys.stdin if (m:=re.match(r"^ *[0-9a-f]+ ((?:[0-9a-f]{2,8} ?)+)",l)))
actual=[int(hexs[i+6:i+8]+hexs[i+4:i+6]+hexs[i+2:i+4]+hexs[i:i+2],16) for i in range(0,len(hexs),8)]
exp=[];asm=[]
import os
for l in open(os.environ["VEC"]):
    w,a=l.rstrip("\n").split("\t");exp.append(int(w));asm.append(a)
if len(actual)!=len(exp):
    print(f"COUNT MISMATCH: clang {len(actual)} vs items {len(exp)}");sys.exit(1)
bad=[(i,s,e,a) for i,(e,a,s) in enumerate(zip(exp,actual,asm)) if e!=a]
for i,s,e,a in bad[:10]: print(f"  [{i}]{s}: items={e:08x} clang={a:08x}")
print(f"{len(exp)-len(bad)}/{len(exp)} AInstr lowerings agree (bytes == clang(text))"+(" OK" if not bad else ""))
print("  (label and branch items are layout-dependent; verify-jit-emit.sh covers those end to end)")
sys.exit(1 if bad else 0)
'
