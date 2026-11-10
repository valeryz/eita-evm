#!/usr/bin/env bash
# verify-rv32-emit.sh — assemble the rv32imac lowering of every structured gadget.
#
# The Lean side (Evm.CL.RV32.Lower) proves COVERAGE: no gadget emits an
# «unlowered» marker. It cannot know whether what it emitted is rv32 that
# assembles — the same gap that let an unencodable x86-64 addressing mode
# through the proofs until scripts/verify-x86-emit.sh existed. This gate is the
# assembler's opinion, which is the authority on that question.
#
# Needs a RISC-V cross-assembler: brew install riscv64-elf-gcc (or set RV32_CC).
set -euo pipefail
cd "$(dirname "$0")/.."
RV32_CC="${RV32_CC:-riscv64-elf-gcc}"
if ! command -v "$RV32_CC" >/dev/null 2>&1; then
  echo "SKIP: $RV32_CC not found (brew install riscv64-elf-gcc)"; exit 0
fi
OUT="${TMPDIR:-/tmp}/eita-rv32-gadgets"
mkdir -p "$OUT"
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitRV32 ) > "$OUT/gadgets.s"
if grep -q '«' "$OUT/gadgets.s"; then
  echo "FAIL: unlowered instruction in the emitted rv32" >&2
  grep -n '«' "$OUT/gadgets.s" >&2
  exit 1
fi
"$RV32_CC" -march=rv32imac -mabi=ilp32 -c -x assembler "$OUT/gadgets.s" -o "$OUT/gadgets.o"
N=$(grep -c '^\.globl' "$OUT/gadgets.s")
I=$(grep -cE '^\s{4}[a-z]' "$OUT/gadgets.s")
echo "$N/6 rv32imac gadgets assemble OK ($I instructions)"

# ...and the real handler bodies that lower completely (Lower.coveredHandlers):
# the gadgets are the hard sequences, the handlers are the volume.
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitRV32 --handlers ) > "$OUT/handlers.s"
if grep -q '«' "$OUT/handlers.s"; then
  echo "FAIL: unlowered instruction in the emitted rv32 handlers" >&2
  grep -n '«' "$OUT/handlers.s" >&2
  exit 1
fi
"$RV32_CC" -march=rv32imac -mabi=ilp32 -c -x assembler "$OUT/handlers.s" -o "$OUT/handlers.o"
HN=$(grep -c '^\.globl' "$OUT/handlers.s")
HI=$(grep -cE '^\s{4}[a-z]' "$OUT/handlers.s")
echo "$HN handlers assemble OK ($HI instructions)"
