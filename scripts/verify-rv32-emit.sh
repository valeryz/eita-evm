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

# ...and the WHOLE interpreter: the frame, the dispatch loop, the epilogue, the
# fault stubs, the 22 fork tables and every handler body. Nothing may be left
# undefined except the C helpers the engine links against.
( cd lean && DYLD_LIBRARY_PATH=/opt/homebrew/lib lake exe emitRV32 --interp ) > "$OUT/interp.s"
if grep -q '«' "$OUT/interp.s"; then
  echo "FAIL: unlowered instruction in the emitted rv32 interpreter" >&2; exit 1
fi
"$RV32_CC" -march=rv32imac -mabi=ilp32 -c -x assembler "$OUT/interp.s" -o "$OUT/interp.o"
for sym in eita_run eita_next eita_sync_and_ret eita_set_fork; do
  "${RV32_CC%-gcc}-nm" -g "$OUT/interp.o" | grep -q " T $sym\$" || {
    echo "FAIL: $sym is not defined in the emitted interpreter" >&2; exit 1; }
done
# every undefined symbol must be one of the C helpers (eita_helper_* / eita_ts_*)
BAD=$("${RV32_CC%-gcc}-nm" -u "$OUT/interp.o" | awk '{print $2}' |
      grep -vE '^eita_(helper_|ts_|spec_|sh_|ws_|keccak)' || true)
if [ -n "$BAD" ]; then
  echo "FAIL: the interpreter references symbols that are not engine C:" >&2
  echo "$BAD" >&2; exit 1
fi
TI=$(grep -cE '^\s{4}[a-z]' "$OUT/interp.s")
TT=$("${RV32_CC%-gcc}-size" "$OUT/interp.o" | awk 'NR==2{print $1}')
# counted, not quoted: a hardcoded number here read "137 handlers" for six
# commits after the real figure was 143
TH=$(grep -cE '^\.globl _?eita_handler_' "$OUT/interp.s")
TF=$(grep -cE '^_?eita_dispatch_table_' "$OUT/interp.s")
echo "whole interpreter assembles OK ($TI instructions, $TT bytes of text, $TH handlers + $TF fork tables)"

# ...and the alignment audit, over the file the firmware actually assembles.
# bao1x's VexRiscv TRAPS a misaligned load or store, so an `lw` on a
# byte-granular address is a lowering bug that no emulator reproduces (QEMU
# emulates misalignment) and that kills the process on hardware before it can
# print. The emitter answers this with a forward analysis; this is the
# independent backward audit of the emitted text.
python3 -I "$(dirname "$0")/check-rv32-alignment.py" c/handlers-rv32.S
