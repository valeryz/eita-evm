#!/usr/bin/env bash
# run-battery.sh — run `bin/eita fixtures` over a fixture tree, one process
# per leaf directory (a flat directory of tests), and aggregate the summaries.
#
#   scripts/run-battery.sh <fixture-dir> [log]
#
# Environment is passed through (EITA_NO_JIT=1 for the interp tier, EITA_LIB
# to point at a side-built libeita; EITA_BIN for another executable than bin/eita;
# SBCL_ARGS for runtime options such as --dynamic-space-size 16GB — stTimeConsuming
# needs more than the default). Prints one line per leaf directory and a
# total; the per-test PASS/FAIL lines go to the log (default: stdout). Exit 0 only when tests
# ran and none failed. The Cancun battery and its expected result: docs/testing.md.
set -uo pipefail
cd "$(dirname "$0")/.."
root="$1"; log="${2:-/dev/stdout}"
[ -d "$root" ] || { echo "run-battery: no directory $root" >&2; exit 2; }
tp=0; tf=0; ts=0; tx=0
while IFS= read -r d; do
  n=$(find "$d" -maxdepth 1 -name '*.json' | wc -l | tr -d ' ')
  [ "$n" -eq 0 ] && continue
  out=$("${EITA_BIN:-bin/eita}" ${SBCL_ARGS:+$SBCL_ARGS --end-runtime-options} fixtures "$d" 2>&1 | grep -v '^;')
  printf '%s\n' "$out" >> "$log"
  s=$(printf '%s\n' "$out" | grep '^summary:' | tail -1)
  p=$(printf '%s' "$s" | sed -n 's/.*pass=\([0-9]*\).*/\1/p'); f=$(printf '%s' "$s" | sed -n 's/.* fail=\([0-9]*\).*/\1/p'); k=$(printf '%s' "$s" | sed -n 's/.*skip=\([0-9]*\).*/\1/p')
  x=$(printf '%s' "$s" | sed -n 's/.*xfail=\([0-9]*\).*/\1/p')
  p=${p:-0}; f=${f:-0}; k=${k:-0}; x=${x:-0}
  if [ -z "$s" ]; then f=$n; printf '  %-60s NO SUMMARY (%d files)\n' "${d#$root/}" "$n"; fi
  tp=$((tp+p)); tf=$((tf+f)); ts=$((ts+k)); tx=$((tx+x))
  printf '  %-60s pass=%-5s fail=%-4s skip=%s xfail=%s\n' "${d#$root/}" "$p" "$f" "$k" "$x"
done < <(find "$root" -type d | sort)
echo "TOTAL pass=$tp fail=$tf skip=$ts xfail=$tx  ($root)"
[ "$tf" -eq 0 ] && [ "$tp" -gt 0 ]     # exit 1 on any FAIL / XPASS / NO SUMMARY, or nothing run
