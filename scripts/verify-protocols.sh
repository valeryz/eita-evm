#!/bin/bash
# verify-protocols.sh — the Veil models of the state layer's concurrent protocols
# (verify/protocols/, its own Lake package: Veil on core's toolchain) check, and describe the
# code they cite:
#   1. CheckCode.lean: every `@code` citation of a model names a defun, a `; @veil` marker or a
#      historical line of the code, and the orderings the proofs rest on hold (seconds);
#   2. each model elaborates without an error and with its expected result: a FIXED model
#      safe (its invariant, IC3 certificate or kernel-checked VCs), an OLD model's violation
#      found; every printed axiom list is propext, Classical.choice, Quot.sound only.
# One model at a time, each under a memory cap (EITA_PROTOCOLS_MAX_GB, default 32: the whole
# process tree, Veil's compiled model checker included, is stopped above it); prints each
# model's wall time and peak RSS.
#   scripts/verify-protocols.sh            the code check and all six models (~30 min on an M-series
#                                          Mac; CompactionDeepReorg alone peaks above 32 GB)
#   scripts/verify-protocols.sh --quick    the code check and the four models under 10 GB (CI:
#                                          ~11 min on that Mac, 9 GB peak): LayerGcFixed's
#                                          certificate, Compaction's VC proofs, two violations
#   scripts/verify-protocols.sh LayerGcFixed ...   the code check and the named models
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/verify/protocols" || exit 2
cap_kb=$(( ${EITA_PROTOCOLS_MAX_GB:-32} * 1024 * 1024 ))
tmp=${TMPDIR:-/tmp}/_verify_protocols.$$
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT

all="LayerGcFixed LayerGcOld LayerGcSwapped CompactionDeepReorgOld CompactionDeepReorg Compaction"
quick="LayerGcFixed LayerGcSwapped CompactionDeepReorgOld Compaction"
case "${1:-}" in
  --quick) models=$quick ;;
  "") models=$all ;;
  *) models="$*" ;;
esac

# what each model must print (one pattern per line)
expect() {
  case $1 in
    LayerGcFixed) printf '%s\n' 'No violation' "'LayerGcFixed.ic3_safe' depends on axioms" ;;
    LayerGcOld) printf '%s\n' 'Violation: safety_failure' 'Satisfying trace found' "'LayerGcOld.ic3_unsafe' depends on axioms" ;;
    LayerGcSwapped) printf '%s\n' 'Violation: safety_failure' ;;
    Compaction) printf '%s\n' 'No violation' 'theorems; axioms:' ;;
    CompactionDeepReorg) printf '%s\n' 'No violation' 'theorems; axioms:' 'Satisfying trace found' ;;
    CompactionDeepReorgOld) printf '%s\n' 'Violation: safety_failure' 'Satisfying trace found' ;;
    *) echo "no expected result for model $1" >&2; return 1 ;;
  esac
}

lake build EitaVeil.Code EitaVeil.LayerGc EitaVeil.CompactionParts >"$tmp/build.log" 2>&1 ||
  { echo "FAIL: lake build (log tail):"; tail -30 "$tmp/build.log"; exit 1; }
lake env lean --run CheckCode.lean >"$tmp/code.log" 2>&1
code=$?
cat "$tmp/code.log"
[ $code -eq 0 ] || { echo "FAIL: the models no longer describe the code (CheckCode.lean)"; exit 1; }

case "$(uname)" in Darwin) ext=dylib ;; *) ext=so ;; esac
ffi=.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.$ext
tree() { echo "$1"; for c in $(pgrep -P "$1"); do tree "$c"; done; }
fail=0
for m in $models; do
  expect "$m" >"$tmp/expect" || exit 2
  out="$tmp/$m.out"
  start=$(date +%s)
  # the cvc5 FFI is loaded explicitly with `lake env lean` (`lake build` holds every message)
  timeout 3600 lake env lean --load-dynlib="$ffi" "EitaVeil/$m.lean" >"$out" 2>&1 &
  pid=$!
  peak=0 over=0
  while kill -0 $pid 2>/dev/null; do
    rss=$(ps -o rss= -p "$(tree $pid | paste -sd, -)" 2>/dev/null | awk '{s+=$1} END {print s+0}')
    [ "$rss" -gt "$peak" ] && peak=$rss
    if [ "$rss" -gt "$cap_kb" ]; then
      over=1
      for p in $(tree $pid); do kill "$p" 2>/dev/null; done
    fi
    sleep 2
  done
  wait $pid
  rc=$?
  wall=$(( $(date +%s) - start ))
  why=""
  [ $over -eq 1 ] && why="over the memory cap"
  [ -z "$why" ] && [ $rc -ne 0 ] && why="exit $rc"
  [ -z "$why" ] && grep -q ': error' "$out" && why="errors"
  while read -r pat; do
    [ -z "$why" ] && ! grep -qF "$pat" "$out" && why="no '$pat'"
  done <"$tmp/expect"
  bad=$(grep -hoE "depends on axioms: \[[^]]*\]|axioms: #\[[^]]*\]" "$out" | sed 's/.*\[//; s/\]$//' |
        tr ',' '\n' | tr -d ' ' | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u | paste -sd, -)
  [ -z "$why" ] && [ -n "$bad" ] && why="non-standard axioms: $bad"
  result=$(grep -hoE "No violation \(explored [0-9]+ states\)|Violation: safety_failure \([^)]*\)" "$out" | head -1)
  printf '%-24s %5ss %7s MB  %s\n' "$m" "$wall" "$((peak / 1024))" "${why:-OK  $result}"
  if [ -n "$why" ]; then
    fail=1
    grep -E ': error' "$out" | head -5
  fi
done
[ $fail -eq 0 ] || { echo "FAIL: verify-protocols"; exit 1; }
echo "verify-protocols OK: $(echo $models | wc -w | tr -d ' ') models as expected, axioms standard"
