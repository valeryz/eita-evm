#!/bin/bash
# cbmc/run.sh — the CBMC proofs of the native slot tables (world_slots_harness.c).
# Each run takes an arbitrary table satisfying the invariant, applies one operation, and
# proves memory safety, the invariant again, and agreement with the finite-map model:
#   capacity 4: get, place (put without growth), remove; grow at every count it can see
#   (0..3, the last one doubling to 8); capacity 8: get, place, remove, same-size grow.
# put = touch + (grow when the load test fails) + place, so place and grow cover it.
# The doubling grow from 8 to 16 is out of reach of the memory cap.
# CBMC: PATH, or CBMC=<path>. Every run under a hard memory cap and a timeout
# (CBMC_MEM, default 6G; CBMC_TIMEOUT, default 900 s). If a proof needs more, shrink the
# harness, don't raise the cap. Exit 0 = every proof VERIFICATION SUCCESSFUL.
# macOS: the kernel refuses `ulimit -v`, so cap and timeout are a watchdog (watch below); and
# the SDK's __DARWIN_ALIAS asm labels rename libc calls (fputs -> _fputs: "no body for callee
# _fputs"), which CBMC's library models do not match, so they are dropped (-D__asm(x)=).
# Runs on bash 3.2 (macOS's /bin/bash).
set -uo pipefail
cd "$(dirname "$0")"
CBMC=${CBMC:-cbmc}
CAPMEM=${CBMC_MEM:-6G}
CHECKS="--bounds-check --pointer-check --pointer-primitive-check --memory-leak-check --div-by-zero-check
  --signed-overflow-check --pointer-overflow-check --conversion-check --undefined-shift-check --unwinding-assertions"
PLATFORM=(); WATCH=
if command -v systemd-run >/dev/null && systemd-run --user --scope --quiet true 2>/dev/null; then
  LIMIT=(systemd-run --user --scope --quiet -p MemoryMax=$CAPMEM -p MemorySwapMax=0)
elif [ "$(uname -s)" = Darwin ]; then
  LIMIT=(); PLATFORM=('-D__asm(x)='); WATCH=1
else
  LIMIT=(); ulimit -v $(( ${CAPMEM%G} * 1024 * 1024 ))
fi
watch() {   # macOS: the memory cap and the timeout on pid $1 (the cbmc, command line checked)
  local kb=$(( ${CAPMEM%G} * 1024 * 1024 )) end=$((SECONDS + ${CBMC_TIMEOUT:-900})) r
  while kill -0 "$1" 2>/dev/null; do
    r=$(ps -o rss= -p "$1" | tr -d ' ')
    if { [ "${r:-0}" -gt "$kb" ] || [ $SECONDS -ge $end ]; } &&
       ps -o args= -p "$1" | grep -q 'world_slots_harness\.c'; then
      kill "$1"; echo "ERROR: cbmc killed (over $CAPMEM or ${CBMC_TIMEOUT:-900} s)"
    fi
    sleep 1
  done
}
fail=0
prove() {
  local name=$1; shift
  local t0=$SECONDS out
  # ${A[@]+"${A[@]}"}: an empty array under set -u on bash 3.2
  local run=("$CBMC" world_slots_harness.c -DWS_DIR_MIN=2 $CHECKS ${PLATFORM[@]+"${PLATFORM[@]}"} "$@")
  if [ -n "$WATCH" ]; then
    out=$("${run[@]}" 2>&1 & watch $!)
  else
    out=$(${LIMIT[@]+"${LIMIT[@]}"} timeout ${CBMC_TIMEOUT:-900} "${run[@]}" 2>&1)
  fi
  if grep -q '^VERIFICATION SUCCESSFUL' <<<"$out"; then
    echo "OK    $name ($((SECONDS - t0)) s)"
  else
    echo "FAIL  $name ($((SECONDS - t0)) s)"; grep -E 'FAILURE|ERROR|error' <<<"$out" | head -5; fail=1
  fi
}
prove "cap 4 get"          -DCAP=4 -DOP=0 --unwind 9
prove "cap 4 place"        -DCAP=4 -DOP=1 --unwind 9
prove "cap 4 remove"       -DCAP=4 -DOP=2 --unwind 9
for c in 0 1 2 3; do
  prove "cap 4 grow, $c present" -DCAP=4 -DOP=3 -DCOUNT=$c --unwind 9
done
prove "cap 8 get"          -DCAP=8 -DOP=0 --unwind 9
prove "cap 8 place"        -DCAP=8 -DOP=1 --unwind 9
prove "cap 8 remove"       -DCAP=8 -DOP=2 --unwind 9
prove "cap 8 grow, 4 present" -DCAP=8 -DOP=3 -DCOUNT=4 --unwind 9
echo "cbmc exit $fail"; exit $fail
