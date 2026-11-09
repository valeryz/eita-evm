#!/bin/bash
# verify-host-emit.sh — fail if src/generated/host.lisp drifts from the Lean
# source of truth (lake exe emitHostCL). The replay LOADS the committed file, so
# a stale artifact means HostEmit.lean changes don't take effect — a silent
# correctness gap (a fix can look applied yet never run). Run in CI / pre-commit.
set -e
cd "$(dirname "$0")/../lean"

# Shared-library lookup for running the emitters: Homebrew on macOS,
# /usr/local/lib (scripts/provision-linux.sh) on Linux.
case "$(uname -s)" in
  Darwin) export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-/opt/homebrew/lib}" ;;
  Linux)  export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}/usr/local/lib" ;;
esac

# A gate that dies silently in CI is useless (2026-10-28: this script exited 1
# with zero output because the failing command's stderr went to /dev/null).
# build LOG TARGETS... — lake build with output captured; the log is the
# diagnosis on failure, so print its tail.
build() {
  local log="$1"; shift
  local rc=0
  lake build "$@" >"$log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: lake build $* (exit $rc), log tail:"; tail -40 "$log"; exit 1
  fi
}

# emit STDERR_LOG ARTIFACT CMD... — run an emitter: stdout is the artifact to
# diff against the committed file, stderr is the diagnosis on failure.
emit() {
  local errlog="$1" artifact="$2"; shift 2
  local rc=0
  "$@" 2>"$errlog" >"$artifact" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: $* (exit $rc), stderr:"; cat "$errlog"; exit 1
  fi
}

build /tmp/_host_emit_build.log emitHostCL
# lake env injects the toolchain lib dir (libc++/libc++abi/libunwind) into
# LD_LIBRARY_PATH/DYLD_LIBRARY_PATH — without it the exe can't start on Linux.
emit /tmp/_host_emit_run.err /tmp/_host_emit_check.lisp lake env ./.lake/build/bin/emitHostCL
if diff -q ../src/generated/host.lisp /tmp/_host_emit_check.lisp >/dev/null 2>&1; then
  echo "host.lisp up to date with HostEmit.lean OK"
else
  echo "DRIFT: src/generated/host.lisp != lake exe emitHostCL"
  echo "  fix: (cd lean && lake exe emitHostCL > ../src/generated/host.lisp)"
  diff ../src/generated/host.lisp /tmp/_host_emit_check.lisp | head -20
  exit 1
fi
# ...the re-costing tool's prices (scripts/reprice.lisp; not loaded by the replay)...
build /tmp/_reprice_emit_build.log emitRepriceCL
emit /tmp/_reprice_emit_run.err /tmp/_reprice_emit_check.lisp lake env ./.lake/build/bin/emitRepriceCL
if cmp -s ../scripts/generated/reprice-amsterdam.lisp /tmp/_reprice_emit_check.lisp; then
  echo "scripts/generated/reprice-amsterdam.lisp up to date with the Lean emitter OK"
else
  echo "DRIFT: scripts/generated/reprice-amsterdam.lisp != lake exe emitRepriceCL"
  echo "  fix: (cd lean && lake exe emitRepriceCL > ../scripts/generated/reprice-amsterdam.lisp)"; exit 1
fi
# ...the derived effect callbacks still carry their proofs against the fork specs (the
# emitter builds the IR terms only; a proof that stopped checking is drift too)...
EFFECT_PROOFS="Evm.CL.EffectSelfdestructProof Evm.CL.EffectSettleProof Evm.CL.EffectEndTxProof Evm.CL.EffectSstoreProof Evm.CL.EffectSloadProof Evm.CL.EffectCreateProof Evm.CL.EffectCallProof Evm.CL.EffectTxProof Evm.CL.EffectSystemProof Evm.CL.EffectBlockProof"
if lake build $EFFECT_PROOFS >/tmp/_effect_proof.log 2>&1 &&
   ! grep -qw sorry Evm/CL/Effect*.lean; then
  echo "effect proofs ($EFFECT_PROOFS) OK, no sorry in Evm/CL/Effect*.lean"
else
  echo "FAIL: an effect proof does not check or has a sorry"; grep -m5 -e error -e sorry /tmp/_effect_proof.log Evm/CL/Effect*.lean; exit 1
fi
# ...the committed interpreter assembly for both backends...
build /tmp/_emit_exe_build.log emitARM64 emitX86Interp
for pair in "emitARM64:handlers.S" "emitX86Interp elf:handlers-x86-elf.S"; do
  exe=${pair%%:*}; out=${pair##*:}
  # $exe is unquoted on purpose: "emitX86Interp elf" passes `elf` as argv[1].
  emit /tmp/_emit_run.err /tmp/_emit_check.S lake env ./.lake/build/bin/$exe
  if cmp -s ../c/$out /tmp/_emit_check.S; then echo "c/$out up to date with the Lean emitter OK"
  else echo "DRIFT: c/$out != lake exe $exe"; echo "  fix: ./build.sh (regenerates it)"; exit 1; fi
done
# ...the native storage path's emitted C: the limb primitives (proved in Evm.CL.LimbC) and
# the effect functions printed from the effect IR (Evm.CL.EffectC)...
build /tmp/_emit_storage_build.log emitLimbC emitStorageC Evm.CL.LimbC
for pair in "emitLimbC:generated/limb_ops.h" "emitStorageC:generated/storage_effect.c"; do
  exe=${pair%%:*}; out=${pair##*:}
  emit /tmp/_emit_run.err /tmp/_emit_check.c lake env ./.lake/build/bin/$exe
  if cmp -s ../c/$out /tmp/_emit_check.c; then echo "c/$out up to date with the Lean emitter OK"
  else echo "DRIFT: c/$out != lake exe $exe"; echo "  fix: (cd lean && lake exe $exe > ../c/$out)"; exit 1; fi
done
# ...and no gas schedule copied by hand into the replay code around it
python3 ../scripts/check-derived-gas.py   # cwd is lean/ here
# ...and the committed interpreter runs against CHECKING callbacks (c/test_interp.c: the
# EXTCODECOPY case failed on handlers.S from f812945 on, but nothing ran it)
make -C ../c test_interp >/dev/null && echo "c/test_interp (handler callbacks pass their arguments) OK"
