#!/bin/bash
# verify-factlog-emit.sh — the fact log's binary format has one owner, lean/Evm/FactLog/.
# Fails if src/generated/factlog-schema.lisp, scripts/generated/factlog_schema.py or
# scripts/generated/factlog-vectors.sexp drift from `lake exe emitFactLog` (run in the Lean
# interpreter: the emitter needs no native libraries), then feeds the Lean-emitted vectors to
# both decoders: src/factlog/format.lisp and scripts/factlog.py must decode every sample group
# and index to exactly the sample rows, encode the rows back to exactly the bytes (the raw
# codec), and hash them to the content hash.
set -e
cd "$(dirname "$0")/.."
# `lean --run` reads whatever .olean is there — a stale one fails with no output under set -e.
(cd lean && lake build Evm.FactLog.Format Evm.FactLog.History Evm.FactLog.Examples >/tmp/_factlog_build.log 2>&1) ||
  { echo "FAIL: lake build Evm.FactLog.Format Evm.FactLog.History Evm.FactLog.Examples"; tail -40 /tmp/_factlog_build.log; exit 1; }
for triple in "lisp:src/generated/factlog-schema.lisp" "python:scripts/generated/factlog_schema.py" \
              "vectors:scripts/generated/factlog-vectors.sexp"; do
  what=${triple%%:*}; out=${triple#*:}
  (cd lean && lake env lean --run EmitFactLog.lean $what 2>/tmp/_factlog_emit_$what.err) > /tmp/_factlog_emit_$what ||
    { echo "FAIL: lake env lean --run EmitFactLog.lean $what"; cat /tmp/_factlog_emit_$what.err; exit 1; }
  if cmp -s $out /tmp/_factlog_emit_$what; then echo "$out up to date OK"
  else echo "DRIFT: $out != lake env lean --run EmitFactLog.lean $what"
       echo "  fix: (cd lean && lake env lean --run EmitFactLog.lean $what > ../$out)"; exit 1; fi
done
python3 -I scripts/factlog.py /dev/null vectors scripts/generated/factlog-vectors.sexp
sbcl --script src/factlog/format.lisp /dev/null vectors scripts/generated/factlog-vectors.sexp
