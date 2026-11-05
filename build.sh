#!/usr/bin/env bash
## Reproducible Eita build: Lean spec -> emitted assembly + CL host code -> native libeita ->
## the Lisp engine (ASDF, dependencies pinned by ocicl.csv) -> bin/eita, one executable.
## Runs on the target: macOS arm64, Linux aarch64, Linux x86-64. Idempotent; the emit
## steps are deterministic (handlers.S / handlers-x86-elf.S / host.lisp regenerate
## byte-identical, which scripts/verify-host-emit.sh checks).
##
##   ./build.sh              full build (Lean toolchain via elan)
##   ./build.sh --leanless   no Lean: use the committed generated files, interpreter only
##
## Needs SBCL and ocicl (https://github.com/ocicl/ocicl; run `ocicl setup` once). EITA_HEAP_MB
## (default 8192) is bin/eita's default heap; `bin/eita --dynamic-space-size N --end-runtime-options
## <command>` overrides it per run.
set -euo pipefail
cd "$(dirname "$0")"
HERE="$(pwd)"

case "$(uname -m)" in
  arm64|aarch64|x86_64) : ;;
  *) echo "ERROR: unsupported architecture $(uname -m) (arm64/aarch64/x86_64)" >&2; exit 1 ;;
esac

if [ "$(uname -s)" = "Darwin" ]; then
  export DYLD_LIBRARY_PATH="${DYLD_LIBRARY_PATH:-}:/opt/homebrew/lib:$HERE/lean/.lake/build/lib"
  LIBEXT=dylib
else
  export LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:/usr/local/lib:/usr/lib:$HERE/lean/.lake/build/lib"
  LIBEXT=so
fi

## Leanless: --leanless, or auto when lake is absent. Skips the Lean emitters and uses the
## COMMITTED generated artifacts. Run interp-only (EITA_NO_JIT=1): the JIT needs the Lean
## emitJIT daemon.
LEANLESS=0
[ "${1:-}" = "--leanless" ] && LEANLESS=1
command -v lake >/dev/null 2>&1 || { echo "lake not found -> Leanless build (interp-only)"; LEANLESS=1; }

echo "[0/6] vendor/blst (BLS12-381; the Lean executables and libeita link it), vendor/secp256k1"
if [ ! -f vendor/blst/bindings/blst.h ]; then
  echo "ERROR: vendor/blst is empty: clone with --recurse-submodules, or run" >&2
  echo "       git submodule update --init vendor/blst" >&2
  exit 1
fi
[ -f vendor/blst/libblst.a ] || ( cd vendor/blst && ./build.sh >/dev/null )
## vendor/secp256k1: the pinned libsecp256k1 release (c/Makefile builds it static, with cmake)
if [ ! -f vendor/secp256k1/include/secp256k1_recovery.h ]; then
  echo "ERROR: vendor/secp256k1 is empty: git submodule update --init vendor/secp256k1" >&2
  exit 1
fi

if [ "$LEANLESS" = 0 ]; then
  echo "[1/6] mathlib olean cache (no-op when up to date)"
  ( cd lean && lake exe cache get )
  echo "[2/6] lake build: the emitters and the emitJIT daemon (a runtime dependency of the JIT)"
  ( cd lean && lake build emitARM64 emitX86Interp emitHostCL emitJIT )
  echo "[3/6] generate c/handlers.S, c/handlers-x86-elf.S, src/generated/host.lisp from the Lean spec"
  ## `lake env` puts the toolchain's lib dir on the library path (Linux needs it).
  ( cd lean && lake env ./.lake/build/bin/emitARM64 )  > c/handlers.S
  ( cd lean && lake env ./.lake/build/bin/emitX86Interp elf ) > c/handlers-x86-elf.S
  ( cd lean && lake env ./.lake/build/bin/emitHostCL ) > src/generated/host.lisp
else
  echo "[1-3/6] Leanless: using the committed c/handlers.S, c/handlers-x86-elf.S, src/generated/host.lisp"
fi

echo "[4/6] build libeita, libkeccak_batch, libeita_pq ($(uname -s)/$(uname -m))"
make -C c clean >/dev/null && make -C c all >/dev/null
ls -1 c/lib*."$LIBEXT"

echo "[5/6] Lisp dependencies (ocicl.csv)"
command -v ocicl >/dev/null 2>&1 || { echo "ERROR: ocicl not found (https://github.com/ocicl/ocicl)" >&2; exit 1; }
OCICL_RUNTIME="${OCICL_RUNTIME:-${XDG_DATA_HOME:-$HOME/.local/share}/ocicl/ocicl-runtime.lisp}"
[ -f "$OCICL_RUNTIME" ] || { echo "ERROR: no ocicl runtime at $OCICL_RUNTIME: run \`ocicl setup\` once (or set OCICL_RUNTIME)" >&2; exit 1; }
ocicl install >/dev/null 2>&1 || ocicl install

echo "[6/6] bin/eita (asdf:make \"eita/cli\")"
rm -f bin/eita
sbcl --dynamic-space-size "${EITA_HEAP_MB:-8192}" --noinform --non-interactive --no-sysinit --no-userinit \
     --load "$OCICL_RUNTIME" \
     --eval '(setf ocicl-runtime:*download* nil)' \
     --eval '(push (truename ".") asdf:*central-registry*)' \
     --eval '(asdf:make "eita/cli")' >/tmp/eita-build-$$.log 2>&1 \
  || { tail -40 /tmp/eita-build-$$.log; rm -f /tmp/eita-build-$$.log; exit 1; }
rm -f /tmp/eita-build-$$.log
[ -x bin/eita ] || { echo "ERROR: bin/eita was not built" >&2; exit 1; }
## The native artifacts beside the executable: bin/ moves as a whole (src/native/libraries.lisp
## looks next to the executable first).
for f in c/libeita."$LIBEXT" c/libkeccak_batch."$LIBEXT" c/libeita_pq."$LIBEXT" lean/.lake/build/bin/emitJIT; do
  [ -f "$f" ] && cp -p "$f" bin/
done

echo "Build OK: $(bin/eita version | head -1)"
if [ "$LEANLESS" = 1 ]; then echo "  (Leanless -> run interp-only: EITA_NO_JIT=1)"; fi
echo "  REPL:      bin/eita repl                                  (docs/quickstart.md)"
echo "  fixtures:  bin/eita fixtures <BlockchainTests dir or file> (docs/testing.md)"
echo "  a chain:   bin/eita replay --chain ethereum --blocks DIR --from 1 --to 1000   (docs/block-input.md)"
