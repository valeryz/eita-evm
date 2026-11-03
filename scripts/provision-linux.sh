#!/usr/bin/env bash
# provision-linux.sh — the C dependencies the Lean executables and libeita link
# against, on Debian/Ubuntu (x86-64 or aarch64). Idempotent; sudo for apt and
# the mcl install only. mcl must be built with MCL_FP_BIT=384 (the bn254 FFI
# includes mcl/bn_c384_256.h); this builds it from source.
set -euo pipefail
echo "== apt"
sudo apt-get update -qq
sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -qq \
  build-essential cmake pkg-config git libsecp256k1-dev libssl-dev libgmp-dev
echo "== mcl (BN254, 384-bit field: bn_c384_256.h)"
if [ ! -f /usr/local/include/mcl/bn_c384_256.h ]; then
  rm -rf /tmp/mcl && git clone -q --depth 1 https://github.com/herumi/mcl /tmp/mcl
  cmake -S /tmp/mcl -B /tmp/mcl/build -DMCL_FP_BIT=384 -DCMAKE_BUILD_TYPE=Release >/dev/null
  cmake --build /tmp/mcl/build -j"$(nproc)" >/dev/null
  sudo cmake --install /tmp/mcl/build >/dev/null
  sudo ldconfig
fi
ls /usr/local/include/mcl/bn_c384_256.h /usr/local/lib/libmcl.* | head -3
echo "== blst (vendored)"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -d "$ROOT/vendor/blst" ] && [ ! -f "$ROOT/vendor/blst/libblst.a" ]; then
  (cd "$ROOT/vendor/blst" && ./build.sh >/dev/null 2>&1) && echo "built libblst.a"
fi
ls "$ROOT/vendor/blst/libblst.a" 2>/dev/null || echo "no vendored blst (ok if not needed on this target)"
echo "== done"
