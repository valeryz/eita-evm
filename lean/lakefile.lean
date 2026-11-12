import Lake
open Lake DSL System

/-- Platform-specific executable link args.

    Crypto libs (all platforms): libsecp256k1 (Evm.Crypto.EcRecover), libmcl
    (Evm.Crypto.Bn254 — EIP-196/197), libcrypto (OpenSSL, P256Verify), and
    vendor/blst's static archive (EIP-2537 BLS12-381, see lean/c/bls12381.cpp).
    blst is a submodule built by its own `build.sh`; the path is relative to
    this package directory, which is the linker's working directory. mcl is NOT
    used for BLS12-381 — switching its global curve cost 2.8 ms per round trip
    and was unmetered, so it is pinned to BN254 (lean/c/mcl_curve.h).

    macOS: Homebrew prefixes; libmcl's dylib install_name is the bare
    "lib/libmcl.dylib", so an rpath entry lets dyld find it at run time. No
    executable links a handler library (none needs an eita_handler_* symbol).

    Linux (aarch64): secp256k1/mcl in /usr/local/lib, libcrypto in /usr/lib64
    (Amazon Linux) or /usr/lib/aarch64-linux-gnu (Debian/Ubuntu).
    The deploy executables (emitARM64/emitHostCL/emitJIT)
    are emitters/validators — none run the threaded interp, so none need a
    handler lib. (interpFixtures, which does, must additionally link
    `c/libeita.so` — built by c/Makefile, which exports the same eita_handler_*
    / eita_dispatch_table symbols — and are outside the deploy bundle.) -/
def evmLinkArgs : Array String :=
  if System.Platform.isOSX then
    #["-L/opt/homebrew/lib",
      "-L/opt/homebrew/opt/openssl@3/lib",
      "-Wl,-rpath,/opt/homebrew/lib",
      "-Wl,-rpath,/opt/homebrew/opt/openssl@3/lib",
      "-lsecp256k1", "-lmcl", "-lcrypto", "-lstdc++",
      "../vendor/blst/libblst.a"]
  else
    -- /usr/lib64: Amazon Linux; /usr/lib/<arch>-linux-gnu: Debian/Ubuntu multiarch
    -- (libcrypto). Lean's bundled lld does not search these on its own.
    #["-L/usr/local/lib", "-L/usr/lib64", "-L/usr/lib/aarch64-linux-gnu", "-L/usr/lib/x86_64-linux-gnu",
      "-Wl,-rpath,/usr/local/lib",
      "-lsecp256k1", "-lmcl", "-lcrypto", "-lstdc++",
      "../vendor/blst/libblst.a"]

package evm where
  -- precompileModules stays false: with it, every module's dynlib links
  -- libevmc and dlopens it during elaboration, where libmcl's bare relative
  -- install_name ("lib/libmcl.dylib") cannot resolve without
  -- DYLD_LIBRARY_PATH (no rpath on that link). The executables get the
  -- rpaths via evmLinkArgs below and resolve it fine.
  precompileModules := false
  moreLinkArgs := evmLinkArgs

require "leanprover-community" / "mathlib" @ git "v4.35.0"

/-- Every module under `Evm/` is part of the default build, not only those reachable from
    `Evm.lean`: an orphaned module (nothing imports it) is still compiled, so it cannot rot
    unnoticed (four had, 2026-11-02). -/
@[default_target]
lean_lib Evm where
  globs := #[.andSubmodules `Evm]

lean_exe test where
  root := `Test

lean_exe replay where
  root := `Replay

lean_exe mainnet where
  root := `Mainnet

lean_exe baseProbe where
  root := `BaseProbe

lean_exe baseReplay where
  root := `BaseReplay

lean_exe interpFixtures where
  root := `InterpFixtures

lean_exe emitARM64 where
  root := `EmitARM64

lean_exe asmGadgetVectors where
  root := `AsmGadgetVectors

lean_exe x86RunVectors where
  root := `X86RunVectors

lean_exe x86AsmVectors where
  root := `X86AsmVectors

lean_exe x86ItemsVectors where
  root := `X86ItemsVectors

lean_exe x86EncodeVectors where
  root := `X86EncodeVectors

lean_exe asmItemsVectors where
  root := `AsmItemsVectors

lean_exe emitX86 where
  root := `EmitX86

lean_exe emitX86Interp where
  root := `EmitX86Interp

lean_exe emitHostCL where
  root := `EmitHostCL

lean_exe emitRepriceCL where
  root := `EmitRepriceCL

lean_exe emitJIT where
  root := `EmitJIT

lean_exe callGasVectors where
  root := `CallGasVectors

lean_exe asmEncodeVectors where
  root := `AsmEncodeVectors

lean_exe sstoreGasVectors where
  root := `SstoreGasVectors

lean_exe worldSlotsVectors where
  root := `WorldSlotsVectors

lean_exe emitLimbC where
  root := `EmitLimbC

lean_exe emitStorageC where
  root := `EmitStorageC

private def cFlags (extra : Array String := #[]) : FetchM (Array String) := do
  let leanInc := (← getLeanIncludeDir).toString
  return #["-I", leanInc, "-I", "/opt/homebrew/include",
           "-I", "/opt/homebrew/opt/openssl@3/include",
           "-fPIC", "-O2"] ++ extra

/-- Build c/keccak.c → keccak.o. -/
target keccak.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "keccak.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "keccak.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/sha256.c → sha256.o. -/
target sha256.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "sha256.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "sha256.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/ripemd160.c → ripemd160.o. -/
target ripemd160.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "ripemd160.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "ripemd160.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/ecrecover.c → ecrecover.o. -/
target ecrecover.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "ecrecover.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "ecrecover.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/bn254.cpp → bn254.o (C++, links against libmcl). -/
target bn254.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "bn254.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "bn254.cpp"
  buildO oFile srcJob (← cFlags) #[] "c++"

/-- Build c/mcl_curve.cpp → mcl_curve.o. Owns mclBn_init and pins mcl to BN254;
    bn254.o calls into it, so libevmc has an undefined symbol without it. -/
target mcl_curve.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "mcl_curve.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "mcl_curve.cpp"
  buildO oFile srcJob (← cFlags) #[] "c++"

/-- Build c/bls12381.cpp → bls12381.o (EIP-2537, C++, links against blst). The
    header comes from the vendored submodule rather than a system prefix. -/
target bls12381.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "bls12381.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "bls12381.cpp"
  let blstInc := (pkg.dir / ".." / "vendor" / "blst" / "bindings").toString
  buildO oFile srcJob (← cFlags #["-I", blstInc]) #[] "c++"

/-- Build c/point_evaluation.c → point_evaluation.o (EIP-4844 0x0a, over blst). -/
target point_evaluation.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "point_evaluation.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "point_evaluation.c"
  let blstInc := (pkg.dir / ".." / "vendor" / "blst" / "bindings").toString
  buildO oFile srcJob (← cFlags #["-I", blstInc]) #[] "cc"

/-- Build c/p256verify.c → p256verify.o (links against OpenSSL libcrypto). -/
target p256verify.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "p256verify.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "p256verify.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/blake2f.c → blake2f.o (EIP-152 F in C; bound only by the cryptoTests
    differential test — the Lean replay runs the pure-Lean `Evm.Crypto.Blake2f`). -/
target blake2f.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "blake2f.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "blake2f.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/uds.c → uds.o (Unix-domain-socket FFI for the emit server, #235). -/
target uds.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "uds.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "uds.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Build c/csu_shim.c → csu_shim.o. Supplies __libc_csu_init/__libc_csu_fini
    for the inconsistent Lean v4.29.1/v4.35.0 Linux toolchains (aarch64 and x86_64):
    old-style bundled Scrt1.o references those symbols, glibc >= 2.34 dropped
    them, so every `lean_exe` fails to link without the shim. Empty TU on
    macOS. See csu_shim.c. -/
target csu_shim.o pkg : FilePath := do
  let oFile  := pkg.buildDir / "c" / "csu_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "csu_shim.c"
  buildO oFile srcJob (← cFlags) #[] "cc"

/-- Bundle the C objects into one static library that Lake links
    into anything pulling our `@[extern]` bindings. The static lib does
    NOT include libsecp256k1 itself — that's resolved via the package's
    `moreLinkArgs`. -/
extern_lib libevmc pkg := do
  let keccak ← keccak.o.fetch
  let sha    ← sha256.o.fetch
  let rmd    ← ripemd160.o.fetch
  let ecr    ← ecrecover.o.fetch
  let bn     ← bn254.o.fetch
  let mclc   ← mcl_curve.o.fetch
  let bls    ← bls12381.o.fetch
  let p256   ← p256verify.o.fetch
  let kzg    ← point_evaluation.o.fetch
  let b2f    ← blake2f.o.fetch
  let uds    ← uds.o.fetch
  let csu    ← csu_shim.o.fetch
  let name := nameToStaticLib "evmc"
  buildStaticLib (pkg.staticLibDir / name) #[keccak, sha, rmd, ecr, bn, mclc, bls, p256, kzg, b2f, uds, csu]

lean_exe recoveryVectors where
  root := `RecoveryVectors

/-- The crypto oracles against the native libraries (CI): the BLS12-381 and P-256
    contracts of `Evm.Crypto.Contracts` as property tests over blst / OpenSSL, the EIP-2537
    precompiles (Lean wrapper over `native`) against the production C entries and the
    chain's vectors, and the pure-Lean BLAKE2b F against lean/c/blake2f.c. -/
lean_exe cryptoTests where
  root := `CryptoTests


/-- The Lean comparator's challenge (the owner-reviewed statements of the headline theorems)
    and its solution (each proved by the real theorem). Not a default target: only
    `scripts/verify-comparator.sh` builds it, through `lake comparator`. -/
lean_lib Comparator where
  globs := #[.andSubmodules `Comparator]
