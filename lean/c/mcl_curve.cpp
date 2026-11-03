/*
 * mcl_curve.cpp — the one place that calls mclBn_init, and it only ever calls
 * it for BN254. See mcl_curve.h for why that is a hard rule.
 */
#define MCL_DONT_USE_OPENSSL
#define MCL_USE_VINT
#define MCL_VINT_FIXED_BUFFER
#define MCL_SIZEOF_UNIT 8
#include <mcl/bn_c384_256.h>
#include <stdio.h>
#include "mcl_curve.h"

static int inited = 0;              /* 1 once mclBn_init has been attempted */
static int init_ok = 0;             /* 1 iff it succeeded */
static unsigned long inits = 0;

extern "C" int eita_mcl_curve(int curve) {
    if (curve != MCL_BN_SNARK1) {
        /* The BLS12-381 precompiles live on blst precisely so this cannot be
         * reached. Refusing here, rather than switching, is what makes the
         * 2.8 ms re-init stall unrepresentable. */
        fprintf(stderr,
                "mcl FFI: refusing to activate curve %d. mcl is pinned to BN254 "
                "(MCL_BN_SNARK1=%d); BLS12-381 is served by blst in bls12381.cpp. "
                "Switching mcl's global curve costs ~2.8 ms per round trip and is "
                "unmetered, so it is not allowed.\n", curve, MCL_BN_SNARK1);
        return 0;
    }
    if (inited) return init_ok;

    int rc = mclBn_init(MCL_BN_SNARK1, MCLBN_COMPILED_TIME_VAR);
    inited = 1;
    init_ok = (rc == 0);
    if (!init_ok) {
        /* Typically a libmcl / header MCLBN_COMPILED_TIME_VAR mismatch. */
        fprintf(stderr,
                "mcl FFI: mclBn_init(BN254) failed (rc=%d). The installed libmcl "
                "must match mcl/bn_c384_256.h (Fp=384, Fr=256, CTV=%d).\n",
                rc, MCLBN_COMPILED_TIME_VAR);
        return 0;
    }
    inits++;
    return 1;
}

extern "C" unsigned long eita_mcl_curve_switches(void) { return inits; }
