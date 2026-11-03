/*
 * mcl_curve.h — mcl is PINNED to BN254 (MCL_BN_SNARK1) for the life of the
 * process. Nothing may switch it.
 *
 * mcl keeps the curve parameters (field modulus, Montgomery constants, curve b,
 * pairing loop count) in process-global state set by mclBn_init, and every mcl
 * value is stored in Montgomery form for whichever modulus is active. Serving
 * both of the EVM's pairing families from it therefore meant re-initialising on
 * every change of family, which measured 2.8 ms per round trip against 0.78 ms
 * for a full 2-pair pairing check — and was charged no gas, so a transaction
 * alternating a 375-gas BLS G1ADD with a 150-gas BN254 add could buy on the
 * order of 80 seconds of switching inside one 30M-gas block.
 *
 * The EIP-2537 BLS12-381 precompiles are therefore built on blst (see
 * bls12381.cpp), which carries no global curve state, and mcl is left to BN254
 * alone. `eita_mcl_curve` rejects any other curve id rather than honouring it,
 * so the stall is unrepresentable instead of merely avoided: the only way to
 * reintroduce it is to delete this check.
 */
#ifndef EITA_MCL_CURVE_H
#define EITA_MCL_CURVE_H

#ifdef __cplusplus
extern "C" {
#endif

/* Ensure mcl is initialised for BN254. `curve` must be MCL_BN_SNARK1 (4);
 * anything else is a programming error — it complains on stderr and returns 0
 * without touching mcl's state. Returns 1 when mcl is ready to be called, 0
 * when init failed (the caller must then not touch any other mcl API).
 * Idempotent and cheap: after the first call it is a load and a compare. */
int eita_mcl_curve(int curve);

/* Number of times mcl has actually been initialised. Pinned to one curve this
 * is 0 before the first precompile call and 1 forever after; it exists so the
 * replay can ASSERT that, which is the observable form of the guarantee above.
 * (It was a switch counter when mcl served both curves.) */
unsigned long eita_mcl_curve_switches(void);

#ifdef __cplusplus
}
#endif

#endif /* EITA_MCL_CURVE_H */
