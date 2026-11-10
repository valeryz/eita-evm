/* c/generated/host.c — EMITTED by `lake exe emitHostC` from lean/Evm/CL/GasEmitC.lean;
   do not edit. Each function is the C printing of the same Evm.CL.GasEmit term that
   src/generated/host.lisp prints as Common Lisp, so a C host and the Lisp host compute
   one formula, owned by Lean. Regenerate, never hand-edit (CONTRIBUTING rule 2). */
#include "host.h"

/* The checked arithmetic the printer targets. `eita_spec_overflow` is the
   consumer's: a replay host may abort, a signing device must refuse to sign. */
void eita_spec_overflow(const char *where) __attribute__((noreturn));

static inline uint64_t eita_c_add(uint64_t a, uint64_t b) {
  uint64_t r; if (__builtin_add_overflow(a, b, &r)) eita_spec_overflow("add"); return r;
}
static inline uint64_t eita_c_mul(uint64_t a, uint64_t b) {
  uint64_t r; if (__builtin_mul_overflow(a, b, &r)) eita_spec_overflow("mul"); return r;
}
/* Nat.sub: truncated at zero, = toCL's (max 0 (- a b)) */
static inline uint64_t eita_c_sub(uint64_t a, uint64_t b) { return a > b ? a - b : 0; }
static inline uint64_t eita_c_fdiv(uint64_t a, uint64_t b) {
  if (b == 0) eita_spec_overflow("div0");
  return a / b;
}
static inline uint64_t eita_c_max(uint64_t a, uint64_t b) { return a > b ? a : b; }
static inline uint64_t eita_c_min(uint64_t a, uint64_t b) { return a < b ? a : b; }
/* = CL integer-length on a non-negative integer: blen 0 = 0, else floor(log2 n)+1 */
static inline uint64_t eita_c_blen(uint64_t a) {
  return a == 0 ? 0 : (uint64_t)(64 - __builtin_clzll(a));
}
/* The same, for a 256-bit leaf: four limbs, least significant first. */
static inline uint64_t eita_c_u256_blen(const uint64_t *a) {
  for (int i = 3; i >= 0; i--)
    if (a[i]) return (uint64_t)(64 * i) + (uint64_t)(64 - __builtin_clzll(a[i]));
  return 0;
}
static inline uint64_t eita_c_pow2(uint64_t a) {
  if (a >= 64) eita_spec_overflow("pow2");
  return UINT64_C(1) << a;
}
/* EIP-4844 fake_exponential (EELS cancun/vm/gas.py), the one loop the IR has —
   line for line the same bridge as GasEmit.fakeExponentialCL. */
static inline uint64_t eita_c_fake_exponential(uint64_t factor, uint64_t numerator,
                                               uint64_t denominator) {
  uint64_t i = 1, output = 0, accum = eita_c_mul(factor, denominator);
  while (accum > 0) {
    output = eita_c_add(output, accum);
    accum = eita_c_fdiv(eita_c_mul(accum, numerator), eita_c_mul(denominator, i));
    i++;
  }
  return eita_c_fdiv(output, denominator);
}

/* SHA2-256 precompile (0x02) */
uint64_t eita_spec_sha256_gas(uint64_t len) {
  return eita_c_add(UINT64_C(60), eita_c_mul(UINT64_C(12), eita_c_fdiv(eita_c_add(len, UINT64_C(31)), UINT64_C(32))));
}

uint64_t eita_spec_ripemd160_gas(uint64_t len) {
  return eita_c_add(UINT64_C(600), eita_c_mul(UINT64_C(120), eita_c_fdiv(eita_c_add(len, UINT64_C(31)), UINT64_C(32))));
}

uint64_t eita_spec_identity_gas(uint64_t len) {
  return eita_c_add(UINT64_C(15), eita_c_mul(UINT64_C(3), eita_c_fdiv(eita_c_add(len, UINT64_C(31)), UINT64_C(32))));
}

uint64_t eita_spec_ecrecover_gas(void) {
  return UINT64_C(3000);
}

uint64_t eita_spec_p256verify_gas(void) {
  return UINT64_C(6900);
}

uint64_t eita_spec_rip7212_gas(void) {
  return UINT64_C(3450);
}

uint64_t eita_spec_point_evaluation_gas(void) {
  return UINT64_C(50000);
}

uint64_t eita_spec_auth_intrinsic_per_auth(void) {
  return UINT64_C(25000);
}

uint64_t eita_spec_auth_refund_existing(void) {
  return UINT64_C(12500);
}

uint64_t eita_spec_bn256_add_gas(uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(8)) ? UINT64_C(500) : UINT64_C(150));
}

uint64_t eita_spec_bn256_mul_gas(uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(8)) ? UINT64_C(40000) : UINT64_C(6000));
}

uint64_t eita_spec_bn256_pairing_gas(uint64_t len, uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(8)) ? eita_c_add(UINT64_C(100000), eita_c_mul(UINT64_C(80000), eita_c_fdiv(len, UINT64_C(192)))) : eita_c_add(UINT64_C(45000), eita_c_mul(UINT64_C(34000), eita_c_fdiv(len, UINT64_C(192)))));
}

uint64_t eita_spec_bls_g1add_gas(void) {
  return UINT64_C(375);
}

uint64_t eita_spec_bls_g2add_gas(void) {
  return UINT64_C(600);
}

uint64_t eita_spec_bls_map_fp_to_g1_gas(void) {
  return UINT64_C(5500);
}

uint64_t eita_spec_bls_map_fp2_to_g2_gas(void) {
  return UINT64_C(23800);
}

uint64_t eita_spec_bls_pairing_gas(uint64_t len) {
  return eita_c_add(UINT64_C(37700), eita_c_mul(UINT64_C(32600), eita_c_fdiv(len, UINT64_C(384))));
}

/* EELS calculate_intrinsic_cost (+ EIP-2930 access list, EIP-3860 initcode words) */
uint64_t eita_spec_intrinsic_gas(uint64_t is_create, uint64_t data_len, uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t al_addrs, uint64_t al_keys, uint64_t fork_ord) {
  return eita_c_add(eita_c_add(eita_c_add(UINT64_C(21000), ((UINT64_C(0) < is_create) ? eita_c_add(((fork_ord < UINT64_C(1)) ? UINT64_C(0) : UINT64_C(32000)), ((fork_ord < UINT64_C(15)) ? UINT64_C(0) : eita_c_mul(UINT64_C(2), eita_c_fdiv(eita_c_add(data_len, UINT64_C(31)), UINT64_C(32))))) : UINT64_C(0))), eita_c_add(eita_c_mul(zero_bytes, UINT64_C(4)), eita_c_mul(nonzero_bytes, ((fork_ord < UINT64_C(8)) ? UINT64_C(68) : UINT64_C(16))))), eita_c_add(eita_c_mul(al_addrs, UINT64_C(2400)), eita_c_mul(al_keys, UINT64_C(1900))));
}

uint64_t eita_spec_code_deposit_gas(uint64_t nbytes) {
  return eita_c_mul(UINT64_C(200), nbytes);
}

uint64_t eita_spec_create_gas(uint64_t fork_ord, uint64_t is_create2, uint64_t initcode_len) {
  return eita_c_add(eita_c_add(UINT64_C(32000), ((fork_ord < UINT64_C(15)) ? UINT64_C(0) : eita_c_mul(UINT64_C(2), eita_c_fdiv(eita_c_add(initcode_len, UINT64_C(31)), UINT64_C(32))))), ((UINT64_C(0) < is_create2) ? eita_c_mul(UINT64_C(6), eita_c_fdiv(eita_c_add(initcode_len, UINT64_C(31)), UINT64_C(32))) : UINT64_C(0)));
}

/* EIP-3860 initcode cap */
uint64_t eita_spec_create_initcode_oversize(uint64_t fork_ord, uint64_t initcode_len) {
  return ((fork_ord < UINT64_C(15)) ? UINT64_C(0) : ((UINT64_C(49152) < initcode_len) ? UINT64_C(1) : UINT64_C(0)));
}

uint64_t eita_spec_selfdestruct_refund(uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(11)) ? UINT64_C(24000) : UINT64_C(0));
}

/* EIP-7623 */
uint64_t eita_spec_calldata_floor_gas(uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(17)) ? UINT64_C(0) : eita_c_add(UINT64_C(21000), eita_c_mul(UINT64_C(10), eita_c_add(zero_bytes, eita_c_mul(UINT64_C(4), nonzero_bytes)))));
}

uint64_t eita_spec_tx_gas_used(uint64_t gas_used, uint64_t refund_counter, uint64_t zero_bytes, uint64_t nonzero_bytes, uint64_t fork_ord) {
  return eita_c_max(eita_c_sub(gas_used, eita_c_min(refund_counter, eita_c_fdiv(gas_used, ((fork_ord < UINT64_C(11)) ? UINT64_C(2) : UINT64_C(5))))), ((fork_ord < UINT64_C(17)) ? UINT64_C(0) : eita_c_add(UINT64_C(21000), eita_c_mul(UINT64_C(10), eita_c_add(zero_bytes, eita_c_mul(UINT64_C(4), nonzero_bytes))))));
}

/* EIP-2929 */
uint64_t eita_spec_selfdestruct_cold_gas(uint64_t cold) {
  return ((UINT64_C(0) < cold) ? UINT64_C(2600) : UINT64_C(0));
}

/* EIP-7702 */
uint64_t eita_spec_delegate_access_gas(uint64_t cold) {
  return ((UINT64_C(0) < cold) ? UINT64_C(2600) : UINT64_C(100));
}

uint64_t eita_spec_retain_63_64(uint64_t gas, uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(3)) ? gas : eita_c_sub(gas, eita_c_fdiv(gas, UINT64_C(64))));
}

uint64_t eita_spec_new_account_fee(void) {
  return UINT64_C(25000);
}

uint64_t eita_spec_max_blob_gas_per_block(uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(17)) ? UINT64_C(786432) : ((fork_ord < UINT64_C(19)) ? UINT64_C(1179648) : ((fork_ord < UINT64_C(20)) ? UINT64_C(1966080) : UINT64_C(2752512))));
}

/* EIP-7825 (Osaka+) */
uint64_t eita_spec_tx_max_gas_limit(void) {
  return UINT64_C(16777216);
}

/* MODEXP (0x05): EIP-198 pre-Berlin / EIP-2565 Berlin+ / EIP-7883 Osaka+ */
uint64_t eita_spec_modexp_gas(uint64_t base_sz, uint64_t exp_sz, uint64_t mod_sz, const uint64_t *exp_head, uint64_t fork_ord) {
  return ((fork_ord < UINT64_C(10)) ? eita_c_fdiv(eita_c_mul(((eita_c_max(base_sz, mod_sz) < UINT64_C(65)) ? eita_c_mul(eita_c_max(base_sz, mod_sz), eita_c_max(base_sz, mod_sz)) : ((eita_c_max(base_sz, mod_sz) < UINT64_C(1025)) ? eita_c_add(eita_c_fdiv(eita_c_mul(eita_c_max(base_sz, mod_sz), eita_c_max(base_sz, mod_sz)), UINT64_C(4)), eita_c_sub(eita_c_mul(UINT64_C(96), eita_c_max(base_sz, mod_sz)), UINT64_C(3072))) : eita_c_add(eita_c_fdiv(eita_c_mul(eita_c_max(base_sz, mod_sz), eita_c_max(base_sz, mod_sz)), UINT64_C(16)), eita_c_sub(eita_c_mul(UINT64_C(480), eita_c_max(base_sz, mod_sz)), UINT64_C(199680))))), eita_c_max(eita_c_add(((UINT64_C(32) < exp_sz) ? eita_c_mul(UINT64_C(8), eita_c_sub(exp_sz, UINT64_C(32))) : UINT64_C(0)), eita_c_sub(eita_c_u256_blen(exp_head), UINT64_C(1))), UINT64_C(1))), UINT64_C(20)) : ((fork_ord < UINT64_C(18)) ? eita_c_max(UINT64_C(200), eita_c_fdiv(eita_c_mul(eita_c_mul(eita_c_fdiv(eita_c_add(eita_c_max(base_sz, mod_sz), UINT64_C(7)), UINT64_C(8)), eita_c_fdiv(eita_c_add(eita_c_max(base_sz, mod_sz), UINT64_C(7)), UINT64_C(8))), eita_c_max(eita_c_add(((UINT64_C(32) < exp_sz) ? eita_c_mul(UINT64_C(8), eita_c_sub(exp_sz, UINT64_C(32))) : UINT64_C(0)), eita_c_sub(eita_c_u256_blen(exp_head), UINT64_C(1))), UINT64_C(1))), UINT64_C(3))) : eita_c_max(UINT64_C(500), eita_c_mul(((eita_c_max(base_sz, mod_sz) < UINT64_C(33)) ? UINT64_C(16) : eita_c_mul(UINT64_C(2), eita_c_mul(eita_c_fdiv(eita_c_add(eita_c_max(base_sz, mod_sz), UINT64_C(7)), UINT64_C(8)), eita_c_fdiv(eita_c_add(eita_c_max(base_sz, mod_sz), UINT64_C(7)), UINT64_C(8))))), eita_c_max(eita_c_add(((UINT64_C(32) < exp_sz) ? eita_c_mul(UINT64_C(16), eita_c_sub(exp_sz, UINT64_C(32))) : UINT64_C(0)), eita_c_sub(eita_c_u256_blen(exp_head), UINT64_C(1))), UINT64_C(1))))));
}

/* Ethereum mainnet fork schedule (Evm.Forks.ofBlock) */
uint64_t eita_spec_mainnet_fork_ord(uint64_t n, uint64_t ts) {
  return ((n < UINT64_C(15537394)) ? ((n < UINT64_C(15050000)) ? ((n < UINT64_C(13773000)) ? ((n < UINT64_C(12965000)) ? ((n < UINT64_C(12244000)) ? ((n < UINT64_C(9200000)) ? ((n < UINT64_C(9069000)) ? ((n < UINT64_C(7280000)) ? ((n < UINT64_C(4370000)) ? ((n < UINT64_C(2675000)) ? ((n < UINT64_C(2463000)) ? ((n < UINT64_C(1920000)) ? ((n < UINT64_C(1150000)) ? UINT64_C(0) : UINT64_C(1)) : UINT64_C(2)) : UINT64_C(3)) : UINT64_C(4)) : UINT64_C(5)) : UINT64_C(7)) : UINT64_C(8)) : UINT64_C(9)) : UINT64_C(10)) : UINT64_C(11)) : UINT64_C(12)) : UINT64_C(13)) : ((ts < UINT64_C(1767747671)) ? ((ts < UINT64_C(1765290071)) ? ((ts < UINT64_C(1764798551)) ? ((ts < UINT64_C(1746612311)) ? ((ts < UINT64_C(1710338135)) ? ((ts < UINT64_C(1681338455)) ? UINT64_C(14) : UINT64_C(15)) : UINT64_C(16)) : UINT64_C(17)) : UINT64_C(18)) : UINT64_C(19)) : UINT64_C(20)));
}
