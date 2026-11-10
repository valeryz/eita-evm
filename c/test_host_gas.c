/* c/test_host_gas.c — EMITTED by `lake exe emitHostC --vectors`; do not edit.
   670 vectors over c/generated/host.c, every expected value computed by
   Evm.CL.GasEmit.Expr.eval in Lean — the meaning the printer is a second view of. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "generated/host.h"

static int fails = 0, checks = 0;

void eita_spec_overflow(const char *where) {
  printf("FAIL: unexpected overflow trap in %s\n", where); exit(1);
}

static void chk(const char *fn, const char *inputs, uint64_t got, uint64_t want) {
  checks++;
  if (got != want) {
    fails++;
    printf("FAIL %s [%s]: C %llu, Lean %llu\n", fn, inputs,
           (unsigned long long)got, (unsigned long long)want);
  }
}

int main(void) {
  /* sha256-gas */
  { chk("eita_spec_sha256_gas", "len=1", eita_spec_sha256_gas(UINT64_C(1)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=0", eita_spec_sha256_gas(UINT64_C(0)), UINT64_C(60)); }
  { chk("eita_spec_sha256_gas", "len=1", eita_spec_sha256_gas(UINT64_C(1)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=2", eita_spec_sha256_gas(UINT64_C(2)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=7", eita_spec_sha256_gas(UINT64_C(7)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=31", eita_spec_sha256_gas(UINT64_C(31)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=32", eita_spec_sha256_gas(UINT64_C(32)), UINT64_C(72)); }
  { chk("eita_spec_sha256_gas", "len=33", eita_spec_sha256_gas(UINT64_C(33)), UINT64_C(84)); }
  { chk("eita_spec_sha256_gas", "len=64", eita_spec_sha256_gas(UINT64_C(64)), UINT64_C(84)); }
  { chk("eita_spec_sha256_gas", "len=65", eita_spec_sha256_gas(UINT64_C(65)), UINT64_C(96)); }
  { chk("eita_spec_sha256_gas", "len=1000", eita_spec_sha256_gas(UINT64_C(1000)), UINT64_C(444)); }
  { chk("eita_spec_sha256_gas", "len=1024", eita_spec_sha256_gas(UINT64_C(1024)), UINT64_C(444)); }
  { chk("eita_spec_sha256_gas", "len=1025", eita_spec_sha256_gas(UINT64_C(1025)), UINT64_C(456)); }
  { chk("eita_spec_sha256_gas", "len=100000", eita_spec_sha256_gas(UINT64_C(100000)), UINT64_C(37560)); }
  /* ripemd160-gas */
  { chk("eita_spec_ripemd160_gas", "len=1", eita_spec_ripemd160_gas(UINT64_C(1)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=0", eita_spec_ripemd160_gas(UINT64_C(0)), UINT64_C(600)); }
  { chk("eita_spec_ripemd160_gas", "len=1", eita_spec_ripemd160_gas(UINT64_C(1)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=2", eita_spec_ripemd160_gas(UINT64_C(2)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=7", eita_spec_ripemd160_gas(UINT64_C(7)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=31", eita_spec_ripemd160_gas(UINT64_C(31)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=32", eita_spec_ripemd160_gas(UINT64_C(32)), UINT64_C(720)); }
  { chk("eita_spec_ripemd160_gas", "len=33", eita_spec_ripemd160_gas(UINT64_C(33)), UINT64_C(840)); }
  { chk("eita_spec_ripemd160_gas", "len=64", eita_spec_ripemd160_gas(UINT64_C(64)), UINT64_C(840)); }
  { chk("eita_spec_ripemd160_gas", "len=65", eita_spec_ripemd160_gas(UINT64_C(65)), UINT64_C(960)); }
  { chk("eita_spec_ripemd160_gas", "len=1000", eita_spec_ripemd160_gas(UINT64_C(1000)), UINT64_C(4440)); }
  { chk("eita_spec_ripemd160_gas", "len=1024", eita_spec_ripemd160_gas(UINT64_C(1024)), UINT64_C(4440)); }
  { chk("eita_spec_ripemd160_gas", "len=1025", eita_spec_ripemd160_gas(UINT64_C(1025)), UINT64_C(4560)); }
  { chk("eita_spec_ripemd160_gas", "len=100000", eita_spec_ripemd160_gas(UINT64_C(100000)), UINT64_C(375600)); }
  /* identity-gas */
  { chk("eita_spec_identity_gas", "len=1", eita_spec_identity_gas(UINT64_C(1)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=0", eita_spec_identity_gas(UINT64_C(0)), UINT64_C(15)); }
  { chk("eita_spec_identity_gas", "len=1", eita_spec_identity_gas(UINT64_C(1)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=2", eita_spec_identity_gas(UINT64_C(2)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=7", eita_spec_identity_gas(UINT64_C(7)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=31", eita_spec_identity_gas(UINT64_C(31)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=32", eita_spec_identity_gas(UINT64_C(32)), UINT64_C(18)); }
  { chk("eita_spec_identity_gas", "len=33", eita_spec_identity_gas(UINT64_C(33)), UINT64_C(21)); }
  { chk("eita_spec_identity_gas", "len=64", eita_spec_identity_gas(UINT64_C(64)), UINT64_C(21)); }
  { chk("eita_spec_identity_gas", "len=65", eita_spec_identity_gas(UINT64_C(65)), UINT64_C(24)); }
  { chk("eita_spec_identity_gas", "len=1000", eita_spec_identity_gas(UINT64_C(1000)), UINT64_C(111)); }
  { chk("eita_spec_identity_gas", "len=1024", eita_spec_identity_gas(UINT64_C(1024)), UINT64_C(111)); }
  { chk("eita_spec_identity_gas", "len=1025", eita_spec_identity_gas(UINT64_C(1025)), UINT64_C(114)); }
  { chk("eita_spec_identity_gas", "len=100000", eita_spec_identity_gas(UINT64_C(100000)), UINT64_C(9390)); }
  /* ecrecover-gas */
  { chk("eita_spec_ecrecover_gas", "", eita_spec_ecrecover_gas(), UINT64_C(3000)); }
  /* p256verify-gas */
  { chk("eita_spec_p256verify_gas", "", eita_spec_p256verify_gas(), UINT64_C(6900)); }
  /* rip7212-gas */
  { chk("eita_spec_rip7212_gas", "", eita_spec_rip7212_gas(), UINT64_C(3450)); }
  /* point-evaluation-gas */
  { chk("eita_spec_point_evaluation_gas", "", eita_spec_point_evaluation_gas(), UINT64_C(50000)); }
  /* auth-intrinsic-per-auth */
  { chk("eita_spec_auth_intrinsic_per_auth", "", eita_spec_auth_intrinsic_per_auth(), UINT64_C(25000)); }
  /* auth-refund-existing */
  { chk("eita_spec_auth_refund_existing", "", eita_spec_auth_refund_existing(), UINT64_C(12500)); }
  /* bn256-add-gas */
  { chk("eita_spec_bn256_add_gas", "fork-ord=1", eita_spec_bn256_add_gas(UINT64_C(1)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=0", eita_spec_bn256_add_gas(UINT64_C(0)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=1", eita_spec_bn256_add_gas(UINT64_C(1)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=2", eita_spec_bn256_add_gas(UINT64_C(2)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=3", eita_spec_bn256_add_gas(UINT64_C(3)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=4", eita_spec_bn256_add_gas(UINT64_C(4)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=5", eita_spec_bn256_add_gas(UINT64_C(5)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=6", eita_spec_bn256_add_gas(UINT64_C(6)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=7", eita_spec_bn256_add_gas(UINT64_C(7)), UINT64_C(500)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=8", eita_spec_bn256_add_gas(UINT64_C(8)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=9", eita_spec_bn256_add_gas(UINT64_C(9)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=10", eita_spec_bn256_add_gas(UINT64_C(10)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=11", eita_spec_bn256_add_gas(UINT64_C(11)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=12", eita_spec_bn256_add_gas(UINT64_C(12)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=13", eita_spec_bn256_add_gas(UINT64_C(13)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=14", eita_spec_bn256_add_gas(UINT64_C(14)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=15", eita_spec_bn256_add_gas(UINT64_C(15)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=16", eita_spec_bn256_add_gas(UINT64_C(16)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=17", eita_spec_bn256_add_gas(UINT64_C(17)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=18", eita_spec_bn256_add_gas(UINT64_C(18)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=19", eita_spec_bn256_add_gas(UINT64_C(19)), UINT64_C(150)); }
  { chk("eita_spec_bn256_add_gas", "fork-ord=20", eita_spec_bn256_add_gas(UINT64_C(20)), UINT64_C(150)); }
  /* bn256-mul-gas */
  { chk("eita_spec_bn256_mul_gas", "fork-ord=1", eita_spec_bn256_mul_gas(UINT64_C(1)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=0", eita_spec_bn256_mul_gas(UINT64_C(0)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=1", eita_spec_bn256_mul_gas(UINT64_C(1)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=2", eita_spec_bn256_mul_gas(UINT64_C(2)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=3", eita_spec_bn256_mul_gas(UINT64_C(3)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=4", eita_spec_bn256_mul_gas(UINT64_C(4)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=5", eita_spec_bn256_mul_gas(UINT64_C(5)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=6", eita_spec_bn256_mul_gas(UINT64_C(6)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=7", eita_spec_bn256_mul_gas(UINT64_C(7)), UINT64_C(40000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=8", eita_spec_bn256_mul_gas(UINT64_C(8)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=9", eita_spec_bn256_mul_gas(UINT64_C(9)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=10", eita_spec_bn256_mul_gas(UINT64_C(10)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=11", eita_spec_bn256_mul_gas(UINT64_C(11)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=12", eita_spec_bn256_mul_gas(UINT64_C(12)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=13", eita_spec_bn256_mul_gas(UINT64_C(13)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=14", eita_spec_bn256_mul_gas(UINT64_C(14)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=15", eita_spec_bn256_mul_gas(UINT64_C(15)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=16", eita_spec_bn256_mul_gas(UINT64_C(16)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=17", eita_spec_bn256_mul_gas(UINT64_C(17)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=18", eita_spec_bn256_mul_gas(UINT64_C(18)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=19", eita_spec_bn256_mul_gas(UINT64_C(19)), UINT64_C(6000)); }
  { chk("eita_spec_bn256_mul_gas", "fork-ord=20", eita_spec_bn256_mul_gas(UINT64_C(20)), UINT64_C(6000)); }
  /* bn256-pairing-gas */
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=0 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(0), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=2 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(2), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=7 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(7), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=31 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(31), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=32 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(32), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=33 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(33), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=64 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(64), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=65 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(65), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1000 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1000), UINT64_C(1)), UINT64_C(500000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1024 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1024), UINT64_C(1)), UINT64_C(500000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1025 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1025), UINT64_C(1)), UINT64_C(500000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=100000 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(100000), UINT64_C(1)), UINT64_C(41700000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=0", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(0)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=1", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=2", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(2)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=3", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(3)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=4", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(4)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=5", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(5)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=6", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(6)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=7", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(7)), UINT64_C(100000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=8", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(8)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=9", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(9)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=10", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(10)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=11", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(11)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=12", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(12)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=13", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(13)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=14", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(14)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=15", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(15)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=16", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(16)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=17", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(17)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=18", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(18)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=19", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(19)), UINT64_C(45000)); }
  { chk("eita_spec_bn256_pairing_gas", "len=1 fork-ord=20", eita_spec_bn256_pairing_gas(UINT64_C(1), UINT64_C(20)), UINT64_C(45000)); }
  /* bls-g1add-gas */
  { chk("eita_spec_bls_g1add_gas", "", eita_spec_bls_g1add_gas(), UINT64_C(375)); }
  /* bls-g2add-gas */
  { chk("eita_spec_bls_g2add_gas", "", eita_spec_bls_g2add_gas(), UINT64_C(600)); }
  /* bls-map-fp-to-g1-gas */
  { chk("eita_spec_bls_map_fp_to_g1_gas", "", eita_spec_bls_map_fp_to_g1_gas(), UINT64_C(5500)); }
  /* bls-map-fp2-to-g2-gas */
  { chk("eita_spec_bls_map_fp2_to_g2_gas", "", eita_spec_bls_map_fp2_to_g2_gas(), UINT64_C(23800)); }
  /* bls-pairing-gas */
  { chk("eita_spec_bls_pairing_gas", "len=1", eita_spec_bls_pairing_gas(UINT64_C(1)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=0", eita_spec_bls_pairing_gas(UINT64_C(0)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=1", eita_spec_bls_pairing_gas(UINT64_C(1)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=2", eita_spec_bls_pairing_gas(UINT64_C(2)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=7", eita_spec_bls_pairing_gas(UINT64_C(7)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=31", eita_spec_bls_pairing_gas(UINT64_C(31)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=32", eita_spec_bls_pairing_gas(UINT64_C(32)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=33", eita_spec_bls_pairing_gas(UINT64_C(33)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=64", eita_spec_bls_pairing_gas(UINT64_C(64)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=65", eita_spec_bls_pairing_gas(UINT64_C(65)), UINT64_C(37700)); }
  { chk("eita_spec_bls_pairing_gas", "len=1000", eita_spec_bls_pairing_gas(UINT64_C(1000)), UINT64_C(102900)); }
  { chk("eita_spec_bls_pairing_gas", "len=1024", eita_spec_bls_pairing_gas(UINT64_C(1024)), UINT64_C(102900)); }
  { chk("eita_spec_bls_pairing_gas", "len=1025", eita_spec_bls_pairing_gas(UINT64_C(1025)), UINT64_C(102900)); }
  { chk("eita_spec_bls_pairing_gas", "len=100000", eita_spec_bls_pairing_gas(UINT64_C(100000)), UINT64_C(8513700)); }
  /* intrinsic-gas */
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=0 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(25372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=2 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=7 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=31 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=32 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=33 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=64 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=65 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1000 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1024 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1025 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=100000 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=0 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=2 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=7 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=31 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=32 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=33 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=64 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=65 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1000 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1024 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1025 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=100000 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=0 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57368)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=2 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57376)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=7 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57396)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=31 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57492)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=32 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57496)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=33 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57500)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=64 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57624)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=65 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57628)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1000 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(61368)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1024 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(61464)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1025 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(61468)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=100000 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(457368)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=0 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57304)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=2 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57440)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=7 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57780)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=31 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(59412)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=32 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(59480)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=33 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(59548)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=64 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(61656)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=65 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(61724)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1000 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(125304)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1024 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(126936)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1025 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(127004)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=100000 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(6857304)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=0 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1)), UINT64_C(54972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=2 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1)), UINT64_C(59772)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=7 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1)), UINT64_C(71772)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=31 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1)), UINT64_C(129372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=32 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1)), UINT64_C(131772)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=33 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1)), UINT64_C(134172)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=64 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1)), UINT64_C(208572)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=65 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1)), UINT64_C(210972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1000 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1)), UINT64_C(2454972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1024 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1)), UINT64_C(2512572)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1025 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1)), UINT64_C(2514972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=100000 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1)), UINT64_C(240054972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=0 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1)), UINT64_C(55472)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=2 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1)), UINT64_C(59272)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=7 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1)), UINT64_C(68772)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=31 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1)), UINT64_C(114372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=32 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1)), UINT64_C(116272)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=33 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1)), UINT64_C(118172)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=64 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1)), UINT64_C(177072)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=65 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1)), UINT64_C(178972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1000 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1)), UINT64_C(1955472)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1024 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1)), UINT64_C(2001072)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1025 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1)), UINT64_C(2002972)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=100000 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1)), UINT64_C(190055472)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=0", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0)), UINT64_C(25372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=1", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=2", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=3", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(3)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=4", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(4)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=5", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(5)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=6", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(6)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=7", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7)), UINT64_C(57372)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=8", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(8)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=9", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(9)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=10", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(10)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=11", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(11)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=12", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(12)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=13", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(13)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=14", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(14)), UINT64_C(57320)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=15", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(15)), UINT64_C(57322)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=16", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(16)), UINT64_C(57322)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=17", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(17)), UINT64_C(57322)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=18", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(18)), UINT64_C(57322)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=19", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(19)), UINT64_C(57322)); }
  { chk("eita_spec_intrinsic_gas", "is-create=1 data-len=1 zero-bytes=1 nonzero-bytes=1 al-addrs=1 al-keys=1 fork-ord=20", eita_spec_intrinsic_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(20)), UINT64_C(57322)); }
  /* code-deposit-gas */
  { chk("eita_spec_code_deposit_gas", "nbytes=1", eita_spec_code_deposit_gas(UINT64_C(1)), UINT64_C(200)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=0", eita_spec_code_deposit_gas(UINT64_C(0)), UINT64_C(0)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=1", eita_spec_code_deposit_gas(UINT64_C(1)), UINT64_C(200)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=2", eita_spec_code_deposit_gas(UINT64_C(2)), UINT64_C(400)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=7", eita_spec_code_deposit_gas(UINT64_C(7)), UINT64_C(1400)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=31", eita_spec_code_deposit_gas(UINT64_C(31)), UINT64_C(6200)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=32", eita_spec_code_deposit_gas(UINT64_C(32)), UINT64_C(6400)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=33", eita_spec_code_deposit_gas(UINT64_C(33)), UINT64_C(6600)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=64", eita_spec_code_deposit_gas(UINT64_C(64)), UINT64_C(12800)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=65", eita_spec_code_deposit_gas(UINT64_C(65)), UINT64_C(13000)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=1000", eita_spec_code_deposit_gas(UINT64_C(1000)), UINT64_C(200000)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=1024", eita_spec_code_deposit_gas(UINT64_C(1024)), UINT64_C(204800)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=1025", eita_spec_code_deposit_gas(UINT64_C(1025)), UINT64_C(205000)); }
  { chk("eita_spec_code_deposit_gas", "nbytes=100000", eita_spec_code_deposit_gas(UINT64_C(100000)), UINT64_C(20000000)); }
  /* create-gas */
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=0 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(0), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=2 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(2), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=3 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(3), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=4 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(4), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=5 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(5), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=6 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(6), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=7 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(7), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=8 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(8), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=9 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(9), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=10 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(10), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=11 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(11), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=12 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(12), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=13 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(13), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=14 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(14), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=15 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(15), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=16 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(16), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=17 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(17), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=18 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(18), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=19 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(19), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=20 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(20), UINT64_C(1), UINT64_C(1)), UINT64_C(32008)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=0 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(0), UINT64_C(1)), UINT64_C(32000)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=2 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(2), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=7 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(7), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=31 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(31), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=32 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(32), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=33 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(33), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=64 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(64), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=65 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(65), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1000 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1000), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1024 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1024), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1025 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1025), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=100000 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(100000), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=0", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(0)), UINT64_C(32000)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=2", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(2)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=7", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(7)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=31", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(31)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=32", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(32)), UINT64_C(32006)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=33", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(33)), UINT64_C(32012)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=64", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(64)), UINT64_C(32012)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=65", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(65)), UINT64_C(32018)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1000", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1000)), UINT64_C(32192)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1024", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1024)), UINT64_C(32192)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=1025", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1025)), UINT64_C(32198)); }
  { chk("eita_spec_create_gas", "fork-ord=1 is-create2=1 initcode-len=100000", eita_spec_create_gas(UINT64_C(1), UINT64_C(1), UINT64_C(100000)), UINT64_C(50750)); }
  /* create-initcode-oversize */
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=0 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(0), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=2 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(2), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=3 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(3), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=4 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(4), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=5 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(5), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=6 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(6), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=7 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(7), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=8 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(8), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=9 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(9), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=10 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(10), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=11 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(11), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=12 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(12), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=13 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(13), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=14 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(14), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=15 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(15), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=16 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(16), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=17 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(17), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=18 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(18), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=19 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(19), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=20 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(20), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=0", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(0)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=2", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(2)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=7", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(7)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=31", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(31)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=32", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(32)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=33", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(33)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=64", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(64)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=65", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(65)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1000", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1000)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1024", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1024)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=1025", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(1025)), UINT64_C(0)); }
  { chk("eita_spec_create_initcode_oversize", "fork-ord=1 initcode-len=100000", eita_spec_create_initcode_oversize(UINT64_C(1), UINT64_C(100000)), UINT64_C(0)); }
  /* selfdestruct-refund */
  { chk("eita_spec_selfdestruct_refund", "fork-ord=1", eita_spec_selfdestruct_refund(UINT64_C(1)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=0", eita_spec_selfdestruct_refund(UINT64_C(0)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=1", eita_spec_selfdestruct_refund(UINT64_C(1)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=2", eita_spec_selfdestruct_refund(UINT64_C(2)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=3", eita_spec_selfdestruct_refund(UINT64_C(3)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=4", eita_spec_selfdestruct_refund(UINT64_C(4)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=5", eita_spec_selfdestruct_refund(UINT64_C(5)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=6", eita_spec_selfdestruct_refund(UINT64_C(6)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=7", eita_spec_selfdestruct_refund(UINT64_C(7)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=8", eita_spec_selfdestruct_refund(UINT64_C(8)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=9", eita_spec_selfdestruct_refund(UINT64_C(9)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=10", eita_spec_selfdestruct_refund(UINT64_C(10)), UINT64_C(24000)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=11", eita_spec_selfdestruct_refund(UINT64_C(11)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=12", eita_spec_selfdestruct_refund(UINT64_C(12)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=13", eita_spec_selfdestruct_refund(UINT64_C(13)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=14", eita_spec_selfdestruct_refund(UINT64_C(14)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=15", eita_spec_selfdestruct_refund(UINT64_C(15)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=16", eita_spec_selfdestruct_refund(UINT64_C(16)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=17", eita_spec_selfdestruct_refund(UINT64_C(17)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=18", eita_spec_selfdestruct_refund(UINT64_C(18)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=19", eita_spec_selfdestruct_refund(UINT64_C(19)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_refund", "fork-ord=20", eita_spec_selfdestruct_refund(UINT64_C(20)), UINT64_C(0)); }
  /* calldata-floor-gas */
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=0 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(0), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=2 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(2), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=7 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(7), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=31 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(31), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=32 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(32), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=33 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(33), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=64 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(64), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=65 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(65), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1000 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1000), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1024 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1024), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1025 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1025), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=100000 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(100000), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=0 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(0), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=2 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(2), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=7 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(7), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=31 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(31), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=32 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(32), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=33 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(33), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=64 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(64), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=65 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(65), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1000 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1000), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1024 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1024), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1025 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1025), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=100000 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(100000), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=0", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(0)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=2", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(2)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=3", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(3)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=4", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(4)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=5", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(5)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=6", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(6)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=7", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(7)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=8", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(8)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=9", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(9)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=10", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(10)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=11", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(11)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=12", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(12)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=13", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(13)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=14", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(14)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=15", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(15)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=16", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(16)), UINT64_C(0)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=17", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(17)), UINT64_C(21050)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=18", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(18)), UINT64_C(21050)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=19", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(19)), UINT64_C(21050)); }
  { chk("eita_spec_calldata_floor_gas", "zero-bytes=1 nonzero-bytes=1 fork-ord=20", eita_spec_calldata_floor_gas(UINT64_C(1), UINT64_C(1), UINT64_C(20)), UINT64_C(21050)); }
  /* tx-gas-used */
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=0 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=2 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=7 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(6)); }
  { chk("eita_spec_tx_gas_used", "gas-used=31 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(30)); }
  { chk("eita_spec_tx_gas_used", "gas-used=32 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(31)); }
  { chk("eita_spec_tx_gas_used", "gas-used=33 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(32)); }
  { chk("eita_spec_tx_gas_used", "gas-used=64 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(63)); }
  { chk("eita_spec_tx_gas_used", "gas-used=65 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(64)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1000 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(999)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1024 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1023)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1025 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1024)); }
  { chk("eita_spec_tx_gas_used", "gas-used=100000 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(99999)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=0 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=2 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=7 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=31 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=32 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=33 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=64 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=65 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1000 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1024 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1025 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=100000 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=0 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=2 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=7 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=31 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=32 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=33 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=64 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=65 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1000 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1024 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1025 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=100000 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=0 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=2 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=7 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=31 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(31), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=32 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(32), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=33 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(33), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=64 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(64), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=65 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(65), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1000 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1000), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1024 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1024), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1025 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1025), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=100000 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(100000), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=0", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(0)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=1", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=2", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(2)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=3", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(3)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=4", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(4)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=5", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(5)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=6", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(6)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=7", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(7)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=8", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(8)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=9", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(9)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=10", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(10)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=11", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(11)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=12", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(12)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=13", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(13)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=14", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(14)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=15", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(15)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=16", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(16)), UINT64_C(1)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=17", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(17)), UINT64_C(21050)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=18", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(18)), UINT64_C(21050)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=19", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(19)), UINT64_C(21050)); }
  { chk("eita_spec_tx_gas_used", "gas-used=1 refund-counter=1 zero-bytes=1 nonzero-bytes=1 fork-ord=20", eita_spec_tx_gas_used(UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(1), UINT64_C(20)), UINT64_C(21050)); }
  /* selfdestruct-cold-gas */
  { chk("eita_spec_selfdestruct_cold_gas", "cold=1", eita_spec_selfdestruct_cold_gas(UINT64_C(1)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=0", eita_spec_selfdestruct_cold_gas(UINT64_C(0)), UINT64_C(0)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=1", eita_spec_selfdestruct_cold_gas(UINT64_C(1)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=2", eita_spec_selfdestruct_cold_gas(UINT64_C(2)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=7", eita_spec_selfdestruct_cold_gas(UINT64_C(7)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=31", eita_spec_selfdestruct_cold_gas(UINT64_C(31)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=32", eita_spec_selfdestruct_cold_gas(UINT64_C(32)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=33", eita_spec_selfdestruct_cold_gas(UINT64_C(33)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=64", eita_spec_selfdestruct_cold_gas(UINT64_C(64)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=65", eita_spec_selfdestruct_cold_gas(UINT64_C(65)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=1000", eita_spec_selfdestruct_cold_gas(UINT64_C(1000)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=1024", eita_spec_selfdestruct_cold_gas(UINT64_C(1024)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=1025", eita_spec_selfdestruct_cold_gas(UINT64_C(1025)), UINT64_C(2600)); }
  { chk("eita_spec_selfdestruct_cold_gas", "cold=100000", eita_spec_selfdestruct_cold_gas(UINT64_C(100000)), UINT64_C(2600)); }
  /* delegate-access-gas */
  { chk("eita_spec_delegate_access_gas", "cold=1", eita_spec_delegate_access_gas(UINT64_C(1)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=0", eita_spec_delegate_access_gas(UINT64_C(0)), UINT64_C(100)); }
  { chk("eita_spec_delegate_access_gas", "cold=1", eita_spec_delegate_access_gas(UINT64_C(1)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=2", eita_spec_delegate_access_gas(UINT64_C(2)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=7", eita_spec_delegate_access_gas(UINT64_C(7)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=31", eita_spec_delegate_access_gas(UINT64_C(31)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=32", eita_spec_delegate_access_gas(UINT64_C(32)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=33", eita_spec_delegate_access_gas(UINT64_C(33)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=64", eita_spec_delegate_access_gas(UINT64_C(64)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=65", eita_spec_delegate_access_gas(UINT64_C(65)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=1000", eita_spec_delegate_access_gas(UINT64_C(1000)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=1024", eita_spec_delegate_access_gas(UINT64_C(1024)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=1025", eita_spec_delegate_access_gas(UINT64_C(1025)), UINT64_C(2600)); }
  { chk("eita_spec_delegate_access_gas", "cold=100000", eita_spec_delegate_access_gas(UINT64_C(100000)), UINT64_C(2600)); }
  /* retain-63-64 */
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=0 fork-ord=1", eita_spec_retain_63_64(UINT64_C(0), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=2 fork-ord=1", eita_spec_retain_63_64(UINT64_C(2), UINT64_C(1)), UINT64_C(2)); }
  { chk("eita_spec_retain_63_64", "gas=7 fork-ord=1", eita_spec_retain_63_64(UINT64_C(7), UINT64_C(1)), UINT64_C(7)); }
  { chk("eita_spec_retain_63_64", "gas=31 fork-ord=1", eita_spec_retain_63_64(UINT64_C(31), UINT64_C(1)), UINT64_C(31)); }
  { chk("eita_spec_retain_63_64", "gas=32 fork-ord=1", eita_spec_retain_63_64(UINT64_C(32), UINT64_C(1)), UINT64_C(32)); }
  { chk("eita_spec_retain_63_64", "gas=33 fork-ord=1", eita_spec_retain_63_64(UINT64_C(33), UINT64_C(1)), UINT64_C(33)); }
  { chk("eita_spec_retain_63_64", "gas=64 fork-ord=1", eita_spec_retain_63_64(UINT64_C(64), UINT64_C(1)), UINT64_C(64)); }
  { chk("eita_spec_retain_63_64", "gas=65 fork-ord=1", eita_spec_retain_63_64(UINT64_C(65), UINT64_C(1)), UINT64_C(65)); }
  { chk("eita_spec_retain_63_64", "gas=1000 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1000), UINT64_C(1)), UINT64_C(1000)); }
  { chk("eita_spec_retain_63_64", "gas=1024 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1024), UINT64_C(1)), UINT64_C(1024)); }
  { chk("eita_spec_retain_63_64", "gas=1025 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1025), UINT64_C(1)), UINT64_C(1025)); }
  { chk("eita_spec_retain_63_64", "gas=100000 fork-ord=1", eita_spec_retain_63_64(UINT64_C(100000), UINT64_C(1)), UINT64_C(100000)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=0", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(0)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=1", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(1)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=2", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(2)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=3", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(3)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=4", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(4)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=5", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(5)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=6", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(6)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=7", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(7)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=8", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(8)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=9", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(9)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=10", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(10)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=11", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(11)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=12", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(12)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=13", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(13)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=14", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(14)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=15", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(15)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=16", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(16)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=17", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(17)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=18", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(18)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=19", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(19)), UINT64_C(1)); }
  { chk("eita_spec_retain_63_64", "gas=1 fork-ord=20", eita_spec_retain_63_64(UINT64_C(1), UINT64_C(20)), UINT64_C(1)); }
  /* new-account-fee */
  { chk("eita_spec_new_account_fee", "", eita_spec_new_account_fee(), UINT64_C(25000)); }
  /* max-blob-gas-per-block */
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=1", eita_spec_max_blob_gas_per_block(UINT64_C(1)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=0", eita_spec_max_blob_gas_per_block(UINT64_C(0)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=1", eita_spec_max_blob_gas_per_block(UINT64_C(1)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=2", eita_spec_max_blob_gas_per_block(UINT64_C(2)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=3", eita_spec_max_blob_gas_per_block(UINT64_C(3)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=4", eita_spec_max_blob_gas_per_block(UINT64_C(4)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=5", eita_spec_max_blob_gas_per_block(UINT64_C(5)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=6", eita_spec_max_blob_gas_per_block(UINT64_C(6)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=7", eita_spec_max_blob_gas_per_block(UINT64_C(7)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=8", eita_spec_max_blob_gas_per_block(UINT64_C(8)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=9", eita_spec_max_blob_gas_per_block(UINT64_C(9)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=10", eita_spec_max_blob_gas_per_block(UINT64_C(10)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=11", eita_spec_max_blob_gas_per_block(UINT64_C(11)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=12", eita_spec_max_blob_gas_per_block(UINT64_C(12)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=13", eita_spec_max_blob_gas_per_block(UINT64_C(13)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=14", eita_spec_max_blob_gas_per_block(UINT64_C(14)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=15", eita_spec_max_blob_gas_per_block(UINT64_C(15)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=16", eita_spec_max_blob_gas_per_block(UINT64_C(16)), UINT64_C(786432)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=17", eita_spec_max_blob_gas_per_block(UINT64_C(17)), UINT64_C(1179648)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=18", eita_spec_max_blob_gas_per_block(UINT64_C(18)), UINT64_C(1179648)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=19", eita_spec_max_blob_gas_per_block(UINT64_C(19)), UINT64_C(1966080)); }
  { chk("eita_spec_max_blob_gas_per_block", "fork-ord=20", eita_spec_max_blob_gas_per_block(UINT64_C(20)), UINT64_C(2752512)); }
  /* tx-max-gas-limit */
  { chk("eita_spec_tx_max_gas_limit", "", eita_spec_tx_max_gas_limit(), UINT64_C(16777216)); }
  /* modexp-gas */
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=0 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(0), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=2 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(2), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=7 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(7), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(2)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=31 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(31), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(48)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=32 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(32), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(51)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=33 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(33), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(54)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=64 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(64), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(204)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=65 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(65), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(211)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1000 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1000), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(17146)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1024 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1024), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(17868)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1025 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1025), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(17899)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=100000 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(100000), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(33640016)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=0 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(0), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=2 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(2), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=7 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(7), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=31 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(31), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=32 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(32), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=33 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(33), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=64 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(64), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(12)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=65 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(65), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(13)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1000 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1000), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(387)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1024 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1024), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(396)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1025 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1025), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(397)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=100000 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(100000), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(39987)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=0 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(0), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=2 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(2), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=7 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(7), exp_head, UINT64_C(1)), UINT64_C(2)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=31 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(31), exp_head, UINT64_C(1)), UINT64_C(48)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=32 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(32), exp_head, UINT64_C(1)), UINT64_C(51)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=33 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(33), exp_head, UINT64_C(1)), UINT64_C(54)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=64 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(64), exp_head, UINT64_C(1)), UINT64_C(204)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=65 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(65), exp_head, UINT64_C(1)), UINT64_C(211)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1000 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1000), exp_head, UINT64_C(1)), UINT64_C(17146)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1024 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1024), exp_head, UINT64_C(1)), UINT64_C(17868)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1025 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1025), exp_head, UINT64_C(1)), UINT64_C(17899)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=100000 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(100000), exp_head, UINT64_C(1)), UINT64_C(33640016)); }
  { const uint64_t exp_head[4] = {UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=0 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(255), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=255 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(9223372036854775808), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=9223372036854775808 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(3)); }
  { const uint64_t exp_head[4] = {UINT64_C(18446744073709551615), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=18446744073709551615 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(3)); }
  { const uint64_t exp_head[4] = {UINT64_C(0), UINT64_C(1), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=18446744073709551616 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(3)); }
  { const uint64_t exp_head[4] = {UINT64_C(0), UINT64_C(0), UINT64_C(1), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=340282366920938463463374607431768211456 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(6)); }
  { const uint64_t exp_head[4] = {UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(256)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1606938044258990275541962092341162602522202993782792835301376 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(10)); }
  { const uint64_t exp_head[4] = {UINT64_C(18446744073709551615), UINT64_C(18446744073709551615), UINT64_C(18446744073709551615), UINT64_C(18446744073709551615)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=115792089237316195423570985008687907853269984665640564039457584007913129639935 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(12)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=0", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(0)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=1", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(1)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=2", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(2)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=3", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(3)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=4", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(4)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=5", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(5)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=6", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(6)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=7", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(7)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=8", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(8)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=9", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(9)), UINT64_C(0)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=10", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(10)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=11", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(11)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=12", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(12)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=13", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(13)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=14", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(14)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=15", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(15)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=16", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(16)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=17", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(17)), UINT64_C(200)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=18", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(18)), UINT64_C(500)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=19", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(19)), UINT64_C(500)); }
  { const uint64_t exp_head[4] = {UINT64_C(1), UINT64_C(0), UINT64_C(0), UINT64_C(0)}; chk("eita_spec_modexp_gas", "base-sz=1 exp-sz=1 mod-sz=1 exp-head=1 fork-ord=20", eita_spec_modexp_gas(UINT64_C(1), UINT64_C(1), UINT64_C(1), exp_head, UINT64_C(20)), UINT64_C(500)); }
  /* mainnet-fork-ord */
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=0 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(0), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=2 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(2), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=7 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(7), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=31 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(31), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=32 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(32), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=33 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(33), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=64 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(64), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=65 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(65), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1000 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1000), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1024 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1024), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1025 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1025), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=100000 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(100000), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=0", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(0)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=2", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(2)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=7", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(7)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=31", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(31)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=32", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(32)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=33", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(33)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=64", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(64)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=65", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(65)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1000", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1000)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1024", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1024)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=1025", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(1025)), UINT64_C(0)); }
  { chk("eita_spec_mainnet_fork_ord", "n=1 ts=100000", eita_spec_mainnet_fork_ord(UINT64_C(1), UINT64_C(100000)), UINT64_C(0)); }
  printf("host gas vectors: %d checked, %d failed\n", checks, fails);
  return fails != 0;
}
