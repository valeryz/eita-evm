/* c/generated/limb_ops.h — EMITTED by `lake exe emitLimbC` from lean/Evm/CL/LimbC.lean; do not edit.
   Each function is the C printing of a term proved equal to its 256-bit operation there
   (eqB_spec, isZeroB_spec, copyA_spec, zeroA_spec). Limbs: four uint64_t, least significant first. */
#ifndef EITA_LIMB_OPS_H
#define EITA_LIMB_OPS_H
#include <stdint.h>

static inline int limb_eq(const uint64_t *a, const uint64_t *b) { return ((((a[0] == b[0]) & (a[1] == b[1])) & (a[2] == b[2])) & (a[3] == b[3])); }
static inline int limb_is_zero(const uint64_t *a) { return ((((a[0] | a[1]) | a[2]) | a[3]) == 0); }
static inline void limb_copy(uint64_t *d, const uint64_t *a) { d[0] = a[0]; d[1] = a[1]; d[2] = a[2]; d[3] = a[3]; }
static inline void limb_zero(uint64_t *d) { d[0] = 0; d[1] = 0; d[2] = 0; d[3] = 0; }
#endif
