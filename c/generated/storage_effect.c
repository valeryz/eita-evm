/* c/generated/storage_effect.c — EMITTED by `lake exe emitStorageC` from the effect IR
   (lean/Evm/CL/EffectC.lean); do not edit. The terms and their proofs: Evm.CL.EffectSload
   (sload_refines), Evm.CL.EffectSstore (sstore_refines), the SSTORE dispatch
   Evm.CL.EffectIR.SstoreSched.ofFork. The Lisp printing of the same terms: spec-sload-effect,
   spec-sstore-effect, spec-sstore-gas-dispatch in src/generated/host.lisp. */
#include "../storage_host.h"
#include "limb_ops.h"

/* SLOAD (Evm.CL.EffectSload.term) */
uint64_t eita_spec_sload_effect(eita_sh *h, uint64_t *out) {
  uint64_t gas = 0;
  if (!eita_sh_hit(h)) return EITA_SH_MISS;
  uint64_t value[4];
  eita_sh_sload(h, value);
  const int cold = (h->fork >= 10) && eita_sh_access_slot(h);
  eita_sh_orig_record(h, value);
  limb_copy(out, value);
  gas += ((h->fork >= 10) ? (cold ? UINT64_C(2100) : UINT64_C(100)) : ((h->fork >= 8) ? UINT64_C(800) : ((h->fork >= 3) ? UINT64_C(200) : UINT64_C(50))));
  return gas;
}

/* SSTORE (Evm.CL.EffectSstore.term) */
uint64_t eita_spec_sstore_effect(eita_sh *h) {
  uint64_t gas = 0;
  const uint64_t *new_val = h->val.limb;
  if (!eita_sh_hit(h)) return EITA_SH_MISS;
  uint64_t current[4];
  eita_sh_sload(h, current);
  const int cold = (h->fork >= 10) && eita_sh_access_slot(h);
  eita_sh_orig_record(h, current);
  uint64_t original[4];
  eita_sh_orig_get(h, current, original);
  gas += eita_sh_sstore_gas(h, original, current, new_val, cold);
  if (!limb_eq(new_val, current)) {
    eita_sh_set_storage(h, new_val);
  }
  return gas;
}

/* The SSTORE schedule of each fork (Evm.CL.EffectIR.SstoreSched.ofFork) */
void eita_sstore_gas_legacy(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);
void eita_sstore_gas_eip1283(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);
void eita_sstore_gas_eip2200(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);
void eita_sstore_gas_berlin(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);
void eita_sstore_gas_london(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);
void eita_spec_sstore_plan(uint64_t fork, uint64_t *out, uint64_t refund, const u256_t *orig,
                           const u256_t *cur, const u256_t *nv, uint64_t cold) {
  switch (fork) {
  case 0:   case 1:   case 2:   case 3:   case 4:   case 5:   case 7: eita_sstore_gas_legacy(out, refund, orig, cur, nv, cold); return;
  case 6: eita_sstore_gas_eip1283(out, refund, orig, cur, nv, cold); return;
  case 8:   case 9: eita_sstore_gas_eip2200(out, refund, orig, cur, nv, cold); return;
  case 10: eita_sstore_gas_berlin(out, refund, orig, cur, nv, cold); return;
  default: eita_sstore_gas_london(out, refund, orig, cur, nv, cold); return;
  }
}
