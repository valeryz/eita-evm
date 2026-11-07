/* c/generated/storage_effect.c — EMITTED by `lake exe emitStorageC` from the effect IR
   (lean/Evm/CL/EffectC.lean); do not edit. The terms and their proofs: Evm.CL.EffectSload
   (sload_refines). The Lisp printing of the same terms: spec-sload-effect in
   src/generated/host.lisp. */
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
