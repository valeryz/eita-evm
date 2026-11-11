/* c/rv32/unlowered.c — refusals for the routines rv32 has not lowered yet.
 *
 * The engine's generated C calls five SSTORE gas schedules
 * (c/generated/storage_effect.c -> eita_spec_sstore_plan), and on ARM64 and
 * x86-64 those are EMITTED NATIVE ASSEMBLY (Evm.CL.ARM64.SstoreGas, proved in
 * SstoreGasSem). rv32 can lower their bodies — 551 AInstrs, only two gaps —
 * but not yet their ARGUMENTS: they are C-ABI leaf functions taking six
 * parameters in x0-x5, and on ILP32 a `uint64_t` parameter takes an ALIGNED
 * REGISTER PAIR, so the sixth argument lands past a7 and on the stack. x86-64
 * hit the same wall and solved it by repacking (X86SstoreGas: the six
 * predicates in one register as bits); rv32 needs its own answer.
 *
 * Until then these are loud refusals rather than absent symbols, so a build
 * links and a bring-up test runs — and anything that actually reaches an
 * SSTORE stops instead of computing a wrong gas number. They are `weak`, so
 * the emitted versions replace them silently once they exist.
 */
#include <stdint.h>

void eita_rv32_abort(const char *why) __attribute__((noreturn));

#define EITA_SSTORE_STUB(name)                                                \
    __attribute__((weak)) void name(uint64_t *out, uint64_t refund,           \
                                    const void *orig, const void *cur,        \
                                    const void *nv, uint64_t cold) {          \
        (void)out; (void)refund; (void)orig; (void)cur; (void)nv; (void)cold; \
        eita_rv32_abort("eita: " #name " is not lowered for rv32");           \
    }

EITA_SSTORE_STUB(eita_sstore_gas_legacy)
EITA_SSTORE_STUB(eita_sstore_gas_eip1283)
EITA_SSTORE_STUB(eita_sstore_gas_eip2200)
EITA_SSTORE_STUB(eita_sstore_gas_berlin)
EITA_SSTORE_STUB(eita_sstore_gas_london)
