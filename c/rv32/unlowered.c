/* c/rv32/unlowered.c — nothing is unlowered any more.
 *
 * This file held weak refusals for the five SSTORE gas schedules, which
 * existed only as emitted ARM64/x86-64 assembly that a 32-bit target cannot
 * enter: they are C-ABI leaf functions with six parameters, and on ILP32
 * `refund` takes an ALIGNED register pair while `cold` lands past a7 and onto
 * the stack, which the handler lowering's argument staging does not build.
 *
 * `Evm.CL.SstoreGasC` settled it by printing the plans as C instead — every
 * plan in `SstoreGasDenote` is a function of seven booleans and a refund
 * counter that only enters as `((refund + add1) - sub) + add2`, so each
 * schedule is a small table and the compiler places the arguments. See
 * `c/generated/sstore_gas.c`, linked for rv32 in place of the assembly.
 *
 * Those four remaining uncovered handlers (`clz`, `slt`, `sgt`, `exp`) did NOT
 * end up needing a C fallback either: `Lower` grew the three sequences
 * rv32imac has no instruction for — `clz64`, `sltSigned256`, and the aliased
 * `mulReg` — and `Lower.no_uncovered_handlers` now holds with the set empty.
 *
 * The file is kept rather than deleted: it is where the NEXT refusal goes. An
 * empty translation unit is not legal C, hence the one symbol.
 */
#include <stdint.h>

/* Referenced by nothing; present so this is a translation unit. */
const uint32_t eita_rv32_unlowered_none = 0;
