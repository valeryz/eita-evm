/* c/rv32/selftest.c — a freestanding self-test for a bring-up board.
 *
 * The same source compiles for the host (where the ARM64 engine is the trusted
 * oracle: 30k GeneralStateTests green) and for rv32imac. Identical answers on
 * both are a cross-backend differential — the check the x86-64 port leaned on
 * ("the Mac and x86-64 Linux logs agree line for line"), and the only way to
 * learn whether the rv32 lowering is right on hardware.
 *
 * Deliberately covers what the port could plausibly have broken:
 *
 *   ADD/SUB over all four limbs   the synthesised carry and borrow chains,
 *                                 which on rv32 are 8 half-adds with the carry
 *                                 materialised in a register
 *   MUL / DIV                     the C helper call path — a call block's
 *                                 argument staging into a0-a5 — and the
 *                                 portable 128-bit layer behind it (c/u128.h)
 *   MSTORE / RETURN               memory expansion, the gas charge, the output
 *   gas_used                      the whole dispatch loop's accounting
 *
 * No allocator: every buffer is static, so a board test does not depend on the
 * firmware's heap being up. No printf: the result is a bitmask.
 */
#include <stdint.h>
#include <string.h>
#include "evm_state.h"

void eita_run(EvmState *state);
void eita_set_fork(uint64_t ord);
void eita_jumpdest_map(const uint8_t *code, uint64_t len, uint8_t *out);   /* eita_compute.c */
/* The London SSTORE gas schedule, emitted as C by Evm.CL.SstoreGasC and linked
   for rv32 in place of the assembly a 32-bit target cannot enter. */
void eita_sstore_gas_london(uint64_t *out, uint64_t refund, const u256_t *orig,
                            const u256_t *cur, const u256_t *nv, uint64_t cold);

#define STACK_WORDS 1024
#define MEM_BYTES   4096
#define CODE_BYTES  128
#define ARENA_BYTES 4096

static EvmState     g_st;
static u256_t       g_stack[STACK_WORDS];
static uint8_t      g_mem[MEM_BYTES];
/* PUSH<n> reads a full 32-byte word from `code + pc`, so the buffer is padded
   past the longest program here by more than the 31 bytes evm_state.h requires. */
static uint8_t      g_code[CODE_BYTES];
static EvmCallbacks g_cb;      /* all-null: none of these programs calls a host hook */
/* cb_ctx must be 8-aligned (evm_state.h); a bare uint8_t[] is only 1-aligned,
   and on rv32 a word access through it would trap on hardware. These opcodes
   never journal, so nothing reads it — the alignment is here so that a test
   someone adds later does not inherit a latent fault. */
static uint8_t      g_arena[ARENA_BYTES] __attribute__((aligned(8)));
/* The valid-JUMPDEST map. The HOST computes this; the handlers only index it.
   A NULL map is not a missing optimisation — the jump handlers load it
   unconditionally, so the first JUMP faults on a near-null address, which is
   exactly what this test did before it supplied one.

   Built by the engine's own `eita_jumpdest_map` (eita_compute.c), NOT by a
   copy here. This file briefly had its own eight-line scan, which is one
   copy too many of EELS `get_valid_jump_destinations` — the duplication
   CONTRIBUTING rule 4 is about, and the kind this tree keeps finding. */
static uint8_t      g_jumpdests[CODE_BYTES];

/* Run CODE; report the 32-byte RETURN value and the gas it used. */
static int run_prog(const uint8_t *code, uint32_t len, uint8_t out32[32],
                    uint64_t *gas_used) {
    const uint64_t gas0 = 1000000;
    memset(&g_st, 0, sizeof g_st);
    memset(g_stack, 0, sizeof g_stack);
    memset(g_mem, 0, sizeof g_mem);
    memset(g_code, 0, sizeof g_code);
    memset(&g_cb, 0, sizeof g_cb);
    memset(g_jumpdests, 0, sizeof g_jumpdests);
    if (len > CODE_BYTES) return -1;
    memcpy(g_code, code, len);
    eita_jumpdest_map(g_code, len, g_jumpdests);

    g_st.gas_left = gas0;
    g_st.stack = g_stack;
    g_st.memory = g_mem;
    g_st.memory_cap = MEM_BYTES;
    g_st.code = g_code;
    g_st.code_size = len;
    g_st.jumpdests = g_jumpdests;
    g_st.cb = &g_cb;
    g_st.cb_ctx = g_arena;

    eita_run(&g_st);

    *gas_used = gas0 - g_st.gas_left;
    memset(out32, 0, 32);
    if (!g_st.output || g_st.output_size < 32) return -2;
    memcpy(out32, g_st.output, 32);
    return 0;
}

/* The 32-byte big-endian word equal to `v`. */
static int is_word(const uint8_t out32[32], uint64_t v) {
    for (int i = 0; i < 24; i++) if (out32[i] != 0) return 0;
    for (int i = 0; i < 8; i++)
        if (out32[31 - i] != (uint8_t)(v >> (8 * i))) return 0;
    return 1;
}

static int all_ff(const uint8_t out32[32]) {
    for (int i = 0; i < 32; i++) if (out32[i] != 0xff) return 0;
    return 1;
}

/* Each program stores its result at memory 0 and returns 32 bytes:
 *   … compute … PUSH1 0 MSTORE PUSH1 32 PUSH1 0 RETURN                      */
#define TAIL 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3

/* PUSH1 2 PUSH1 1 ADD            → 3 */
static const uint8_t p_add[]     = { 0x60, 0x02, 0x60, 0x01, 0x01, TAIL };
/* PUSH32 2^256-1 PUSH1 2 ADD     → 1  (carry through all four limbs) */
static const uint8_t p_addc[]    = { 0x7f,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0x60, 0x02, 0x01, TAIL };
/* PUSH1 1 PUSH1 0 SUB            → 2^256-1  (borrow through all four limbs) */
static const uint8_t p_subb[]    = { 0x60, 0x01, 0x60, 0x00, 0x03, TAIL };
/* PUSH1 7 PUSH1 9 MUL            → 63  (the helper call path) */
static const uint8_t p_mul[]     = { 0x60, 0x07, 0x60, 0x09, 0x02, TAIL };
/* PUSH1 3 PUSH1 100 DIV          → 33  (Knuth D, and the one 128/64 divide) */
static const uint8_t p_div[]     = { 0x60, 0x03, 0x60, 0x64, 0x04, TAIL };
/* A JUMPI loop: counter 3, decremented to 0, then return 42.
 *   PUSH1 3 | JUMPDEST | PUSH1 1 SWAP1 SUB | DUP1 PUSH1 2 JUMPI | PUSH1 42 TAIL
 * Exercises JUMPDEST validity, JUMPI taken AND not-taken, and the jumpdest
 * bitmap read — which is the whole of `eita_handler_jumpi`. Until 2026-11-25
 * neither jump handler lowered for rv32 (one missing compare-and-branch
 * fusion), so no bytecode containing a loop could run at all; this is here so
 * that cannot regress unnoticed. */
static const uint8_t p_loop[]    = {
    0x60, 0x03,              /* 0: PUSH1 3                  */
    0x5b,                    /* 2: JUMPDEST  <- the target   */
    0x60, 0x01, 0x90, 0x03,  /* 3: PUSH1 1 SWAP1 SUB         */
    0x80, 0x60, 0x02, 0x57,  /* 7: DUP1 PUSH1 2 JUMPI        */
    0x60, 0x2a, TAIL };      /* 11: PUSH1 42, store, return  */

/* An unconditional JUMP over an INVALID opcode, then return 7. If the jump
 * does not land exactly on the JUMPDEST at 4, this executes 0xfe and reverts
 * — so a wrong target cannot read as a pass. */
static const uint8_t p_jump[]    = {
    0x60, 0x04,              /* 0: PUSH1 4                   */
    0x56,                    /* 2: JUMP                      */
    0xfe,                    /* 3: INVALID   <- jumped over  */
    0x5b,                    /* 4: JUMPDEST                  */
    0x60, 0x07, TAIL };      /* 5: PUSH1 7, store, return    */

/* PUSH32 2^64 PUSH32 2^64 MUL    → 2^128  (a wide product, limb-crossing) */
static const uint8_t p_mulw[]    = { 0x7f,
    0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0x01, 0,0,0,0,0,0,0,0,
    0x7f,
    0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0x01, 0,0,0,0,0,0,0,0,
    0x02, TAIL };

/* ---- the four handlers that did not lower until 2026-11-27 ----------------
 *
 * SLT/SGT, EXP and CLZ were the last entries in `Lower.uncovered`, each
 * blocked on a sequence rv32 has no instruction for. Closing them added three
 * hand-written lowerings, so these programs are here to EXECUTE them: the
 * emit gate only proves the assembler accepts the text.
 *
 *   slt/sgt   `sltSigned256` — the chain's borrow is already the unsigned
 *             answer, and signed differs only when the operands' signs do, so
 *             the lowering branches on sign(a) == sign(b). Both sides of that
 *             branch need a test, which is why there are five SLT programs and
 *             not one: a lowering that ignored the sign test entirely would
 *             still pass `1 <ₛ 2`.
 *   exp       square-and-multiply, whose accumulator multiplies into its own
 *             operand (`mulReg x14 x14 x15`) — the aliased case that used to
 *             emit the «unlowered» marker.
 *   clz       `clz64`, the five-step branchless ladder rv32imac needs with no
 *             Zbb. Probed at all four limbs and at zero, because the ladder
 *             has a separate correction for the all-zero word.
 */
#define W_NEG1 0x7f, \
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, \
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff
#define W_NEG2 0x7f, \
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, \
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff, 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe

/* SLT pops a (top of stack) then b, and pushes a <ₛ b — so the SECOND push is
   a. Same order the DIV program above relies on (100/3, not 3/100). */
/* a=-1 b=1   signs differ, a negative → 1 */
static const uint8_t p_slt_a[] = { 0x60, 0x01, W_NEG1, 0x12, TAIL };
/* a=1  b=-1  signs differ, a positive → 0 */
static const uint8_t p_slt_b[] = { W_NEG1, 0x60, 0x01, 0x12, TAIL };
/* a=1  b=2   same sign → the unsigned borrow decides → 1 */
static const uint8_t p_slt_c[] = { 0x60, 0x02, 0x60, 0x01, 0x12, TAIL };
/* a=-2 b=-1  both negative: 2^256-2 <ᵤ 2^256-1 → 1 */
static const uint8_t p_slt_d[] = { W_NEG1, W_NEG2, 0x12, TAIL };
/* a=1  b=1   equal: no borrow, and the sign test must not invent one → 0 */
static const uint8_t p_slt_e[] = { 0x60, 0x01, 0x60, 0x01, 0x12, TAIL };

/* a=1 b=-1 → 1 */
static const uint8_t p_sgt_a[] = { W_NEG1, 0x60, 0x01, 0x13, TAIL };
/* a=-1 b=1 → 0 */
static const uint8_t p_sgt_b[] = { 0x60, 0x01, W_NEG1, 0x13, TAIL };

/* EXP pops a=base then b=exponent: PUSH 5, PUSH 3 → 3^5 = 243 */
static const uint8_t p_exp[]   = { 0x60, 0x05, 0x60, 0x03, 0x0a, TAIL };
/* 2^255 — 7 squarings and a multiply, the aliased accumulator all the way up */
static const uint8_t p_exp2[]  = { 0x60, 0xff, 0x60, 0x02, 0x0a, TAIL };

/* CLZ (EIP-7939, 0x1e) is in the OSAKA table only — these run at fork 18. */
static const uint8_t p_clz1[]  = { 0x60, 0x01, 0x1e, TAIL };          /* → 255 */
static const uint8_t p_clz0[]  = { 0x60, 0x00, 0x1e, TAIL };          /* → 256 */
/* 2^255: the top limb's MSB → 0 */
static const uint8_t p_clzt[]  = { 0x7f,
    0x80,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
    0x1e, TAIL };
/* 2^128: limb 2 → 127 */
static const uint8_t p_clzm[]  = { 0x7f,
    0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0x01, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
    0x1e, TAIL };
/* 2^200: limb 3, mid-ladder (clz64(0x100) = 55) → 55 */
static const uint8_t p_clz200[] = { 0x7f,
    0,0,0,0,0,0,0x01,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
    0x1e, TAIL };

/* The 256-bit signed compare, both sides of its sign branch. */
static int check_signed_cmp(void) {
    uint8_t out[32]; uint64_t gas;
    struct { const uint8_t *p; uint32_t n; uint64_t want; } cases[] = {
        { p_slt_a, sizeof p_slt_a, 1 }, { p_slt_b, sizeof p_slt_b, 0 },
        { p_slt_c, sizeof p_slt_c, 1 }, { p_slt_d, sizeof p_slt_d, 1 },
        { p_slt_e, sizeof p_slt_e, 0 },
    };
    for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; i++)
        if (run_prog(cases[i].p, cases[i].n, out, &gas) != 0 ||
            !is_word(out, cases[i].want)) return 1;
    return 0;
}

static int check_sgt(void) {
    uint8_t out[32]; uint64_t gas;
    if (run_prog(p_sgt_a, sizeof p_sgt_a, out, &gas) != 0 || !is_word(out, 1)) return 1;
    if (run_prog(p_sgt_b, sizeof p_sgt_b, out, &gas) != 0 || !is_word(out, 0)) return 1;
    return 0;
}

/* CLZ at every limb and at zero. Runs under OSAKA and puts the fork back. */
static int check_clz(void) {
    uint8_t out[32]; uint64_t gas; int bad = 0;
    struct { const uint8_t *p; uint32_t n; uint64_t want; } cases[] = {
        { p_clz1,   sizeof p_clz1,   255 }, { p_clz0,   sizeof p_clz0,   256 },
        { p_clzt,   sizeof p_clzt,     0 }, { p_clzm,   sizeof p_clzm,  127 },
        { p_clz200, sizeof p_clz200,  55 },
    };
    eita_set_fork(18);
    for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; i++)
        if (run_prog(cases[i].p, cases[i].n, out, &gas) != 0 ||
            !is_word(out, cases[i].want)) { bad = 1; break; }
    eita_set_fork(16);
    return bad;
}

/* The emitted SSTORE gas schedule, ON THE TARGET.
 *
 * c/test_sstore_gas.c sweeps all five schedules at every reachable predicate
 * pattern — but on the HOST, where the tables are 64-bit-compiled. These three
 * probes run the same emitted C built for rv32imac, which is what would catch
 * a 32-bit arithmetic or table-indexing problem in it. Values read off
 * `rows_london` / `idx_london` and independently recognisable as London's
 * schedule: 20000 to set, 2900 to reset, 4800 cleared refund (EIP-3529), and
 * +2100 for a cold slot (EIP-2929). */
static int check_sstore_gas(void) {
    u256_t zero, one; uint64_t out[2];
    memset(&zero, 0, sizeof zero);
    memset(&one, 0, sizeof one);
    one.limb[0] = 1;

    /* warm SET: orig 0, cur 0, new nonzero */
    eita_sstore_gas_london(out, 0, &zero, &zero, &one, 0);
    if (out[0] != 20000 || out[1] != 0) return 1;

    /* the same, COLD: +2100 */
    eita_sstore_gas_london(out, 0, &zero, &zero, &one, 1);
    if (out[0] != 22100 || out[1] != 0) return 1;

    /* warm RESET to zero: 2900, and 4800 added to the refund counter */
    eita_sstore_gas_london(out, 100, &one, &one, &zero, 0);
    if (out[0] != 2900 || out[1] != 4900) return 1;

    return 0;
}

/* The check names, owned HERE.
 *
 * Three places print them — the host main below, the QEMU runtime, and the
 * dabao firmware — and each used to keep its own array and its own loop bound.
 * Adding checks 10-14 left two of the three printing ten lines, so a failure
 * in the newly closed handlers would have been invisible in the per-check
 * list, visible only in the mask. The name list is the bitmask's
 * documentation; one owner, like every other table in this tree.
 *
 * Returns NULL past the last check, so callers loop to exhaustion and never
 * restate the count. */
const char *eita_selftest_check(unsigned i) {
    static const char *const names[] = {
        "ADD", "ADD-carry", "SUB-borrow", "MUL", "DIV", "MUL-wide",
        "gas(ADD)==24", "JUMPI-loop", "JUMP", "sstore-gas",
        "SLT-signed", "SGT-signed", "EXP", "gas(EXP)==81", "CLZ",
    };
    return i < sizeof names / sizeof names[0] ? names[i] : (const char *)0;
}

/** Run every check. Returns 0 on success, else a bitmask of the ones that
    failed (bit k = check k). `gas_add_out`, when non-null, receives the gas the
    ADD program used — the number a host run pins and a board run must match. */
uint32_t eita_selftest(uint64_t *gas_add_out) {
    uint8_t out[32];
    uint64_t gas;
    uint32_t bad = 0;

    eita_set_fork(16);                 /* Cancun: the default dispatch table */

    if (run_prog(p_add, sizeof p_add, out, &gas) != 0 || !is_word(out, 3)) bad |= 1u << 0;
    if (gas_add_out) *gas_add_out = gas;
    /* The gas the ADD program costs, pinned by a host run and by hand from the
       schedule: PUSH1 x2 = 6, ADD = 3, PUSH1 = 3, MSTORE = 3 + 3 of memory
       expansion, PUSH1 x2 = 6. A board that disagrees has a gas bug, which is
       the failure mode a clear-signing wallet least wants to discover late. */
    if (gas != 24) bad |= 1u << 6;

    if (run_prog(p_addc, sizeof p_addc, out, &gas) != 0 || !is_word(out, 1)) bad |= 1u << 1;
    if (run_prog(p_subb, sizeof p_subb, out, &gas) != 0 || !all_ff(out))     bad |= 1u << 2;
    if (run_prog(p_mul,  sizeof p_mul,  out, &gas) != 0 || !is_word(out, 63)) bad |= 1u << 3;
    if (run_prog(p_div,  sizeof p_div,  out, &gas) != 0 || !is_word(out, 33)) bad |= 1u << 4;

    if (check_sstore_gas() != 0) bad |= 1u << 9;

    if (run_prog(p_loop, sizeof p_loop, out, &gas) != 0 || !is_word(out, 42)) bad |= 1u << 7;
    if (run_prog(p_jump, sizeof p_jump, out, &gas) != 0 || !is_word(out, 7))  bad |= 1u << 8;

    if (check_signed_cmp() != 0) bad |= 1u << 10;
    if (check_sgt() != 0)        bad |= 1u << 11;

    /* 3^5 = 243, and the gas EXP's clz-derived ebytes charges for it:
       PUSH1 x2 = 6, EXP = 10 + 50x1 byte of exponent = 60, TAIL = 15. */
    if (run_prog(p_exp, sizeof p_exp, out, &gas) != 0 || !is_word(out, 243)) bad |= 1u << 12;
    else if (gas != 81) bad |= 1u << 13;
    /* 2^255: bit 255, i.e. byte 0 == 0x80 and nothing else. */
    if (run_prog(p_exp2, sizeof p_exp2, out, &gas) != 0) bad |= 1u << 12;
    else {
        int ok = out[0] == 0x80;
        for (int i = 1; i < 32 && ok; i++) if (out[i] != 0) ok = 0;
        if (!ok) bad |= 1u << 12;
    }

    if (check_clz() != 0) bad |= 1u << 14;

    /* 2^64 * 2^64 = 2^128: byte 15 of the big-endian word, nothing else. */
    if (run_prog(p_mulw, sizeof p_mulw, out, &gas) != 0) bad |= 1u << 5;
    else {
        int ok = out[15] == 1;
        for (int i = 0; i < 32 && ok; i++) if (i != 15 && out[i] != 0) ok = 0;
        if (!ok) bad |= 1u << 5;
    }
    return bad;
}

#ifdef EITA_SELFTEST_MAIN
#include <stdio.h>
int main(void) {
    uint64_t gas = 0;
    uint32_t bad = eita_selftest(&gas);
    for (unsigned i = 0; eita_selftest_check(i); i++)
        printf("  %-13s %s\n", eita_selftest_check(i),
               (bad & (1u << i)) ? "FAIL" : "ok");
    printf("---\nselftest: %s (mask 0x%02x), ADD program gas_used = %llu\n",
           bad ? "FAIL" : "PASS", bad, (unsigned long long)gas);
    return bad != 0;
}
#endif
