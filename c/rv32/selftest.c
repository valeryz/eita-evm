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
/* The valid-JUMPDEST map (evm_state.h: `jumpdests[pc] == 1` iff code[pc] is a
   JUMPDEST that is not inside a PUSH immediate). The HOST computes this; the
   handlers only index it. A NULL map is not a missing optimisation — the jump
   handlers load it unconditionally, so the first JUMP faults on a near-null
   address, which is exactly what this test did before it supplied one. */
static uint8_t      g_jumpdests[CODE_BYTES];

/* EELS `get_valid_jump_destinations`: a JUMPDEST counts only outside a PUSH
   immediate, so the scan has to skip each PUSH's data rather than look at
   every byte. */
static void build_jumpdests(const uint8_t *code, uint32_t len, uint8_t *out) {
    for (uint32_t pc = 0; pc < len; ) {
        uint8_t op = code[pc];
        if (op == 0x5b) out[pc] = 1;
        if (op >= 0x60 && op <= 0x7f) pc += 1u + (uint32_t)(op - 0x5f);   /* PUSH1..32 */
        else pc += 1;
    }
}

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
    build_jumpdests(g_code, len, g_jumpdests);

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

    if (run_prog(p_loop, sizeof p_loop, out, &gas) != 0 || !is_word(out, 42)) bad |= 1u << 7;
    if (run_prog(p_jump, sizeof p_jump, out, &gas) != 0 || !is_word(out, 7))  bad |= 1u << 8;

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
    static const char *names[] = { "ADD", "ADD-carry", "SUB-borrow", "MUL",
                                   "DIV", "MUL-wide", "gas(ADD)=24",
                                   "JUMPI-loop", "JUMP" };
    for (int i = 0; i < 9; i++)
        printf("  %-11s %s\n", names[i], (bad & (1u << i)) ? "FAIL" : "ok");
    printf("---\nselftest: %s (mask 0x%02x), ADD program gas_used = %llu\n",
           bad ? "FAIL" : "PASS", bad, (unsigned long long)gas);
    return bad != 0;
}
#endif
