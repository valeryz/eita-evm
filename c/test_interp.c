/* test_interp.c — validate the threaded interpreter (handlers.S → eita_run)
 * with no Lisp/Lean: set up an EvmState the way replay-cl does (incl. the cb
 * vtable + cb_ctx the stale eita_run_program omits), run simple bytecode, check
 * the 32-byte RETURN. Validates the aarch64-Linux ELF port of handlers.S (#249).
 * Build: clang handlers(-elf).o eita_compute.c tx_state.c <keccak>.c test_interp.c */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "evm_state.h"

void eita_run(EvmState *state);
void eita_set_fork(uint64_t ord);

static int g_fail = 0;

/* A callback that CHECKS its arguments: the Rosetta vectors' fake callbacks
 * ignore theirs, which is how the x86-64 argument staging bugs got through. */
static uint64_t g_ecc_calls = 0, g_ecc_bad = 0;
static uint64_t cb_ext_code_copy_check(void *ctx, const u256_t *addr, uint8_t *dst,
                                       uint64_t src_off, uint64_t len) {
    g_ecc_calls++;
    if (ctx == NULL || addr == NULL || dst == NULL) g_ecc_bad++;
    if (addr && addr->limb[0] != 0x1234) g_ecc_bad++;
    if (src_off != 7) g_ecc_bad++;
    if (len != 9) g_ecc_bad++;
    if (dst && len == 9) for (int i = 0; i < 9; i++) dst[i] = (uint8_t)(0xa0 + i);
    return 700;
}
static uint64_t g_log_calls = 0;
static void cb_log_n_nop(void *ctx, const u256_t *self, uint8_t n, const u256_t *topics,
                         const uint8_t *data, uint64_t len) {
    (void)ctx; (void)self; (void)n; (void)topics; (void)data; (void)len; g_log_calls++;
}
static void check_extcodecopy(void) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));
    uint8_t      *arena = calloc(1 << 20, 1);
    /* PUSH1 0, PUSH1 0, LOG0 first: a callback-bearing op whose ARM64 handler leaves a
     * memory POINTER in x4 (the fifth argument register), so EXTCODECOPY's len is
     * checked against a stale value that can never equal 9 — the handler must load
     * len itself (f812945 left it inherited from the gas gadget; mainnet 4,972,698).
     * Then PUSH1 9 (len), PUSH1 7 (src), PUSH1 0x20 (dst), PUSH2 0x1234 (addr),
     * EXTCODECOPY, STOP. */
    uint8_t code[] = {0x60,0, 0x60,0, 0xa0, 0x60,9, 0x60,7, 0x60,0x20, 0x61,0x12,0x34, 0x3c, 0x00};
    uint8_t *cbuf = calloc(sizeof code + 64, 1); memcpy(cbuf, code, sizeof code);
    cb->ext_code_copy = cb_ext_code_copy_check;
    cb->log_n = cb_log_n_nop;
    st->gas_left = 1000000; st->stack = stack; st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = sizeof code; st->cb = cb; st->cb_ctx = arena;
    eita_run(st);
    int ok = (g_log_calls == 1 && g_ecc_calls == 1 && g_ecc_bad == 0 &&
              mem[0x20] == 0xa0 && mem[0x28] == 0xa8);
    printf("  %-10s calls=%llu bad-args=%llu mem[0x20]=%02x gas-used=%llu  %s\n", "EXTCODECOPY",
           (unsigned long long)g_ecc_calls, (unsigned long long)g_ecc_bad, mem[0x20],
           (unsigned long long)(1000000 - st->gas_left), ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}

/* run CODE under a freshly set-up frame; return olen + the 32-byte word value. */
static void run(const uint8_t *code, int len, uint64_t *olen_out, uint64_t *val_out) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    uint8_t      *cbuf  = calloc(len + 64, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));   /* null fps; pure-compute bytecode never calls them */
    uint8_t      *arena = calloc(1 << 20, 1);                /* dummy TxArena (no journaling on these ops) */
    memcpy(cbuf, code, len);
    st->gas_left = 1000000; st->stack = stack;
    st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = len;
    st->cb = cb; st->cb_ctx = arena;
    eita_run(st);
    uint64_t v = 0;
    if (st->output && st->output_size >= 32)
        for (int i = 24; i < 32; i++) v = (v << 8) | st->output[i];
    *olen_out = st->output_size; *val_out = v;
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}

static void run_hash(const uint8_t *code, int len, char *hex_out) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    uint8_t      *cbuf  = calloc(len + 64, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));
    uint8_t      *arena = calloc(1 << 20, 1);
    memcpy(cbuf, code, len);
    st->gas_left = 1000000; st->stack = stack; st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = len; st->cb = cb; st->cb_ctx = arena;
    eita_run(st);
    hex_out[0] = 0;
    for (int i = 0; i < 32 && i < (int)st->output_size; i++) sprintf(hex_out + 2*i, "%02x", st->output[i]);
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}

/* run CODE and report gas_left — the cross-backend differential for gas
 * (EELS by hand: PUSH 3, DUP 3, CODECOPY 3 + 3/word + memexp). */
static void check_gas(const char *tag, const uint8_t *code, int len, uint64_t want) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    uint8_t      *cbuf  = calloc(len + 64, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));
    uint8_t      *arena = calloc(1 << 20, 1);
    memcpy(cbuf, code, len);
    st->gas_left = 1000000; st->stack = stack; st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = len; st->cb = cb; st->cb_ctx = arena;
    eita_run(st);
    uint64_t used = 1000000 - st->gas_left;
    int ok = (used == want);
    printf("  %-10s gas-used=%llu want=%llu msize=%llu  %s\n", tag,
           (unsigned long long)used, (unsigned long long)want,
           (unsigned long long)st->memory_size, ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}

static void check_word(const char *tag, const uint8_t *code, int len, uint64_t want) {
    uint64_t olen, got; run(code, len, &olen, &got);
    int ok = (olen == 32) && (got == want);
    printf("  %-10s olen=%llu got=%llu want=%llu  %s\n", tag,
           (unsigned long long)olen, (unsigned long long)got, (unsigned long long)want, ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
}

/* PUSH-N at the end of the code. The handler reads its immediate with whole-limb
 * loads and no bounds check (lean/Evm/CL/PushWide.lean): the bytes past code_size
 * come from the code buffer's zero padding — EELS zero-fills them, no fault — and
 * the fetch after a PUSH32 in the last byte (pc = code_size + 32) reads padding too,
 * i.e. STOP. Like the replay's frame image, the buffer here is code + 64 zero bytes.
 * The run stops at the end, so the pushed word is read back from the stack. */
static void check_push_at_end(const char *tag, const uint8_t *code, int len,
                              uint64_t w0, uint64_t w1, uint64_t w2, uint64_t w3) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    uint8_t      *cbuf  = calloc(len + 64, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));
    uint8_t      *arena = calloc(1 << 20, 1);
    memcpy(cbuf, code, len);
    st->gas_left = 1000000; st->stack = stack; st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = len; st->cb = cb; st->cb_ctx = arena;
    eita_run(st);
    const uint64_t *t = stack[0].limb;
    int ok = st->sp == 1 && t[0] == w0 && t[1] == w1 && t[2] == w2 && t[3] == w3 &&
             1000000 - st->gas_left == 3;
    printf("  %-10s sp=%llu tos=%016llx_%016llx_%016llx_%016llx  %s\n", tag, (unsigned long long)st->sp,
           (unsigned long long)t[3], (unsigned long long)t[2], (unsigned long long)t[1],
           (unsigned long long)t[0], ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}
static void check_push_end_cases(void) {
    uint8_t p32[] = {0x7f};                                   /* PUSH32, the last byte: 0 */
    check_push_at_end("PUSH32end", p32, sizeof p32, 0, 0, 0, 0);
    uint8_t p32b[] = {0x7f, 0xaa, 0xbb};                      /* 2 of 32 bytes: 0xaabb << 240 */
    check_push_at_end("PUSH32str", p32b, sizeof p32b, 0, 0, 0, 0xaabbull << 48);
    uint8_t p9[] = {0x68, 1, 2, 3, 4, 5};                     /* 5 of 9 bytes: 0x0102030405 << 32 */
    check_push_at_end("PUSH9str", p9, sizeof p9, 0x0203040500000000ull, 0x01, 0, 0);
    uint8_t p3[] = {0x62, 0xcd};                              /* 1 of 3 (partial limb only): 0xcd0000 */
    check_push_at_end("PUSH3str", p3, sizeof p3, 0xcd0000, 0, 0, 0);
    uint8_t p16[] = {0x6f, 0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88, 0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x10};
    check_push_at_end("PUSH16", p16, sizeof p16, 0x99aabbccddeeff10ull, 0x1122334455667788ull, 0, 0);
}

/* EIP-4844 (Cancun): BLOBHASH reads the tx's versioned-hash table (state->blob_hashes,
 * blob_hash_count) and BLOBBASEFEE the block's fee (state->blob_base_fee); both were
 * stubs pushing 0 until 2026-10-25. Runs CODE with two hashes installed and the fee
 * set; reports the returned word's low 8 bytes and the gas used. */
static void run_blob(const uint8_t *code, int len, uint64_t fee, uint64_t *val_out, uint64_t *gas_out) {
    EvmState     *st    = calloc(1, sizeof(EvmState));
    u256_t       *stack = calloc(1024, sizeof(u256_t));
    uint8_t      *mem   = calloc(64 * 1024, 1);
    uint8_t      *cbuf  = calloc(len + 64, 1);
    EvmCallbacks *cb    = calloc(1, sizeof(EvmCallbacks));
    uint8_t      *arena = calloc(1 << 20, 1);
    u256_t        hashes[2] = {{{0x1111, 0x2222, 0x3333, 0x4444}}, {{0xdeadbeef, 5, 6, 7}}};
    memcpy(cbuf, code, len);
    st->gas_left = 1000000; st->stack = stack; st->memory = mem; st->memory_cap = 64 * 1024;
    st->code = cbuf; st->code_size = len; st->cb = cb; st->cb_ctx = arena;
    st->blob_hashes = hashes; st->blob_hash_count = 2; st->blob_base_fee.limb[0] = fee;
    eita_run(st);
    uint64_t v = 0;
    if (st->output && st->output_size >= 32)
        for (int i = 24; i < 32; i++) v = (v << 8) | st->output[i];
    *val_out = v; *gas_out = 1000000 - st->gas_left;
    free(st); free(stack); free(mem); free(cbuf); free(cb); free(arena);
}
static void check_blob(const char *tag, const uint8_t *code, int len, uint64_t want, uint64_t want_gas) {
    uint64_t got, gas; run_blob(code, len, 12345, &got, &gas);
    int ok = (got == want) && (gas == want_gas);
    printf("  %-10s got=%llx want=%llx gas=%llu want=%llu  %s\n", tag,
           (unsigned long long)got, (unsigned long long)want,
           (unsigned long long)gas, (unsigned long long)want_gas, ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
}
static void check_blob_ops(void) {
    eita_set_fork(16);   /* Cancun: BLOBHASH / BLOBBASEFEE admitted */
    /* PUSH1 1, BLOBHASH, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, RETURN: hash 1's low limb; 3+3+3+3+3+3+0 + memexp 3 */
    uint8_t h1[] = {0x60,1, 0x49, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_blob("BLOBHASH1", h1, sizeof h1, 0xdeadbeef, 21);
    /* index 0: the first hash */
    uint8_t h0[] = {0x60,0, 0x49, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_blob("BLOBHASH0", h0, sizeof h0, 0x1111, 21);
    /* index 2 of 2: out of range → 0 */
    uint8_t h2[] = {0x60,2, 0x49, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_blob("BLOBHASH2", h2, sizeof h2, 0, 21);
    /* PUSH9 2^64 + 1: the low limb is a valid index, the high limb makes it out of range → 0 */
    uint8_t hw[] = {0x68,1,0,0,0,0,0,0,0,1, 0x49, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_blob("BLOBHASHW", hw, sizeof hw, 0, 21);
    /* BLOBBASEFEE, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, RETURN: the fee the host wrote; 2+3+3+3+3 + memexp 3 */
    uint8_t bf[] = {0x4a, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_blob("BLOBBASEFEE", bf, sizeof bf, 12345, 17);
    eita_set_fork(6);
}

int main(void) {
    eita_set_fork(6);   /* Byzantium */
    printf("threaded-interp ELF validation:\n");
    uint8_t add[]  = {0x60,5, 0x60,3, 0x01, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_word("ADD", add, sizeof add, 8);
    uint8_t mul[]  = {0x60,7, 0x60,6, 0x02, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_word("MUL", mul, sizeof mul, 42);
    uint8_t sub[]  = {0x60,7, 0x60,100, 0x03, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    check_word("SUB", sub, sizeof sub, 93);
    uint8_t shl[]  = {0x60,1, 0x60,4, 0x1b, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3}; /* 1<<4=16 */
    check_word("SHL", shl, sizeof shl, 16);
    /* value checks for the TOS/NOS discipline */
    uint8_t v1[] = {0x60,5, 0x80, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};          /* DUP1 → 5 */
    check_word("DUP1v", v1, sizeof v1, 5);
    uint8_t v2[] = {0x60,5, 0x80, 0x01, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};    /* DUP1 ADD → 10 */
    check_word("DUP1ADD", v2, sizeof v2, 10);
    uint8_t v3[] = {0x60,7, 0x60,5, 0x90, 0x03, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3}; /* SWAP1 SUB: top=7, nos=5 → 2 */
    check_word("SWAP1SUB", v3, sizeof v3, 2);
    uint8_t v4[] = {0x60,5, 0x60,7, 0x81, 0x01, 0x01, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3}; /* DUP2 ADD ADD → 17 */
    check_word("DUP2ADD", v4, sizeof v4, 17);
    char h[80];
    uint8_t sha3[] = {0x60,0, 0x60,0, 0x20, 0x60,0, 0x52, 0x60,32, 0x60,0, 0xf3};
    run_hash(sha3, sizeof sha3, h);
    int ok = (strcmp(h, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470") == 0);
    printf("  %-10s got=%s  %s\n", "KECCAK\"\"", h, ok ? "ok" : "FAIL");
    if (!ok) g_fail++;
    /* PUSH1 5, DUP1, PUSH1 0, PUSH1 0, CODECOPY, STOP: 3+3+3+3 + (3 + 3*1 + memexp(32)=3) = 21 */
    uint8_t cc[] = {0x60,5, 0x80, 0x60,0, 0x60,0, 0x39, 0x00};
    check_gas("CODECOPY", cc, sizeof cc, 21);
    /* PUSH1 0x40, PUSH1 0, PUSH1 0, CALLDATACOPY, STOP: 9 + (3 + 3*2 + memexp(64)=6) = 24 */
    uint8_t cd[] = {0x60,0x40, 0x60,0, 0x60,0, 0x37, 0x00};
    check_gas("CDCOPY", cd, sizeof cd, 24);
    /* PUSH1 5, DUP1, STOP: 6; and with one more push: 9 (msize must stay 0) */
    uint8_t d1[] = {0x60,5, 0x80, 0x00};
    check_gas("DUP1", d1, sizeof d1, 6);
    uint8_t d2[] = {0x60,5, 0x80, 0x60,0, 0x00};
    check_gas("DUP1+PUSH", d2, sizeof d2, 9);
    uint8_t d3[] = {0x60,5, 0x80, 0x60,0, 0x60,0, 0x00};
    check_gas("DUP1+2PUSH", d3, sizeof d3, 12);
    /* CODECOPY without DUP: PUSH1 5, PUSH1 0, PUSH1 0, CODECOPY, STOP: 9 + 9 = 18 */
    uint8_t cc2[] = {0x60,5, 0x60,0, 0x60,0, 0x39, 0x00};
    check_gas("CODECOPY2", cc2, sizeof cc2, 18);
    /* CALLDATACOPY with DUP: PUSH1 0x40, DUP1, PUSH1 0, CALLDATACOPY, STOP: 9 + (3 + 6 + 6) = 24 */
    uint8_t cd2[] = {0x60,0x40, 0x80, 0x60,0, 0x37, 0x00};
    check_gas("CDCOPY2", cd2, sizeof cd2, 24);
    check_extcodecopy();
    check_push_end_cases();
    check_blob_ops();
    printf("---\ninterp test: %s (%d failures)\n", g_fail ? "FAIL" : "PASS", g_fail);
    return g_fail ? 1 : 0;
}
