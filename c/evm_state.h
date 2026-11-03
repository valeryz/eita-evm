/*
 * evm_state.h — concrete native state layout for Eita's threaded interp
 *
 * Mirrors `Evm.CL.MacroSpec.CLState` exactly. Form.toARM64Interp (and
 * future toAMD64) emit code that loads and stores at the offsets named
 * here. Offsets are documented inline AND statically asserted at the
 * bottom of this header so any drift breaks the build, not silently.
 *
 * ABI:
 *   - All multibyte fields are little-endian (host endianness on ARM64).
 *   - u256_t is 4 × uint64_t in little-endian limb order (limb[0] is LSB).
 *   - The struct is packed by C's default alignment; no #pragma pack needed
 *     because every field is already 8-byte-aligned by size.
 *
 * Verification boundary:
 *   - This struct is the ONLY shared mutable state between the threaded
 *     interpreter and the host (caller). Everything else is callbacks.
 *   - Form.interp operates over an abstract CLState; the proof obligations
 *     for the native backend are that each generated handler reads/writes
 *     the right offsets (mirror of the abstract field set).
 */

#ifndef EITA_EVM_STATE_H
#define EITA_EVM_STATE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===========================================================================
 * U256 — 256-bit unsigned integer, little-endian limbs.
 *
 * limb[0] holds bits 0..63 (LSB), limb[3] holds bits 192..255 (MSB).
 * Memory layout on disk / on the EVM stack (when serialized) is BIG-endian;
 * the threaded interp converts at the buffer boundary (CALLDATALOAD etc.).
 * ===========================================================================
 */

typedef struct {
    uint64_t limb[4];
} u256_t;

_Static_assert(sizeof(u256_t) == 32, "u256_t must be 32 bytes");
_Static_assert(_Alignof(u256_t) == 8, "u256_t must be 8-byte aligned");

/* ===========================================================================
 * EvmCallbacks — host-provided vtable for everything outside pure compute.
 *
 * Callbacks pass the caller-opaque `ctx` pointer back so the host can hang
 * its DB handle, RPC client, etc. off it without globals.
 *
 * Output U256s and ByteArrays are written through caller-supplied pointers
 * — never returned by value — so the ABI works identically across host
 * languages (no struct return convention dependence).
 * ===========================================================================
 */

/* CallParams: laid out by the CALL/CALLCODE/DELEGATECALL/STATICCALL/CREATE/
 * CREATE2 handlers before invoking cb->call or cb->create. The host reads
 * these fields, builds a sub-frame EvmState, runs eita_run on it, and writes
 * the result back into CallResult.
 *
 * `kind` encodes which variant:
 *   0 = CALL          (value transfer; can mutate state)
 *   1 = CALLCODE      (execute other code in our state)
 *   2 = DELEGATECALL  (execute other code, preserve caller+value)
 *   3 = STATICCALL    (no state mutation)
 *   4 = CREATE        (deploy new contract, address from sender+nonce)
 *   5 = CREATE2       (deploy with salt-derived address)
 */
typedef struct CallParams {
    int             kind;                 /* offset  0 */
    int             staticp;              /* offset  4 — 1 = sub-frame is static */
    u256_t          addr;                 /* offset  8 — callee address */
    u256_t          value;                /* offset 40 — wei transferred */
    const uint8_t  *input;                /* offset 72 — calldata */
    uint64_t        input_len;            /* offset 80 */
    uint64_t        gas;                  /* offset 88 — gas to forward */
    u256_t          salt;                 /* offset 96 — for CREATE2 */
} CallParams;

typedef struct CallResult {
    int             success;              /* offset  0 — 1 ok, 0 reverted */
    uint8_t        *output;               /* offset  8 — sub-frame's RETURN/REVERT bytes */
    uint64_t        output_len;           /* offset 16 */
    uint64_t        gas_used;             /* offset 24 — gas the sub-frame consumed */
    u256_t          created_addr;         /* offset 32 — for CREATE/CREATE2 */
} CallResult;

_Static_assert(sizeof(CallParams)  == 128, "CallParams must be 128 bytes");
_Static_assert(sizeof(CallResult)  == 64,  "CallResult must be 64 bytes");
_Static_assert(offsetof(CallParams, kind)      == 0,   "CallParams.kind offset");
_Static_assert(offsetof(CallParams, staticp)   == 4,   "CallParams.staticp offset");
_Static_assert(offsetof(CallParams, addr)      == 8,   "CallParams.addr offset");
_Static_assert(offsetof(CallParams, value)     == 40,  "CallParams.value offset");
_Static_assert(offsetof(CallParams, input)     == 72,  "CallParams.input offset");
_Static_assert(offsetof(CallParams, input_len) == 80,  "CallParams.input_len offset");
_Static_assert(offsetof(CallParams, gas)       == 88,  "CallParams.gas offset");
_Static_assert(offsetof(CallParams, salt)      == 96,  "CallParams.salt offset");
_Static_assert(offsetof(CallResult, success)      == 0,  "CallResult.success offset");
_Static_assert(offsetof(CallResult, output)       == 8,  "CallResult.output offset");
_Static_assert(offsetof(CallResult, output_len)   == 16, "CallResult.output_len offset");
_Static_assert(offsetof(CallResult, gas_used)     == 24, "CallResult.gas_used offset");
_Static_assert(offsetof(CallResult, created_addr) == 32, "CallResult.created_addr offset");

typedef struct EvmCallbacks {
    /* --- Storage (per-frame contract address known from EvmState.address) ---
     *
     * State-access callbacks return the gas to charge for the operation.
     * For EIP-2929 (Berlin+) the host tracks warm/cold accessed sets;
     * for EIP-2200 (Istanbul+) the host tracks original-vs-current values.
     * Native handlers subtract the returned gas from x22 and trap on OOG.
     * Audit/test callbacks that don't care just return the flat per-op gas
     * (100/2100/etc) and ignore the bookkeeping. */
    /* SLOAD: read slot of the executing contract. Returns gas to charge. */
    uint64_t (*sload)(void *ctx, const u256_t *addr, const u256_t *slot,
                      u256_t *out);
    /* SSTORE: write slot of the executing contract. Returns gas (incl. EIP-2929
     * cold surcharge and EIP-2200 transition cost). */
    uint64_t (*sstore)(void *ctx, const u256_t *addr, const u256_t *slot,
                       const u256_t *val);

    /* --- Transient storage (EIP-1153) --- */
    uint64_t (*tload) (void *ctx, const u256_t *slot, u256_t *out);
    uint64_t (*tstore)(void *ctx, const u256_t *slot, const u256_t *val);

    /* --- World hooks (cross-contract reads) --- */
    uint64_t (*balance)        (void *ctx, const u256_t *addr, u256_t *out);
    uint64_t (*ext_code_size)  (void *ctx, const u256_t *addr, uint64_t *out);
    uint64_t (*ext_code_hash)  (void *ctx, const u256_t *addr, u256_t *out);
    /* EXTCODECOPY: copy world code of addr to memory at dst. Returns gas
     * (cold-access surcharge + base cost; caller handles per-word copy cost). */
    uint64_t (*ext_code_copy)  (void *ctx, const u256_t *addr,
                                uint8_t *dst, uint64_t src_off, uint64_t len);
    /* BLOCKHASH: fixed 20 gas; returns value. */
    void (*block_hash)     (void *ctx, const u256_t *blk, u256_t *out);

    /* --- Logging --- */
    void (*log_n)(void *ctx, const u256_t *self_addr,
                  uint8_t n_topics, const u256_t *topics,
                  const uint8_t *data, uint64_t len);

    /* --- Crypto --- */
    void (*keccak256)(const uint8_t *data, uint64_t len, u256_t *out);

    /* --- Sub-call / create / selfdestruct ---
     *
     * These recurse into the interpreter; the host owns the call stack and
     * may run them on a fresh thread, fiber, or just iteratively. The
     * results are written back to the caller's frame via out-params. */
    int  (*call)        (void *ctx, struct CallParams *params,
                         struct CallResult *result);
    int  (*create)      (void *ctx, struct CallParams *params,
                         struct CallResult *result);
    /* SELFDESTRUCT returns extra gas to charge beyond the 5000 base:
     * EIP-2929 cold beneficiary (2600) + EIP-161 new-account creation
     * (25000 if beneficiary is empty and self has nonzero balance). */
    uint64_t (*selfdestruct)(void *ctx, const u256_t *self,
                             const u256_t *beneficiary);

    /* --- Tracing (optional, NULL in production) ---
     *
     * If non-NULL, `_eita_next` calls this on every opcode dispatch with
     * (state, pc, gas_left, sp, opcode). Used for opcode-level debugging.
     * Production runs leave it NULL — the hot path is a load + cbz. */
    void (*trace_step)(void *ctx, uint64_t pc, uint64_t gas_left,
                       uint64_t sp, uint8_t opcode);
} EvmCallbacks;

/* ===========================================================================
 * EvmState — the per-frame mutable state.
 *
 * Field order is chosen so the hot path (pc, gas_left, sp, mp, stack) lives
 * in the first cache line. The struct is exactly 600 bytes (asserted below).
 * ===========================================================================
 */

typedef struct EvmState {
    /* --- Hot path — first cache line (64 bytes) -------------------------- */
    uint64_t   pc;             /* offset   0 — program counter */
    uint64_t   gas_left;       /* offset   8 — remaining gas (signed semantics) */
    uint64_t   sp;             /* offset  16 — stack pointer (next free slot) */
    uint64_t   mp;             /* offset  24 — memory high-water mark (bytes) */
    u256_t    *stack;          /* offset  32 — 1024-entry U256 array */
    uint8_t   *memory;         /* offset  40 — resizable byte buffer */
    uint64_t   memory_size;    /* offset  48 — actual size (bytes) */
    uint64_t   memory_cap;     /* offset  56 — capacity (bytes); resize when size = cap */

    /* --- Buffers (immutable per frame) ----------------------------------- */
    const uint8_t *code;       /* offset  64 — contract code */
    uint64_t       code_size;  /* offset  72 */
    const uint8_t *calldata;   /* offset  80 — inputs from the caller */
    uint64_t       calldata_size; /* offset 88 */

    /* --- Outputs --------------------------------------------------------- */
    uint8_t       *returndata; /* offset  96 — set by sub-call return */
    uint64_t       returndata_size; /* offset 104 */
    uint8_t       *output;     /* offset 112 — set by RETURN/REVERT */
    uint64_t       output_size; /* offset 120 */

    /* --- Flags ----------------------------------------------------------- */
    uint8_t        halted;     /* offset 128 — frame terminated */
    uint8_t        reverted;   /* offset 129 — frame terminated via REVERT */
    uint8_t        staticp;    /* offset 130 — STATICCALL: state-mod forbidden */
    uint8_t        pad_flags[5]; /* offset 131..135 — alignment */

    /* --- Untamed-mode loop bound ---------------------------------------- */
    /* Valid-JUMPDEST map of `code`: jumpdests[pc] = 1 iff code[pc] is a JUMPDEST
     * opcode that is not inside a PUSH immediate (EELS get_valid_jump_destinations).
     * Built by the host per frame (eita_jumpdest_map); JUMP/JUMPI consult it after
     * the bounds check, never the code byte. Was `jump_count` (dead: no handler
     * wrote it) until the 5,800,596 jump-into-PUSH-data divergence. */
    const uint8_t *jumpdests;  /* offset 136 */

    /* --- Frame-level env (U256-valued) ---------------------------------- */
    u256_t         address;    /* offset 144 — executing contract */
    u256_t         origin;     /* offset 176 — tx originator */
    u256_t         caller;     /* offset 208 — immediate caller */
    u256_t         callvalue;  /* offset 240 — wei sent with this call */
    u256_t         gasprice;   /* offset 272 — tx gas price */

    /* --- Block-level env (U256-valued) ---------------------------------- */
    u256_t         chainid;    /* offset 304 */
    u256_t         coinbase;   /* offset 336 — block proposer */
    u256_t         timestamp;  /* offset 368 */
    u256_t         block_number; /* offset 400 */
    u256_t         gaslimit;   /* offset 432 */
    u256_t         basefee;    /* offset 464 */

    /* --- Host link ------------------------------------------------------- */
    const EvmCallbacks *cb;    /* offset 496 — vtable */
    void               *cb_ctx; /* offset 504 — opaque host context */

    /* --- Post-Merge env ------------------------------------------------- */
    u256_t         prev_randao; /* offset 512 — RANDAO mix (EIP-4399) */
    /* x86-64 frame (#238 stage 4): the post-prologue rsp, so a fault stub
     * reached at any call depth can unwind to the epilogue. ARM64 keeps this
     * in x28; x86-64 has no callee-saved register left. Unused on ARM64. */
    uint64_t       frame_sp;   /* offset 544 */

    /* --- EIP-4844 blob env (Cancun) -------------------------------------- */
    /* The tx's versioned blob hashes (EELS tx_env.blob_versioned_hashes): one u256
     * per index, four little-endian limbs, `blob_hash_count` entries; installed by
     * the host per tx (empty for a non-blob tx). BLOBHASH (0x49) indexes it over the
     * full u256 index and pushes 0 past the count. */
    const u256_t  *blob_hashes;      /* offset 552 */
    uint64_t       blob_hash_count;  /* offset 560 */
    /* The block's blob base fee, fake_exponential(excess_blob_gas) per the block's
     * fork, computed once per block by the host (emitted spec-blob-base-fee) and
     * pushed by BLOBBASEFEE (0x4a, EIP-7516). */
    u256_t         blob_base_fee;    /* offset 568 */
} EvmState;

/* ===========================================================================
 * Static offset assertions — guarantee the layout matches what Form.toARM64
 * emits. If you reorder fields, the offsets emitted in the assembly will
 * not match this struct; these assertions catch that at compile time.
 *
 * Drift caught here is preferable to silent corruption at run time.
 * ===========================================================================
 */

#define EITA_ASSERT_OFFSET(field, expected) \
  _Static_assert(offsetof(EvmState, field) == (expected), \
                 "EvmState." #field " offset drifted from documented " #expected)

EITA_ASSERT_OFFSET(pc,              0);
EITA_ASSERT_OFFSET(gas_left,        8);
EITA_ASSERT_OFFSET(sp,             16);
EITA_ASSERT_OFFSET(mp,             24);
EITA_ASSERT_OFFSET(stack,          32);
EITA_ASSERT_OFFSET(memory,         40);
EITA_ASSERT_OFFSET(memory_size,    48);
EITA_ASSERT_OFFSET(memory_cap,     56);
EITA_ASSERT_OFFSET(code,           64);
EITA_ASSERT_OFFSET(code_size,      72);
EITA_ASSERT_OFFSET(calldata,       80);
EITA_ASSERT_OFFSET(calldata_size,  88);
EITA_ASSERT_OFFSET(returndata,     96);
EITA_ASSERT_OFFSET(returndata_size,104);
EITA_ASSERT_OFFSET(output,        112);
EITA_ASSERT_OFFSET(output_size,   120);
EITA_ASSERT_OFFSET(halted,        128);
EITA_ASSERT_OFFSET(reverted,      129);
EITA_ASSERT_OFFSET(staticp,       130);
EITA_ASSERT_OFFSET(jumpdests,     136);
EITA_ASSERT_OFFSET(address,       144);
EITA_ASSERT_OFFSET(origin,        176);
EITA_ASSERT_OFFSET(caller,        208);
EITA_ASSERT_OFFSET(callvalue,     240);
EITA_ASSERT_OFFSET(gasprice,      272);
EITA_ASSERT_OFFSET(chainid,       304);
EITA_ASSERT_OFFSET(coinbase,      336);
EITA_ASSERT_OFFSET(timestamp,     368);
EITA_ASSERT_OFFSET(block_number,  400);
EITA_ASSERT_OFFSET(gaslimit,      432);
EITA_ASSERT_OFFSET(basefee,       464);
EITA_ASSERT_OFFSET(cb,            496);
EITA_ASSERT_OFFSET(cb_ctx,        504);
EITA_ASSERT_OFFSET(prev_randao,   512);
EITA_ASSERT_OFFSET(frame_sp,      544);
EITA_ASSERT_OFFSET(blob_hashes,   552);
EITA_ASSERT_OFFSET(blob_hash_count, 560);
EITA_ASSERT_OFFSET(blob_base_fee, 568);

_Static_assert(sizeof(EvmState) == 600, "EvmState must be exactly 600 bytes");

#undef EITA_ASSERT_OFFSET

/* ===========================================================================
 * Threaded-interp entry point.
 *
 * Loaded by the host once (single allocation of EvmState + stack + memory
 * buffers); called per frame after caller has set up code/calldata/env.
 * Returns when the frame halts (RETURN/REVERT/STOP), reverts on exception,
 * or recurses out via the call/create callback.
 * ===========================================================================
 */

extern void eita_run(EvmState *state);

#ifdef __cplusplus
}
#endif

#endif /* EITA_EVM_STATE_H */
