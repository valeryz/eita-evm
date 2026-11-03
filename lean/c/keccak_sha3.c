/*
 * keccak_sha3.c — Ethereum-style Keccak-256 (pad byte 0x01) accelerated with
 * the ARMv8.2 FEAT_SHA3 NEON instructions (EOR3 / RAX1 / XAR / BCAX).
 *
 * Provides `eita_keccak256_sha3`, bit-identical to the portable
 * `eita_keccak256` in keccak.c. Same Keccak-f[1600]: rate=1088 bits
 * (136 bytes), capacity=512 bits, 24 rounds, little-endian state/output.
 *
 * The permutation carries the FEAT_SHA3 target attribute so the default -O2
 * build (without -march=armv8.2-a+sha3 on the whole TU) still emits the SHA3
 * instructions for that one function. To compile the whole file you can pass
 * `-march=armv8.2-a+sha3`; the function attribute makes that optional.
 *
 * Lane layout: the 25 lanes are held as scalar uint64_t st[25] (same memory
 * order as the portable version, st[x + 5*y]). The permutation loads pairs of
 * lanes into uint64x2_t vectors and applies the fused SHA3 ops. The pairing
 * follows the standard XKCP/OpenSSL "two columns at a time" scheme: lanes are
 * grouped so theta and chi each operate on vector pairs.
 *
 * Only the intrinsic path is compiled under __aarch64__. On other targets the
 * symbol is provided as a thin alias to the portable implementation so the
 * file is always linkable.
 */

#include <stdint.h>
#include <string.h>
#include <stddef.h>

/* Portable entry from keccak.c — always available. */
void eita_keccak256(const uint8_t *in, size_t len, uint8_t out[32]);

#if defined(__aarch64__)

#include <arm_neon.h>

static const uint64_t sha3_rndc[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL
};

/*
 * Keccak-f[1600] using FEAT_SHA3.
 *
 * We keep the 25 lanes as scalars and build the needed uint64x2_t pairs on the
 * fly. This is the most readable correct layout; the compiler keeps everything
 * in registers at -O2. Each intrinsic maps to one SHA3 instruction:
 *   veor3q_u64(a,b,c) = a^b^c, vrax1q_u64(a,b)=a^ROL(b,1),
 *   vxarq_u64(a,b,n)=ROR(a^b,n), vbcaxq_u64(a,b,c)=a^(b&~c).
 *
 * Helpers operate lane-by-lane via these vector ops by packing one value per
 * vector (lane 0) — but to actually use the hardware width we pair the 5
 * columns of theta and the 5 lanes of chi where it is natural. For maximum
 * clarity and guaranteed bit-identity we implement the round using the vector
 * ops over pairs derived directly from the reference algorithm.
 */
/* ROL64(x, n) via XAR: vxarq_u64(a, b, imm) = ROR64(a^b, imm); with b=0 and
   imm = 64-n this is ROL64(a, n). Requires 1 <= n <= 63 (XAR imm 1..63).
   vxarq_u64 is a function-like macro, so we feed it plain lvalues, not braces. */
__attribute__((target("sha3")))
static inline uint64_t rol64_xar(uint64_t x, int n)
{
    const uint64x2_t zero = vdupq_n_u64(0);
    uint64x2_t v = vdupq_n_u64(x);
    switch (n) {
        case 1:  v = vxarq_u64(v, zero, 63); break;
        case 3:  v = vxarq_u64(v, zero, 61); break;
        case 6:  v = vxarq_u64(v, zero, 58); break;
        case 10: v = vxarq_u64(v, zero, 54); break;
        case 15: v = vxarq_u64(v, zero, 49); break;
        case 21: v = vxarq_u64(v, zero, 43); break;
        case 28: v = vxarq_u64(v, zero, 36); break;
        case 36: v = vxarq_u64(v, zero, 28); break;
        case 45: v = vxarq_u64(v, zero, 19); break;
        case 55: v = vxarq_u64(v, zero, 9);  break;
        case 2:  v = vxarq_u64(v, zero, 62); break;
        case 14: v = vxarq_u64(v, zero, 50); break;
        case 27: v = vxarq_u64(v, zero, 37); break;
        case 41: v = vxarq_u64(v, zero, 23); break;
        case 56: v = vxarq_u64(v, zero, 8);  break;
        case 8:  v = vxarq_u64(v, zero, 56); break;
        case 25: v = vxarq_u64(v, zero, 39); break;
        case 43: v = vxarq_u64(v, zero, 21); break;
        case 62: v = vxarq_u64(v, zero, 2);  break;
        case 18: v = vxarq_u64(v, zero, 46); break;
        case 39: v = vxarq_u64(v, zero, 25); break;
        case 61: v = vxarq_u64(v, zero, 3);  break;
        case 20: v = vxarq_u64(v, zero, 44); break;
        case 44: v = vxarq_u64(v, zero, 20); break;
        default: return x;  /* n == 0 */
    }
    return vgetq_lane_u64(v, 0);
}

__attribute__((target("sha3")))
static void keccakf_sha3(uint64_t st[25])
{
    /* Single-lane helpers expressed via the SHA3 intrinsics. Each packs the
       operands into lane 0 of a uint64x2_t, runs the fused op, extracts lane 0.
       At -O2 with the sha3 target these still lower to the scalar+SHA3 forms,
       but more importantly they are provably equal to the reference ops:
         eor3(a,b,c) = a^b^c
         rax1(a,b)   = a ^ ROL64(b,1)
         xar(a,b,n)  = ROR64(a^b, n)              (n in 0..63)
         bcax(a,b,c) = a ^ (b & ~c)
       We use the genuine 2-lane width for theta and chi below. */

    for (int r = 0; r < 24; r++) {
        /* ---- Theta ---- */
        /* Column parities c[x] = XOR of the 5 lanes in column x, via EOR3
           (two columns at a time, lane 0 = even column, lane 1 = odd). */
        uint64_t c0, c1, c2, c3, c4;
        {
            /* columns 0,1 */
            uint64x2_t a = veor3q_u64((uint64x2_t){st[0], st[1]},
                                      (uint64x2_t){st[5], st[6]},
                                      (uint64x2_t){st[10], st[11]});
            a = veor3q_u64(a, (uint64x2_t){st[15], st[16]},
                              (uint64x2_t){st[20], st[21]});
            c0 = vgetq_lane_u64(a, 0); c1 = vgetq_lane_u64(a, 1);
            /* columns 2,3 */
            uint64x2_t b = veor3q_u64((uint64x2_t){st[2], st[3]},
                                      (uint64x2_t){st[7], st[8]},
                                      (uint64x2_t){st[12], st[13]});
            b = veor3q_u64(b, (uint64x2_t){st[17], st[18]},
                              (uint64x2_t){st[22], st[23]});
            c2 = vgetq_lane_u64(b, 0); c3 = vgetq_lane_u64(b, 1);
            /* column 4 */
            uint64x2_t e = veor3q_u64((uint64x2_t){st[4], 0},
                                      (uint64x2_t){st[9], 0},
                                      (uint64x2_t){st[14], 0});
            e = veor3q_u64(e, (uint64x2_t){st[19], 0},
                              (uint64x2_t){st[24], 0});
            c4 = vgetq_lane_u64(e, 0);
        }

        /* d[x] = c[x-1] ^ ROL64(c[x+1], 1)  — RAX1. */
        uint64_t d0, d1, d2, d3, d4;
        {
            uint64x2_t a = (uint64x2_t){ c4, c0 };
            uint64x2_t b = (uint64x2_t){ c1, c2 };
            uint64x2_t r01 = vrax1q_u64(a, b);   /* {c4^ROL(c1,1), c0^ROL(c2,1)} */
            d0 = vgetq_lane_u64(r01, 0);
            d1 = vgetq_lane_u64(r01, 1);

            uint64x2_t a2 = (uint64x2_t){ c1, c2 };
            uint64x2_t b2 = (uint64x2_t){ c3, c4 };
            uint64x2_t r23 = vrax1q_u64(a2, b2); /* {c1^ROL(c3,1), c2^ROL(c4,1)} */
            d2 = vgetq_lane_u64(r23, 0);
            d3 = vgetq_lane_u64(r23, 1);

            uint64x2_t a3 = (uint64x2_t){ c3, 0 };
            uint64x2_t b3 = (uint64x2_t){ c0, 0 };
            uint64x2_t r4 = vrax1q_u64(a3, b3);  /* {c3^ROL(c0,1), ...} */
            d4 = vgetq_lane_u64(r4, 0);
        }

        st[0] ^= d0; st[5] ^= d0; st[10] ^= d0; st[15] ^= d0; st[20] ^= d0;
        st[1] ^= d1; st[6] ^= d1; st[11] ^= d1; st[16] ^= d1; st[21] ^= d1;
        st[2] ^= d2; st[7] ^= d2; st[12] ^= d2; st[17] ^= d2; st[22] ^= d2;
        st[3] ^= d3; st[8] ^= d3; st[13] ^= d3; st[18] ^= d3; st[23] ^= d3;
        st[4] ^= d4; st[9] ^= d4; st[14] ^= d4; st[19] ^= d4; st[24] ^= d4;

        /* ---- Rho + Pi ---- */
        /* B[pi(x,y)] = ROL64(A'[x,y], rho[x,y]). We compute via XAR with the
           second operand 0 so XAR(a,0,64-n) = ROR(a,64-n) = ROL(a,n).
           XAR's immediate is a *right* rotation amount; ROL(a,n)=ROR(a,64-n).
           For n==0 we keep the lane as-is (XAR imm must be 1..63 to be safe;
           rho[0,0]==0 so lane st[0] is untouched). */
        uint64_t b[25];

        /* B[pi(i)] = ROL64(st[src_i], rho_i), following the reference rho+pi
           chain (keccakf_piln / keccakf_rotc). Lane 0 (rho 0) is the identity. */
        b[0]  = st[0];
        b[10] = rol64_xar(st[1],  1);
        b[7]  = rol64_xar(st[10], 3);
        b[11] = rol64_xar(st[7],  6);
        b[17] = rol64_xar(st[11], 10);
        b[18] = rol64_xar(st[17], 15);
        b[3]  = rol64_xar(st[18], 21);
        b[5]  = rol64_xar(st[3],  28);
        b[16] = rol64_xar(st[5],  36);
        b[8]  = rol64_xar(st[16], 45);
        b[21] = rol64_xar(st[8],  55);
        b[24] = rol64_xar(st[21], 2);
        b[4]  = rol64_xar(st[24], 14);
        b[15] = rol64_xar(st[4],  27);
        b[23] = rol64_xar(st[15], 41);
        b[19] = rol64_xar(st[23], 56);
        b[13] = rol64_xar(st[19], 8);
        b[12] = rol64_xar(st[13], 25);
        b[2]  = rol64_xar(st[12], 43);
        b[20] = rol64_xar(st[2],  62);
        b[14] = rol64_xar(st[20], 18);
        b[22] = rol64_xar(st[14], 39);
        b[9]  = rol64_xar(st[22], 61);
        b[6]  = rol64_xar(st[9],  20);
        b[1]  = rol64_xar(st[6],  44);

        /* ---- Chi ---- using BCAX: out = a ^ (~b & c) = bcax(a, c, b). */
        for (int j = 0; j < 25; j += 5) {
            uint64_t b0 = b[j+0], b1 = b[j+1], b2 = b[j+2], b3 = b[j+3], b4 = b[j+4];
            uint64x2_t r01 = vbcaxq_u64((uint64x2_t){b0, b1},
                                        (uint64x2_t){b2, b3},
                                        (uint64x2_t){b1, b2});
            uint64x2_t r23 = vbcaxq_u64((uint64x2_t){b2, b3},
                                        (uint64x2_t){b4, b0},
                                        (uint64x2_t){b3, b4});
            uint64_t r4  = b4 ^ ((~b0) & b1);
            st[j+0] = vgetq_lane_u64(r01, 0);
            st[j+1] = vgetq_lane_u64(r01, 1);
            st[j+2] = vgetq_lane_u64(r23, 0);
            st[j+3] = vgetq_lane_u64(r23, 1);
            st[j+4] = r4;
        }

        /* ---- Iota ---- */
        st[0] ^= sha3_rndc[r];
    }
}

void eita_keccak256_sha3(const uint8_t *in, size_t len, uint8_t out[32])
{
    uint64_t st[25];
    uint8_t *sb = (uint8_t *)st;
    const size_t rate = 136;  /* 1088 / 8 */
    size_t i;

    memset(st, 0, sizeof(st));

    while (len >= rate) {
        for (i = 0; i < rate; i++) sb[i] ^= in[i];
        keccakf_sha3(st);
        in += rate;
        len -= rate;
    }

    uint8_t pad[136];
    memset(pad, 0, sizeof(pad));
    memcpy(pad, in, len);
    pad[len]     |= 0x01;
    pad[rate - 1] |= 0x80;

    for (i = 0; i < rate; i++) sb[i] ^= pad[i];
    keccakf_sha3(st);

    memcpy(out, sb, 32);
}

#else  /* !__aarch64__ : provide the symbol as a thin alias. */

void eita_keccak256_sha3(const uint8_t *in, size_t len, uint8_t out[32])
{
    eita_keccak256(in, len, out);
}

#endif
