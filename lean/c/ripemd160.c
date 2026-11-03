/*
 * ripemd160.c — RIPEMD-160 reference implementation.
 *
 * Based on the public-domain reference (Bosselaers / Dobbertin, COSIC).
 * Little-endian word order; 20-byte output.
 */

#include <stdint.h>
#include <string.h>
#include <stddef.h>
#ifndef EITA_NO_LEAN_WRAPPER
#include <lean/lean.h>
#endif

#define ROL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))

#define F(x, y, z) ((x) ^ (y) ^ (z))
#define G(x, y, z) (((x) & (y)) | ((~(x)) & (z)))
#define H(x, y, z) (((x) | (~(y))) ^ (z))
#define I(x, y, z) (((x) & (z)) | ((y) & (~(z))))
#define J(x, y, z) ((x) ^ ((y) | (~(z))))

#define FF(a, b, c, d, e, x, s) { (a) += F((b),(c),(d)) + (x);              (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define GG(a, b, c, d, e, x, s) { (a) += G((b),(c),(d)) + (x) + 0x5a827999u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define HH(a, b, c, d, e, x, s) { (a) += H((b),(c),(d)) + (x) + 0x6ed9eba1u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define II(a, b, c, d, e, x, s) { (a) += I((b),(c),(d)) + (x) + 0x8f1bbcdcu; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define JJ(a, b, c, d, e, x, s) { (a) += J((b),(c),(d)) + (x) + 0xa953fd4eu; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }

#define FFF(a, b, c, d, e, x, s) { (a) += F((b),(c),(d)) + (x);              (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define GGG(a, b, c, d, e, x, s) { (a) += G((b),(c),(d)) + (x) + 0x7a6d76e9u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define HHH(a, b, c, d, e, x, s) { (a) += H((b),(c),(d)) + (x) + 0x6d703ef3u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define III(a, b, c, d, e, x, s) { (a) += I((b),(c),(d)) + (x) + 0x5c4dd124u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }
#define JJJ(a, b, c, d, e, x, s) { (a) += J((b),(c),(d)) + (x) + 0x50a28be6u; (a) = ROL((a),(s)) + (e); (c) = ROL((c), 10); }

static void ripemd160_block(uint32_t h[5], const uint8_t block[64]) {
    uint32_t X[16];
    for (int i = 0; i < 16; i++) {
        X[i] = ((uint32_t)block[i * 4])           |
               ((uint32_t)block[i * 4 + 1] <<  8) |
               ((uint32_t)block[i * 4 + 2] << 16) |
               ((uint32_t)block[i * 4 + 3] << 24);
    }

    uint32_t a  = h[0], b  = h[1], c  = h[2], d  = h[3], e  = h[4];
    uint32_t aa = h[0], bb = h[1], cc = h[2], dd = h[3], ee = h[4];

    /* Left round 1 */
    FF(a, b, c, d, e, X[ 0], 11); FF(e, a, b, c, d, X[ 1], 14);
    FF(d, e, a, b, c, X[ 2], 15); FF(c, d, e, a, b, X[ 3], 12);
    FF(b, c, d, e, a, X[ 4],  5); FF(a, b, c, d, e, X[ 5],  8);
    FF(e, a, b, c, d, X[ 6],  7); FF(d, e, a, b, c, X[ 7],  9);
    FF(c, d, e, a, b, X[ 8], 11); FF(b, c, d, e, a, X[ 9], 13);
    FF(a, b, c, d, e, X[10], 14); FF(e, a, b, c, d, X[11], 15);
    FF(d, e, a, b, c, X[12],  6); FF(c, d, e, a, b, X[13],  7);
    FF(b, c, d, e, a, X[14],  9); FF(a, b, c, d, e, X[15],  8);

    /* Left round 2 */
    GG(e, a, b, c, d, X[ 7],  7); GG(d, e, a, b, c, X[ 4],  6);
    GG(c, d, e, a, b, X[13],  8); GG(b, c, d, e, a, X[ 1], 13);
    GG(a, b, c, d, e, X[10], 11); GG(e, a, b, c, d, X[ 6],  9);
    GG(d, e, a, b, c, X[15],  7); GG(c, d, e, a, b, X[ 3], 15);
    GG(b, c, d, e, a, X[12],  7); GG(a, b, c, d, e, X[ 0], 12);
    GG(e, a, b, c, d, X[ 9], 15); GG(d, e, a, b, c, X[ 5],  9);
    GG(c, d, e, a, b, X[ 2], 11); GG(b, c, d, e, a, X[14],  7);
    GG(a, b, c, d, e, X[11], 13); GG(e, a, b, c, d, X[ 8], 12);

    /* Left round 3 */
    HH(d, e, a, b, c, X[ 3], 11); HH(c, d, e, a, b, X[10], 13);
    HH(b, c, d, e, a, X[14],  6); HH(a, b, c, d, e, X[ 4],  7);
    HH(e, a, b, c, d, X[ 9], 14); HH(d, e, a, b, c, X[15],  9);
    HH(c, d, e, a, b, X[ 8], 13); HH(b, c, d, e, a, X[ 1], 15);
    HH(a, b, c, d, e, X[ 2], 14); HH(e, a, b, c, d, X[ 7],  8);
    HH(d, e, a, b, c, X[ 0], 13); HH(c, d, e, a, b, X[ 6],  6);
    HH(b, c, d, e, a, X[13],  5); HH(a, b, c, d, e, X[11], 12);
    HH(e, a, b, c, d, X[ 5],  7); HH(d, e, a, b, c, X[12],  5);

    /* Left round 4 */
    II(c, d, e, a, b, X[ 1], 11); II(b, c, d, e, a, X[ 9], 12);
    II(a, b, c, d, e, X[11], 14); II(e, a, b, c, d, X[10], 15);
    II(d, e, a, b, c, X[ 0], 14); II(c, d, e, a, b, X[ 8], 15);
    II(b, c, d, e, a, X[12],  9); II(a, b, c, d, e, X[ 4],  8);
    II(e, a, b, c, d, X[13],  9); II(d, e, a, b, c, X[ 3], 14);
    II(c, d, e, a, b, X[ 7],  5); II(b, c, d, e, a, X[15],  6);
    II(a, b, c, d, e, X[14],  8); II(e, a, b, c, d, X[ 5],  6);
    II(d, e, a, b, c, X[ 6],  5); II(c, d, e, a, b, X[ 2], 12);

    /* Left round 5 */
    JJ(b, c, d, e, a, X[ 4],  9); JJ(a, b, c, d, e, X[ 0], 15);
    JJ(e, a, b, c, d, X[ 5],  5); JJ(d, e, a, b, c, X[ 9], 11);
    JJ(c, d, e, a, b, X[ 7],  6); JJ(b, c, d, e, a, X[12],  8);
    JJ(a, b, c, d, e, X[ 2], 13); JJ(e, a, b, c, d, X[10], 12);
    JJ(d, e, a, b, c, X[14],  5); JJ(c, d, e, a, b, X[ 1], 12);
    JJ(b, c, d, e, a, X[ 3], 13); JJ(a, b, c, d, e, X[ 8], 14);
    JJ(e, a, b, c, d, X[11], 11); JJ(d, e, a, b, c, X[ 6],  8);
    JJ(c, d, e, a, b, X[15],  5); JJ(b, c, d, e, a, X[13],  6);

    /* Right round 1 */
    JJJ(aa, bb, cc, dd, ee, X[ 5],  8); JJJ(ee, aa, bb, cc, dd, X[14],  9);
    JJJ(dd, ee, aa, bb, cc, X[ 7],  9); JJJ(cc, dd, ee, aa, bb, X[ 0], 11);
    JJJ(bb, cc, dd, ee, aa, X[ 9], 13); JJJ(aa, bb, cc, dd, ee, X[ 2], 15);
    JJJ(ee, aa, bb, cc, dd, X[11], 15); JJJ(dd, ee, aa, bb, cc, X[ 4],  5);
    JJJ(cc, dd, ee, aa, bb, X[13],  7); JJJ(bb, cc, dd, ee, aa, X[ 6],  7);
    JJJ(aa, bb, cc, dd, ee, X[15],  8); JJJ(ee, aa, bb, cc, dd, X[ 8], 11);
    JJJ(dd, ee, aa, bb, cc, X[ 1], 14); JJJ(cc, dd, ee, aa, bb, X[10], 14);
    JJJ(bb, cc, dd, ee, aa, X[ 3], 12); JJJ(aa, bb, cc, dd, ee, X[12],  6);

    /* Right round 2 */
    III(ee, aa, bb, cc, dd, X[ 6],  9); III(dd, ee, aa, bb, cc, X[11], 13);
    III(cc, dd, ee, aa, bb, X[ 3], 15); III(bb, cc, dd, ee, aa, X[ 7],  7);
    III(aa, bb, cc, dd, ee, X[ 0], 12); III(ee, aa, bb, cc, dd, X[13],  8);
    III(dd, ee, aa, bb, cc, X[ 5],  9); III(cc, dd, ee, aa, bb, X[10], 11);
    III(bb, cc, dd, ee, aa, X[14],  7); III(aa, bb, cc, dd, ee, X[15],  7);
    III(ee, aa, bb, cc, dd, X[ 8], 12); III(dd, ee, aa, bb, cc, X[12],  7);
    III(cc, dd, ee, aa, bb, X[ 4],  6); III(bb, cc, dd, ee, aa, X[ 9], 15);
    III(aa, bb, cc, dd, ee, X[ 1], 13); III(ee, aa, bb, cc, dd, X[ 2], 11);

    /* Right round 3 */
    HHH(dd, ee, aa, bb, cc, X[15],  9); HHH(cc, dd, ee, aa, bb, X[ 5],  7);
    HHH(bb, cc, dd, ee, aa, X[ 1], 15); HHH(aa, bb, cc, dd, ee, X[ 3], 11);
    HHH(ee, aa, bb, cc, dd, X[ 7],  8); HHH(dd, ee, aa, bb, cc, X[14],  6);
    HHH(cc, dd, ee, aa, bb, X[ 6],  6); HHH(bb, cc, dd, ee, aa, X[ 9], 14);
    HHH(aa, bb, cc, dd, ee, X[11], 12); HHH(ee, aa, bb, cc, dd, X[ 8], 13);
    HHH(dd, ee, aa, bb, cc, X[12],  5); HHH(cc, dd, ee, aa, bb, X[ 2], 14);
    HHH(bb, cc, dd, ee, aa, X[10], 13); HHH(aa, bb, cc, dd, ee, X[ 0], 13);
    HHH(ee, aa, bb, cc, dd, X[ 4],  7); HHH(dd, ee, aa, bb, cc, X[13],  5);

    /* Right round 4 */
    GGG(cc, dd, ee, aa, bb, X[ 8], 15); GGG(bb, cc, dd, ee, aa, X[ 6],  5);
    GGG(aa, bb, cc, dd, ee, X[ 4],  8); GGG(ee, aa, bb, cc, dd, X[ 1], 11);
    GGG(dd, ee, aa, bb, cc, X[ 3], 14); GGG(cc, dd, ee, aa, bb, X[11], 14);
    GGG(bb, cc, dd, ee, aa, X[15],  6); GGG(aa, bb, cc, dd, ee, X[ 0], 14);
    GGG(ee, aa, bb, cc, dd, X[ 5],  6); GGG(dd, ee, aa, bb, cc, X[12],  9);
    GGG(cc, dd, ee, aa, bb, X[ 2], 12); GGG(bb, cc, dd, ee, aa, X[13],  9);
    GGG(aa, bb, cc, dd, ee, X[ 9], 12); GGG(ee, aa, bb, cc, dd, X[ 7],  5);
    GGG(dd, ee, aa, bb, cc, X[10], 15); GGG(cc, dd, ee, aa, bb, X[14],  8);

    /* Right round 5 */
    FFF(bb, cc, dd, ee, aa, X[12],  8); FFF(aa, bb, cc, dd, ee, X[15],  5);
    FFF(ee, aa, bb, cc, dd, X[10], 12); FFF(dd, ee, aa, bb, cc, X[ 4],  9);
    FFF(cc, dd, ee, aa, bb, X[ 1], 12); FFF(bb, cc, dd, ee, aa, X[ 5],  5);
    FFF(aa, bb, cc, dd, ee, X[ 8], 14); FFF(ee, aa, bb, cc, dd, X[ 7],  6);
    FFF(dd, ee, aa, bb, cc, X[ 6],  8); FFF(cc, dd, ee, aa, bb, X[ 2], 13);
    FFF(bb, cc, dd, ee, aa, X[13],  6); FFF(aa, bb, cc, dd, ee, X[14],  5);
    FFF(ee, aa, bb, cc, dd, X[ 0], 15); FFF(dd, ee, aa, bb, cc, X[ 3], 13);
    FFF(cc, dd, ee, aa, bb, X[ 9], 11); FFF(bb, cc, dd, ee, aa, X[11], 11);

    uint32_t t = h[1] + c + dd;
    h[1] = h[2] + d + ee;
    h[2] = h[3] + e + aa;
    h[3] = h[4] + a + bb;
    h[4] = h[0] + b + cc;
    h[0] = t;
}

void ripemd160_hash(const uint8_t *in, size_t n, uint8_t out[20]) {
    uint32_t h[5] = {
        0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
    };
    uint64_t total_bits = (uint64_t)n * 8;

    while (n >= 64) {
        ripemd160_block(h, in);
        in += 64;
        n  -= 64;
    }

    uint8_t buf[128];
    memcpy(buf, in, n);
    buf[n] = 0x80;
    size_t pad = (n + 1 <= 56) ? 56 - (n + 1) : 120 - (n + 1);
    memset(buf + n + 1, 0, pad);
    size_t tail = n + 1 + pad;
    for (int i = 0; i < 8; i++)
        buf[tail + i] = (uint8_t)(total_bits >> (i * 8));
    ripemd160_block(h, buf);
    if (tail + 8 > 64) ripemd160_block(h, buf + 64);

    for (int i = 0; i < 5; i++) {
        out[i * 4]     = (uint8_t)(h[i]);
        out[i * 4 + 1] = (uint8_t)(h[i] >>  8);
        out[i * 4 + 2] = (uint8_t)(h[i] >> 16);
        out[i * 4 + 3] = (uint8_t)(h[i] >> 24);
    }
}

#ifndef EITA_NO_LEAN_WRAPPER
LEAN_EXPORT lean_obj_res lean_ripemd160(b_lean_obj_arg input) {
    size_t n = lean_sarray_size(input);
    const uint8_t *src = lean_sarray_cptr(input);
    lean_obj_res out = lean_alloc_sarray(1, 20, 20);
    ripemd160_hash(src, n, lean_sarray_cptr(out));
    return out;
}
#endif
