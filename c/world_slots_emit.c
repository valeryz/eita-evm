/* world_slots_emit.c: GENERATED, do not edit. Printed by Eita's Velvet C printer from the slot
   table's Velvet methods, each proved (in Lean, with Velvet) against the slot-table model for every
   capacity: find, place, remove, next, create, rehash, grow, put, lookup, dirGrow, copyArrs, fresh.
   The proofs and the printer are in Eita's separate velvet-slots package (to be published); a drift
   check there regenerates this file and fails if it differs. Glue: world_slots.c. */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Printer temporaries, unused parameters and functions are expected: silence them here only. */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-function"
static inline uint64_t nat_sub(uint64_t a, uint64_t b) { return a < b ? 0 : a - b; }
static void *vv_zeroed(void *p, uint64_t bytes) {
  if (!p) { fputs("eita_ws: out of memory\n", stderr); abort(); }
  memset(p, 0, bytes);
  return p;
}
static inline uint64_t *alloc_zero64(uint64_t n) { return vv_zeroed(malloc(n * sizeof(uint64_t)), n * sizeof(uint64_t)); }
static inline uint8_t *alloc_zero8(uint64_t n) { return vv_zeroed(malloc(n * sizeof(uint8_t)), n * sizeof(uint8_t)); }

struct ret_vv_find { bool f0; uint64_t f1; };
/* find: contract forbids failure; consumes no array parameter */
static struct ret_vv_find vv_find(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  uint64_t h_0 = ((((k0 * 11400714819323198485ULL) + k1) >> ((17ULL) & 63)) & nat_sub(cap, 1ULL));
  uint64_t i_1 = h_0;
  uint64_t n_2 = 0ULL;
  uint64_t tomb_3 = cap;
  bool st_4 = false;
  bool st_5 = false;
  uint64_t st_6 = 0;
  uint64_t st_7 = 0;
  uint64_t st_8 = 0;
  uint64_t st_9 = 0;
  bool tmp_10 = false;
  bool tmp_11 = false;
  uint64_t tmp_12 = 0;
  uint64_t tmp_13 = i_1;
  uint64_t tmp_14 = n_2;
  uint64_t tmp_15 = tomb_3;
  st_4 = tmp_10;
  st_5 = tmp_11;
  st_6 = tmp_12;
  st_7 = tmp_13;
  st_8 = tmp_14;
  st_9 = tmp_15;
  for (;;) {
    uint64_t __s_16 = st_7;
    uint64_t __s_17 = st_8;
    uint64_t __s_18 = st_9;
    uint64_t i_19 = __s_16;
    uint64_t __s_20 = __s_17;
    uint64_t __s_21 = __s_18;
    uint64_t n_22 = __s_20;
    uint64_t tomb_23 = __s_21;
    if (n_22 < cap) {
      uint8_t blk_24 = 0;
      uint8_t tmp_25 = s[i_19];
      blk_24 = tmp_25;
      uint8_t st_26 = blk_24;
      if (st_26 == 0) {
        if (tomb_23 < cap) {
          bool tmp_27 = true;
          bool tmp_28 = false;
          uint64_t tmp_29 = tomb_23;
          uint64_t tmp_30 = i_19;
          uint64_t tmp_31 = n_22;
          uint64_t tmp_32 = tomb_23;
          st_4 = tmp_27;
          st_5 = tmp_28;
          st_6 = tmp_29;
          st_7 = tmp_30;
          st_8 = tmp_31;
          st_9 = tmp_32;
          break;
        } else {
          bool tmp_33 = true;
          bool tmp_34 = false;
          uint64_t tmp_35 = i_19;
          uint64_t tmp_36 = i_19;
          uint64_t tmp_37 = n_22;
          uint64_t tmp_38 = tomb_23;
          st_4 = tmp_33;
          st_5 = tmp_34;
          st_6 = tmp_35;
          st_7 = tmp_36;
          st_8 = tmp_37;
          st_9 = tmp_38;
          break;
        }
      } else {
        if (st_26 == 2) {
          if (tomb_23 == cap) {
            uint64_t tomb_39 = i_19;
            uint64_t i_40 = ((i_19 + 1ULL) & nat_sub(cap, 1ULL));
            uint64_t n_41 = (n_22 + 1ULL);
            bool tmp_42 = false;
            bool tmp_43 = false;
            uint64_t tmp_44 = 0;
            uint64_t tmp_45 = i_40;
            uint64_t tmp_46 = n_41;
            uint64_t tmp_47 = tomb_39;
            st_4 = tmp_42;
            st_5 = tmp_43;
            st_6 = tmp_44;
            st_7 = tmp_45;
            st_8 = tmp_46;
            st_9 = tmp_47;
            continue;
          } else {
            uint64_t i_48 = ((i_19 + 1ULL) & nat_sub(cap, 1ULL));
            uint64_t n_49 = (n_22 + 1ULL);
            bool tmp_50 = false;
            bool tmp_51 = false;
            uint64_t tmp_52 = 0;
            uint64_t tmp_53 = i_48;
            uint64_t tmp_54 = n_49;
            uint64_t tmp_55 = tomb_23;
            st_4 = tmp_50;
            st_5 = tmp_51;
            st_6 = tmp_52;
            st_7 = tmp_53;
            st_8 = tmp_54;
            st_9 = tmp_55;
            continue;
          }
        } else {
          uint64_t blk_56 = 0;
          uint64_t tmp_57 = w[(8ULL * i_19)];
          blk_56 = tmp_57;
          uint64_t e0_58 = blk_56;
          uint64_t blk_59 = 0;
          uint64_t tmp_60 = w[((8ULL * i_19) + 1ULL)];
          blk_59 = tmp_60;
          uint64_t e1_61 = blk_59;
          uint64_t blk_62 = 0;
          uint64_t tmp_63 = w[((8ULL * i_19) + 2ULL)];
          blk_62 = tmp_63;
          uint64_t e2_64 = blk_62;
          uint64_t blk_65 = 0;
          uint64_t tmp_66 = w[((8ULL * i_19) + 3ULL)];
          blk_65 = tmp_66;
          uint64_t e3_67 = blk_65;
          if ((((e0_58 == k0) && (e1_61 == k1)) && (e2_64 == k2)) && (e3_67 == k3)) {
            bool tmp_68 = true;
            bool tmp_69 = true;
            uint64_t tmp_70 = i_19;
            uint64_t tmp_71 = i_19;
            uint64_t tmp_72 = n_22;
            uint64_t tmp_73 = tomb_23;
            st_4 = tmp_68;
            st_5 = tmp_69;
            st_6 = tmp_70;
            st_7 = tmp_71;
            st_8 = tmp_72;
            st_9 = tmp_73;
            break;
          } else {
            uint64_t i_74 = ((i_19 + 1ULL) & nat_sub(cap, 1ULL));
            uint64_t n_75 = (n_22 + 1ULL);
            bool tmp_76 = false;
            bool tmp_77 = false;
            uint64_t tmp_78 = 0;
            uint64_t tmp_79 = i_74;
            uint64_t tmp_80 = n_75;
            uint64_t tmp_81 = tomb_23;
            st_4 = tmp_76;
            st_5 = tmp_77;
            st_6 = tmp_78;
            st_7 = tmp_79;
            st_8 = tmp_80;
            st_9 = tmp_81;
            continue;
          }
        }
      }
    } else {
      bool tmp_82 = false;
      bool tmp_83 = false;
      uint64_t tmp_84 = 0;
      uint64_t tmp_85 = i_19;
      uint64_t tmp_86 = n_22;
      uint64_t tmp_87 = tomb_23;
      st_4 = tmp_82;
      st_5 = tmp_83;
      st_6 = tmp_84;
      st_7 = tmp_85;
      st_8 = tmp_86;
      st_9 = tmp_87;
      break;
    }
  }
  bool __s_88 = st_4;
  bool __s_89 = st_5;
  uint64_t __s_90 = st_6;
  uint64_t __s_91 = st_7;
  uint64_t __s_92 = st_8;
  uint64_t __s_93 = st_9;
  bool __r_94 = __s_88;
  bool __r_95 = __s_89;
  uint64_t __r_96 = __s_90;
  uint64_t __s_97 = __s_91;
  uint64_t __s_98 = __s_92;
  uint64_t __s_99 = __s_93;
  uint64_t __s_100 = __s_98;
  uint64_t __s_101 = __s_99;
  uint64_t tomb_102 = __s_101;
  if (__r_94) {
    return (struct ret_vv_find){__r_95, __r_96};
  } else {
    return (struct ret_vv_find){false, tomb_102};
  }
}

struct ret_vv_place { uint64_t * f0; uint8_t * f1; uint64_t f2; uint64_t f3; };
/* place: contract forbids failure; consumes (may store into or return): w, s */
static struct ret_vv_place vv_place(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t used, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3) {
  struct ret_vv_find find_103 = vv_find(cap, w, s, k0, k1, k2, k3);
  bool f_104 = find_103.f0;
  uint64_t f_105 = find_103.f1;
  if (f_104) {
    uint64_t * blk_106 = NULL;
    uint64_t * blk_107 = NULL;
    w[((8ULL * f_105) + 4ULL)] = v0;
    uint64_t * tmp_108 = w;
    blk_107 = tmp_108;
    uint64_t * w_109 = blk_107;
    uint64_t * blk_110 = NULL;
    w_109[((8ULL * f_105) + 5ULL)] = v1;
    uint64_t * tmp_111 = w_109;
    blk_110 = tmp_111;
    uint64_t * w_112 = blk_110;
    uint64_t * blk_113 = NULL;
    w_112[((8ULL * f_105) + 6ULL)] = v2;
    uint64_t * tmp_114 = w_112;
    blk_113 = tmp_114;
    uint64_t * w_115 = blk_113;
    w_115[((8ULL * f_105) + 7ULL)] = v3;
    uint64_t * tmp_116 = w_115;
    blk_106 = tmp_116;
    uint64_t * w_p_117 = blk_106;
    return (struct ret_vv_place){w_p_117, s, count, used};
  } else {
    uint8_t blk_118 = 0;
    uint8_t tmp_119 = s[f_105];
    blk_118 = tmp_119;
    uint8_t st_120 = blk_118;
    uint64_t ite_121 = 0;
    if (st_120 == 0) {
      uint64_t tmp_122 = (used + 1ULL);
      ite_121 = tmp_122;
    } else {
      uint64_t tmp_123 = used;
      ite_121 = tmp_123;
    }
    uint64_t used_p_124 = ite_121;
    uint64_t * blk_125 = NULL;
    uint64_t * blk_126 = NULL;
    w[(8ULL * f_105)] = k0;
    uint64_t * tmp_127 = w;
    blk_126 = tmp_127;
    uint64_t * w_128 = blk_126;
    uint64_t * blk_129 = NULL;
    w_128[((8ULL * f_105) + 1ULL)] = k1;
    uint64_t * tmp_130 = w_128;
    blk_129 = tmp_130;
    uint64_t * w_131 = blk_129;
    uint64_t * blk_132 = NULL;
    w_131[((8ULL * f_105) + 2ULL)] = k2;
    uint64_t * tmp_133 = w_131;
    blk_132 = tmp_133;
    uint64_t * w_134 = blk_132;
    uint64_t * blk_135 = NULL;
    w_134[((8ULL * f_105) + 3ULL)] = k3;
    uint64_t * tmp_136 = w_134;
    blk_135 = tmp_136;
    uint64_t * w_137 = blk_135;
    uint64_t * blk_138 = NULL;
    w_137[((8ULL * f_105) + 4ULL)] = v0;
    uint64_t * tmp_139 = w_137;
    blk_138 = tmp_139;
    uint64_t * w_140 = blk_138;
    uint64_t * blk_141 = NULL;
    w_140[((8ULL * f_105) + 5ULL)] = v1;
    uint64_t * tmp_142 = w_140;
    blk_141 = tmp_142;
    uint64_t * w_143 = blk_141;
    uint64_t * blk_144 = NULL;
    w_143[((8ULL * f_105) + 6ULL)] = v2;
    uint64_t * tmp_145 = w_143;
    blk_144 = tmp_145;
    uint64_t * w_146 = blk_144;
    w_146[((8ULL * f_105) + 7ULL)] = v3;
    uint64_t * tmp_147 = w_146;
    blk_125 = tmp_147;
    uint64_t * w_p_148 = blk_125;
    uint8_t * blk_149 = NULL;
    s[f_105] = 1;
    uint8_t * tmp_150 = s;
    blk_149 = tmp_150;
    uint8_t * s_p_151 = blk_149;
    return (struct ret_vv_place){w_p_148, s_p_151, (count + 1ULL), used_p_124};
  }
}

struct ret_vv_remove { uint8_t * f0; uint64_t f1; };
/* remove: contract forbids failure; consumes (may store into or return): s */
static struct ret_vv_remove vv_remove(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  struct ret_vv_find find_152 = vv_find(cap, w, s, k0, k1, k2, k3);
  bool f_153 = find_152.f0;
  uint64_t f_154 = find_152.f1;
  if (f_153) {
    uint8_t * blk_155 = NULL;
    s[f_154] = 2;
    uint8_t * tmp_156 = s;
    blk_155 = tmp_156;
    uint8_t * s_p_157 = blk_155;
    return (struct ret_vv_remove){s_p_157, nat_sub(count, 1ULL)};
  } else {
    return (struct ret_vv_remove){s, count};
  }
}

/* next: contract forbids failure; consumes no array parameter */
static uint64_t vv_next(uint64_t cap, uint8_t *s, uint64_t i) {
  uint64_t j_158 = i;
  bool st_159 = false;
  uint64_t st_160 = 0;
  uint64_t st_161 = 0;
  bool tmp_162 = false;
  uint64_t tmp_163 = 0;
  uint64_t tmp_164 = j_158;
  st_159 = tmp_162;
  st_160 = tmp_163;
  st_161 = tmp_164;
  for (;;) {
    uint64_t j_165 = st_161;
    if (j_165 < cap) {
      uint8_t blk_166 = 0;
      uint8_t tmp_167 = s[j_165];
      blk_166 = tmp_167;
      uint8_t st_168 = blk_166;
      if (st_168 == 1) {
        bool tmp_169 = true;
        uint64_t tmp_170 = j_165;
        uint64_t tmp_171 = j_165;
        st_159 = tmp_169;
        st_160 = tmp_170;
        st_161 = tmp_171;
        break;
      } else {
        uint64_t j_172 = (j_165 + 1ULL);
        bool tmp_173 = false;
        uint64_t tmp_174 = 0;
        uint64_t tmp_175 = j_172;
        st_159 = tmp_173;
        st_160 = tmp_174;
        st_161 = tmp_175;
        continue;
      }
    } else {
      bool tmp_176 = false;
      uint64_t tmp_177 = 0;
      uint64_t tmp_178 = j_165;
      st_159 = tmp_176;
      st_160 = tmp_177;
      st_161 = tmp_178;
      break;
    }
  }
  bool __s_179 = st_159;
  uint64_t __s_180 = st_160;
  uint64_t __s_181 = st_161;
  bool __r_182 = __s_179;
  uint64_t __r_183 = __s_180;
  uint64_t j_184 = __s_181;
  if (__r_182) {
    return __r_183;
  } else {
    return j_184;
  }
}

struct ret_vv_create { uint64_t * f0; uint8_t * f1; };
/* create: contract forbids failure; consumes no array parameter */
static struct ret_vv_create vv_create(uint64_t cap) {
  uint64_t *arr_185 = alloc_zero64((8ULL * cap));
  uint8_t *arr_186 = alloc_zero8(cap);
  return (struct ret_vv_create){arr_185, arr_186};
}

struct ret_vv_rehash { uint64_t * f0; uint8_t * f1; uint64_t f2; };
/* rehash: contract forbids failure; consumes no array parameter */
static struct ret_vv_rehash vv_rehash(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t ncap) {
  uint64_t *arr_187 = alloc_zero64((8ULL * ncap));
  uint64_t * nw_188 = arr_187;
  uint8_t *arr_189 = alloc_zero8(ncap);
  uint8_t * ns_190 = arr_189;
  uint64_t ncount_191 = 0ULL;
  uint64_t nused_192 = 0ULL;
  uint64_t j_193 = 0ULL;
  uint64_t * st_194 = NULL;
  uint8_t * st_195 = NULL;
  uint64_t st_196 = 0;
  uint64_t st_197 = 0;
  uint64_t st_198 = 0;
  uint64_t * tmp_199 = nw_188;
  uint8_t * tmp_200 = ns_190;
  uint64_t tmp_201 = ncount_191;
  uint64_t tmp_202 = nused_192;
  uint64_t tmp_203 = j_193;
  st_194 = tmp_199;
  st_195 = tmp_200;
  st_196 = tmp_201;
  st_197 = tmp_202;
  st_198 = tmp_203;
  for (;;) {
    uint64_t * nw_204 = st_194;
    uint8_t * __s_205 = st_195;
    uint64_t __s_206 = st_196;
    uint64_t __s_207 = st_197;
    uint64_t __s_208 = st_198;
    uint8_t * ns_209 = __s_205;
    uint64_t __s_210 = __s_206;
    uint64_t __s_211 = __s_207;
    uint64_t __s_212 = __s_208;
    uint64_t ncount_213 = __s_210;
    uint64_t __s_214 = __s_211;
    uint64_t __s_215 = __s_212;
    uint64_t nused_216 = __s_214;
    uint64_t j_217 = __s_215;
    if (j_217 < cap) {
      uint8_t blk_218 = 0;
      uint8_t tmp_219 = s[j_217];
      blk_218 = tmp_219;
      uint8_t st_220 = blk_218;
      if (st_220 == 1) {
        uint64_t blk_221 = 0;
        uint64_t tmp_222 = w[(8ULL * j_217)];
        blk_221 = tmp_222;
        uint64_t a0_223 = blk_221;
        uint64_t blk_224 = 0;
        uint64_t tmp_225 = w[((8ULL * j_217) + 1ULL)];
        blk_224 = tmp_225;
        uint64_t a1_226 = blk_224;
        uint64_t blk_227 = 0;
        uint64_t tmp_228 = w[((8ULL * j_217) + 2ULL)];
        blk_227 = tmp_228;
        uint64_t a2_229 = blk_227;
        uint64_t blk_230 = 0;
        uint64_t tmp_231 = w[((8ULL * j_217) + 3ULL)];
        blk_230 = tmp_231;
        uint64_t a3_232 = blk_230;
        uint64_t blk_233 = 0;
        uint64_t tmp_234 = w[((8ULL * j_217) + 4ULL)];
        blk_233 = tmp_234;
        uint64_t a4_235 = blk_233;
        uint64_t blk_236 = 0;
        uint64_t tmp_237 = w[((8ULL * j_217) + 5ULL)];
        blk_236 = tmp_237;
        uint64_t a5_238 = blk_236;
        uint64_t blk_239 = 0;
        uint64_t tmp_240 = w[((8ULL * j_217) + 6ULL)];
        blk_239 = tmp_240;
        uint64_t a6_241 = blk_239;
        uint64_t blk_242 = 0;
        uint64_t tmp_243 = w[((8ULL * j_217) + 7ULL)];
        blk_242 = tmp_243;
        uint64_t a7_244 = blk_242;
        struct ret_vv_place place_245 = vv_place(ncap, nw_204, ns_209, ncount_213, nused_216, a0_223, a1_226, a2_229, a3_232, a4_235, a5_238, a6_241, a7_244);
        uint64_t * r_246 = place_245.f0;
        uint8_t * r_247 = place_245.f1;
        uint64_t r_248 = place_245.f2;
        uint64_t r_249 = place_245.f3;
        uint64_t * nw_250 = r_246;
        uint8_t * ns_251 = r_247;
        uint64_t ncount_252 = r_248;
        uint64_t nused_253 = r_249;
        uint64_t j_254 = (j_217 + 1ULL);
        uint64_t * tmp_255 = nw_250;
        uint8_t * tmp_256 = ns_251;
        uint64_t tmp_257 = ncount_252;
        uint64_t tmp_258 = nused_253;
        uint64_t tmp_259 = j_254;
        st_194 = tmp_255;
        st_195 = tmp_256;
        st_196 = tmp_257;
        st_197 = tmp_258;
        st_198 = tmp_259;
        continue;
      } else {
        uint64_t j_260 = (j_217 + 1ULL);
        uint64_t * tmp_261 = nw_204;
        uint8_t * tmp_262 = ns_209;
        uint64_t tmp_263 = ncount_213;
        uint64_t tmp_264 = nused_216;
        uint64_t tmp_265 = j_260;
        st_194 = tmp_261;
        st_195 = tmp_262;
        st_196 = tmp_263;
        st_197 = tmp_264;
        st_198 = tmp_265;
        continue;
      }
    } else {
      uint64_t * tmp_266 = nw_204;
      uint8_t * tmp_267 = ns_209;
      uint64_t tmp_268 = ncount_213;
      uint64_t tmp_269 = nused_216;
      uint64_t tmp_270 = j_217;
      st_194 = tmp_266;
      st_195 = tmp_267;
      st_196 = tmp_268;
      st_197 = tmp_269;
      st_198 = tmp_270;
      break;
    }
  }
  uint64_t * __s_271 = st_194;
  uint8_t * __s_272 = st_195;
  uint64_t __s_273 = st_196;
  uint64_t __s_274 = st_197;
  uint64_t __s_275 = st_198;
  uint64_t * nw_276 = __s_271;
  uint8_t * __s_277 = __s_272;
  uint64_t __s_278 = __s_273;
  uint64_t __s_279 = __s_274;
  uint64_t __s_280 = __s_275;
  uint8_t * ns_281 = __s_277;
  uint64_t __s_282 = __s_278;
  uint64_t __s_283 = __s_279;
  uint64_t __s_284 = __s_280;
  uint64_t ncount_285 = __s_282;
  return (struct ret_vv_rehash){nw_276, ns_281, ncount_285};
}

struct ret_vv_grow { uint64_t f0; uint64_t * f1; uint8_t * f2; uint64_t f3; uint64_t f4; };
/* grow: contract may abort (signals); consumes (may store into or return): w, s */
static struct ret_vv_grow vv_grow(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t used, uint64_t maxCap) {
  uint64_t ite_286 = 0;
  if ((2ULL * count) > cap) {
    uint64_t tmp_287 = (2ULL * cap);
    ite_286 = tmp_287;
  } else {
    uint64_t tmp_288 = cap;
    ite_286 = tmp_288;
  }
  uint64_t ncap_289 = ite_286;
  if (ncap_289 > maxCap) {
    fputs("eita_ws: table too large\n", stderr); abort();
  } else {
    struct ret_vv_rehash rehash_290 = vv_rehash(cap, w, s, count, ncap_289);
    uint64_t * g_291 = rehash_290.f0;
    uint8_t * g_292 = rehash_290.f1;
    uint64_t g_293 = rehash_290.f2;
    return (struct ret_vv_grow){ncap_289, g_291, g_292, g_293, g_293};
  }
}

struct ret_vv_put { uint64_t f0; uint64_t * f1; uint8_t * f2; uint64_t f3; uint64_t f4; };
/* put: contract may abort (signals); consumes (may store into or return): w, s */
static struct ret_vv_put vv_put(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t used, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3, uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3, uint64_t maxCap) {
  if ((4ULL * (used + 1ULL)) >= (3ULL * cap)) {
    struct ret_vv_grow grow_294 = vv_grow(cap, w, s, count, used, maxCap);
    uint64_t g_295 = grow_294.f0;
    uint64_t * g_296 = grow_294.f1;
    uint8_t * g_297 = grow_294.f2;
    uint64_t g_298 = grow_294.f3;
    uint64_t g_299 = grow_294.f4;
    struct ret_vv_place place_300 = vv_place(g_295, g_296, g_297, g_298, g_299, k0, k1, k2, k3, v0, v1, v2, v3);
    uint64_t * p_301 = place_300.f0;
    uint8_t * p_302 = place_300.f1;
    uint64_t p_303 = place_300.f2;
    uint64_t p_304 = place_300.f3;
    return (struct ret_vv_put){g_295, p_301, p_302, p_303, p_304};
  } else {
    struct ret_vv_place place_305 = vv_place(cap, w, s, count, used, k0, k1, k2, k3, v0, v1, v2, v3);
    uint64_t * p_306 = place_305.f0;
    uint8_t * p_307 = place_305.f1;
    uint64_t p_308 = place_305.f2;
    uint64_t p_309 = place_305.f3;
    return (struct ret_vv_put){cap, p_306, p_307, p_308, p_309};
  }
}

struct ret_vv_lookup { bool f0; uint64_t f1; };
/* lookup: contract forbids failure; consumes no array parameter */
static struct ret_vv_lookup vv_lookup(uint64_t cap, uint64_t *w, uint8_t *s, uint64_t count, uint64_t used, uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3) {
  struct ret_vv_find find_310 = vv_find(cap, w, s, k0, k1, k2, k3);
  return (struct ret_vv_lookup){find_310.f0, find_310.f1};
}

/* dirGrow: contract may abort (signals); consumes no array parameter */
static uint64_t vv_dirGrow(uint64_t n, uint64_t id, uint64_t dmin) {
  if (id < n) {
    return n;
  } else {
    if (id >= 1099511627776ULL) {
      fputs("eita_ws: account id out of range\n", stderr); abort();
    } else {
      uint64_t ite_311 = 0;
      if (n == 0ULL) {
        uint64_t tmp_312 = dmin;
        ite_311 = tmp_312;
      } else {
        uint64_t tmp_313 = (2ULL * n);
        ite_311 = tmp_313;
      }
      uint64_t m_314 = ite_311;
      uint64_t st_315 = 0;
      uint64_t tmp_316 = m_314;
      st_315 = tmp_316;
      for (;;) {
        uint64_t m_317 = st_315;
        if (m_317 <= id) {
          uint64_t m_318 = (2ULL * m_317);
          uint64_t tmp_319 = m_318;
          st_315 = tmp_319;
          continue;
        } else {
          uint64_t tmp_320 = m_317;
          st_315 = tmp_320;
          break;
        }
      }
      uint64_t __s_321 = st_315;
      uint64_t m_322 = __s_321;
      return m_322;
    }
  }
}

struct ret_vv_copyArrs { uint64_t * f0; uint8_t * f1; };
/* copyArrs: contract forbids failure; consumes no array parameter */
static struct ret_vv_copyArrs vv_copyArrs(uint64_t cap, uint64_t *w, uint8_t *s) {
  uint64_t *arr_323 = alloc_zero64((8ULL * cap));
  uint64_t * nw_324 = arr_323;
  uint8_t *arr_325 = alloc_zero8(cap);
  uint8_t * ns_326 = arr_325;
  uint64_t j_327 = 0ULL;
  uint64_t * st_328 = NULL;
  uint8_t * st_329 = NULL;
  uint64_t st_330 = 0;
  uint64_t * tmp_331 = nw_324;
  uint8_t * tmp_332 = ns_326;
  uint64_t tmp_333 = j_327;
  st_328 = tmp_331;
  st_329 = tmp_332;
  st_330 = tmp_333;
  for (;;) {
    uint64_t * nw_334 = st_328;
    uint8_t * __s_335 = st_329;
    uint64_t __s_336 = st_330;
    uint8_t * ns_337 = __s_335;
    uint64_t j_338 = __s_336;
    if (j_338 < cap) {
      uint64_t blk_339 = 0;
      uint64_t tmp_340 = w[(8ULL * j_338)];
      blk_339 = tmp_340;
      uint64_t a0_341 = blk_339;
      uint64_t blk_342 = 0;
      uint64_t tmp_343 = w[((8ULL * j_338) + 1ULL)];
      blk_342 = tmp_343;
      uint64_t a1_344 = blk_342;
      uint64_t blk_345 = 0;
      uint64_t tmp_346 = w[((8ULL * j_338) + 2ULL)];
      blk_345 = tmp_346;
      uint64_t a2_347 = blk_345;
      uint64_t blk_348 = 0;
      uint64_t tmp_349 = w[((8ULL * j_338) + 3ULL)];
      blk_348 = tmp_349;
      uint64_t a3_350 = blk_348;
      uint64_t blk_351 = 0;
      uint64_t tmp_352 = w[((8ULL * j_338) + 4ULL)];
      blk_351 = tmp_352;
      uint64_t a4_353 = blk_351;
      uint64_t blk_354 = 0;
      uint64_t tmp_355 = w[((8ULL * j_338) + 5ULL)];
      blk_354 = tmp_355;
      uint64_t a5_356 = blk_354;
      uint64_t blk_357 = 0;
      uint64_t tmp_358 = w[((8ULL * j_338) + 6ULL)];
      blk_357 = tmp_358;
      uint64_t a6_359 = blk_357;
      uint64_t blk_360 = 0;
      uint64_t tmp_361 = w[((8ULL * j_338) + 7ULL)];
      blk_360 = tmp_361;
      uint64_t a7_362 = blk_360;
      uint64_t * blk_363 = NULL;
      uint64_t * blk_364 = NULL;
      nw_334[(8ULL * j_338)] = a0_341;
      uint64_t * tmp_365 = nw_334;
      blk_364 = tmp_365;
      uint64_t * w_366 = blk_364;
      uint64_t * blk_367 = NULL;
      w_366[((8ULL * j_338) + 1ULL)] = a1_344;
      uint64_t * tmp_368 = w_366;
      blk_367 = tmp_368;
      uint64_t * w_369 = blk_367;
      uint64_t * blk_370 = NULL;
      w_369[((8ULL * j_338) + 2ULL)] = a2_347;
      uint64_t * tmp_371 = w_369;
      blk_370 = tmp_371;
      uint64_t * w_372 = blk_370;
      uint64_t * blk_373 = NULL;
      w_372[((8ULL * j_338) + 3ULL)] = a3_350;
      uint64_t * tmp_374 = w_372;
      blk_373 = tmp_374;
      uint64_t * w_375 = blk_373;
      uint64_t * blk_376 = NULL;
      w_375[((8ULL * j_338) + 4ULL)] = a4_353;
      uint64_t * tmp_377 = w_375;
      blk_376 = tmp_377;
      uint64_t * w_378 = blk_376;
      uint64_t * blk_379 = NULL;
      w_378[((8ULL * j_338) + 5ULL)] = a5_356;
      uint64_t * tmp_380 = w_378;
      blk_379 = tmp_380;
      uint64_t * w_381 = blk_379;
      uint64_t * blk_382 = NULL;
      w_381[((8ULL * j_338) + 6ULL)] = a6_359;
      uint64_t * tmp_383 = w_381;
      blk_382 = tmp_383;
      uint64_t * w_384 = blk_382;
      w_384[((8ULL * j_338) + 7ULL)] = a7_362;
      uint64_t * tmp_385 = w_384;
      blk_363 = tmp_385;
      uint64_t * __x_386 = blk_363;
      uint64_t * nw_387 = __x_386;
      uint8_t blk_388 = 0;
      uint8_t tmp_389 = s[j_338];
      blk_388 = tmp_389;
      uint8_t b_390 = blk_388;
      uint8_t * blk_391 = NULL;
      ns_337[j_338] = b_390;
      uint8_t * tmp_392 = ns_337;
      blk_391 = tmp_392;
      uint8_t * __x_393 = blk_391;
      uint8_t * ns_394 = __x_393;
      uint64_t j_395 = (j_338 + 1ULL);
      uint64_t * tmp_396 = nw_387;
      uint8_t * tmp_397 = ns_394;
      uint64_t tmp_398 = j_395;
      st_328 = tmp_396;
      st_329 = tmp_397;
      st_330 = tmp_398;
      continue;
    } else {
      uint64_t * tmp_399 = nw_334;
      uint8_t * tmp_400 = ns_337;
      uint64_t tmp_401 = j_338;
      st_328 = tmp_399;
      st_329 = tmp_400;
      st_330 = tmp_401;
      break;
    }
  }
  uint64_t * __s_402 = st_328;
  uint8_t * __s_403 = st_329;
  uint64_t __s_404 = st_330;
  uint64_t * nw_405 = __s_402;
  uint8_t * __s_406 = __s_403;
  uint64_t __s_407 = __s_404;
  uint8_t * ns_408 = __s_406;
  return (struct ret_vv_copyArrs){nw_405, ns_408};
}

struct ret_vv_fresh { uint64_t f0; uint64_t * f1; uint8_t * f2; };
/* fresh: contract forbids failure; consumes no array parameter */
static struct ret_vv_fresh vv_fresh() {
  struct ret_vv_create create_409 = vv_create(4ULL);
  uint64_t * c_410 = create_409.f0;
  uint8_t * c_411 = create_409.f1;
  return (struct ret_vv_fresh){4ULL, c_410, c_411};
}

#pragma GCC diagnostic pop
