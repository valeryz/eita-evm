;;;; native/ffi.lisp — the FFI bindings of libeita (handlers, precompiles, per-tx state tables) and libc.

(in-package #:eita.native)

(defcfun ("eita_run" eita-run) :void (state :pointer))
;; Valid-JUMPDEST map of LEN code bytes into OUT: 1 at every 0x5b that is not PUSH
;; data (EELS get_valid_jump_destinations). JUMP/JUMPI read it via EvmState #136.
(defcfun ("eita_jumpdest_map" %jumpdest-map) :void
  (code :pointer) (len :uint64) (out :pointer))
;; The CALL-family gas plan, emitted from the Lean spec
;; (`Evm.Berlin.Vm.Effect.callGasPlan` via `Evm.CL.ARM64.CallGas`).
;; out = {charge, forward, stipend}; flags: bit0 isCold, bit1
;; chargesValue, bit2 chargesNewAccount. Audited differentially by
;; tests/audit-call-gas.lisp.
(defcfun ("eita_call_gas" %call-gas) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))
;; Pre-Berlin variants of the same plan, emitted from the same spec:
;; frontier (pre-EIP-150: base 40, NO forwarding cap — the host OOGs
;; the parent when charge+forward exceeds its pool) and tangerine
;; (EIP-150: base 700, 63/64 cap, no cold/delegated terms).
(defcfun ("eita_call_gas_frontier" %call-gas-frontier) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))
(defcfun ("eita_call_gas_tangerine" %call-gas-tangerine) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))
;; The per-fork SSTORE gas/refund routines (Evm.CL.ARM64.SstoreGas) are bound, and
;; dispatched on *fork-ord*, by the Lean-emitted spec-sstore-gas-dispatch
;; (src/generated/host.lisp; Evm.CL.EffectIR.SstoreSched). Uniform ABI: out[2] =
;; {cost, newRefund}; orig/cur/new point at u256 values; cold is 0/1. Precondition: refund < 2^63.
;; Repoint the native dispatch table (emitted per-fork from the Lean
;; metadata) — defaults to Cancun when never called.
(defcfun ("eita_set_fork" %set-fork) :void (ord :uint64))

;; The chunk-dispatch trampoline, emitted from the Lean spec
;; (`IR.executeProgram` via `Evm.CL.ARM64.RunProgram`). Returns
;; 0 = halted, 1 = manifest miss (spec: .invalidJumpDest),
;; 2 = fuel exhausted (spec: .outOfGas).
(defcfun ("eita_execute_program" %run-program) :uint64
  (state :pointer) (entries :pointer) (run-chunk :pointer) (fuel :uint64))
(defcfun ("eita_keccak256" eita-keccak256) :void
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("sha256_hash" %sha256-hash) :void
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("ripemd160_hash" %ripemd160-hash) :void
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_ecrecover" %eita-ecrecover) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bn254_add" %eita-bn254-add) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bn254_mul" %eita-bn254-mul) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bn254_pairing" %eita-bn254-pairing) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_modexp" %eita-modexp) :int
  (input :pointer) (inlen :uint64) (output :pointer) (out-len :pointer))
(defcfun ("eita_blake2f" %eita-blake2f) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_p256_verify_raw" %eita-p256-verify) :int
  (input :pointer))
;; EIP-4844 point evaluation (0x0a), Cancun+: 1 with the 64-byte output, or 0 on any
;; KZGProofError (lean/c/point_evaluation.c, EELS point_evaluation.py), which fails the
;; call and consumes the whole forwarded pool.
(defcfun ("eita_point_evaluation" %eita-point-evaluation) :int
  (input :pointer) (inlen :uint64) (output :pointer))
;; EIP-2537 BLS12-381 (0x0b..0x11), Prague+. Each returns 1 with OUTPUT filled, or 0
;; for an invalid input — which per the EIP fails the precompile and consumes the whole
;; forwarded pool. Length and encoding validation lives in C (lean/c/bls12381.cpp);
;; the gas is derived from Evm.CL.GasEmit like every other precompile.
(defcfun ("eita_bls_g1add" %eita-bls-g1add) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_g1msm" %eita-bls-g1msm) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_g2add" %eita-bls-g2add) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_g2msm" %eita-bls-g2msm) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_pairing" %eita-bls-pairing) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_map_fp_to_g1" %eita-bls-map-fp-to-g1) :int
  (input :pointer) (inlen :uint64) (output :pointer))
(defcfun ("eita_bls_map_fp2_to_g2" %eita-bls-map-fp2-to-g2) :int
  (input :pointer) (inlen :uint64) (output :pointer))

;;; Inlined: one C call each on the SLOAD/SSTORE/CALL path, where the out-of-line Lisp
;;; wrapper (a full call before the foreign call) was ~1 % of the replay thread.
(declaim (inline %ts-access-addr %ts-access-slot %ts-refund-add %ts-created-insert %ts-created-p
                 %ts-orig-record %ts-orig-get))
;;; Native per-tx state tables (c/tx_state.h). One TxState + one root
;;; TxArena, shared by every frame in a tx; see ensure-arenas.
(defcfun ("eita_ts_reset" %ts-reset) :void (ts :pointer))
(defcfun ("eita_ts_access_addr" %ts-access-addr) :uint64
  (ts :pointer) (ar :pointer) (addr :pointer))
(defcfun ("eita_ts_access_addrs" %ts-access-addrs) :void
  (ts :pointer) (ar :pointer) (addrs :pointer) (n :uint64))
(defcfun ("eita_ts_access_slot" %ts-access-slot) :uint64
  (ts :pointer) (ar :pointer) (addr :pointer) (slot :pointer))
;; (eita_ts_tload/tstore have no Lisp binding: the TLOAD/TSTORE
;;  handlers call them natively via arena->tx_state.)
(defcfun ("eita_ts_refund_add" %ts-refund-add) :void
  (ts :pointer) (ar :pointer) (delta :int64))
(defcfun ("eita_ts_created_insert" %ts-created-insert) :uint64
  (ts :pointer) (ar :pointer) (addr :pointer))
(defcfun ("eita_ts_created_p" %ts-created-p) :uint64
  (ts :pointer) (addr :pointer))
(defcfun ("eita_ts_orig_record" %ts-orig-record) :void
  (ts :pointer) (addr :pointer) (slot :pointer) (cur :pointer))
(defcfun ("eita_ts_orig_get" %ts-orig-get) :void
  (ts :pointer) (addr :pointer) (slot :pointer) (cur :pointer) (out :pointer))
(defcfun ("eita_ts_revert" %ts-revert) :void
  (ts :pointer) (ar :pointer) (target :uint64))

;;; libc: anonymous mappings (the JIT code arena, guard-paged arenas).
(defcfun ("mmap" %mmap) :pointer
  (addr :pointer) (len :size) (prot :int) (flags :int)
  (fd :int) (offset :int64))
(defcfun ("mprotect" %mprotect) :int
  (addr :pointer) (len :size) (prot :int))

;;; The world's storage slots (c/world_slots.h): one ws_world per account table, keys and
;;; values as four limbs (least significant first). Inlined: on the SLOAD/SSTORE path.
(declaim (inline %ws-get %ws-put %ws-remove))
(defcfun ("eita_ws_new" %ws-new) :pointer)
(defcfun ("eita_ws_free" %ws-free) :void (w :pointer))
(defcfun ("eita_ws_get" %ws-get) :pointer
  (w :pointer) (id :uint64) (k0 :uint64) (k1 :uint64) (k2 :uint64) (k3 :uint64))
(defcfun ("eita_ws_put" %ws-put) :void
  (w :pointer) (id :uint64) (k0 :uint64) (k1 :uint64) (k2 :uint64) (k3 :uint64)
  (v0 :uint64) (v1 :uint64) (v2 :uint64) (v3 :uint64))
(defcfun ("eita_ws_remove" %ws-remove) :void
  (w :pointer) (id :uint64) (k0 :uint64) (k1 :uint64) (k2 :uint64) (k3 :uint64))
(defcfun ("eita_ws_drop" %ws-drop) :void (w :pointer) (id :uint64))
(defcfun ("eita_ws_copy" %ws-copy) :void (dst :pointer) (id :uint64) (src :pointer))
;; The native SLOAD/SSTORE path (c/storage_host.h): the Lisp path records a frame account's id;
;; a revert restores the SSTORE entries it can natively first.
(defcfun ("eita_sh_revert_storage" %sh-revert-storage) :void (arena :pointer) (target :uint64))
(defcfun ("eita_sh_cache_put" %sh-cache-put) :void (a0 :uint64) (a1 :uint64) (a2 :uint64) (id :uint64))
