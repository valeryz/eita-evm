;;;; test-jump-truncation.lisp — JUMP/JUMPI destinations are u256, not u64.
;;;;
;;;; The native handlers validated a jump destination by comparing the LOW LIMB
;;;; only (`cmp x6, x14` against code_size), so a destination of 2^64 + k whose
;;;; low limb landed on a real JUMPDEST jumped to k — where the spec
;;;; (`Frontier…jump`: `dest.toNat`, then `isValidJumpDest`) halts exceptionally,
;;;; because dest.toNat ≥ 2^64 ≥ code_size.
;;;;
;;;; Why ethereum/tests did not catch it: stMemoryStressTest/JUMP_Bounds2 and
;;;; JUMPI_Bounds jump to 0xffffffff, 2^64-1, 2^128-1, 2^176-1 — every one of
;;;; which has a huge LOW limb too, so the truncated compare rejected them for
;;;; the right reason by accident. The shape that breaks it is a SMALL low limb
;;;; with a nonzero high limb, which is what this file tests.
;;;;
;;;; Proofs: lean/Evm/CL/JumpDest.lean (`jump_wide_traps`, `jumpi_taken_wide_traps`,
;;;; `truncating_form_is_wrong`). This is the executable half.
;;;;
;;;; Run: (eita.test:run-all :only '("jump-truncation")), or (asdf:test-system "eita") for all suites.

(defpackage #:eita.test.jump-truncation (:use #:cl #:cffi))
(in-package :eita.test.jump-truncation)

;; EITA_LIB overrides the library (a worktree's side build), as for the fixture runner.
(defcfun ("eita_run" eita-run) :void (state :pointer))
(defcfun ("eita_jumpdest_map" %jumpdest-map) :void
  (code :pointer) (len :uint64) (out :pointer))

(defparameter *fails* 0)

(defun run-program (bytecode &key (initial-gas 1000000))
  "Run BYTECODE through the production threaded driver; return a plist. The frame's
   code buffer has the replay's layout: code, 64-byte PUSH pad, valid-JUMPDEST map."
  (let* ((state   (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (stack   (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (mem     (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (clen    (length bytecode))
         (code    (foreign-alloc :uint8 :count (+ clen 64 clen) :initial-element 0))
         (arena   (foreign-alloc :uint8 :count 64 :initial-element 0))
         (journal (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (cb      (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (loop for b in bytecode for i from 0 do (setf (mem-aref code :uint8 i) b))
    (%jumpdest-map code clen (inc-pointer code (+ clen 64)))
    (setf (mem-ref state :uint64 8)   initial-gas
          (mem-ref state :pointer 32) stack
          (mem-ref state :pointer 40) mem
          (mem-ref state :uint64 56)  (* 64 1024)
          (mem-ref state :pointer 64) code
          (mem-ref state :uint64 72)  clen
          (mem-ref state :pointer 136) (inc-pointer code (+ clen 64))
          (mem-ref arena :pointer 16) journal
          (mem-ref state :pointer 496) cb
          (mem-ref state :pointer 504) arena)
    (eita-run state)
    (let ((r (list :sp (mem-ref state :uint64 16)
                   :gas (mem-ref state :uint64 8)
                   :pc (mem-ref state :uint64 0)
                   :halted (not (zerop (mem-ref state :uint8 128))))))
      (mapc #'foreign-free (list state stack mem code arena journal cb))
      r)))

(defun chk (label got want)
  (if (equal got want)
      (format t "  ok    ~A: ~S~%" label got)
      (progn (incf *fails*)
             (format t "  FAIL  ~A: got ~S, want ~S~%" label got want))))

;;; An exceptional halt (invalid jump) burns the whole frame's gas and leaves
;;; the frame halted — that is how `_eita_invalid_jump` exits.
(defun exceptional-p (r) (and (getf r :halted) (zerop (getf r :gas))))

(format t "~%=== JUMP/JUMPI destination width (native handlers) ===~%~%")

;;; Baseline: an in-range jump to a real JUMPDEST works.
;;;   0: PUSH1 4   2: JUMP   3: INVALID   4: JUMPDEST   5: STOP
(format t "in-range JUMP to a JUMPDEST~%")
(let ((r (run-program '(#x60 #x04 #x56 #xfe #x5b #x00))))
  (chk "halted"      (getf r :halted) t)
  (chk "not exceptional (gas remains)" (plusp (getf r :gas)) t)
  (chk "pc after STOP" (getf r :pc) 5))

;;; THE CASE: dest = 2^64 + 12, and offset 12 IS a JUMPDEST in this very
;;; program — so truncating to the low limb jumps there and runs on, while the
;;; spec halts. The low limb must point at REAL code, not into the PUSH9
;;; immediate (offsets 1-9), or the test proves nothing: a first version of this
;;; file used low limb 4, which lands inside the immediate and is invalid for
;;; the ordinary reason. It passed against the UNFIXED asm.
;;;   0: PUSH9 0x01_00000000_0000000c   10: JUMP   11: INVALID   12: JUMPDEST   13: STOP
(format t "~%JUMP to 2^64+12 (low limb 12 IS a JUMPDEST here)~%")
(let ((r (run-program (append '(#x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x0c)
                              '(#x56 #xfe #x5b #x00)))))
  (chk "exceptional halt" (exceptional-p r) t))

;;; The control that makes the case above meaningful: the SAME program with the
;;; destination narrowed to just 12 runs to completion. So the only difference
;;; is the high limb, which is the whole point.
(format t "~%control: the same program with dest 12 (narrow) succeeds~%")
(let ((r (run-program (append '(#x68 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x0c)
                              '(#x56 #xfe #x5b #x00)))))
  (chk "narrow jump to 12 succeeds" (not (exceptional-p r)) t))

;;; JUMPI with a nonzero condition and a wide destination: same rule.
;;;   PUSH1 1 (cond)  PUSH9 2^64+6 (dest)  JUMPI  INVALID  JUMPDEST  STOP
;;; Stack order: JUMPI pops dest then cond, so push cond first.
;;;   0-1: PUSH1 1 (cond)   2-11: PUSH9 2^64+14 (dest)   12: JUMPI
;;;   13: INVALID   14: JUMPDEST   15: STOP     — low limb 14 IS a JUMPDEST.
(format t "~%JUMPI to 2^64+14, condition 1 (low limb 14 IS a JUMPDEST here)~%")
(let ((r (run-program (append '(#x60 #x01)
                              '(#x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x0e)
                              '(#x57 #xfe #x5b #x00)))))
  (chk "exceptional halt" (exceptional-p r) t))

(format t "~%control: the same JUMPI with dest 14 (narrow) succeeds~%")
(let ((r (run-program (append '(#x60 #x01)
                              '(#x68 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x0e)
                              '(#x57 #xfe #x5b #x00)))))
  (chk "narrow JUMPI to 14 succeeds" (not (exceptional-p r)) t))

;;; JUMPI with a ZERO condition must NOT trap, even with a wide destination —
;;; the branch is not taken, so the destination is never validated.
(format t "~%JUMPI to 2^64+14 with condition 0 falls through~%")
(let ((r (run-program (append '(#x5f)                                   ; PUSH0 cond
                              '(#x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x0e)
                              '(#x57 #x00)))))                          ; JUMPI, STOP
  (chk "not exceptional" (exceptional-p r) nil)
  (chk "halted"          (getf r :halted) t))

;;; The condition is folded over all four limbs: a condition whose low limb is
;;; zero but whose high limb is not must TAKE the branch (this half the asm
;;; always had right; pinned so it stays right).
(format t "~%JUMPI with condition 2^64 (low limb 0) takes the branch~%")
;; offsets: 0-9 PUSH9, 10-11 PUSH1, 12 JUMPI, 13 INVALID, 14 JUMPDEST, 15 STOP
(let ((r (run-program (append '(#x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00) ; cond 2^64
                              '(#x60 #x0e)                                          ; dest 14
                              '(#x57 #xfe #x5b #x00)))))                            ; JUMPI, INVALID, JUMPDEST, STOP
  (chk "not exceptional (branch taken to a JUMPDEST)" (exceptional-p r) nil)
  (chk "halted" (getf r :halted) t))

;;; ---------------------------------------------------------------------------
;;; The second class: a JUMPDEST BYTE inside PUSH data is not a destination.
;;; EELS get_valid_jump_destinations skips PUSH immediates; the handlers used to
;;; test `code[dest] = 0x5b` and accepted it. Mainnet 5,800,596 tx 117
;;; (0x3666640316df11865abd1352f4c0b4c5126f8ac1d858ef2a0c6e744a4865bca2) is a
;;; creation whose init code is exactly this program: geth halts with all gas
;;; ("invalid jump destination"); the byte test jumped to 1 and ran the PUSH9
;;; immediate as code (PUSH1 0xaa, PUSH1 0, PUSH1 0, LOG1, STOP: 54,466 gas).
;;; Lean: Evm.CL.JumpDest `byte_test_is_wrong`, `tx117_has_no_jumpdests`.
;;;   0: PUSH9 0x5b60aa60006000a100   10: PUSH1 1   12: JUMP      — offset 1 is 0x5b, PUSH data
(format t "~%JUMP into PUSH data (the 5,800,596 tx 117 init code)~%")
(let ((r (run-program '(#x68 #x5b #x60 #xaa #x60 #x00 #x60 #x00 #xa1 #x00 #x60 #x01 #x56))))
  (chk "exceptional halt" (exceptional-p r) t))

;;; Control: the same bytes after the PUSH9 as real code — JUMPDEST at 10 is valid.
;;;   0: PUSH1 10   2: JUMP   3..9: INVALID×7   10: JUMPDEST   11: STOP
(format t "~%control: JUMP to a JUMPDEST that is real code succeeds~%")
(let ((r (run-program '(#x60 #x0a #x56 #xfe #xfe #xfe #xfe #xfe #xfe #xfe #x5b #x00))))
  (chk "not exceptional" (exceptional-p r) nil)
  (chk "pc after STOP" (getf r :pc) 11))

;;; JUMPI with a nonzero condition into PUSH data: same rule (jumpi.json d14).
;;;   0: PUSH1 1 (cond)   2: PUSH1 5 (dest)   4: JUMPI   5: PUSH1 0x5b   7: STOP
;;; Offset 6 holds the 0x5b, inside PUSH1's immediate — dest 6 is invalid.
(format t "~%JUMPI into PUSH data, condition 1~%")
(let ((r (run-program '(#x60 #x01 #x60 #x06 #x57 #x60 #x5b #x00))))
  (chk "exceptional halt" (exceptional-p r) t))

;;; A PUSH whose immediate runs past the end of the code still hides nothing that
;;; follows (there is nothing), and the scan must stop: PUSH32 at offset 1 with 3
;;; bytes of code left. dest 3 (a 0x5b inside the truncated immediate) is invalid.
(format t "~%JUMP into a truncated PUSH32 immediate at the end of the code~%")
(let ((r (run-program '(#x60 #x03 #x56 #x7f #x5b #x00))))
  (chk "exceptional halt" (exceptional-p r) t))

(format t "~&~%~A~%" (if (zerop *fails*) "ALL JUMP-WIDTH CHECKS PASS"
                         (format nil "~D FAILURE(S)" *fails*)))
(finish-output)
(eita.test:finish :code (if (zerop *fails*) 0 1))
