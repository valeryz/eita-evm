;;;; test-return-width.lisp — RETURN/REVERT lengths are u256, not u64.
;;;;
;;;; `memExpandIfLen` decided "zero length, no expansion" from the LENGTH'S LOW
;;;; LIMB (`cbz x10, 4f`) and then computed the end as `off.l0 + len.l0` with no
;;;; high-limb fold and no carry check. So a RETURN of 2^64 bytes (low limb 0)
;;;; skipped the expansion entirely and returned EMPTY with gas to spare, where
;;;; EELS charges an unaffordable expansion and the frame OOGs.
;;;;
;;;; This is #260 in a different op: that was the CALL family reading in/out
;;;; offsets and lengths as u64; the fix there introduced `memRangeInstrs`,
;;;; whose full-u256 semantics are proved against EELS in
;;;; lean/Evm/CL/MemExpandSpec.lean. RETURN/REVERT simply never got routed
;;;; through it — the gadget's own docstring claimed they were.
;;;;
;;;; Measured on the pre-fix build: RETURN with length 2^64 halted with 999 994
;;;; of 1 000 000 gas left. After: gas 0, i.e. the exceptional halt EELS gives.
;;;;
;;;; Proofs: lean/Evm/CL/MemExpandSpec.lean (`memRangeEnd_*`, `memexp_unaffordable`).
;;;; Run: (eita.test:run-all :only '("return-width")), or (asdf:test-system "eita") for all suites.

(defpackage #:eita.test.return-width (:use #:cl #:cffi))
(in-package :eita.test.return-width)

(defcfun ("eita_run" eita-run) :void (state :pointer))

(defparameter *fails* 0)
(defparameter *start-gas* 1000000)

(defun run-program (bytecode)
  (let* ((state   (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (stack   (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (mem     (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (clen    (length bytecode))
         (code    (foreign-alloc :uint8 :count (+ clen 64) :initial-element 0))
         (arena   (foreign-alloc :uint8 :count 64 :initial-element 0))
         (journal (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (cb      (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (loop for b in bytecode for i from 0 do (setf (mem-aref code :uint8 i) b))
    (setf (mem-ref state :uint64 8)   *start-gas*
          (mem-ref state :pointer 32) stack
          (mem-ref state :pointer 40) mem
          (mem-ref state :uint64 56)  (* 64 1024)
          (mem-ref state :pointer 64) code
          (mem-ref state :uint64 72)  clen
          (mem-ref arena :pointer 16) journal
          (mem-ref state :pointer 496) cb
          (mem-ref state :pointer 504) arena)
    (eita-run state)
    (let ((r (list :gas (mem-ref state :uint64 8)
                   :halted (not (zerop (mem-ref state :uint8 128)))
                   :out-size (mem-ref state :uint64 120))))
      (mapc #'foreign-free (list state stack mem code arena journal cb))
      r)))

(defun chk (label got want)
  (if (equal got want)
      (format t "  ok    ~A: ~S~%" label got)
      (progn (incf *fails*) (format t "  FAIL  ~A: got ~S, want ~S~%" label got want))))

(defun oog-p (r) (and (getf r :halted) (zerop (getf r :gas))))

;; PUSH9 <8 bytes> builds a length whose high limb is set; PUSH1 0 is the offset.
;; RETURN pops offset then length, so the length is pushed first.
(defun ret-program (len-bytes op) (append (cons #x68 len-bytes) '(#x60 #x00) (list op)))

(format t "~%=== RETURN/REVERT length width (native handlers) ===~%~%")

(format t "RETURN length 2^64 (low limb 0)~%")
(let ((r (run-program (ret-program '(#x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00) #xf3))))
  (chk "exceptional halt (OOG)" (oog-p r) t))

(format t "~%REVERT length 2^64 (low limb 0)~%")
(let ((r (run-program (ret-program '(#x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00) #xfd))))
  (chk "exceptional halt (OOG)" (oog-p r) t))

;; A length whose low limb is nonzero AND high limb set — the end is ≥ 2^64 too.
(format t "~%RETURN length 2^64 + 32~%")
(let ((r (run-program (ret-program '(#x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x20) #xf3))))
  (chk "exceptional halt (OOG)" (oog-p r) t))

;; Controls: the same shape with a narrow length must still work, and cost the
;; same as it always did — the fix must not charge anything new on the happy path.
(format t "~%control: RETURN length 32, offset 0~%")
(let ((r (run-program '(#x60 #x20 #x60 #x00 #xf3))))
  (chk "not OOG"   (oog-p r) nil)
  (chk "halted"    (getf r :halted) t)
  (chk "out size"  (getf r :out-size) 32)
  ;; two PUSH1 = 6, plus one word of memory expansion = 3
  (chk "gas used"  (- *start-gas* (getf r :gas)) 9))

(format t "~%control: RETURN length 0 charges no expansion~%")
(let ((r (run-program '(#x5f #x60 #x00 #xf3))))        ; PUSH0 len, PUSH1 0 off, RETURN
  (chk "not OOG"  (oog-p r) nil)
  (chk "out size" (getf r :out-size) 0)
  ;; PUSH0 = 2, PUSH1 = 3, no expansion
  (chk "gas used" (- *start-gas* (getf r :gas)) 5))

;; …and a zero length must not OOG even with a WIDE offset: with no bytes to
;; return there is no range, which is the `some 0` case of memRangeEnd.
(format t "~%control: length 0 with a wide offset still returns~%")
(let ((r (run-program (append '(#x5f)                                        ; len 0
                              '(#x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00) ; off 2^64
                              '(#xf3)))))
  (chk "not OOG" (oog-p r) nil)
  (chk "halted"  (getf r :halted) t))

(format t "~&~%~A~%" (if (zerop *fails*) "ALL RETURN-WIDTH CHECKS PASS"
                         (format nil "~D FAILURE(S)" *fails*)))
(finish-output)
(eita.test:finish :code (if (zerop *fails*) 0 1))
