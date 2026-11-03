;;;; test-call-memexp-oog.lisp — regression for #260.
;;;; A CALL whose in_len/out_len has any HIGH u256 limb set means the memory
;;;; expansion end is >= 2^64 ⇒ unaffordable ⇒ OOG (consume all gas), exactly
;;;; as mainnet does (InvalidOperandOOG). Before the fix .callFamilyCore read
;;;; only limb0, so argsLen=2^64 (low limb 0) wrapped to a 0-length CALL and
;;;; proceeded cheaply (block 4466928 relay 0x39dc3f7a: we succeeded @46264 gas
;;;; where mainnet burned all 250000 and reverted).

(defpackage #:eita.test.call-memexp-oog (:use #:cl #:cffi))
(in-package :eita.test.call-memexp-oog)

(defcfun ("eita_run" eita-run) :void (state :pointer))

(defparameter *cb-called* nil)
(defcallback cb-call :int ((ctx :pointer) (params :pointer) (result :pointer))
  (declare (ignore ctx params))
  (setf *cb-called* t)
  ;; report a trivially-successful empty sub-call
  (setf (mem-ref result :int 0) 1)
  (setf (mem-ref result :pointer 8) (null-pointer))
  (setf (mem-ref result :uint64 16) 0)
  (setf (mem-ref result :uint64 24) 0)
  0)

(defun run-outer (bytecode &optional (gas 1000000))
  (let* ((state (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (stack (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (mem   (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (clen  (length bytecode))
         (code  (foreign-alloc :uint8 :count (+ clen 64) :initial-element 0))
         (arena (foreign-alloc :uint8 :count 64 :initial-element 0))
         (journ (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (cb    (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (setf (mem-aref cb :pointer 11) (callback cb-call))
    (loop for b in bytecode for i from 0 do (setf (mem-aref code :uint8 i) b))
    (setf (mem-ref state :uint64 8) gas)
    (setf (mem-ref state :pointer 32) stack)
    (setf (mem-ref state :pointer 40) mem)
    (setf (mem-ref state :uint64 56) (* 64 1024))
    (setf (mem-ref state :pointer 64) code)
    (setf (mem-ref state :uint64 72) clen)
    (setf (mem-ref arena :pointer 16) journ)
    (setf (mem-ref state :pointer 496) cb)
    (setf (mem-ref state :pointer 504) arena)
    (setf *cb-called* nil)
    (eita-run state)
    (prog1
        (list :sp (mem-ref state :uint64 16)
              :gas-left (mem-ref state :uint64 8)
              :halted (not (zerop (mem-ref state :uint8 128)))
              :reverted (not (zerop (mem-ref state :uint8 129)))
              :cb-called *cb-called*)
      (foreign-free state) (foreign-free stack) (foreign-free mem)
      (foreign-free code) (foreign-free arena) (foreign-free journ) (foreign-free cb))))

(defvar *fails* 0)
(defun expect (label actual expected)
  (if (equal actual expected)
      (format t "  PASS  ~A: ~A~%" label actual)
      (progn (incf *fails*) (format t "  FAIL  ~A: got ~A, expected ~A~%" label actual expected))))

;; --- Control: normal CALL (in_len=0) → cb invoked, success, gas NOT all gone.
(format t "~%Control: CALL in_len=0 (well-formed) → cb runs~%")
(let ((r (run-outer '(#x60 #x00 #x60 #x00 #x60 #x00 #x60 #x00 #x60 #x00 #x60 #x42
                      #x61 #xff #xff #xf1 #x00))))
  (expect "cb-called" (getf r :cb-called) t)
  (expect "not all gas burned" (> (getf r :gas-left) 0) t))

;; --- Bug case: CALL in_len = 2^64 (PUSH9 01 00*8), in_off = 0xb4.
;; High limb set ⇒ memexp end >= 2^64 ⇒ OOG before cb. (relay 0x39dc3f7a shape)
(format t "~%#260: CALL in_len=2^64 (high limb set) → OOG, cb must NOT run~%")
(let ((r (run-outer '(#x60 #x00            ; out_len
                      #x60 #x00            ; out_off
                      #x68 #x01 #x00 #x00 #x00 #x00 #x00 #x00 #x00 #x00 ; PUSH9 in_len=2^64
                      #x60 #xb4            ; in_off=180
                      #x60 #x00            ; value
                      #x60 #x42            ; addr
                      #x61 #xff #xff       ; gas
                      #xf1 #x00))))        ; CALL ; STOP
  (expect "halted" (getf r :halted) t)
  (expect "reverted (OOG)" (getf r :reverted) t)
  (expect "all gas consumed" (getf r :gas-left) 0)
  (expect "cb NOT called (OOG before call)" (getf r :cb-called) nil))

(if (zerop *fails*)
    (format t "~%ALL PASS~%")
    (progn (format t "~%~D FAIL~%" *fails*) (eita.test:finish :code 1)))
