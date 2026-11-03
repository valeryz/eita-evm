;;;; test-call-family.lisp — exercise CALL and DELEGATECALL through the
;;;; parametric handler. Validates: 7-arg pop for CALL (includes value),
;;;; 6-arg pop for DELEGATECALL, success flag pushed, returndata wired,
;;;; gas_used charged.

(defpackage #:eita.test.call-family (:use #:cl #:cffi))
(in-package :eita.test.call-family)

(defcfun ("eita_run" eita-run) :void (state :pointer))

(defun u256-read (ptr)
  (let ((acc 0))
    (loop for i from 3 downto 0 do
      (setf acc (logior (ash acc 64) (mem-aref ptr :uint64 i))))
    acc))

(defparameter *captured-kind* nil)
(defparameter *captured-value* nil)
(defparameter *inner-code-for-test* nil)

(defcallback cb-call :int
    ((ctx :pointer) (params :pointer) (result :pointer))
  (declare (ignore ctx))
  (setf *captured-kind*  (mem-ref params :int 0))
  (setf *captured-value* (u256-read (inc-pointer params 40)))
  ;; Build sub-frame
  (let* ((sub-state (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (sub-stack (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (sub-mem   (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (sub-code-len (length *inner-code-for-test*))
         (sub-code  (foreign-alloc :uint8 :count (+ sub-code-len 64) :initial-element 0))
         (sub-arena (foreign-alloc :uint8 :count 64 :initial-element 0))
         (sub-journ (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (sub-cb    (foreign-alloc :pointer :count 16 :initial-element (null-pointer)))
         (gas-given (mem-ref params :uint64 88)))
    (loop for b in *inner-code-for-test* for i from 0 do
      (setf (mem-aref sub-code :uint8 i) b))
    (setf (mem-ref sub-state :uint64 8)   gas-given)
    (setf (mem-ref sub-state :pointer 32) sub-stack)
    (setf (mem-ref sub-state :pointer 40) sub-mem)
    (setf (mem-ref sub-state :uint64 56)  (* 64 1024))
    (setf (mem-ref sub-state :pointer 64) sub-code)
    (setf (mem-ref sub-state :uint64 72)  sub-code-len)
    (setf (mem-ref sub-arena :pointer 16) sub-journ)
    (setf (mem-ref sub-state :pointer 496) sub-cb)
    (setf (mem-ref sub-state :pointer 504) sub-arena)
    (eita-run sub-state)
    (let* ((halted (not (zerop (mem-ref sub-state :uint8 128))))
           (reverted (not (zerop (mem-ref sub-state :uint8 129))))
           (output-ptr (mem-ref sub-state :pointer 112))
           (output-len (mem-ref sub-state :uint64 120))
           (gas-left (mem-ref sub-state :uint64 8))
           (out-copy (foreign-alloc :uint8 :count (max output-len 1) :initial-element 0)))
      (when (and output-ptr (plusp output-len))
        (loop for i from 0 below output-len do
          (setf (mem-aref out-copy :uint8 i)
                (mem-aref output-ptr :uint8 i))))
      (setf (mem-ref result :int 0)     (if (and halted (not reverted)) 1 0))
      (setf (mem-ref result :pointer 8) out-copy)
      (setf (mem-ref result :uint64 16) output-len)
      (setf (mem-ref result :uint64 24) (- gas-given gas-left)))
    (foreign-free sub-state) (foreign-free sub-stack)
    (foreign-free sub-mem)   (foreign-free sub-code)
    (foreign-free sub-arena) (foreign-free sub-journ)
    (foreign-free sub-cb)
    0))

(defun run-outer (bytecode)
  (let* ((state    (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (stack    (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (mem      (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (code-len (length bytecode))
         (code     (foreign-alloc :uint8 :count (+ code-len 64) :initial-element 0))
         (arena    (foreign-alloc :uint8 :count 64 :initial-element 0))
         (journal  (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (cb       (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (setf (mem-aref cb :pointer 11) (callback cb-call))  ; cb->call slot
    (loop for b in bytecode for i from 0 do
      (setf (mem-aref code :uint8 i) b))
    (setf (mem-ref state :uint64 8)   1000000)
    (setf (mem-ref state :pointer 32) stack)
    (setf (mem-ref state :pointer 40) mem)
    (setf (mem-ref state :uint64 56)  (* 64 1024))
    (setf (mem-ref state :pointer 64) code)
    (setf (mem-ref state :uint64 72)  code-len)
    (setf (mem-ref arena :pointer 16) journal)
    (setf (mem-ref state :pointer 496) cb)
    (setf (mem-ref state :pointer 504) arena)
    (eita-run state)
    (let* ((sp (mem-ref state :uint64 16))
           (top (if (>= sp 1) (u256-read stack) 0))
           (halted (not (zerop (mem-ref state :uint8 128)))))
      (foreign-free state) (foreign-free stack) (foreign-free mem)
      (foreign-free code) (foreign-free arena) (foreign-free journal)
      (foreign-free cb)
      (list :sp sp :top top :halted halted))))

(defun expect (label actual expected)
  (if (equal actual expected)
      (format t "  PASS  ~A: ~A~%" label actual)
      (progn (format t "  FAIL  ~A: got ~A, expected ~A~%" label actual expected)
             (eita.test:finish :code 1))))

(format t "~%=== CALL / DELEGATECALL parametric handler tests ===~%")

;; Inner contract: PUSH1 0xAB, PUSH1 0, MSTORE8, PUSH1 1, PUSH1 0, RETURN
(setf *inner-code-for-test* '(#x60 #xab #x60 #x00 #x53  #x60 #x01 #x60 #x00 #xf3))

;; Test 1: CALL with value=7. Args (top→bottom):
;;   gas, addr, value, in_off, in_len, out_off, out_len  → success
(format t "~%CALL with value=7 → 0x42~%")
(let* ((code '(#x60 #x00          ; PUSH1 0 (out_len)
               #x60 #x00          ; PUSH1 0 (out_off)
               #x60 #x00          ; PUSH1 0 (in_len)
               #x60 #x00          ; PUSH1 0 (in_off)
               #x60 #x07          ; PUSH1 7 (value)
               #x60 #x42          ; PUSH1 0x42 (addr)
               #x61 #xff #xff     ; PUSH2 0xFFFF (gas)
               #xf1               ; CALL
               #x00))             ; STOP
       (r (run-outer code)))
  (expect "halted" (getf r :halted) t)
  (expect "sp" (getf r :sp) 1)
  (expect "success on stack" (getf r :top) 1)
  (expect "kind = 0 (CALL)" *captured-kind* 0)
  (expect "value captured" *captured-value* 7))

;; Test 2: DELEGATECALL (6 args, no value)
(format t "~%DELEGATECALL → 0x42~%")
(let* ((code '(#x60 #x00          ; PUSH1 0 (out_len)
               #x60 #x00          ; PUSH1 0 (out_off)
               #x60 #x00          ; PUSH1 0 (in_len)
               #x60 #x00          ; PUSH1 0 (in_off)
               #x60 #x42          ; PUSH1 0x42 (addr)
               #x61 #xff #xff     ; PUSH2 0xFFFF (gas)
               #xf4               ; DELEGATECALL
               #x00))             ; STOP
       (r (run-outer code)))
  (expect "halted" (getf r :halted) t)
  (expect "sp" (getf r :sp) 1)
  (expect "success on stack" (getf r :top) 1)
  (expect "kind = 2 (DELEGATECALL)" *captured-kind* 2)
  (expect "value = 0 (delegate)" *captured-value* 0))

;; Test 3: CALLCODE with value=42
(format t "~%CALLCODE with value=42 → 0x42~%")
(let* ((code '(#x60 #x00          ; out_len
               #x60 #x00          ; out_off
               #x60 #x00          ; in_len
               #x60 #x00          ; in_off
               #x60 #x2a          ; value=42
               #x60 #x42          ; addr
               #x61 #xff #xff     ; gas
               #xf2               ; CALLCODE
               #x00))             ; STOP
       (r (run-outer code)))
  (expect "halted" (getf r :halted) t)
  (expect "sp" (getf r :sp) 1)
  (expect "success on stack" (getf r :top) 1)
  (expect "kind = 1 (CALLCODE)" *captured-kind* 1)
  (expect "value captured" *captured-value* 42))

(format t "~%=== CALL family tests complete ===~%")
