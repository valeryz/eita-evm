;;;; test-staticcall.lisp — end-to-end recursive sub-call via STATICCALL.
;;;;
;;;; Outer program does STATICCALL to sub-frame address 0x42. The Lisp-side
;;;; callback recognizes 0x42, sets up a fresh EvmState with sub-bytecode,
;;;; calls eita_run on it (RECURSIVE re-entry into native), reads the
;;;; sub-frame's RETURN output back into a CallResult, returns to ARM64.
;;;; Outer program then reads returndata back via RETURNDATACOPY (skipped
;;;; for MVP — we just check that state.returndata_size was set correctly
;;;; and success was pushed.

(defpackage #:eita.test.staticcall (:use #:cl #:cffi))
(in-package :eita.test.staticcall)

(defcfun ("eita_run" eita-run) :void (state :pointer))

(defun u256-read (ptr)
  (let ((acc 0))
    (loop for i from 3 downto 0 do
      (setf acc (logior (ash acc 64) (mem-aref ptr :uint64 i))))
    acc))

;; --- Sub-call infrastructure ---

;; Inner contract at address 0x42:
;;   PUSH1 0x99, PUSH1 0x00, MSTORE8,
;;   PUSH1 0x01, PUSH1 0x00, RETURN
;; → returns the single byte 0x99
(defparameter *inner-code*
  '(#x60 #x99 #x60 #x00 #x53
    #x60 #x01 #x60 #x00 #xf3))

;; Track sub-frame state across the callback.
(defparameter *sub-result-output* nil)
(defparameter *sub-result-output-len* 0)
(defparameter *sub-result-gas-used* 0)
(defparameter *sub-result-success* 0)

(defun u8-vec-to-foreign (vec)
  "Allocate a foreign buffer and copy bytes from a vector. Returns ptr."
  (let* ((n (length vec))
         (buf (foreign-alloc :uint8 :count (max n 1) :initial-element 0)))
    (loop for b in (coerce vec 'list) for i from 0 do
      (setf (mem-aref buf :uint8 i) b))
    buf))

;; The call callback runs the inner contract recursively.
(defcallback cb-call :int
    ((ctx :pointer) (params :pointer) (result :pointer))
  (declare (ignore ctx))
  (let ((addr (u256-read (inc-pointer params 8))))
    (cond
      ((= addr #x42)
       ;; Build a sub-frame EvmState
       (let* ((sub-state (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
              (sub-stack (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
              (sub-mem   (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
              (sub-code-len (length *inner-code*))
              (sub-code  (foreign-alloc :uint8 :count (+ sub-code-len 64) :initial-element 0))
              (sub-arena (foreign-alloc :uint8 :count 64 :initial-element 0))
              (sub-journ (foreign-alloc :uint8 :count 10000 :initial-element 0))
              (sub-cb    (foreign-alloc :pointer :count 16 :initial-element (null-pointer)))
              (gas-given (mem-ref params :uint64 88)))
         (loop for b in *inner-code* for i from 0 do
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
         ;; Recursive re-entry into native!
         (eita-run sub-state)
         ;; Read result from sub-state
         (let* ((halted (not (zerop (mem-ref sub-state :uint8 128))))
                (reverted (not (zerop (mem-ref sub-state :uint8 129))))
                (output-ptr (mem-ref sub-state :pointer 112))
                (output-len (mem-ref sub-state :uint64 120))
                (gas-left (mem-ref sub-state :uint64 8))
                (gas-used (- gas-given gas-left)))
           ;; Write CallResult fields
           (setf (mem-ref result :int 0) (if (and halted (not reverted)) 1 0))
           ;; Copy output into a fresh buffer the caller owns (the sub-state is
           ;; about to be freed). For MVP, leak the buffer; production would
           ;; arena-allocate.
           (let ((out-copy (foreign-alloc :uint8 :count (max output-len 1) :initial-element 0)))
             (when (and output-ptr (plusp output-len))
               (loop for i from 0 below output-len do
                 (setf (mem-aref out-copy :uint8 i)
                       (mem-aref output-ptr :uint8 i))))
             (setf (mem-ref result :pointer 8) out-copy)
             (setf *sub-result-output* out-copy))
           (setf (mem-ref result :uint64 16) output-len)
           (setf (mem-ref result :uint64 24) gas-used)
           (setf *sub-result-output-len* output-len)
           (setf *sub-result-gas-used* gas-used)
           (setf *sub-result-success* (mem-ref result :int 0)))
         ;; Free sub-frame state
         (foreign-free sub-state) (foreign-free sub-stack)
         (foreign-free sub-mem)   (foreign-free sub-code)
         (foreign-free sub-arena) (foreign-free sub-journ)
         (foreign-free sub-cb)
         0))
      (t
       (setf (mem-ref result :int 0) 0)
       0))))

(defun alloc-callbacks-with-call ()
  (let ((cb (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (setf (mem-aref cb :pointer 11) (callback cb-call))   ; cb->call at offset 88 = index 11
    cb))

;; --- Outer test: program does STATICCALL into addr 0x42 ---

;; Outer bytecode:
;;   PUSH1 0      ; out_len
;;   PUSH1 0      ; out_off
;;   PUSH1 0      ; in_len
;;   PUSH1 0      ; in_off
;;   PUSH1 0x42   ; addr
;;   PUSH2 0xFFFF ; gas
;;   STATICCALL
;;   STOP
(defparameter *outer-code*
  '(#x60 #x00          ; PUSH1 0 (out_len)
    #x60 #x00          ; PUSH1 0 (out_off)
    #x60 #x00          ; PUSH1 0 (in_len)
    #x60 #x00          ; PUSH1 0 (in_off)
    #x60 #x42          ; PUSH1 0x42 (addr)
    #x61 #xff #xff     ; PUSH2 0xFFFF (gas)
    #xfa               ; STATICCALL
    #x00))             ; STOP

(format t "~%=== Test: STATICCALL recursive sub-frame ===~%")

(let* ((state    (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
       (stack    (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
       (mem      (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
       (code-len (length *outer-code*))
       (code     (foreign-alloc :uint8 :count (+ code-len 64) :initial-element 0))
       (arena    (foreign-alloc :uint8 :count 64 :initial-element 0))
       (journal  (foreign-alloc :uint8 :count 10000 :initial-element 0))
       (cb       (alloc-callbacks-with-call)))
  (loop for b in *outer-code* for i from 0 do
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
  (let* ((sp        (mem-ref state :uint64 16))
         (halted    (not (zerop (mem-ref state :uint8 128))))
         (returndata-len (mem-ref state :uint64 104))
         (returndata-ptr (mem-ref state :pointer 96))
         (top       (if (>= sp 1) (u256-read stack) 0))
         (first-rd-byte (if (and returndata-ptr (plusp returndata-len))
                            (mem-ref returndata-ptr :uint8 0)
                            nil)))
    (format t "Outer halted: ~A~%" halted)
    (format t "Outer sp: ~A (expect 1)~%" sp)
    (format t "Outer top of stack (STATICCALL success flag): ~A (expect 1)~%" top)
    (format t "state.returndata_size: ~A (expect 1)~%" returndata-len)
    (format t "First byte of returndata: 0x~2,'0X (expect 0x99)~%" (or first-rd-byte 0))
    (format t "Sub-frame consumed gas: ~A~%" *sub-result-gas-used*)
    (cond
      ((and halted (= sp 1) (= top 1) (= returndata-len 1) (eql first-rd-byte #x99))
       (format t "~%STATICCALL end-to-end recursive sub-frame: PASS~%"))
      (t
       (format t "~%STATICCALL test FAILED~%")
       (eita.test:finish :code 1))))
  (foreign-free state) (foreign-free stack) (foreign-free mem)
  (foreign-free code) (foreign-free arena) (foreign-free journal)
  (foreign-free cb))
