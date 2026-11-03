;;;; test-eita-run.lisp — exercise the production threaded driver eita_run().
;;;;
;;;; Builds an EvmState with a small bytecode program, calls eita_run() once,
;;;; verifies the state after the chain of handlers ran (each ending with
;;;; `br x27` = `_eita_next`, dispatching to the next opcode without
;;;; per-opcode CFFI roundtrip).

(defpackage #:eita.test.eita-run (:use #:cl #:cffi))
(in-package :eita.test.eita-run)

(defcfun ("eita_run" eita-run) :void (state :pointer))

(defun u256-read (ptr)
  (let ((acc 0))
    (loop for i from 3 downto 0 do
      (setf acc (logior (ash acc 64) (mem-aref ptr :uint64 i))))
    acc))

(defun run-program (bytecode &key (initial-gas 1000000) (gas nil))
  "Run BYTECODE (list of bytes) through eita_run, return (sp gas pc halted stack)."
  (let* ((state    (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
         (stack    (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
         (mem      (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
         (code-len (length bytecode))
         (code     (foreign-alloc :uint8 :count (+ code-len 64) :initial-element 0))
         (arena    (foreign-alloc :uint8 :count 64 :initial-element 0))
         (journal  (foreign-alloc :uint8 :count 10000 :initial-element 0))
         (cb       (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    ;; Populate code
    (loop for b in bytecode for i from 0 do
      (setf (mem-aref code :uint8 i) b))
    ;; Wire state
    (setf (mem-ref state :uint64 8)   (or gas initial-gas))    ; gas_left
    (setf (mem-ref state :pointer 32) stack)          ; stack
    (setf (mem-ref state :pointer 40) mem)            ; memory
    (setf (mem-ref state :uint64 56)  (* 64 1024))   ; memory_cap
    (setf (mem-ref state :pointer 64) code)           ; code
    (setf (mem-ref state :uint64 72)  code-len)       ; code_size
    (setf (mem-ref arena :pointer 16) journal)        ; arena.journal_data
    (setf (mem-ref state :pointer 496) cb)            ; cb table (empty)
    (setf (mem-ref state :pointer 504) arena)         ; cb_ctx
    ;; Run!
    (eita-run state)
    ;; Snapshot
    (let* ((sp     (mem-ref state :uint64 16))
           (gas    (mem-ref state :uint64 8))
           (pc     (mem-ref state :uint64 0))
           (halted (not (zerop (mem-ref state :uint8 128))))
           (stack-vals
             (loop for i from 0 below sp
                   collect (u256-read (inc-pointer stack (* i 32))))))
      (foreign-free state) (foreign-free stack) (foreign-free mem)
      (foreign-free code) (foreign-free arena) (foreign-free journal)
      (foreign-free cb)
      (list :sp sp :gas gas :pc pc :halted halted :stack stack-vals))))

(defun expect (label actual expected)
  (if (equal actual expected)
      (format t "  PASS  ~A: ~A~%" label actual)
      (progn
        (format t "  FAIL  ~A: got ~A, expected ~A~%" label actual expected)
        (eita.test:finish :code 1))))

(format t "~%=== eita_run driver test (production threaded chain) ===~%~%")

;; Test 1: PUSH1 0x42, STOP — should push 0x42 and halt.
(format t "Test 1: PUSH1 0x42, STOP~%")
(let ((r (run-program '(#x60 #x42 #x00))))
  (expect "halted" (getf r :halted) t)
  (expect "sp"     (getf r :sp)     1)
  (expect "stack"  (getf r :stack)  '(#x42))
  ;; PUSH1 charges 3, STOP charges 0. PUSH1 advances pc by 2, STOP leaves it.
  (expect "gas"    (getf r :gas)    (- 1000000 3))
  (expect "pc"     (getf r :pc)     2))

;; Test 2: PUSH1 1, PUSH1 2, ADD, STOP — should push 3.
(format t "~%Test 2: PUSH1 1, PUSH1 2, ADD, STOP~%")
(let ((r (run-program '(#x60 #x01 #x60 #x02 #x01 #x00))))
  (expect "halted" (getf r :halted) t)
  (expect "sp"     (getf r :sp)     1)
  (expect "stack"  (getf r :stack)  '(3))
  (expect "gas"    (getf r :gas)    (- 1000000 3 3 3))  ; 2 pushes + 1 add

;; Test 3: PUSH1 7, PUSH1 5, MUL, STOP — 35.
(format t "~%Test 3: PUSH1 7, PUSH1 5, MUL, STOP~%")
(let ((r (run-program '(#x60 #x07 #x60 #x05 #x02 #x00))))
  (expect "halted" (getf r :halted) t)
  (expect "stack"  (getf r :stack)  '(35)))

;; Test 4: PUSH1 10, PUSH1 20, SUB, STOP — 10 (20 - 10).
(format t "~%Test 4: PUSH1 10, PUSH1 20, SUB, STOP~%")
(let ((r (run-program '(#x60 #x0a #x60 #x14 #x03 #x00))))
  (expect "halted" (getf r :halted) t)
  (expect "stack"  (getf r :stack)  '(10))))

;;; Guard tests — verify OOG, stack overflow, static-call enforcement
;;; actually trip and halt-with-revert.

(defun run-program-low-gas (bytecode initial-gas)
  (run-program bytecode :gas initial-gas))

;; Test 5: OOG. PUSH1 1 (3 gas), gas-left = 2. Should halt+revert mid-PUSH.
(format t "~%Test 5: OOG trips when gas insufficient~%")
(let ((r (run-program-low-gas '(#x60 #x01 #x00) 2)))
  ;; PUSH1 charges 3, exit-with-gas detects underflow → b.lo _eita_oog
  (expect "halted"   (getf r :halted) t)
  ;; sync_and_ret writes back. OOG sets reverted=1 and gas=0.
  (expect "gas-zero" (getf r :gas)    0))

;; Test 6: Stack overflow. Push 1025 things via DUP loop. Hand-build:
;; PUSH1 0 (then DUP1 × 1024 = 1025 stack items, overflow on the 1025th).
(format t "~%Test 6: Stack overflow trips at sp = 1024~%")
(let* ((push-once '(#x60 #x00))           ; PUSH1 0  → sp=1
       (dups (loop repeat 1024 collect #x80))   ; DUP1 × 1024 → tries to make sp 1025
       (code (append push-once dups (list #x00))))
  (let ((r (run-program code)))
    (expect "halted"   (getf r :halted) t)
    (expect "gas-zero" (getf r :gas)    0)))

;; Test 7: Static-call violation. Set staticp=true, run SSTORE.
;; This requires a custom state setup; piggyback on run-program but flip the flag.
(format t "~%Test 7: SSTORE in static context traps~%")
(let* ((state    (foreign-alloc :uint8 :count eita.evm::+substate-bytes+ :initial-element 0))
       (stack    (foreign-alloc :uint8 :count (* 1024 32) :initial-element 0))
       (mem      (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0))
       ;; PUSH1 1 PUSH1 2 SSTORE STOP
       (bytecode '(#x60 #x01 #x60 #x02 #x55 #x00))
       (code-len (length bytecode))
       (code     (foreign-alloc :uint8 :count (+ code-len 64) :initial-element 0))
       (arena    (foreign-alloc :uint8 :count 64 :initial-element 0))
       (journal  (foreign-alloc :uint8 :count 10000 :initial-element 0))
       (cb       (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
  (loop for b in bytecode for i from 0 do (setf (mem-aref code :uint8 i) b))
  (setf (mem-ref state :uint64 8)   1000000)
  (setf (mem-ref state :pointer 32) stack)
  (setf (mem-ref state :pointer 40) mem)
  (setf (mem-ref state :uint64 56)  (* 64 1024))
  (setf (mem-ref state :pointer 64) code)
  (setf (mem-ref state :uint64 72)  code-len)
  (setf (mem-ref state :uint8  130) 1)         ; staticp = true
  (setf (mem-ref arena :pointer 16) journal)
  (setf (mem-ref state :pointer 496) cb)
  (setf (mem-ref state :pointer 504) arena)
  (eita-run state)
  (let ((halted (not (zerop (mem-ref state :uint8 128))))
        (reverted (not (zerop (mem-ref state :uint8 129)))))
    (expect "halted"   halted   t)
    (expect "reverted" reverted t))
  (foreign-free state) (foreign-free stack) (foreign-free mem)
  (foreign-free code) (foreign-free arena) (foreign-free journal)
  (foreign-free cb))

(format t "~%=== eita_run driver test complete ===~%")
