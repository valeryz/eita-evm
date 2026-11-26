;;;; evm/interp.lisp — running a frame on the threaded interpreter, the code hash memo, and
;;;; the frame's outcome.

(in-package #:eita.evm)

;; Fork.ord of the network under replay (Evm.Fork: frontier=0 ...
;; berlin=10 ... cancun=16). Selects the native dispatch table and the
;; call-gas plan symbol cb-call binds.
(defparameter *fork-ord* 16)

;; mmap protection and flags (the guard-paged arenas, evm/frames.lisp).
(defconstant +prot-rw+ 3)            ; PROT_READ|PROT_WRITE
;; MAP_PRIVATE|MAP_ANON: the MAP_ANON bit differs by OS — Darwin 0x1000, Linux
;; 0x20. (MAP_PRIVATE is 0x2 on both; MAP_SHARED is 0x1 on both.)
(defconstant +map-priv-anon+ #+darwin #x1002 #+linux #x22 #-(or darwin linux) #x1002)

;; One frame's EvmState (c/evm_state.h), the unit the substate arena is sliced in
;; (evm/frames.lisp).
(defconstant +substate-bytes+ 608)   ; sizeof(EvmState), c/evm_state.h

;; The code hash memo: keccak256(code) as a 256-bit int, memoized per code OBJECT (code is
;; the stable world-code vector), so keccak runs once per contract and is O(1) thereafter.
;; Weak keys: a self-destructed code's entry is GC'd. The snapshot world seeds it from the
;; stored codehash when it faults code in (state/snapshot-world.lisp).
(defparameter *code-hash-memo* (make-hash-table :test 'eq :weakness :key)
  "code vector -> keccak256(code) as a 256-bit int. keccak once per contract.")
(defun code-hash-int (code)
  (or (gethash code *code-hash-memo*)
      (setf (gethash code *code-hash-memo*)
            (let ((h 0))
              (loop for b across (keccak256-bytes code)   ; defined later; runtime-resolved
                    do (setf h (logior (ash h 8) b)))
              h))))

(declaim (ftype function storage-host-sync!))

(defun run-frame (state)
  "Run one frame on the threaded interpreter. Every frame entry syncs the native storage path."
  (storage-host-sync!)
  (eita-run state))

(defun %frame-output (state)
  "Copy the frame's output bytes (ptr@112, size@120) to a Lisp vector."
  (let ((p (mem-ref state :pointer 112)) (n (mem-ref state :uint64 120)))
    (if (or (null-pointer-p p) (zerop n)) #()
        (foreign->bytes p n))))

(defun frame-status (state)
  "How the frame in STATE ended: :return, :revert or :halt (an exceptional halt: EELS
   execute_code's `except ExceptionalHalt` -- out of gas, invalid opcode or jump, stack
   under/overflow, static-context write, out-of-bounds returndata, ... -- gas_left := 0,
   output := b\"\"). The interpreter raises `reverted` (offset 129) for REVERT and
   for every exceptional halt; only REVERT writes the output pointer (offset 112, zeroed per
   frame), so reverted with a NULL output is the exceptional halt."
  (let ((halted (not (zerop (mem-ref state :uint8 128))))
        (reverted (not (zerop (mem-ref state :uint8 129)))))
    (cond ((and halted (not reverted)) :return)
          ((and reverted (not (null-pointer-p (mem-ref state :pointer 112)))) :revert)
          (t :halt))))
