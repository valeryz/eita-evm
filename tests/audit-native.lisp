;;;; audit-native.lisp — native (ARM64) handler audit pass.
;;;;
;;;; Loads c/libeita.dylib (built by `lake exe emitARM64 > c/handlers.S`
;;;; then `clang -shared`), and verifies that the native handler for ADD
;;;; produces the same post-state as the Form.interp fixtures.
;;;;
;;;; Same fixture file as audit-macros.lisp, same comparison logic. The
;;;; only difference: instead of running the CL macro on a Lisp evm-state,
;;;; we allocate a C EvmState struct, copy pre into it, call the native
;;;; handler, and read the result back.
;;;;
;;;; Run: (eita.test:run-all :only '("audit-native")), or (asdf:test-system "eita") for all suites.

(defpackage #:eita.test.audit-native (:use #:cl #:cffi))
(in-package :eita.test.audit-native)

(load (merge-pathnames "audit-lib.lisp" *load-truename*))
(defun audit-native-op (name opcode-byte cases)
  (let ((mismatches 0)
        first-mismatch)
    (dolist (case cases)
      (let* ((pre (getf case :pre))
             (post (getf case :post)))
        (cond
          ((getf post :none) nil)  ; skip Form.interp=none cases
          (t
           (multiple-value-bind (state stack arena journal) (build-native-state pre)
             (eita-run-one state opcode-byte)
             (unless (state-matches-fixture state post)
               (incf mismatches)
               (unless first-mismatch
                 (setf first-mismatch
                       (list :pre pre :expected post
                             :got (snapshot-native-state state)))))
             (foreign-free state)
             (foreign-free stack)
             (foreign-free arena)
             (foreign-free journal)
             (dolist (b *aux-buffers*) (foreign-free b))
             (setf *aux-buffers* nil))))))
    (if (zerop mismatches)
        (format t "  PASS  ~A/native  (~D fixtures)~%" name (length cases))
        (progn
          (format t "  FAIL  ~A/native  ~D/~D mismatched~%"
                  name mismatches (length cases))
          (format t "        first mismatch:~%")
          (format t "          pre:      ~A~%" (getf first-mismatch :pre))
          (format t "          expected: ~A~%" (getf first-mismatch :expected))
          (format t "          got:      ~A~%" (getf first-mismatch :got))))))

;; Subset of opcodes that have ARM64 handlers implemented.
(defparameter *implemented-ops*
  '("ADD" "SUB" "AND" "OR" "XOR" "LT" "GT" "SLT" "SGT" "EQ" "ISZERO" "NOT" "POP"
    "STOP" "JUMPDEST" "ADDRESS" "ORIGIN" "CALLER" "COINBASE"
    "CALLVALUE" "GASPRICE" "CHAINID" "TIMESTAMP" "NUMBER" "GASLIMIT"
    "BASEFEE" "PC" "MSIZE" "GAS"
    "CALLDATASIZE" "CODESIZE" "RETURNDATASIZE"
    "MLOAD" "MSTORE" "MSTORE8"
    "SSTORE" "TSTORE"
    "MUL" "DIV" "SDIV" "MOD" "SMOD" "EXP"
    "SHL" "SHR" "SAR" "BYTE" "SIGNEXTEND"
    "ADDMOD" "MULMOD"
    "CALLDATALOAD" "CALLDATACOPY" "CODECOPY" "RETURNDATACOPY" "MCOPY"
    "KECCAK256"
    "SLOAD" "TLOAD" "BALANCE" "SELFBALANCE" "EXTCODESIZE" "EXTCODEHASH"
    "BLOCKHASH" "EXTCODECOPY"
    "RETURN" "REVERT"
    "JUMP" "JUMPI"
    "PUSH0" "PUSH1" "PUSH2" "PUSH3" "PUSH4" "PUSH5" "PUSH8"
    "PUSH9" "PUSH16" "PUSH17" "PUSH24" "PUSH25" "PUSH32"
    "LOG0" "LOG1" "LOG2" "LOG3" "LOG4"
    "DUP1" "DUP3" "SWAP1" "SWAP3"))

(defparameter *native-runners*
  (remove-if-not (lambda (entry)
                   (member (car entry) *implemented-ops* :test #'string=))
                 *opcode-bytes*))

(format t "~%=== Native (ARM64) handler audit ===~%")

(let ((fixtures (load-fixtures (merge-pathnames "interp-fixtures.sexp" *load-truename*))))
  (dolist (entry fixtures)
    (let* ((name (getf entry :name))
           (cases (getf entry :cases))
           (opcode-byte (cdr (assoc name *native-runners* :test #'string=))))
      (when opcode-byte
        (audit-native-op name opcode-byte cases)))))

(format t "Native audit complete.~%")
