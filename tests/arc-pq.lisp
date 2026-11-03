;;;; test-arc-pq.lisp — the Arc PQ precompile (0x1800…0004) against the chain.
;;;;
;;;; The fixture is the REAL call that stopped the continuous replay (stop #14):
;;;; block 21 452 605 tx 17, a STATICCALL at depth 4 into 0x1800…0004 with 8 132
;;;; bytes of input. Alchemy's callTracer reports gasUsed = 230 006 and output
;;;; 0x…01 for it, and those two numbers are what this file asserts.
;;;;
;;;; Why a fixture test and not only the replay: a lazy-mode replay of that block
;;;; is RPC-bound (minutes), while this runs in a second and still pins both
;;;; halves of the contract — the gas, which the header gate would catch, and the
;;;; verdict, which it would NOT: the cost is identical either way, so a wrong
;;;; bool is invisible to every gas check in the system.
;;;;
;;;; Run: (eita.test:run-all :only '("arc-pq")), or (asdf:test-system "eita") for all suites.

(in-package #:eita.chain.arc)

(defparameter *fails* 0)

(defun chk (name got want)
  (if (equalp got want)
      (format t "  ok    ~A~%" name)
      (progn (incf *fails*)
             (format t "  FAIL  ~A~%        got  ~S~%        want ~S~%" name got want))))

(defun hex->u8 (s)
  (let ((v (make-array (floor (length s) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v)
      (setf (aref v i) (parse-integer s :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))

(defparameter *input*
  (hex->u8 (string-trim '(#\Newline #\Space)
                        (with-open-file (in (merge-pathnames "data/arc-pq-21452605-tx17.hex" *load-truename*))
                          (read-line in)))))

(defmacro with-input ((ptr len &optional (bytes '*input*)) &body body)
  "Copy BYTES into a foreign buffer, as a frame's input buffer would be."
  `(let ((,len (length ,bytes)))
     (cffi:with-foreign-object (,ptr :uint8 (max ,len 1))
       (dotimes (i ,len) (setf (cffi:mem-aref ,ptr :uint8 i) (aref ,bytes i)))
       ,@body)))

(format t "~&== Arc PQ precompile: block 21452605 tx 17 (the real call) ==~%")
(format t "  input ~D bytes, selector ~(~8,'0x~)~%" (length *input*)
        (with-input (p n) (arc-selector p n)))

;;; 1. The ABI decode finds the three arguments where the chain's call put them.
(with-input (p n)
  (multiple-value-bind (vk-off vk-len msg-off msg-len sig-off sig-len) (arc-pq-decode p n)
    (chk "selector" (arc-selector p n) +arc-pq-selector+)
    (chk "vk length"  vk-len  32)
    (chk "msg length" msg-len 32)
    (chk "sig length" sig-len 7856)
    (chk "vk offset"  vk-off  132)         ; 4 + 96 head + 32 length word
    (chk "offsets are inside the buffer"
         (and (< (+ vk-off vk-len) n) (< (+ msg-off msg-len) n) (<= (+ sig-off sig-len) n)) t)))

;;; 2. The whole precompile: gas AND verdict, against the trace.
(with-input (p n)
  (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)   ; gas the chain forwarded
    (chk "gasUsed == the chain's 230006" used 230006)
    (chk "success" ok t)
    (chk "output == abi(true)" out (arc-abi-bool t))))

;;; 3. The gas is the emitted formula, and does not move with the verdict.
(chk "spec-arc-pq-verify-gas(1)" (spec-arc-pq-verify-gas 1) 230006)
(chk "spec-arc-pq-verify-gas(0)" (spec-arc-pq-verify-gas 0) 230000)
(chk "base/word/lengths from the spec"
     (list (spec-arc-pq-base-gas) (spec-arc-pq-msg-word-gas)
           (spec-arc-pq-vk-len) (spec-arc-pq-sig-len))
     (list 230000 6 32 7856))

;;; 4. A tampered message must verify FALSE — at exactly the same gas. This is
;;; the assertion that a lookalike SPHINCS+ (round 3.1 vs FIPS 205) fails.
(let ((bad (copy-seq *input*)))
  (setf (aref bad 132 ) (aref bad 132))                    ; (vk untouched)
  (setf (aref bad 196) (logxor 1 (aref bad 196)))          ; flip a message bit
  (with-input (p n bad)
    (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
      (chk "tampered message: still 230006 gas" used 230006)
      (chk "tampered message: success (the CALL succeeds)" ok t)
      (chk "tampered message: output == abi(false)" out (arc-abi-bool nil)))))

;;; 5. Early paths charge the 200 penalty and nothing else.
(with-input (p n (subseq *input* 0 3))
  (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
    (declare (ignore out))
    (chk "3-byte input: 200 gas, revert" (list used ok) (list 200 nil))))
(let ((short (subseq *input* 0 99)))                       ; selector + 95 head bytes
  (with-input (p n short)
    (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
      (declare (ignore out))
      (chk "truncated head: 200 gas, revert" (list used ok) (list 200 nil)))))

;;; 6. Two different ways a 31-byte verifying key is rejected, and they cost
;;; DIFFERENT gas — which is exactly why the strict decode has to match alloy.
;;;   (a) declare 31 but leave the 32nd byte set: non-zero padding, so
;;;       `abi_decode_raw_validate` fails and only the 200-gas penalty is charged;
;;;   (b) declare 31 AND zero that byte: the decode succeeds, the base and
;;;       per-word gas are charged, and only then comes the typed length revert.
(let ((bad (copy-seq *input*)))
  (setf (aref bad 131) 31)                                 ; vk length word -> 31
  (with-input (p n bad)
    (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
      (chk "vk length 31, dirty padding: decode fails for 200" (list used ok) (list 200 nil))
      (chk "vk length 31, dirty padding: revert message"
           out (arc-revert-bytes "Execution reverted")))))
(let ((bad (copy-seq *input*)))
  (setf (aref bad 131) 31)                                 ; vk length word -> 31
  (setf (aref bad (+ 132 31)) 0)                           ; …and its padding byte
  (with-input (p n bad)
    (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
      (chk "vk length 31, clean padding: charged 230006 then reverted"
           (list used ok) (list 230006 nil))
      (chk "vk length 31, clean padding: revert message"
           out (arc-revert-bytes "Invalid verifying key length")))))
;;; A short signature reverts the same way (a separate, typed message).
(let ((bad (copy-seq *input*)))
  (setf (aref bad 259) (logand #xff 7855))                 ; sig length word low byte
  (setf (aref bad 258) (ash 7855 -8))
  (setf (aref bad (+ 260 7855)) 0)                         ; and its padding byte
  (with-input (p n bad)
    (multiple-value-bind (used out ok) (arc-pq-verify p n 358134)
      (chk "sig length 7855: charged 230006 then reverted" (list used ok) (list 230006 nil))
      (chk "sig length 7855: revert message"
           out (arc-revert-bytes "Invalid signature length")))))

;;; 7. Out of gas one unit below base + words; fine at exactly base + words.
(with-input (p n)
  (multiple-value-bind (used out ok) (arc-pq-verify p n 230005)
    (declare (ignore out))
    (chk "230005 gas: OOG consumes the pool" (list used ok) (list 230005 nil)))
  (multiple-value-bind (used out ok) (arc-pq-verify p n 230006)
    (declare (ignore out))
    (chk "230006 gas: exactly enough" (list used ok) (list 230006 t))))

;;; 8. The parameter-set guard the library carries.
(chk "libeita_pq self-test" (progn (arc-pq-ensure-lib!) (%arc-slhdsa-selftest)) 1)

(format t "~&~A~%" (if (zerop *fails*) "ALL PQ CHECKS PASS" (format nil "~D FAILURE(S)" *fails*)))
(finish-output)
(eita.test:finish :code (if (zerop *fails*) 0 1))
