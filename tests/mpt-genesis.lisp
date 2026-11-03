;;;; test-mpt-genesis.lisp — standalone proof-by-oracle for src/state/mpt.lisp.
;;;;
;;;; Builds the mainnet genesis account state trie and checks its root
;;;; against the canonical mainnet genesis stateRoot:
;;;;   d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544
;;;;
;;;; Run: (eita.test:run-all :only '("mpt-genesis")), or (asdf:test-system "eita") for all suites.

(in-package #:eita.mpt)

(load (merge-pathnames "genesis-alloc.lisp" *load-truename*))

(defparameter *genesis-target*
  "d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544")


(defun strip-hex (s)
  (if (and (>= (length s) 2) (string= "0x" (subseq s 0 2))) (subseq s 2) s))

(defun hex->bytes (s)
  (let* ((s (strip-hex s))
         (s (if (oddp (length s)) (concatenate 'string "0" s) s))
         (n (floor (length s) 2))
         (bs (make-array n :element-type '(unsigned-byte 8))))
    (loop for i from 0 below n do
      (setf (aref bs i)
            (parse-integer s :radix 16 :start (* 2 i) :end (* 2 (+ i 1)))))
    bs))

(defun load-genesis-accounts ()
  "Return a list of (addr nonce balance storage-alist code-bytes).
   Genesis has empty storage for every account."
  (progn
    (loop for acct in (genesis-alloc)
          collect (let* ((addr (getf acct :addr))
                         (balance (getf acct :balance))
                         (nonce (getf acct :nonce))
                         (code-str (getf acct :code))
                         (code (when (and code-str (plusp (length code-str)))
                                 (hex->bytes code-str))))
                    (list addr nonce balance '() code)))))

(defun main ()
  (let* ((accounts (load-genesis-accounts))
         (root (account-state-root accounts))
         (got (bytes->hex root))
         (pass (string-equal got *genesis-target*)))
    (format t "~&genesis accounts : ~D~%" (length accounts))
    (format t "computed root    : ~A~%" got)
    (format t "canonical root   : ~A~%" *genesis-target*)
    (format t "empty-trie root  : ~A~%" (bytes->hex (empty-root-bytes)))
    (format t "empty-code hash  : ~A~%" (bytes->hex (empty-code-hash)))
    (format t "~%~A~%" (if pass "PASS" "FAIL"))
    (unless pass (eita.test:finish :code 1))))

(main)
