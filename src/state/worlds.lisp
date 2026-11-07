;;;; state/worlds.lisp — a world as a whole: populating one from a pre-state, copying one,
;;;; its state root over the reference trie. The REPL API (src/eita.lisp) and the fixture
;;;; runner build their worlds with these.

(in-package #:eita.state)

(defun populate-world (world pre-accounts)
  (dolist (entry pre-accounts)
    (let ((addr (car entry))
          (acct (cdr entry)))
      ;; Every pre-state account EXISTS, including an all-zero one: pre-Spurious a CALL
      ;; to an existing empty account pays no new-account fee (the replay's
      ;; world-accounts set; ethereum/tests ZeroValue_/NonZeroValue_*_ToEmpty).
      (with-acct (tb a) world addr (acct-set-flag! tb a +acct-marked+))
      (setf (balance-of world addr) (getf acct :balance))
      (setf (nonce-of world addr)   (getf acct :nonce))
      (let ((code (getf acct :code)))
        (when (plusp (length code))
          (with-acct (tb a) world addr (setf (acct-code tb a) code))))
      (dolist (kv (getf acct :storage))
        (world-storage-set world addr (car kv) (cdr kv))))))

(defun copy-world* (w)
  "An independent copy of W (an invalid block runs on one and is thrown away)."
  (let ((c (make-world)))
    (map-accts (lambda (r &aux (tb (world-accts w)))
                 (with-acct (cb x) c (acct-addr tb r)
                   (setf (acct-balance cb x) (acct-balance tb r) (acct-nonce cb x) (acct-nonce tb r)
                         (acct-code cb x) (acct-code tb r)
                         (acct-bits cb x) (logandc2 (acct-bits tb r) (logior +acct-destroyed+ +acct-touched+)))
                   (let ((tbl (acct-slots tb r)))
                     (when tbl (%ws-copy (acct-table-ws! cb) x tbl)))))
               (world-accts w))
    c))

(defun world-state-root (world)
  "The state root of WORLD (\"0x…\"): every present account (an empty one too), its non-zero
   slots, over the reference trie (mpt.lisp account-state-root). The driver checks the root at
   its anchors (state/root.lisp); a fixture's blocks are few and small, so every block."
  (let ((*current-world* world) (tb (world-accts world)) (accounts '()))
    (map-accts (lambda (r &aux (addr (acct-addr tb r)))
                 (when (world-account-present-p addr)
                   (let ((slots '()))
                     (acct-slots-map (lambda (k v) (unless (zerop v) (push (cons k v) slots))) tb r)
                     (push (list addr (nonce-of world addr) (balance-of world addr) slots (acct-code-entry tb r))
                           accounts))))
               tb)
    (concatenate 'string "0x" (eita.mpt:bytes->hex (eita.mpt:account-state-root accounts)))))
