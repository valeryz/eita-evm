;;;; evm/simulate.lisp — what-if execution on the state after the newest block, discarded on
;;;; return (docs/hooks.md, "Simulation"): `eita:simulate` opens an overlay, `eita:sim-tx`
;;;; runs a transaction in it, `eita:sim-set` / `eita:sim-read` write and read it.
;;;;
;;;; The overlay is the layered world's own mechanism, a hot set over colder tiers: the
;;;; world's account table is swapped for a fresh one whose fault hooks read the table it
;;;; replaced first (the block's writes, its faulted reads), then the hooks that were
;;;; installed (the frozen layers and the base, a lazy world's RPC); a plain in-memory world
;;;; has no colder tier, so its table is the whole state. Every write lands in the fresh
;;;; table, which is dropped on return. The transactions run the replay's own path
;;;; (run-evm-tx, or the chain's tx hook), with the observers, the read stream, the read-set
;;;; recorder and the incremental root check off: nothing reaches the world, the fact log,
;;;; a layer or a read set. Replay thread only, between blocks: an `:executed` handler.

(in-package #:eita.evm)

(defvar *simulating* nil "True inside `eita:simulate`.")

(defun overlay-hooks (saved lazy fault-acct fault-slot cold-map)
  "The fault hooks of an overlay over SAVED (the account table it replaced). LAZY: SAVED holds
   only what was faulted (an account is there iff faulted), the colder tiers are behind
   FAULT-ACCT / FAULT-SLOT / COLD-MAP; else SAVED is the whole state."
  (labels ((found (addr)
             (let ((a (eita.state::acct-table-find saved addr)))
               (and (>= a 0) (or (not lazy) (eita.state::acct-flag-p saved a eita.state::+acct-faulted+)) a)))
           (wiped-here-p (addr)
             (let ((tb (world-accts *current-world*)) (b (eita.state::acct-table-find (world-accts *current-world*) addr)))
               (and (>= b 0) (eita.state::acct-flag-p tb b eita.state::+acct-wiped+))))
           (put-slot (addr slot v)
             (eita.state::with-acct (tb b) *current-world* addr (eita.state::acct-slot-put! tb b slot v))))
    (values
     (lambda (addr)                                   ; account: SAVED's fields, else the tiers
       (let ((a (found addr)))
         (if a
             (eita.state::with-acct (tb b) *current-world* addr
               (setf (eita.state::acct-nonce tb b) (eita.state::acct-nonce saved a)
                     (eita.state::acct-balance tb b) (eita.state::acct-balance saved a))
               (let ((c (eita.state::acct-code-entry saved a))) (when c (setf (eita.state::acct-code tb b) c)))
               (setf (eita.state::acct-bits tb b)     ; existence mark, wiped; not the per-tx sets
                     (logior (eita.state::acct-bits tb b)
                             (logand (eita.state::acct-bits saved a) (logior eita.state::+acct-marked+ eita.state::+acct-wiped+)))))
             (when fault-acct (funcall fault-acct addr)))))
     (lambda (addr slot)                              ; slot: SAVED's, 0 under a wipe, else the tiers
       (let ((a (eita.state::acct-table-find saved addr)))
         (multiple-value-bind (v present) (if (>= a 0) (eita.state::acct-slot-get saved a slot) (values 0 nil))
           (cond ((wiped-here-p addr) (put-slot addr slot 0))
                 (present (put-slot addr slot v))
                 ((and (>= a 0) (eita.state::acct-flag-p saved a eita.state::+acct-wiped+)) (put-slot addr slot 0))
                 ((and lazy fault-slot) (funcall fault-slot addr slot))
                 (t (put-slot addr slot 0))))))
     (lambda (addr fn)                                ; the slots below the overlay, each once
       (unless (wiped-here-p addr)
         (let ((tb (world-accts *current-world*)) (a (eita.state::acct-table-find saved addr)))
           (flet ((here-p (k) (let ((b (eita.state::acct-table-find tb addr)))
                                (and (>= b 0) (eita.state::acct-slot-present-p tb b k)))))
             (when (>= a 0)
               (eita.state::acct-slots-map (lambda (k v) (unless (or (here-p k) (zerop v)) (funcall fn k v))) saved a))
             (when (and lazy cold-map (not (and (>= a 0) (eita.state::acct-flag-p saved a eita.state::+acct-wiped+))))
               (funcall cold-map addr (lambda (k v) (unless (and (>= a 0) (eita.state::acct-slot-present-p saved a k))
                                                      (funcall fn k v)))))))))
     (lambda (addr)                                   ; wipe: mark the overlay's entry
       (eita.state::with-acct (tb b) *current-world* addr
         (eita.state::acct-set-flag! tb b eita.state::+acct-wiped+))))))

(defun eita:simulate (fn)
  "Call FN (no arguments) on the state after the newest block, in an overlay that is
   dropped when FN returns: what FN's transactions (`eita:sim-tx`) and writes (`eita:sim-set`)
   change, and what they read, never reaches the world, the observers, the fact log, a layer
   or a read set. Replay thread only, between blocks (an `:executed` handler); nested calls
   share the outer overlay. Returns FN's values."
  (cond
    (*simulating* (funcall fn))
    ((null *current-world*) (error "eita:simulate: no world (the replay thread, between blocks)"))
    (t
     (let* ((w *current-world*) (saved (world-accts w)) (lazy (and eita.state::*fault-account-hook* t)))
       (multiple-value-bind (fa fs cm wipe)
           (overlay-hooks saved lazy eita.state::*fault-account-hook* eita.state::*fault-slot-hook*
                          eita.state::*cold-storage-map-hook*)
         (let ((*simulating* t)
               (*observer* nil) (*observe-capture* nil) (*view-log* nil) (*capture-reads* nil)
               (*readset-dir* nil) (*mpt-tracking* nil)
               (eita.state::*keep-zero-slots* t)
               (eita.state::*fault-account-hook* fa) (eita.state::*fault-slot-hook* fs)
               (eita.state::*cold-storage-map-hook* cm) (eita.state::*storage-wipe-hook* wipe)
               (*receipt-cumulative-gas* 0) (*block-blob-gas* 0) (*stats* (copy-list *stats*))
               (*last-tx-logs* '()) (*last-tx-output* #())
               (eita.chain::*tx-receipt-extension* nil))
           (setf (world-accts w) (eita.state::make-acct-table))
           (unwind-protect (funcall fn)
             (forget-tx-sets!)
             (setf (world-accts w) saved)
             (reset-tx-state))))))))      ; the native storage path back on the world's own table

(defun sim-check ()
  (unless *simulating* (error "outside eita:simulate")))

(defun eita:sim-tx (&key from to (data #()) (value 0) (gas 1000000) (tip 0) (fund t) block)
  "Run a transaction from FROM (an address with no code) to TO in the current simulation,
   on the replay's own transaction path, at the next block's context (BLOCK, a block-ctx
   plist; default the newest block's, numbered one above it): its nonce is FROM's, its fee
   the base fee plus TIP per gas; FUND tops FROM's balance up to what the transaction can
   cost. Its effects stay in the overlay for the next transactions of the simulation.
   Returns (:status 1|0 :gas-used n :egp wei :output octets :logs ((address topics data)…)),
   or (:status :invalid :why text) for a transaction the rules reject."
  (sim-check)
  (let* ((w *current-world*) (ctx (or block *sim-block*)) (base (or (getf ctx :base-fee) 0))
         (nonce (progn (fault-account! from) (nonce-of w from)))
         (tx (make-tx :type 2 :sender from :to to :nonce nonce :gas-limit gas :max-fee (+ base tip)
                      :max-priority tip :value value :data data :chain-id (getf ctx :chain-id))))
    (unless ctx (error "eita:sim-tx: no block context (no block was run)"))
    (when fund
      (let ((need (+ value (* gas (+ base tip)))))
        (when (< (balance-of w from) need) (setf (balance-of w from) need))))
    (handler-case
        (multiple-value-bind (gas-used status egp)
            (if eita.chain::*chain-run-tx-hook*
                (funcall eita.chain::*chain-run-tx-hook* w tx nil ctx (getf ctx :coinbase) (getf ctx :number) 0)
                (run-evm-tx w tx ctx (getf ctx :coinbase) (getf ctx :number) 0))
          (list :status status :gas-used gas-used :egp egp :output *last-tx-output*
                :logs (if (eql status 1) (reverse *last-tx-logs*) '())))
      (block-invalid (e) (list :status :invalid :why (princ-to-string e))))))

(defun eita:sim-read (kind addr &optional slot)
  "In the current simulation: ADDR's :balance, :nonce, :code or :storage SLOT."
  (sim-check)
  (let ((w *current-world*))
    (ecase kind
      (:balance (fault-account! addr) (balance-of w addr))
      (:nonce (fault-account! addr) (nonce-of w addr))
      (:code (fault-account! addr) (code-of w addr))
      (:storage (fault-account! addr) (fault-slot! addr slot) (eita.state:world-storage-get w addr slot)))))

(defun eita:sim-set (kind addr &rest args)
  "In the current simulation, an eth_call state override: (eita:sim-set :balance ADDR V),
   :nonce, :code (octets), or (eita:sim-set :storage ADDR SLOT V). Returns the value set."
  (sim-check)
  (let ((w *current-world*))
    (fault-account! addr)
    (ecase kind
      (:balance (setf (balance-of w addr) (first args)))
      (:nonce (setf (nonce-of w addr) (first args)))
      (:code (setf (code-of w addr) (first args)))
      (:storage (destructuring-bind (slot v) args
                  (fault-slot! addr slot)
                  (eita.state:world-storage-set w addr slot v)
                  v)))))

(defun eita:sim-slots-read (fn)
  "Call FN in the current simulation and return (values FN's value READS): what it read for
   the first time in the overlay, oldest first, each (addr . slot) for a storage slot or
   (addr . :account) for an account's balance, nonce and code. In a fresh overlay every
   first read is a fault, so this is FN's read set: where a contract keeps a value
   (whatever its layout), and which state changes can change FN's result."
  (sim-check)
  (let* ((slot-hook eita.state::*fault-slot-hook*) (acct-hook eita.state::*fault-account-hook*) (seen '())
         (v (let ((eita.state::*fault-slot-hook* (lambda (addr slot) (push (cons addr slot) seen) (funcall slot-hook addr slot)))
                  (eita.state::*fault-account-hook* (lambda (addr) (push (cons addr :account) seen) (funcall acct-hook addr))))
              (funcall fn))))
    (values v (nreverse seen))))
