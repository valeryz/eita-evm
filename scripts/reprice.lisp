;;;; scripts/reprice.lisp — counterfactual re-costing: history executed exactly as it
;;;; happened, every charge whose price EIP-8037/8038 changes priced a second time under
;;;; Amsterdam's schedule. An observer (`--observer scripts/reprice.lisp`); nothing in the
;;;; replay is re-decided and the header gate still checks every block.
;;;;
;;;;   REPRICE_OUT=<dir> bin/eita-node … replay --chain ethereum --lazy --from A --to B \
;;;;     --source … --observer core/scripts/reprice.lisp
;;;;   (REPRICE_TX_TSV=1 also writes one line per tx; REPRICE_TOP=N rows per table, 50)
;;;;
;;;; PRICES: both schedules come from scripts/generated/reprice-amsterdam.lisp (lake exe
;;;; emitRepriceCL; Evm.CL.RepriceEmit proves each term equal to its spec — Osaka's
;;;; schedule, and EIP-8037/8038 from EELS 636b5f1 in Evm.Amsterdam.Vm.Gas/StatePricing).
;;;; This file only observes and adds up.
;;;;
;;;; WHERE IT LOOKS (no production code changes; `sb-int:encapsulate` on the replay's own
;;;; charge points, active only in a process that loads this file):
;;;;   SSTORE        the storage view's write stream (a reads subscriber turns it on): each
;;;;                 changing SSTORE as (current → new); the slot's tx-start value is the
;;;;                 `current` of its first change in the tx (journal restores and CREATE
;;;;                 wipes are not SSTOREs and are skipped). Warmth: the slot's earlier
;;;;                 reads, writes and access-list entry in the tx, NOT revert-scoped (a
;;;;                 slot first read in a reverted frame counts warm: 100 too little).
;;;;   BALANCE/EXT*  addr-access-gas (warmth decoded from the Osaka price it returns)
;;;;   CALL family   call-gas-plan (cold, value, new account, delegate access) inside
;;;;                 spec-call-effect (whether the child succeeded)
;;;;   CREATE*       spec-create-effect (destination alive before; outcome; deployed length)
;;;;   SELFDESTRUCT  spec-selfdestruct-effect (cold, new account, decoded from its price)
;;;;   the tx        apply-tx (value/creation to a non-alive account, delegated target,
;;;;                 access list, creation code), spec-tx-gas-used (the real pre-refund
;;;;                 gas, refund counter and floor)
;;;; and resolves each charge at tx end against the tx's call frames (EIP-8037's rules):
;;;;   * state gas is kept iff its frame and every ancestor returned (a revert or halt
;;;;     refills it), and for CALL/CREATE's NEW_ACCOUNT iff the child succeeded;
;;;;   * refund-counter moves are kept on the same rule (EELS drops a failed frame's);
;;;;   * an execution-gas difference counts unless a frame on its chain halted: a halted
;;;;     frame burns its whole grant under either schedule ("absorbed", reported apart).
;;;; The repriced tx gas is then settle_transaction_gas over (real pre-refund gas + counted
;;;; execution differences + kept state gas), the repriced refund counter, the real floor.
;;;;
;;;; SCOPE: EIP-8037/8038 only, on top of Osaka. Not applied: EIP-2780 (intrinsic
;;;; restructuring; a creation tx's 32000 is priced as CREATE_ACCESS, the 21000 base kept),
;;;; EIP-7976/7981 floors, EIP-7778 block accounting, EIP-7928 BAL item costs. EIP-7702
;;;; authorisations are NOT repriced (their txs are counted and flagged). The code deposit
;;;; is attributed to the creating contract (EELS charges it in the init frame).

(in-package #:eita.evm)

(load (merge-pathnames "generated/reprice-amsterdam.lisp" (or *load-truename* *default-pathname-defaults*)))

;;; --- per tx --------------------------------------------------------------------------
;;; A charge: #(frame class osaka-exec ams-exec ams-state ams-credit d-refund-osaka d-refund-ams ok)
;;; OK nil = a condition beyond the frame chain failed (NEW_ACCOUNT of a failed child).
(defvar *rp-charges* (make-array 64 :adjustable t :fill-pointer 0))
(defvar *rp-orig* (make-hash-table :test 'equal) "(addr . slot) -> tx-start value, this tx")
(defvar *rp-restoring* nil)
(defvar *rp-call* nil "The innermost CALL's plan inputs: #(cold vf na deleg) once planned.")
(defvar *rp-settle* nil "(before refund floor) of this tx, from spec-tx-gas-used.")
(defvar *rp-pending* nil "This tx's result, finished at tx-result (which knows the limit).")
(defvar *rp-active* nil "True inside a user tx (between apply-tx and its tx-end).")

(defun rp-b (x) (if x 1 0))

(defun rp-charge! (class osaka ams-exec &key (state 0) (credit 0) (dro 0) (dra 0) (ok t))
  (when *rp-active*
    (vector-push-extend (vector *obs-frame* class osaka ams-exec state credit dro dra ok) *rp-charges*)))

;;; --- the charge points -----------------------------------------------------------------
(defvar *rp-reads* (make-hash-table :test 'equal)
  "(addr . slot) -> storage-view reads of the slot this tx, or :warm once accessed by an
   SSTORE or listed in the access list. The view reads a slot once per SLOAD and per no-op
   SSTORE, twice before a changing SSTORE's write: a changing SSTORE found the slot warm iff
   it had more than those two.")

(defun rp-sstore! (addr slot cur new)
  (let* ((k (cons addr slot))
         (orig (multiple-value-bind (v hit) (gethash k *rp-orig*)
                 (if hit v (setf (gethash k *rp-orig*) cur))))
         (seen (gethash k *rp-reads* 0))
         (cold (and (integerp seen) (<= seen 2)))
         (f (list (rp-b cold) (rp-b (= new cur)) (rp-b (= cur orig)) (rp-b (= new orig))
                  (rp-b (zerop orig)) (rp-b (zerop cur)) (rp-b (zerop new)))))
    (setf (gethash k *rp-reads*) :warm)
    (rp-charge! :sstore (apply #'rp-osaka-sstore-cost f) (apply #'rp-ams-sstore-execution f)
                :state (apply #'rp-ams-sstore-state f) :credit (apply #'rp-ams-sstore-state-credit f)
                :dro (- (apply #'rp-osaka-sstore-refund-add f) (apply #'rp-osaka-sstore-refund-sub f))
                :dra (- (apply #'rp-ams-sstore-refund-add f) (apply #'rp-ams-sstore-refund-sub f)))))

(defmacro rp-wrap (name (f &rest args) &body body)
  `(sb-int:encapsulate ',name 'reprice (lambda (,f ,@args) ,@body)))

(rp-wrap eita.state::view-log-read (f kind addr slot value)
  (declare (ignore f))                       ; no event: only the slot reads are counted
  (when (and (eq kind :storage) *rp-active* (not *rp-restoring*))
    (let ((k (cons addr (word-int slot))))
      (let ((n (gethash k *rp-reads* 0))) (when (integerp n) (setf (gethash k *rp-reads*) (1+ n))))))
  value)
(rp-wrap eita.state::view-log-write (f kind addr slot pre post)
  (declare (ignore f))
  (when (and (eq kind :storage) (not *rp-restoring*) (/= pre post))
    (rp-sstore! addr (word-int slot) pre post)))
(rp-wrap revert-journal-to (f &rest a) (let ((*rp-restoring* t)) (apply f a)))
(rp-wrap storage-wipe-journaled! (f &rest a) (let ((*rp-restoring* t)) (apply f a)))

(rp-wrap addr-access-gas (f addr kind)
  (let ((g (funcall f addr kind)))
    (let ((cold (/= g (rp-osaka-account-access 0))))   ; Osaka's warm price = warm
      (rp-charge! (if (= kind 2) :extcode :account-access) (rp-osaka-account-access (rp-b cold))
                  (rp-ams-account-access (rp-b cold) (rp-b (= kind 2)))))
    g))

(rp-wrap call-gas-plan (f cold vf na deleg gas-arg avail)
  (when *rp-call* (setf (car *rp-call*) (vector cold vf na deleg)))
  (funcall f cold vf na deleg gas-arg avail))

(rp-wrap spec-call-effect (f &rest args)
  (let ((cell (list nil)))
    (multiple-value-bind (gas out rd) (let ((*rp-call* cell)) (apply f args))
      (let ((p (car cell)))
        (when p
          (let* ((cold (svref p 0)) (vf (svref p 1)) (na (svref p 2)) (deleg (svref p 3)))
            (rp-charge! (cond (na :call-new-account) (vf :call-value) (t :call-access))
                        (rp-osaka-call-charge (rp-b cold) (rp-b vf) (rp-b na) deleg)
                        (rp-ams-call-execution (rp-b cold) (rp-b vf) (rp-b (plusp deleg)) (rp-b (= deleg (spec-delegate-access-gas 1))))
                        :state (rp-ams-call-state (rp-b na)) :ok (eql out 1)))))
      (values gas out rd))))

(rp-wrap spec-create-effect (f self new value gas base &rest more)
  (let ((alive (not (world-account-empty-p new))))
    (multiple-value-bind (g out rd) (apply f self new value gas base more)
      (when (>= gas base)              ; else the creating frame ran out of gas on the charge
        (rp-charge! :create (rp-osaka-create-flat) (rp-ams-create-execution)
                    :state (rp-ams-create-state (rp-b alive)) :ok (/= out 0))
        (when (/= out 0)
          (let ((n (length (code-of *current-world* new))))
            (rp-charge! :code-deposit (rp-osaka-code-deposit n) (rp-ams-code-deposit-execution n)
                        :state (rp-ams-code-deposit-state n)))))
      (values g out rd))))

(rp-wrap spec-selfdestruct-effect (f self beneficiary)
  ;; its price is (spec-selfdestruct-cold-gas cold) + (spec-new-account-fee if new)
  (let* ((g (funcall f self beneficiary)) (na (>= g (spec-new-account-fee)))
         (cold (plusp (- g (if na (spec-new-account-fee) 0)))))
    (rp-charge! :selfdestruct (rp-osaka-selfdestruct (rp-b cold) (rp-b na))
                (rp-ams-selfdestruct-execution (rp-b cold) (rp-b na))
                :state (rp-ams-selfdestruct-state (rp-b na)))
    g))

(rp-wrap spec-tx-gas-used (f gas-used refund zero nz fork)
  (setf *rp-settle* (list gas-used refund (spec-calldata-floor-gas zero nz fork)))
  (funcall f gas-used refund zero nz fork))

(defvar *rp-tx-info* nil "#(to-or-created type4) of the tx being applied.")
(rp-wrap apply-tx (f tx coinbase block-ctx &rest keys)
  (setf (fill-pointer *rp-charges*) 0 *rp-settle* nil *rp-active* t)
  (clrhash *rp-orig*) (clrhash *rp-reads*)
  (dolist (e (tx-access-list tx))
    (dolist (key (cdr e)) (setf (gethash (cons (car e) key) *rp-reads*) :warm)))
  (let* ((from (tx-sender tx)) (to (tx-to tx)) (value (tx-value tx))
         (target (or to (progn (fault-account! from) (derive-create-address from (nonce-of *current-world* from)))))
         (dead (world-account-empty-p target))
         (deleg (and to (delegation-target (code-of *current-world* to)))))
    (setf *rp-tx-info* (vector target (eql (tx-type tx) 4)))
    (multiple-value-bind (zero nz al-addrs al-keys) (calldata-byte-counts tx)
      (declare (ignore zero nz))
      (let ((*obs-frame* -1))
        (when (or (plusp al-addrs) (plusp al-keys))
          (rp-charge! :tx-access-list (rp-osaka-access-list al-addrs al-keys) (rp-ams-access-list al-addrs al-keys)))
        (when deleg
          (let ((warm (or (= deleg from) (= deleg to) (= deleg coinbase) (precompile-address-p deleg)
                          (assoc deleg (tx-access-list tx)))))
            (rp-charge! :tx-delegation 0 (rp-ams-top-level-delegation 1 (rp-b (not warm))))))
        (when (null to)
          (rp-charge! :tx-create (rp-osaka-create-flat) (rp-ams-create-execution)))
        (when (or (null to) (plusp value))
          (rp-charge! :tx-new-account 0 0 :state (rp-ams-top-level-state (rp-b dead)))))
      (multiple-value-bind (ok used rej) (apply f tx coinbase block-ctx keys)
        (when (and ok (null to))
          (let ((n (length (code-of *current-world* target))) (*obs-frame* -1))
            (rp-charge! :code-deposit (rp-osaka-code-deposit n) (rp-ams-code-deposit-execution n)
                        :state (rp-ams-code-deposit-state n))))
        (values ok used rej)))))

;;; --- tx end: resolve, aggregate ----------------------------------------------------------
(defun rp-zero () (make-array 6 :initial-element 0))
(defvar *rp-contracts* (make-hash-table :test 'eql)
  "ctx address -> #(real-self-gas d-exec state charges frames d-exec-absorbed)")
(defvar *rp-classes* (make-hash-table :test 'eq) "class -> #(osaka ams-exec ams-state n absorbed-d refilled-state)")
(defvar *rp-totals* (make-hash-table :test 'eq))
(defvar *rp-hist* (make-hash-table :test 'eql) "ratio bucket -> #(txs real repriced)")
(defvar *rp-top-ratio* '()) (defvar *rp-top-abs* '())
(defvar *rp-tx-out* nil)
(defvar *rp-mismatches* '() "The first refund self-check failures: (block tx replay-refund tally status).")
(defun rp-tot (k &optional (d 1)) (incf (gethash k *rp-totals* 0) d))

(defun rp-keep-top (place row key n)
  (let ((l (merge 'list (list row) place #'> :key key)))
    (if (> (length l) n) (subseq l 0 n) l)))

(defun rp-tx-end (block tx success)
  (when (and *rp-active* (integerp tx) (<= 0 tx) (< tx +postblock-tx+))
    (setf *rp-active* nil)
    (let* ((nf *obs-frame-next*)
           (parent (make-array nf)) (status (make-array nf)) (ctx (make-array nf)) (used (make-array nf))
           (self (make-array nf :initial-element 0)))
      (do-call-frames (fr pa dep kind from to v sel il g gu st)
        (declare (ignore dep v sel il g))
        (setf (aref parent fr) pa (aref status fr) st (aref used fr) (or gu 0)
              (aref ctx fr) (if (member kind '(1 2)) from to)))
      (dotimes (fr nf)
        (incf (aref self fr) (aref used fr))
        (let ((pa (aref parent fr))) (when (>= pa 0) (decf (aref self pa) (aref used fr)))))
      (flet ((chain (fr)                       ; (values all-returned any-halted)
               (if (< fr 0)
                   (values success (and (> nf 0) (eql (aref status 0) 2)))
                   (loop with ok = success and halted = nil
                         for k = fr then (aref parent k) while (>= k 0)
                         do (case (aref status k) (0) (2 (setf ok nil halted t)) (t (setf ok nil)))
                         finally (return (values ok halted)))))
             (contract (fr) (cond ((>= fr 0) (aref ctx fr)) ((> nf 0) (aref ctx 0)) (t (svref *rp-tx-info* 0)))))
        (dotimes (fr nf)
          (let ((c (or (gethash (aref ctx fr) *rp-contracts*) (setf (gethash (aref ctx fr) *rp-contracts*) (rp-zero)))))
            (incf (svref c 0) (max 0 (aref self fr))) (incf (svref c 4))))
        (let ((dexec 0) (state 0) (dro 0) (dra 0) (absorbed 0))
          (loop for ch across *rp-charges*
                do (destructuring-bind (fr class osaka ams st cr ro ra ok) (coerce ch 'list)
                     (multiple-value-bind (kept halted) (chain fr)
                       (let* ((kst (and kept ok)) (d (- ams osaka))
                              (cl (or (gethash class *rp-classes*) (setf (gethash class *rp-classes*) (rp-zero))))
                              (c (let ((a (contract fr))) (or (gethash a *rp-contracts*) (setf (gethash a *rp-contracts*) (rp-zero))))))
                         (incf (svref cl 3)) (incf (svref c 3))
                         (if halted
                             (progn (incf absorbed d) (incf (svref cl 4) d) (incf (svref c 5) d))
                             (progn (incf dexec d) (incf (svref cl 0) osaka) (incf (svref cl 1) ams) (incf (svref c 1) d)))
                         (if (and kept (if (eq class :sstore) t kst))
                             (let ((s (- (if kst st 0) cr)))   ; a credit needs only the chain
                               (incf state s) (incf (svref cl 2) s) (incf (svref c 2) s))
                             (incf (svref cl 5) st))
                         (when kept (incf dro ro) (incf dra ra))))))
          (setf *rp-pending* (list block tx dexec state dro dra absorbed *rp-settle* (svref *rp-tx-info* 1)
                                   (contract -1))))))
    (setf (fill-pointer *rp-charges*) 0)))

(defun rp-tx-result (n idx tx gas status egp)
  (declare (ignore egp))
  (let ((p *rp-pending*))
    (setf *rp-pending* nil)
    (when (and p (eql (first p) n) (eql (second p) idx) (integerp gas))
      (destructuring-bind (b i dexec state dro dra absorbed settle type4 to) p
        (declare (ignore b i))
        (rp-tot :txs) (rp-tot :real-gas gas) (rp-tot :d-exec dexec) (rp-tot :state-gas state)
        (rp-tot :absorbed absorbed)
        (when type4 (rp-tot :type4-txs))
        (if (null settle)
            (rp-tot :no-settle)
            (destructuring-bind (before refund floor) settle
              ;; the replay's refund counter vs this file's Osaka tally (SSTORE only; 7702
              ;; refunds are not tallied): the per-tx check that every SSTORE was seen
              (unless (or type4 (= refund dro))
                (rp-tot :refund-check-mismatch)
                (when (< (length *rp-mismatches*) 20) (push (list n idx refund dro status) *rp-mismatches*)))
              (let* ((before2 (max 0 (+ before dexec state)))
                     (refund2 (max 0 (+ refund (- dra dro))))
                     (gas2 (rp-ams-tx-gas-used before2 refund2 floor))
                     (limit (tx-gas-limit tx))
                     (ratio (if (plusp gas) (/ gas2 gas) 1))
                     (bucket (cond ((< ratio 0.5) 0.5) ((< ratio 0.9) 0.9) ((< ratio 0.99) 0.99) ((<= ratio 1.01) 1.0)
                                   ((< ratio 1.1) 1.1) ((< ratio 1.5) 1.5) ((< ratio 2) 2) ((< ratio 3) 3) ((< ratio 5) 5)
                                   ((< ratio 10) 10) (t 1000)))
                     (h (or (gethash bucket *rp-hist*) (setf (gethash bucket *rp-hist*) (rp-zero)))))
                (incf (svref h 0)) (incf (svref h 1) gas) (incf (svref h 2) gas2)
                (rp-tot :repriced-gas gas2) (rp-tot :refund-real (min refund (floor before 5)))
                (when (> before2 limit) (rp-tot :over-gas-limit))
                (when (> (- before2 state) (spec-tx-max-gas-limit)) (rp-tot :exec-over-tx-max))
                (let ((row (list n idx to gas gas2 dexec state status)))
                  (setf *rp-top-ratio* (rp-keep-top *rp-top-ratio* row (lambda (r) (/ (fifth r) (max 1 (fourth r)))) 30)
                        *rp-top-abs* (rp-keep-top *rp-top-abs* row (lambda (r) (- (fifth r) (fourth r))) 30)))
                (when *rp-tx-out*
                  (format *rp-tx-out* "~D	~D	~(~40,'0x~)	~D	~D	~D	~D	~D	~D	~D~%"
                          n idx (or to 0) gas gas2 dexec state (- dra dro) status (if type4 1 0))))))))))

;;; --- report ------------------------------------------------------------------------------
(defun rp-out (name) (concatenate 'string (or (nonempty-env "REPRICE_OUT") "reprice-out") "/" name))
(defun rp-report ()
  (ensure-directories-exist (rp-out "x"))
  (let ((top (let ((s (nonempty-env "REPRICE_TOP"))) (if s (parse-integer s) 50)))
        (rows '()))
    (maphash (lambda (a v) (push (cons a v) rows)) *rp-contracts*)
    (with-open-file (o (rp-out "contracts.tsv") :direction :output :if-exists :supersede)
      (format o "contract	real_self_gas	d_exec	state_gas	repriced	ratio	charges	frames	d_exec_absorbed~%")
      (dolist (r (sort (copy-list rows) #'> :key (lambda (r) (+ (svref (cdr r) 1) (svref (cdr r) 2)))))
        (let* ((v (cdr r)) (real (svref v 0)) (rep (+ real (svref v 1) (svref v 2))))
          (format o "~(~40,'0x~)	~D	~D	~D	~D	~,4F	~D	~D	~D~%" (car r) real (svref v 1) (svref v 2) rep
                  (if (plusp real) (/ rep real) 0) (svref v 3) (svref v 4) (svref v 5)))))
    (with-open-file (o (rp-out "summary.txt") :direction :output :if-exists :supersede)
      (let* ((g (lambda (k) (gethash k *rp-totals* 0))) (real (funcall g :real-gas)) (rep (funcall g :repriced-gas)))
        (format o "Re-costing under EIP-8037/8038 (EELS 636b5f1), engine ~A~%schedule ~S~%~%" (engine-code-version) *rp-schedule*)
        (format o "txs ~D (7702 txs ~D, not repriced for their authorisations)~%real gas ~:D~%repriced gas ~:D (x~,4F)~%"
                (funcall g :txs) (funcall g :type4-txs) real rep (if (plusp real) (/ rep real) 0))
        (format o "  execution-gas difference counted ~:D, absorbed by halted frames ~:D~%  state gas kept ~:D (~,2F % of repriced gas)~%"
                (funcall g :d-exec) (funcall g :absorbed) (funcall g :state-gas) (if (plusp rep) (* 100 (/ (funcall g :state-gas) rep)) 0))
        (format o "txs whose repriced pre-refund gas exceeds their gas limit ~D; whose execution gas exceeds TX_MAX_GAS_LIMIT ~D~%"
                (funcall g :over-gas-limit) (funcall g :exec-over-tx-max))
        (format o "self-checks: refund counter vs this tool's Osaka SSTORE tally, mismatching txs ~D; txs without settlement ~D~%~%"
                (funcall g :refund-check-mismatch) (funcall g :no-settle))
        (when *rp-mismatches* (format o "  first mismatches (block tx replay tally status): ~S~%~%" (reverse *rp-mismatches*)))
        (format o "by cost class (counted charges):~%~16A ~10@A ~16@A ~16@A ~16@A ~14@A ~14@A~%"
                "class" "n" "osaka" "ams-exec" "ams-state" "absorbed-d" "refilled-st")
        (let ((cls '())) (maphash (lambda (k v) (push (cons k v) cls)) *rp-classes*)
          (dolist (c (sort cls #'> :key (lambda (c) (+ (svref (cdr c) 1) (svref (cdr c) 2)))))
            (let ((v (cdr c)))
              (format o "~16A ~10D ~16:D ~16:D ~16:D ~14:D ~14:D~%" (string-downcase (car c)) (svref v 3) (svref v 0) (svref v 1)
                      (svref v 2) (svref v 4) (svref v 5)))))
        (format o "~%per-tx distribution of repriced/real gas:~%~10A ~10@A ~20@A ~20@A~%" "ratio<" "txs" "real" "repriced")
        (let ((hs '())) (maphash (lambda (k v) (push (cons k v) hs)) *rp-hist*)
          (dolist (h (sort hs #'< :key #'car))
            (format o "~10A ~10D ~20:D ~20:D~%" (car h) (svref (cdr h) 0) (svref (cdr h) 1) (svref (cdr h) 2))))
        (flet ((contracts (title key pred)
                 (format o "~%~A~%~42A ~14@A ~14@A ~14@A ~8@A ~8@A~%" title "contract" "real-self" "repriced" "increase" "ratio" "frames")
                 (dolist (r (subseq (sort (remove-if-not pred rows) #'> :key key) 0 (min top (count-if pred rows))))
                   (let* ((v (cdr r)) (real (svref v 0)) (rep (+ real (svref v 1) (svref v 2))))
                     (format o "0x~(~40,'0x~) ~14:D ~14:D ~14:D ~8,3F ~8D~%" (car r) real rep (- rep real)
                             (if (plusp real) (/ rep real) 0) (svref v 4))))))
          (contracts "top contracts by absolute increase:" (lambda (r) (+ (svref (cdr r) 1) (svref (cdr r) 2))) (constantly t))
          (contracts "top contracts by repriced/real (real self gas >= 10M):"
                     (lambda (r) (let ((v (cdr r))) (/ (+ (svref v 0) (svref v 1) (svref v 2)) (max 1 (svref v 0)))))
                     (lambda (r) (>= (svref (cdr r) 0) 10000000))))
        (flet ((txs (title l)
                 (format o "~%~A~%~10A ~4A ~42A ~10@A ~10@A ~10@A ~10@A ~3A~%" title "block" "tx" "to/created" "real" "repriced" "d-exec" "state" "st")
                 (dolist (r l)
                   (destructuring-bind (n i to gas gas2 dx st status) r
                     (format o "~10D ~4D 0x~(~40,'0x~) ~10D ~10D ~10D ~10D ~3D~%" n i (or to 0) gas gas2 dx st status)))))
          (txs "top txs by ratio:" *rp-top-ratio*)
          (txs "top txs by absolute increase:" *rp-top-abs*))))
    (when *rp-tx-out* (finish-output *rp-tx-out*))
    (format t "~&[reprice] report in ~A~%" (rp-out ""))))

;;; --- install -----------------------------------------------------------------------------
;; The subscribers attach lazily (check-subscribers, after the first block has run): turn the
;; write stream on now so the first block's SSTOREs are seen too. Its events go nowhere (the
;; two view-log functions are wrapped above), the attach below keeps it on.
(setf *observe-calls* t *capture-reads* t)
(setf eita.state:*observer*
      (make-observer
       :name "reprice-8037-8038"
       :attach (lambda ()
                 (when (nonempty-env "REPRICE_TX_TSV")
                   (ensure-directories-exist (rp-out "x"))
                   (setf *rp-tx-out* (open (rp-out "txs.tsv") :direction :output :if-exists :supersede))
                   (format *rp-tx-out* "block	tx	to	real_gas	repriced_gas	d_exec	state_gas	d_refund	status	type4~%"))
                 ;; a reads subscriber turns the storage view's write stream on (SSTOREs)
                 (attach-subscriber! "reprice-reads" (lambda (ev) ev) :wants-reads t
                                                     :on-finalize #'rp-report))
       :tx-end #'rp-tx-end
       :tx-result #'rp-tx-result))
