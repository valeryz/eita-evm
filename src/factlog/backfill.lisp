;;;; factlog/backfill.lisp — past blocks from the fact log to the subscriptions (docs/hooks.md,
;;;; "Querying history"): the records a replay delivers, rebuilt from the facts, through the
;;;; hooks' own delivery (evm/hooks.lisp `hooks-deliver`), so a subscription folds a past range
;;;; without executing it and then follows a replay from the next block.

(in-package #:eita.evm)

(defun factlog-cursor (path kind)
  "A function of N returning the rows of block N in the rows file PATH (blocks asked in
   increasing order), decoding one group at a time: memory is a group, not a shard."
  (let* ((binary (string= (pathname-type path) "fct"))
         (buf (and binary (eita-factlog::read-file-bytes path)))
         (rows (unless binary (eita-factlog:read-shard path kind)))
         (off 0))
    (lambda (n)
      (let ((out '()))
        (loop
          (when (and (null rows) binary off)
            (multiple-value-bind (columns next) (eita-factlog::decode-group buf off kind)
              (if (or (null columns) (eq columns :index))
                  (setf off nil)
                  (setf rows (eita-factlog::columns->rows columns) off next))))
          (cond ((null rows) (return))
                ((< (first (first rows)) n) (pop rows))
                ((= (first (first rows)) n) (push (pop rows) out))
                (t (return))))
        (nreverse out)))))

(defun factlog-committed (dir)
  (with-open-file (in (merge-pathnames "committed" (eita-factlog::as-dir dir)) :if-does-not-exist nil)
    (and in (ignore-errors (parse-integer (read-line in nil ""))))))

(defun factlog-block-records (n block-row rows-of)
  "The block record and the tx and system records of block N, as the hooks observer captures
   them (`hooks-tx-record`), from its rows: ROWS-OF maps a kind to the block's rows. The facts
   carry no block hash, parent hash, tx nonce or gas limit: those fields are NIL. Within a tx
   the changes are in key order (the fact log's), accounts before storage."
  (let ((recs (make-hash-table)) (log-index 0))
    (flet ((rec (tx)
             (or (gethash tx recs)
                 (setf (gethash tx recs)
                       (list :block n :index (cond ((< eita.chain:+preblock-tx+ tx eita.chain:+postblock-tx+) tx)
                                                   ((= tx eita.chain:+preblock-tx+) :pre-block)
                                                   (t :post-block))
                             :logs '() :transfers '() :changes '()))))
           (idx (tx) (cond ((< eita.chain:+preblock-tx+ tx eita.chain:+postblock-tx+) tx)
                           ((= tx eita.chain:+preblock-tx+) :pre-block)
                           (t :post-block))))
      (macrolet ((add (tx field x) `(let ((r (rec ,tx))) (push ,x (getf r ,field)) (setf (gethash ,tx recs) r))))
        (dolist (row (funcall rows-of :transfer))
          (destructuring-bind (b tx kind depth from to value) row
            (add tx :transfers (list :block b :tx (idx tx) :kind (svref +transfer-kinds+ kind) :depth depth
                                     :from from :to to :value value))))
        (dolist (row (funcall rows-of :log))   ; in execution order, as the rows are
          (destructuring-bind (b tx i addr topics data) row
            (declare (ignore i))
            (let ((user (< eita.chain:+preblock-tx+ tx eita.chain:+postblock-tx+)))
              (add tx :logs (list :block b :tx (idx tx) :index (and user (prog1 log-index (incf log-index)))
                                  :address addr :topics topics :data (eita-factlog::hex->bytes data))))))
        (dolist (row (funcall rows-of :account_diff))
          (destructuring-bind (b tx addr n0 n1 b0 b1 h0 h1) row
            (unless (= b0 b1) (add tx :changes (list :block b :tx (idx tx) :kind :balance :address addr :pre b0 :post b1)))
            (unless (= n0 n1) (add tx :changes (list :block b :tx (idx tx) :kind :nonce :address addr :pre n0 :post n1)))
            (unless (= h0 h1) (add tx :changes (list :block b :tx (idx tx) :kind :code :address addr :pre h0 :post h1)))))
        (dolist (row (funcall rows-of :storage_diff))
          (destructuring-bind (b tx addr slot pre post) row
            (add tx :changes (list :block b :tx (idx tx) :kind :storage :address addr :slot slot :pre pre :post post))))
        (dolist (row (funcall rows-of :tx))
          (destructuring-bind (b tx hash from to value type gas-used status egp) row
            (declare (ignore b))
            (setf (gethash tx recs)
                  (list* :hash hash :type type :from from :to to :value value :nonce nil :gas-limit nil
                         :gas-used gas-used :status status :gas-price egp (rec tx)))))))
    (values
     (destructuring-bind (b timestamp coinbase base-fee gas-used gas-limit &rest more) block-row
       (declare (ignore b more))
       (list :number n :hash nil :parent-hash nil :timestamp timestamp :coinbase coinbase
             :base-fee base-fee :gas-limit gas-limit :gas-used gas-used))
     (loop for tx in (sort (loop for k being the hash-keys of recs collect k) #'<)
           collect (let ((r (gethash tx recs)))
                     (dolist (f '(:logs :transfers :changes) r)
                       (setf (getf r f) (reverse (getf r f)))))))))

(defun eita:backfill (dir from to)
  "Deliver blocks FROM..TO of the fact log at DIR to the subscriptions, with the records a
   replay delivers (docs/hooks.md), without executing them: a subscription's handlers fold the
   range, and a replay from TO+1 then continues it (no second :start). Call it while no
   replay runs. Blocks past the log's `committed` marker, or missing from it, signal an error.
   Returns the number of blocks delivered."
  (let ((committed (factlog-committed dir)) (count 0) (ranges (eita-factlog:shard-ranges dir :block)))
    (unless (and committed (<= to committed))
      (error "backfill: block ~D is past the fact log's committed block ~A" to committed))
    (unless (loop for r in ranges thereis (<= (first r) from (second r)))
      (error "backfill: block ~D is not in the fact log at ~A" from dir))
    (dolist (r ranges)
      (destructuring-bind (lo hi block-path) r
        (when (and (<= lo to) (>= hi from))
          (let ((cursors (loop for kind in '(:block :tx :log :transfer :account_diff :storage_diff)
                               for path = (if (eq kind :block) block-path (eita-factlog:rows-file dir kind lo hi))
                               collect (cons kind (and path (factlog-cursor path kind))))))
            (loop for n from (max lo from) to (min hi to)
                  do (let ((rows (loop for (kind . c) in cursors collect (cons kind (and c (funcall c n))))))
                       (flet ((rows-of (kind) (cdr (assoc kind rows))))
                         (let ((block-row (first (rows-of :block))))
                           (unless block-row (error "backfill: block ~D is not in the fact log at ~A" n dir))
                           (multiple-value-bind (header recs) (factlog-block-records n block-row #'rows-of)
                             (hooks-deliver header recs))
                           (incf count)))))))))
    count))
