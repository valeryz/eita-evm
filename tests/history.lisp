;;;; tests/history.lisp — the fact log (src/factlog/) and the history examples of docs/hooks.md and
;;;; docs/fact-log.md (examples/history/), on Eita's mainnet repro block
;;;; (tests/data/mainnet-24538111.json.gz, 756 txs). The block runs once with the writer on and
;;;; a subscription recording what the replay delivers; every question asked of the log is then
;;;; checked against those records:
;;;;   1. the writer sealed every table; one tx row per tx record, one log row per log record;
;;;;   2. state-at (state-at.lisp): each account's balance and nonce and each slot's value at the
;;;;      end of the block is the last change's post; before the block, the first change's pre;
;;;;   3. key-history (changes.lisp): a slot's and an account's changes are the records', in order;
;;;;   4. token-transfers.lisp: a token's Transfer logs are the records', also by address;
;;;;   5. daily.lisp: txs, gas, fees burnt and distinct senders are the records';
;;;;   6. backfill (backfill.lisp): the hook examples gas-per-block and transfers folded from the
;;;;      log reach the state the live run gave them, and the records match, field for field
;;;;      (the hashes and fields the log does not carry aside).

(defpackage #:eita.test.history (:use #:cl))
(in-package #:eita.test.history)

(defvar *fails* 0)
(defun fail (fmt &rest args) (incf *fails*) (format t "  FAIL: ~?~%" fmt args))
(defmacro check (form fmt &rest args) `(unless ,form (fail ,fmt ,@args)))

(defun example (dir name) (load (eita.test::home (format nil "examples/~A/~A.lisp" dir name))))
(defun clear () (dolist (s (eita:subscriptions)) (eita:unsubscribe (first s))))

(defvar *blocks* '())
(defun record! ()
  (setf *blocks* '())
  (eita:subscribe "record" :block (lambda (b) (push b *blocks*))))

;; the examples' packages exist before the forms below are read
(example "history" "state-at") (example "history" "changes") (example "history" "token-transfers")
(example "history" "daily") (example "history" "backfill")
(example "hooks" "gas-per-block") (example "hooks" "transfers")
(clear)

(defun stripped (r)
  "Record R without the fields a fact log does not carry, its changes as a set."
  (let ((r (copy-list r)))
    (dolist (k '(:hash :parent-hash :nonce :gas-limit)) (remf r k))
    (when (getf r :changes)
      (setf (getf r :changes) (sort (mapcar #'prin1-to-string (getf r :changes)) #'string<)))
    (when (getf r :txs) (setf (getf r :txs) (mapcar #'stripped (getf r :txs))))
    r))

(let* ((gz (eita.test::home "tests/data/mainnet-24538111.json.gz"))
       (json (format nil "/tmp/eita-test-history-~D.json" (sb-posix:getpid)))
       (dir (format nil "/tmp/eita-test-history-~D/" (sb-posix:getpid)))
       (n 24538111))
  (with-open-file (s json :direction :output :if-exists :supersede)
    (sb-ext:run-program "gzip" (list "-dc" gz) :search t :output s :error nil))
  (unwind-protect
       (progn
         ;; --- the block, once: the writer on, the records kept, the hook examples folding ---
         (eita.factlog.writer:install-factlog-observer! dir)
         (record!) (example "hooks" "gas-per-block") (example "hooks" "transfers")
         (hooks.gas::on-start 0) (hooks.transfers::on-start 0)   ; whatever an earlier suite left
         (let ((*standard-output* (make-broadcast-stream))) (eita.fixtures:main (list json)))
         (setf eita:*observer* nil)
         (let* ((live-gas (hooks.gas:summary)) (live-transfers (hooks.transfers:summary 5))
                (block (first *blocks*)) (txs (getf block :txs))
                (changes (loop for tx in txs append (getf tx :changes)))
                (logs (loop for tx in txs append (getf tx :logs)))
                (fl (eita-factlog:open-factlog dir)))
           (clear)
           (check (and block (= (getf block :number) n) (= 756 (length txs))) "the run delivered ~A" (getf block :number))
           ;; --- 1. the tables --------------------------------------------------------------
           (dolist (kind eita-factlog:+kinds+)
             (check (eita-factlog:footer-complete-p
                     (eita-factlog:read-footer (eita-factlog:shard-file dir kind 24538000 24538999 "sealed")) n n)
                    "~(~A~): no sealed shard covering block ~D" kind n))
           (check (= (length txs) (length (eita-factlog:fact-scan fl :tx n n))) "tx rows /= tx records")
           (check (= (length logs) (count-if (lambda (r) (< -1 (second r) 1000000000)) (eita-factlog:fact-scan fl :log n n)))
                  "log rows /= log records")
           ;; --- 2. state-at -------------------------------------------------------------------
           (let ((lasts (make-hash-table :test 'equal)) (firsts (make-hash-table :test 'equal)) (k 0))
             (dolist (c changes)
               (let ((key (list (getf c :kind) (getf c :address) (getf c :slot))))
                 (unless (gethash key firsts) (setf (gethash key firsts) (getf c :pre)))
                 (setf (gethash key lasts) (getf c :post))))
             ;; every 20th key: a lookup reads the shard, so the sample keeps the suite short
             (maphash
              (lambda (key post)
                (when (zerop (mod (incf k) 20))
                  (destructuring-bind (kind address slot) key
                    (flet ((at (b) (if (eq kind :storage)
                                       (eita-factlog:state-at dir :storage_diff (list address slot) b)
                                       (let ((a (history.state:account-at dir address b)))
                                         (if (eq a :unknown) a (getf a (if (eq kind :code) :code-hash kind)))))))
                      (check (eql post (at n)) "~A at ~D: ~A, the records say ~A" key n (at n) post)
                      (check (eql (gethash key firsts) (at (1- n))) "~A at ~D: ~A, the records say ~A"
                             key (1- n) (at (1- n)) (gethash key firsts))))))
              lasts)
             (format t "  state-at: ~D keys changed, every 20th looked up at ~D and ~D~%" k n (1- n)))
           ;; ERC-20 balances through their mapping slot: WETH9's balanceOf is at slot 3; the
           ;; holders are the parties of its Transfer logs
           (let* ((weth (eita:addr "0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"))
                  (holders (remove-duplicates (loop for l in logs when (and (eql (getf l :address) weth) (= 3 (length (getf l :topics))))
                                                     append (rest (getf l :topics)))))
                  (found 0))
             (dolist (h holders)
               (let ((post (getf (car (last (remove-if-not (lambda (c) (and (eql (getf c :address) weth)
                                                                            (eql (getf c :slot) (history.state:mapping-slot h 3))))
                                                           changes)))
                                 :post)))
                 (when post
                   (incf found)
                   (check (eql post (history.state:erc20-balance-at dir weth h n :slot 3)) "WETH balance of ~A" (eita:hex h)))))
             (check (plusp found) "no WETH balance slot among the changes")
             (format t "  state-at: ~D WETH9 balances through mapping-slot~%" found))
           ;; --- 3. key-history ----------------------------------------------------------------
           (flet ((hottest (kind)
                    (let ((counts (make-hash-table :test 'equal)))
                      (dolist (c changes) (when (eq (getf c :kind) kind) (incf (gethash (list (getf c :address) (getf c :slot)) counts 0))))
                      (let ((best nil) (m 0)) (maphash (lambda (k v) (when (> v m) (setf best k m v))) counts) best)))
                  (expected (kind address slot)
                    (loop for c in changes
                          when (and (eq (getf c :kind) kind) (eql (getf c :address) address) (eql (getf c :slot) slot))
                            collect (list :block (getf c :block) :tx (let ((tx (getf c :tx))) (case tx (:pre-block -1) (:post-block 1000000000) (t tx)))
                                          :pre (getf c :pre) :post (getf c :post)))))
             (destructuring-bind (address slot) (hottest :storage)
               (let ((got (history.changes:changes dir address (- n 10) n :slot slot)))
                 (check (equal got (expected :storage address slot)) "the history of slot ~A of ~A: ~S" slot (eita:hex address) got)
                 (format t "  key-history: slot of ~A changed ~D times in the block~%" (eita:hex address) (length got))))
             (destructuring-bind (address slot) (hottest :balance)
               (declare (ignore slot))
               (let ((got (history.changes:changes dir address n n :kind :balance)))
                 (check (equal got (expected :balance address nil)) "the balance history of ~A: ~S" (eita:hex address) got)
                 (format t "  key-history: balance of ~A changed ~D times~%" (eita:hex address) (length got)))))
           ;; --- 4. token transfers ---------------------------------------------------------------
           (let* ((topic #xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)
                  (erc20 (remove-if-not (lambda (l) (let ((tp (getf l :topics)))
                                                      (and (= 3 (length tp)) (eql topic (first tp)) (= 32 (length (getf l :data))))))
                                        logs))
                  (token (getf (first erc20) :address))
                  (want (loop for l in erc20 when (eql (getf l :address) token)
                              collect (list :block n :tx (getf l :tx) :from (second (getf l :topics)) :to (third (getf l :topics))
                                            :value (reduce (lambda (a x) (+ (* a 256) x)) (getf l :data) :initial-value 0))))
                  (got (history.transfers:transfers dir token n n))
                  (who (getf (first want) :to)))
             (check (and want (equal got want)) "the Transfers of ~A: ~D, the records ~D" (eita:hex token) (length got) (length want))
             (check (equal (history.transfers:transfers dir token n n :address who)
                           (remove-if-not (lambda (x) (or (eql (getf x :from) who) (eql (getf x :to) who))) want))
                    "the Transfers of ~A involving ~A" (eita:hex token) (eita:hex who))
             (format t "  token-transfers: ~D Transfers of ~A~%" (length got) (eita:hex token)))
           ;; --- 5. daily ---------------------------------------------------------------------------
           (let ((days (history.daily:daily dir (- n 5) n))
                 (gas (reduce #'+ txs :key (lambda (tx) (getf tx :gas-used)))))
             (check (and (= 1 (length days))
                         (eql 756 (getf (first days) :txs))
                         (eql gas (getf (first days) :gas))
                         (eql (* gas (getf block :base-fee)) (getf (first days) :burnt))
                         (eql (length (remove-duplicates (mapcar (lambda (tx) (getf tx :from)) txs))) (getf (first days) :senders)))
                    "daily: ~S" days)
             (format t "  daily: ~S~%" (first days)))
           ;; --- 6. backfill: the same subscriptions, the past from the log --------------------------
           (record!) (example "hooks" "gas-per-block") (example "hooks" "transfers")
           (check (= 1 (eita:backfill dir n n)) "backfill: not one block")
           (check (equal live-gas (hooks.gas:summary)) "gas-per-block from the log ~S, live ~S" (hooks.gas:summary) live-gas)
           (check (equal live-transfers (hooks.transfers:summary 5)) "transfers from the log ~S, live ~S"
                  (hooks.transfers:summary 5) live-transfers)
           (let ((a (stripped block)) (b (stripped (first *blocks*))))
             (unless (equalp a b)                       ; equalp: log data are octet vectors
               (fail "the block record from the log differs: ~S"
                     (or (loop for (k v) on a by #'cddr unless (or (eq k :txs) (equalp v (getf b k))) return (list k v (getf b k)))
                         (loop for x in (getf a :txs) for y in (getf b :txs)
                               unless (equalp x y)
                                 return (loop for (k v) on x by #'cddr unless (equalp v (getf y k)) return (list (getf x :index) k v (getf y k))))))))
           (check (handler-case (progn (eita:backfill dir n (1+ n)) nil) (error () t))
                  "backfill past the committed block did not refuse")
           (format t "  backfill: gas-per-block and transfers from the log = live; the records match~%")
           (clear)))
    (setf eita:*observer* nil)
    (clear)
    (ignore-errors (delete-file json))
    (sb-ext:run-program "rm" (list "-rf" dir) :search t)))

(format t "~&history: ~:[FAIL~;the fact log answers what the replay delivered: lookups, histories, scans, backfill~]~%" (zerop *fails*))
(eita.test:finish :code (if (zerop *fails*) 0 1))
