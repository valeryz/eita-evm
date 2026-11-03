;;;; eita.lisp — the EITA package: a small API over the verified EVM.
;;;;
;;;;   (asdf:load-system "eita")   or   bin/eita repl          then (in-package :eita)
;;;;
;;;; Thin wrappers over the engine every replay runs (src/evm/, src/chains/run-tx.lisp, the
;;;; fixture runner): a world is the replay's world, a transaction runs through the same
;;;; run-evm-tx (the Lean-derived tx effect, settlement, end of tx) a mainnet block does.
;;;; Nothing here re-implements execution. docs/quickstart.md walks through a session.
;;;;
;;;; Transactions are not signed: FROM is taken as the sender (as a dev chain that lets you
;;;; impersonate would). Blocks: every TRANSACT runs as its own block, without the pre/post
;;;; block system calls; to run real blocks use REPLAY (system eita/chains; docs/block-input.md).
;;;; LOAD-FIXTURE and RUN-FIXTURE-FILE come with the fixture runner (system eita/fixtures).

(in-package #:eita)

(defvar *block* (list :number 1 :timestamp 1700000000 :base-fee 0 :gas-limit 30000000
                      :coinbase 0 :prev-randao 0 :chain-id 1 :excess-blob-gas 0)
  "The block environment TRANSACT and CALL run in (each call bumps :number).")

(defmethod print-object ((w eita.state:world) stream)
  (print-unreadable-object (w stream :type t :identity t)
    (let ((n 0)) (eita.state:map-accts (lambda (r) (declare (ignore r)) (incf n)) (eita.state:world-accts w))
      (format stream "~D account~:P" n))))

(defun addr (x)
  "X as an address integer: an integer, or a \"0x…\" string."
  (etypecase x (integer x) (string (eita.core:hex->int x))))

(defun bytes (x)
  (etypecase x
    (null (make-array 0 :element-type '(unsigned-byte 8)))
    (string (eita.core:hex->bytes x))
    (vector (coerce x '(simple-array (unsigned-byte 8) (*))))))

(defun hex (x)
  "Octets or an integer as \"0x…\"."
  (etypecase x
    (integer (format nil "0x~(~x~)" x))
    (vector (eita.state:bytes->hex-string (coerce x '(simple-array (unsigned-byte 8) (*))) "0x"))))

(defun set-fork (network)
  "Run at NETWORK's rules: \"Frontier\" … \"Cancun\", \"Prague\", \"Osaka\" (the fixture names)."
  (eita.evm:set-fork! network)
  network)

(defun fork () eita.evm:*fork-ord*)

(defun new-world (&key (fork "Prague") alloc)
  "A fresh world at FORK. ALLOC: a list of (address &key balance nonce code storage), STORAGE
   an alist of (slot . value); addresses and code may be integers/octets or hex strings."
  (set-fork fork)
  (let ((w (eita.state:make-world)))
    (eita.state:populate-world
     w (loop for (a . plist) in alloc
             collect (cons (addr a) (list :balance (getf plist :balance 0) :nonce (getf plist :nonce 0)
                                          :code (bytes (getf plist :code))
                                          :storage (getf plist :storage)))))
    w))

(defun fund (world address wei)
  (eita.state:populate-world world (list (list (addr address) :balance wei :nonce (nonce world address)
                                                 :code (code world address) :storage nil)))
  (balance world address))

(defun set-code (world address code)
  (eita.state:populate-world world (list (list (addr address) :balance (balance world address)
                                                 :nonce (nonce world address) :code (bytes code) :storage nil)))
  (length (code world address)))

(defun set-storage (world address slot value)
  (eita.state:world-storage-set world (addr address) slot value))

(defun balance (world address) (eita.state:balance-of world (addr address)))
(defun nonce (world address) (eita.state:nonce-of world (addr address)))
(defun code (world address)
  (or (eita.state:code-of world (addr address)) (make-array 0 :element-type '(unsigned-byte 8))))
(defun storage (world address slot) (eita.state:world-storage-get world (addr address) slot))

(defun state-root (world)
  "The Merkle-Patricia state root of WORLD (the root a block header commits to)."
  (eita.state:world-state-root world))

(defun transact (world &key from to (value 0) data (gas 1000000) (gas-price 0) nonce access-list)
  "Run one transaction on WORLD and commit it. TO NIL creates a contract. Returns a plist:
   :status (1 success, 0 revert/halt), :gas-used, :output (octets), :logs ((address topics
   data) ...), :created (the new contract's address, for a creation). A transaction the
   rules reject (nonce, balance, intrinsic gas) signals an error naming why."
  (let* ((from (addr from)) (to (and to (addr to)))
         (n (or nonce (eita.state:nonce-of world from)))
         (tx (eita.evm:make-tx :type 0 :sender from :to to :nonce n :gas-limit gas
                                   :gas-price gas-price :value value :data (bytes data)
                                   :access-list access-list :chain-id (getf *block* :chain-id)))
         (ctx (copy-list *block*))
         (created (and (null to) (eita.core:derive-create-address from n))))
    (setf (getf ctx :blob-base-fee) (eita.evm:block-blob-base-fee 0 eita.evm:*fork-ord*)
          eita.evm:*current-block-number* (getf ctx :number)
          eita.evm:*el-fork-ord* nil
          eita.evm:*prague-delegation* (>= eita.evm:*fork-ord* eita.evm:+fork-ord-prague+))
    (eita.chain:receipts-block-begin!)
    (multiple-value-bind (gas-used status)
        (let ((eita.evm:*current-world* world))
          (eita.evm:run-evm-tx world tx ctx (getf ctx :coinbase) (getf ctx :number) 0))
      (incf (getf *block* :number))
      (incf (getf *block* :timestamp) 12)
      (list :status status :gas-used gas-used
            :output eita.evm:*last-tx-output*
            :logs (mapcar (lambda (l) (destructuring-bind (a topics data) l (list a topics data)))
                          eita.evm:*last-tx-logs*)
            :created (and created (= status 1) created)))))

(defun deploy (world &key from code (value 0) (gas 3000000))
  "Create a contract from init CODE; returns its address (or NIL when creation failed)."
  (getf (transact world :from from :to nil :data code :value value :gas gas) :created))

(defun call (world &key from to data (value 0) (gas 10000000))
  "Execute a transaction on a COPY of WORLD (WORLD is unchanged), like eth_call: returns the
   same plist as TRANSACT."
  (transact (eita.state:copy-world* world) :from (or from 0) :to to :data data :value value :gas gas))
