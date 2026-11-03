;;;; chains/replay.lisp — EITA:REPLAY, one entry to every chain's replay (`eita replay`).
;;;;
;;;; The driver reads its run policy from the environment (EITA_<NAME>, or the chain's
;;;; prefix: chains/driver.lisp `env`), as deployments configure it; REPLAY's arguments set
;;;; the same variables, so a flag and its variable are one setting, not two.

(in-package #:eita.chain)

(defparameter +replay-chains+
  '(("ethereum" :ethereum) ("arc" :arc) ("arc-testnet" :arc "testnet") ("arc-mainnet" :arc "mainnet")
    ("base" :op "base") ("opt" :op "opt") ("world" :op "world"))
  "The chains REPLAY runs: name, driver, and the driver's network.")

(defun setenv! (name value)
  (if value
      (sb-posix:setenv name (princ-to-string value) 1)
      (sb-posix:unsetenv name)))

(defun eita:replay (chain from &key to blocks source observer state checkpoint-every
                                    (full-state nil full-state-p) resume genesis)
  "Replay CHAIN (\"ethereum\", \"arc\" | \"arc-testnet\" | \"arc-mainnet\", \"base\" | \"opt\" |
   \"world\") from block FROM to TO (default FROM; :tip follows the head, when the source can).
   BLOCKS: a directory of block files (docs/block-input.md); SOURCE: a Lisp file installing a
   block source; OBSERVER: a Lisp file installing an observer; STATE: the state directory
   (snapshots, layers, anchors); CHECKPOINT-EVERY: the anchor interval. FULL-STATE (default:
   true but on the OP chains) runs from the genesis alloc (GENESIS overrides the chain's) or
   from the anchored snapshot at RESUME; without it the source serves state lazily."
  (let* ((row (or (assoc chain +replay-chains+ :test #'string-equal)
                  (error "unknown chain ~S (~{~A~^, ~})" chain (mapcar #'first +replay-chains+))))
         (driver (second row)) (net (third row))
         (full (if full-state-p full-state (not (eq driver :op))))
         (prefix (case driver (:ethereum "ETH") (:arc "ARC"))))
    (when blocks (setenv! "EITA_BLOCKS_DIR" blocks))
    (when source (setenv! "EITA_SOURCE" source))
    (when observer (setenv! "EITA_OBSERVER" observer))
    (when state (setenv! "EITA_STATE_DIR" state))
    (when genesis (setenv! "EITA_GENESIS" genesis))
    (when resume (setenv! "EITA_RESUME_FROM" resume))
    (when checkpoint-every
      (setenv! "EITA_CHECKPOINT_EVERY" checkpoint-every)
      (setf eita.state::*checkpoint-every* checkpoint-every))
    (setenv! "EITA_FROM_GENESIS" (and full 1))
    (when prefix (setenv! (concatenate 'string prefix "_FROM_GENESIS") (and full 1)))
    (let ((args (list (princ-to-string from))))
      (cond ((member to '(:tip "tip") :test #'equalp) (setf args (append args (list "tip"))))
            (to (setf args (append args (list (princ-to-string to))))))
      (ecase driver
        (:ethereum (eita.chain.ethereum::main-ethereum args))
        (:arc (eita.chain.arc::main-arc args (or net eita.chain.arc::*arc-net*)))
        (:op (eita.chain.op::main-base args net))))))
