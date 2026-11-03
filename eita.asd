;;;; eita.asd — Eita: an EVM specified in Lean 4, with native handlers emitted from the spec.
;;;;
;;;; Systems:
;;;;   eita            the engine: native libraries, the EVM (interpreter and JIT tiers, the
;;;;                   Lean-emitted host effects), world state and snapshots, block input, the
;;;;                   chain-neutral block pipeline and driver, the EITA API package
;;;;   eita/chains     Ethereum, Arc, the OP-Stack chains, and EITA:REPLAY
;;;;   eita/fixtures   the BlockchainTests runner
;;;;   eita/mpt-live   the incremental state-root validator (kept, not armed: chains/driver.lisp)
;;;;   eita/cli        bin/eita (asdf:make "eita/cli")
;;;;   eita/test       (asdf:test-system "eita"): the Lisp test suites and oracles (tests/)
;;;;
;;;; Native artifacts (libeita, libkeccak_batch, libeita_pq, the emitJIT daemon) are built by
;;;; build.sh and found at RUN time (src/native/libraries.lisp), never baked into a fasl.
;;;; Dependencies come from ocicl (ocicl.csv pins them); build.sh shows how to load them.

(defsystem "eita"
  :description "Eita: an EVM specified in Lean 4, with native handlers emitted from the spec."
  :author "Valeriy Zamaraiev"
  :license "MIT"
  :version "0.3.0"
  :depends-on ("cffi" "jsown" "cl-fad" "alexandria" (:require "sb-posix") (:require "sb-bsd-sockets"))
  :pathname "src/"
  :serial t
  :components ((:file "packages")
               ;; native artifacts: the startup registry, opening the libraries, FFI, code version
               (:file "native/startup")
               (:file "native/libraries")
               (:file "native/code-version")
               (:file "native/ffi")
               ;; byte-level primitives
               (:file "core/bytes")
               (:file "core/hex")
               (:file "core/u256")
               ;; the EVM, and world state under it
               (:file "evm/jit")
               (:file "evm/interp")
               (:file "state/world")
               (:file "evm/frames")
               (:file "evm/journal")
               (:file "evm/seams")
               (:file "evm/observe")
               (:file "evm/stream")
               (:file "evm/observe-tx")
               (:file "evm/callbacks")
               (:file "evm/precompiles")
               (:file "evm/host-seam")
               (:file "generated/host")       ; Lean-emitted: lake exe emitHostCL
               (:file "evm/calls")
               (:file "evm/tx")
               ;; block input
               (:file "input/decode")
               (:file "input/source")
               (:file "evm/run-tx")
               (:file "evm/networks")
               ;; full state: snapshots, recovery, anchors, the layered world
               (:file "state/snapshot")
               (:file "state/recovery")
               (:file "state/anchors")
               (:file "state/snapshot-world")
               ;; the chain-neutral block pipeline and driver
               (:file "chains/block-system")
               (:file "chains/chain-spec")
               (:file "chains/driver")
               (:file "state/mpt")
               (:file "chains/receipts")
               (:file "state/worlds")
               (:file "state/root")
               ;; the API
               (:file "eita"))
  :in-order-to ((test-op (test-op "eita/test"))))

(defsystem "eita/chains"
  :description "Eita's chains: Ethereum, Arc, OP-Stack (Base, OP Mainnet, World Chain); EITA:REPLAY."
  :depends-on ("eita")
  :pathname "src/chains/"
  :serial t
  :components ((:file "ethereum")
               (:file "arc-precompiles")
               (:file "arc")
               (:file "op")
               (:file "replay")))

(defsystem "eita/fixtures"
  :description "The BlockchainTests runner (ethereum/tests, execution-spec-tests)."
  :depends-on ("eita")
  :pathname "src/fixtures/"
  :serial t
  :components ((:file "runner")
               (:file "api")))

(defsystem "eita/mpt-live"
  :description "The incremental state-root validator (#237). Loading it redefines the journal's
   dirty-set hooks; it is not armed until it reads snapshots (src/chains/driver.lisp)."
  :depends-on ("eita" (:require "sb-concurrency"))
  :pathname "src/state/"
  :components ((:file "mpt-live")))

(defsystem "eita/cli"
  :description "bin/eita: replay, fixtures, repl, check-root, recovery, version."
  :depends-on ("eita" "eita/chains" "eita/fixtures")
  :components ((:file "src/cli"))
  :build-operation "program-op"
  :build-pathname "bin/eita"
  :entry-point "eita.cli:main")

(defsystem "eita/test"
  :description "The test suites (tests/harness.lisp): native handlers, gas, the MPT oracles,
   snapshots and layers, recovery, the Lean vector audits, the Arc PQ precompile, a
   BlockchainTests sample on both tiers, optionally the Lean gates."
  :depends-on ("eita" "eita/chains" "eita/fixtures")
  :pathname "tests/"
  :components ((:file "harness"))
  :perform (test-op (o c) (unless (uiop:symbol-call :eita.test :run-all)
                            (error "eita/test: a suite failed (see above)"))))

;;; bin/eita keeps SBCL's runtime options: `eita --dynamic-space-size 16GB --end-runtime-options
;;; <command> …` (program-op's default would fix them). Its default heap is the one it was
;;; built in (build.sh: EITA_HEAP_MB). Before the image is saved the Lisp sources are hashed
;;; (the code version) and the build tree's shared objects are dropped from it: the
;;; executable opens its libraries where it finds them when it starts.
(defmethod perform ((o program-op) (s (eql (find-system "eita/cli"))))
  (uiop:symbol-call :eita.native :freeze-lisp-manifest!)
  (uiop:symbol-call :eita.native :forget-shared-objects!)
  (let ((exe (output-file o s)))
    (ensure-directories-exist exe)
    (setf uiop:*image-dumped-p* :executable)
    (uiop:call-image-dump-hook)
    (setf uiop/image::*image-restored-p* nil)
    (sb-ext:save-lisp-and-die exe :executable t :toplevel #'uiop:restore-image
                                  :save-runtime-options :accept-runtime-options)))
