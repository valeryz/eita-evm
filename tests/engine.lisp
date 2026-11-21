;;;; engine.lisp — the Engine API (src/engine/engine.lisp) without a consensus client: block 0
;;;; derived from genesis.json hashes to each network's genesis hash (mainnet, Hoodi, and a geth
;;;; --dev Osaka devnet, tests/data/devnet-genesis.json), and newPayloadV4's fork window is
;;;; Prague..BPO2 of each network's Lean schedule (-38005 outside it). The calls themselves
;;;; are checked against a running node: tests/engine-checks.py.
;;;;
;;;; Run: (eita.test:run-all :only '("engine")), or (asdf:test-system "eita") for all suites.

(let ((ok t) (saved (sb-ext:posix-getenv "EITA_GENESIS")) (spec eita.chain::*chain-spec*))
  (labels ((expect (what pass) (format t "~:[FAIL~;ok  ~] ~A~%" pass what) (unless pass (setf ok nil)))
           (install (net)
             (setf eita.engine::*genesis* nil)
             (eita.chain::install-chain-spec! (eita.chain.ethereum::ethereum-chain-spec net)))
           (genesis-is (net want)
             (install net)
             (let ((got (jsown:val (cdr (eita.engine::genesis-block)) "hash")))
               (expect (format nil "~A: block 0 from genesis.json ~A = ~A" net got want) (string-equal got want))))
           (v4-p (n ts) (eita.engine::payload-fork-ok-p n ts)))
    (unwind-protect
         (progn
           (genesis-is "mainnet" "0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3")
           (genesis-is "hoodi" "0xbbe312868b376a3001692a646dd2d7d1e4406380dfd86b98aa8a34d1557c971b")
           (sb-posix:setenv "EITA_GENESIS" (namestring (asdf:system-relative-pathname "eita" "tests/data/devnet-genesis.json")) 1)
           (genesis-is "devnet" "0x287b25c4a5fc1259ab9dfa04dac93e36401316645c8eb13a24b25e825396a52f")
           (expect "devnet: Osaka at genesis is V4's" (v4-p 1 #x6b005f48))
           (install "hoodi")                 ; Prague 1742999832; BPO2 1762955544, then nothing
           (expect "hoodi: Cancun is not V4's (-38005)" (not (v4-p 1 1742999831)))
           (expect "hoodi: Prague is" (v4-p 1 1742999832))
           (expect "hoodi: BPO2 is" (v4-p 1 1900000000))
           (install "mainnet")               ; Prague 1746612311
           (expect "mainnet: Cancun is not V4's" (not (v4-p 22431083 1746612310)))
           (expect "mainnet: Prague is" (v4-p 22431084 1746612311))
           (expect "mainnet: a pre-Merge block is not" (not (v4-p 1000 1746612311))))
      (if saved (sb-posix:setenv "EITA_GENESIS" saved 1) (sb-posix:unsetenv "EITA_GENESIS"))
      (setf eita.engine::*genesis* nil)
      (when spec (eita.chain::install-chain-spec! spec))))
  (unless ok (eita.test:finish :code 1)))
