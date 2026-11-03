;;;; arc-precompiles.lisp — Circle Arc native-USDC precompiles (host seam)
;;;;
;;;; 0x1800…0000 NativeCoinAuthority `transfer` / `mint` / `burn` / `totalSupply`
;;;; 0x1800…0001 NativeCoinControl   `isBlocklisted(account)`
;;;;
;;;; Spec: lean/Evm/Arc/Spec/NativeCoin.lean (`runTransfer` / `runIsBlocklisted`,
;;;; kernel-checked examples), ported clause-by-clause from circlefin/arc-node
;;;; @6e76402 crates/precompiles/src/{native_coin_authority,native_coin_control,
;;;; helpers,macros}.rs. Every gas number here comes from the EMITTED
;;;; `spec-arc-*` functions (src/generated/host.lisp ← Evm.Arc.Spec.NativeCoin);
;;;; this file is the hand-written seam: world reads/writes, warm/cold via the
;;;; tx access set, journaling, and the control flow in the spec's step order.
;;;; On a success path the accumulated gas is cross-checked against the emitted
;;;; total formula — a live consistency check between the two derived forms.
;;;;
;;;; Why this exists: genesis gives every 0x1800…00xx a one-byte placeholder
;;;; code 0x01; a stock EVM executing it (ADD, empty stack) burns all forwarded
;;;; gas and reverts. Arc's client intercepts these addresses as precompiles.
;;;; Not ported yet (loud, not silent): SystemAccounting 0x1800…0002 — an `error`
;;;; names the address. PQ 0x1800…0004 IS ported: see arc-pq-verify (stop #14).
;;;; 0x1800…0003 CallFrom (subcall precompile) IS ported: see arc-call-from.

(in-package #:eita.chain.arc)

(defconstant +arc-native-coin-authority+ #x1800000000000000000000000000000000000000)
(defconstant +arc-native-coin-control+   #x1800000000000000000000000000000000000001)
(defconstant +arc-native-fiat-token+     #x3600000000000000000000000000000000000000)
(defconstant +arc-blocklist-mapping-slot+ 2) ; execution-config native_coin_control.rs:23
(defconstant +arc-total-supply-slot+ 2)      ; TOTAL_SUPPLY_STORAGE_KEY = [0..0, 2] (native_coin_authority.rs:47-49)
(defconstant +arc-system-address+ #xfffffffffffffffffffffffffffffffffffffffe) ; EIP-7708 log emitter (revm SYSTEM_ADDRESS)
;; keccak256("Blocklisted(address)") / keccak256("UnBlocklisted(address)") — native_coin_control.rs:85-91
(defconstant +arc-blocklisted-topic+   #x917c251bb231c4b997a420bebe47edad5c20e70715da16c38e9b2e172e44ab92)
(defconstant +arc-unblocklisted-topic+ #xbc3fe0fc667d12a7a22748747f024a7d971127ffc48f6622675d3e97a2591a51)
(defconstant +erc20-transfer-topic+ #xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)

(defun arc-7708-log! (from to value)
  "EIP-7708 `Transfer(from, to, value)` log from SYSTEM_ADDRESS (2 indexed topics +
   32-byte data) — emitted by the client for every native value move except
   self-transfers (evm.rs create_eip7708_transfer_log; precompile emit_event)."
  (unless (= from to)
    (observe-log! +arc-system-address+ (list +erc20-transfer-topic+ from to) (arc-abi-u256 value))))

(defparameter *arc-zero6* t
  "ArcHardfork::Zero6 active for the current block. arc-node HEAD encodes only the
   Zero6+ precompile rules (account-load costs and the +25000 empty-recipient
   surcharge are ungated in helpers.rs; the tests call them \"Zero6\"), so blocks
   before Zero6 (testnet ts < 1779894517; mainnet: none) are NOT reproducible from
   the source — the driver refuses them loudly rather than run a partial model.")
(defparameter *arc-zero7* nil
  "Zero7 active for the block being replayed. Gates the CallFrom precompile
   (evm.rs:1672 registers 0x1800…0003 only from Zero7).")

(defparameter *arc-zero8* nil
  "ArcHardfork::Zero8 active for the current block (by timestamp; hardforks.rs:410-411).
   Pre-Zero8 a transfer that would drain `from` to an empty account reverts (+2900);
   Zero8 also adds the +200 penalty to delegatecall rejections.")

;;; --- ABI helpers -----------------------------------------------------------

(defun arc-selector (input-ptr input-len)
  (when (>= input-len 4)
    (loop with v = 0 for k below 4
          do (setf v (logior (ash v 8) (mem-aref input-ptr :uint8 k)))
          finally (return v))))

(defun arc-abi-word (input-ptr input-len i)
  "Argument word I (after the 4-byte selector) as an integer, NIL if the input is
   short. Trailing bytes beyond the head are accepted (arc-node test
   `total_supply_accepts_extra_input`)."
  (let ((off (+ 4 (* 32 i))))
    (when (<= (+ off 32) input-len)
      (loop with v = 0 for k below 32
            do (setf v (logior (ash v 8) (mem-aref input-ptr :uint8 (+ off k))))
            finally (return v)))))

(defun arc-abi-address (w)
  "Validated `address` word: canonical left-padding (upper 12 bytes zero) —
   `abi_decode_raw_validated` (helpers.rs:229) rejects anything else."
  (and w (< w (ash 1 160)) w))

(defun arc-abi-bool (b)
  (let ((o (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
    (when b (setf (aref o 31) 1))
    o))

(defun arc-abi-u256 (n)
  (let ((o (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
    (loop for k below 32 do (setf (aref o (- 31 k)) (ldb (byte 8 (* 8 k)) n)))
    o))

(defun arc-revert-bytes (msg)
  "Solidity `Error(string)`: 0x08c379a0 ++ abi(string) (helpers.rs:66). The
   length matters — a caller's RETURNDATACOPY of it expands memory."
  (let* ((n (length msg)) (padded (* 32 (ceiling n 32)))
         (o (make-array (+ 4 64 padded) :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref o 0) #x08 (aref o 1) #xc3 (aref o 2) #x79 (aref o 3) #xa0)
    (setf (aref o 35) 32)                                    ; offset of the string
    (loop for k below 32 do (setf (aref o (- 67 k)) (ldb (byte 8 (* 8 k)) n)))
    (loop for i below n do (setf (aref o (+ 68 i)) (char-code (char msg i))))
    o))

(defun arc-blocklist-slot (addr)
  "keccak256(pad32(addr) ++ pad32(2)) — execution-config native_coin_control.rs:35-46."
  (let ((buf (make-array 64 :element-type '(unsigned-byte 8) :initial-element 0)))
    (loop for i below 20 do (setf (aref buf (+ 12 i)) (ldb (byte 8 (* 8 (- 19 i))) addr)))
    (setf (aref buf 63) +arc-blocklist-mapping-slot+)
    (loop with h = 0 for b across (keccak256-bytes buf)
          do (setf h (logior (ash h 8) b)) finally (return h))))

;;; --- Metered execution -------------------------------------------------------
;;; Each handler returns (values gas-used output success). OOG = all forwarded
;;; gas, empty output, failure (revm halt). Revert = gas-so-far (+ penalty on
;;; the early paths), Error(string) output, failure.

(defmacro arc-with-meter ((used remaining gas) &body body)
  "Bind USED/REMAINING over GAS and provide local CHARGE / OOG / REVERT / EARLY.
   CHARGE mirrors `record_cost_or_out_of_gas`; EARLY `new_reverted_with_early_penalty`.
   The block is outermost so the locals can return through it (labels: they refer
   to each other)."
  `(block arc-meter
     (let ((,used 0) (,remaining ,gas))
       (labels ((oog () (when *trace-frames* (format *error-output* "~&[arc-pre] OOG gas=~D used=~D~%" ,gas ,used))
                        (return-from arc-meter (values ,gas #() nil)))
                (revert (msg) (when *trace-frames* (format *error-output* "~&[arc-pre] REVERT ~S used=~D~%" msg ,used))
                        (return-from arc-meter (values ,used (arc-revert-bytes msg) nil)))
                (charge (c) (if (<= c ,remaining) (progn (incf ,used c) (decf ,remaining c)) (oog)))
                (early (msg) (charge (spec-arc-early-revert-penalty)) (revert msg)))
         (declare (ignorable #'charge #'early #'oog #'revert))
         ,@body))))

(defun arc-slot-read! (addr slot)
  "Metered storage read shared with the EVM access set: (values cold? value)."
  (fault-slot! addr slot)
  (let ((cold? (access-slot! addr slot)))
    (values cold? (storage-of *current-world* addr slot))))

(defun arc-native-transfer (caller kind input-ptr input-len gas is-static)
  "NativeCoinAuthority.transfer — native_coin_authority.rs:281-349, in
   `runTransfer` order. KIND 1/2 (CALLCODE/DELEGATECALL) is `check_delegatecall`."
  (arc-with-meter (used remaining gas)
    ;; check_staticcall: spend all, revert (helpers.rs:548)
    (when is-static
      (return-from arc-meter (values gas (arc-revert-bytes "State change during static call") nil)))
    (let ((from (arc-abi-address (arc-abi-word input-ptr input-len 0)))
          (to   (arc-abi-address (arc-abi-word input-ptr input-len 1)))
          (amount (arc-abi-word input-ptr input-len 2)))
      (unless (and from to amount) (early "Execution reverted"))
      (unless (= caller +arc-native-fiat-token+) (early "Not enabled for native coin transfers"))
      (when (or (= kind 1) (= kind 2))                       ; check_delegatecall (helpers.rs:565)
        (if *arc-zero8* (early "Delegate call not allowed") (revert "Delegate call not allowed")))
      (when (or (zerop from) (zerop to)) (early "Zero address not allowed"))
      ;; is_blocklisted(from), is_blocklisted(to) — reads on NativeCoinControl
      (multiple-value-bind (bl-from-cold bl-from) (arc-slot-read! +arc-native-coin-control+ (arc-blocklist-slot from))
        (charge (spec-arc-slot-read-gas (if bl-from-cold 1 0)))
        (unless (zerop bl-from) (early "Blocked address"))
        (multiple-value-bind (bl-to-cold bl-to) (arc-slot-read! +arc-native-coin-control+ (arc-blocklist-slot to))
          (charge (spec-arc-slot-read-gas (if bl-to-cold 1 0)))
          (unless (zerop bl-to) (early "Blocked address"))
          ;; zero amount: allowed, no transfer, no log
          (when (zerop amount)
            (return-from arc-meter (values used (arc-abi-bool t) t)))
          ;; helpers.rs transfer (L381-457)
          (fault-account! from)
          (let* ((from-cold (access-addr! from))
                 (w *current-world*)
                 (from-bal (balance-of w from)))
            (charge (spec-arc-account-load-gas (if from-cold 1 0)))
            ;; check_can_decr_account (helpers.rs:595)
            (when (< from-bal amount) (revert "Insufficient funds"))
            (when (and (not *arc-zero8*) (= from-bal amount)
                       (zerop (nonce-of w from))
                       (zerop (length (code-of w from))))
              (charge (spec-arc-precompile-sstore-gas))
              (revert "Cannot clear balance of empty account"))
            (charge (spec-arc-precompile-sstore-gas))
            (fault-account! to)
            (let ((to-cold (access-addr! to)))
              (charge (spec-arc-account-load-gas (if to-cold 1 0)))
              (charge (spec-arc-precompile-sstore-gas))
              (when (destroyed-p to)
                (revert "Cannot increase the balance of selfdestructed account"))
              (let ((to-empty (account-dead-p to)))            ; revm is_empty, before the credit
                (when to-empty (charge (spec-arc-empty-account-gas)))
                ;; journal transfer(from, to, amount): both balances journaled + touched
                (journal-balance! (current-arena) from)
                (journal-balance! (current-arena) to)
                (decf (balance-of w from) amount)
                (incf (balance-of w to) amount)
                (touch! from) (touch! to)
                (observe-transfer! 4 (1+ *call-depth*) from to amount)
                ;; EIP-7708 Transfer log from SYSTEM_ADDRESS unless self-transfer.
                (unless (= from to) (charge (spec-arc-transfer-log-gas)))
                (arc-7708-log! from to amount)
                ;; Cross-check: step accumulation == emitted success-path total.
                (let ((total (spec-arc-native-transfer-gas (if bl-from-cold 1 0) (if bl-to-cold 1 0) 1
                                                           (if from-cold 1 0) (if to-cold 1 0)
                                                           (if to-empty 1 0) (if (= from to) 1 0))))
                  (when *trace-frames*
                    (format *error-output* "~&[arc-pre] transfer from=~40,'0x to=~40,'0x amt=~D bl-from-cold=~A bl-to-cold=~A from-cold=~A to-cold=~A to-empty=~A used=~D~%"
                            from to amount bl-from-cold bl-to-cold from-cold to-cold to-empty used))
                  (unless (= total used)
                    (error "arc transfer gas: stepped ~D vs spec total ~D" used total)))
                (values used (arc-abi-bool t) t)))))))))

(defun arc-slot-write-gas! (addr slot new)
  "Metered `write` (helpers.rs:320-378) minus the sentry: the slot is warm from the
   preceding read; cost = sstore_base_cost(original, present, new). Returns the
   cost; the caller charges it, then stores. ORIGINAL = start-of-tx value via the
   engine's orig-record!/orig-get! seam (same one cb-sstore uses)."
  (let* ((present (storage-of *current-world* addr slot))
         (original (progn (orig-record! addr slot present) (orig-get! addr slot present))))
    (spec-arc-write-gas (if (= new present) 1 0) (if (= original present) 1 0) (if (zerop original) 1 0))))

(defun arc-slot-store! (addr slot new)
  "Journaled precompile storage write (revert restores it like an SSTORE)."
  (let ((present (storage-of *current-world* addr slot)))
    (unless (= new present)
      (journal-push! (current-arena) 0 addr slot present)
      (setf (storage-of *current-world* addr slot) new))))

(defun arc-native-mint (caller kind input-ptr input-len gas is-static)
  "NativeCoinAuthority.mint — native_coin_authority.rs:100-186, in `runMint` order."
  (arc-with-meter (used remaining gas)
    (when is-static
      (return-from arc-meter (values gas (arc-revert-bytes "State change during static call") nil)))
    (let ((to (arc-abi-address (arc-abi-word input-ptr input-len 0)))
          (amount (arc-abi-word input-ptr input-len 1)))
      (unless (and to amount) (early "Execution reverted"))
      (unless (= caller +arc-native-fiat-token+) (early "Not enabled native coin minter"))
      (when (or (= kind 1) (= kind 2))
        (if *arc-zero8* (early "Delegate call not allowed") (revert "Delegate call not allowed")))
      (when (zerop to) (early "Zero address not allowed"))
      (multiple-value-bind (bl-cold bl) (arc-slot-read! +arc-native-coin-control+ (arc-blocklist-slot to))
        (charge (spec-arc-slot-read-gas (if bl-cold 1 0)))
        (unless (zerop bl) (early "Blocked address")))
      (when (zerop amount) (early "Zero amount invalid"))
      ;; total supply: read, overflow check, write (sentry, base cost)
      (multiple-value-bind (ts-cold supply) (arc-slot-read! +arc-native-coin-authority+ +arc-total-supply-slot+)
        (charge (spec-arc-slot-read-gas (if ts-cold 1 0)))
        (let ((new-supply (+ supply amount)))
          (when (>= new-supply (ash 1 256)) (early "Arithmetic overflow"))
          (when (<= remaining (spec-arc-call-stipend)) (oog))
          (charge (arc-slot-write-gas! +arc-native-coin-authority+ +arc-total-supply-slot+ new-supply))
          (arc-slot-store! +arc-native-coin-authority+ +arc-total-supply-slot+ new-supply)))
      ;; balance_incr(to) (helpers.rs:459-501)
      (fault-account! to)
      (let* ((to-cold (access-addr! to)) (w *current-world*))
        (charge (spec-arc-account-load-gas (if to-cold 1 0)))
        (when (destroyed-p to)
          (revert "Cannot increase the balance of selfdestructed account"))
        (when (>= (+ (balance-of w to) amount) (ash 1 256)) (revert "Arithmetic overflow"))
        (charge (spec-arc-precompile-sstore-gas))
        (let ((to-empty (account-dead-p to)))
          (when to-empty (charge (spec-arc-empty-account-gas))))
        (journal-balance! (current-arena) to)
        (incf (balance-of w to) amount)
        (touch! to)
        (observe-transfer! 4 (1+ *call-depth*) 0 to amount)
        (charge (spec-arc-transfer-log-gas))
        (observe-log! +arc-system-address+ (list +erc20-transfer-topic+ 0 to) (arc-abi-u256 amount))
        (when *trace-frames* (format *error-output* "~&[arc-pre] mint to=~40,'0x amt=~D used=~D~%" to amount used))
        (values used (arc-abi-bool t) t)))))

(defun arc-native-burn (caller kind input-ptr input-len gas is-static)
  "NativeCoinAuthority.burn — native_coin_authority.rs:188-279, in `runBurn` order."
  (arc-with-meter (used remaining gas)
    (when is-static
      (return-from arc-meter (values gas (arc-revert-bytes "State change during static call") nil)))
    (let ((from (arc-abi-address (arc-abi-word input-ptr input-len 0)))
          (amount (arc-abi-word input-ptr input-len 1)))
      (unless (and from amount) (early "Execution reverted"))
      (unless (= caller +arc-native-fiat-token+) (early "Not enabled native coin burner"))
      (when (or (= kind 1) (= kind 2))
        (if *arc-zero8* (early "Delegate call not allowed") (revert "Delegate call not allowed")))
      (when (zerop from) (early "Zero address not allowed"))
      (multiple-value-bind (bl-cold bl) (arc-slot-read! +arc-native-coin-control+ (arc-blocklist-slot from))
        (charge (spec-arc-slot-read-gas (if bl-cold 1 0)))
        (unless (zerop bl) (early "Blocked address")))
      (when (zerop amount) (early "Zero amount invalid"))
      ;; balance_decr(from) (helpers.rs:503-546)
      (fault-account! from)
      (let* ((from-cold (access-addr! from)) (w *current-world*)
             (from-bal (balance-of w from)))
        (charge (spec-arc-account-load-gas (if from-cold 1 0)))
        (when (< from-bal amount) (revert "Insufficient funds"))
        (when (and (not *arc-zero8*) (= from-bal amount)
                   (zerop (nonce-of w from))
                   (zerop (length (code-of w from))))
          (charge (spec-arc-precompile-sstore-gas))
          (revert "Cannot clear balance of empty account"))
        (charge (spec-arc-precompile-sstore-gas))
        (journal-balance! (current-arena) from)
        (decf (balance-of w from) amount)
        (touch! from)
        (observe-transfer! 4 (1+ *call-depth*) from 0 amount)
        ;; total supply: read, write(saturating_sub)
        (multiple-value-bind (ts-cold supply) (arc-slot-read! +arc-native-coin-authority+ +arc-total-supply-slot+)
          (charge (spec-arc-slot-read-gas (if ts-cold 1 0)))
          (let ((new-supply (max 0 (- supply amount))))
            (when (<= remaining (spec-arc-call-stipend)) (oog))
            (charge (arc-slot-write-gas! +arc-native-coin-authority+ +arc-total-supply-slot+ new-supply))
            (arc-slot-store! +arc-native-coin-authority+ +arc-total-supply-slot+ new-supply)))
        (charge (spec-arc-transfer-log-gas))
        (observe-log! +arc-system-address+ (list +erc20-transfer-topic+ from 0) (arc-abi-u256 amount))
        (values used (arc-abi-bool t) t)))))

(defun arc-native-total-supply (input-ptr input-len gas)
  "NativeCoinAuthority.totalSupply — native_coin_authority.rs:350-380: a metered
   read of TOTAL_SUPPLY_STORAGE_KEY on the authority; no static/caller checks."
  (declare (ignore input-ptr input-len))
  (arc-with-meter (used remaining gas)
    (when (< remaining (spec-arc-slot-read-gas 1)) (oog))    ; check_gas_remaining(TOTAL_SUPPLY_GAS_COST = cold read)
    (multiple-value-bind (cold v) (arc-slot-read! +arc-native-coin-authority+ +arc-total-supply-slot+)
      (charge (spec-arc-slot-read-gas (if cold 1 0)))
      (values used (arc-abi-u256 v) t))))

(defun arc-native-is-blocklisted (input-ptr input-len gas)
  "NativeCoinControl.isBlocklisted — native_coin_control.rs:180-215."
  (arc-with-meter (used remaining gas)
    (let ((acct (arc-abi-address (arc-abi-word input-ptr input-len 0))))
      (unless acct (early "Execution reverted"))
      (when (< remaining (spec-arc-is-blocklisted-gas 1)) (oog)) ; check_gas_remaining(IS_BLOCKLISTED_GAS_COST = cold)
      (multiple-value-bind (cold v) (arc-slot-read! +arc-native-coin-control+ (arc-blocklist-slot acct))
        (charge (spec-arc-is-blocklisted-gas (if cold 1 0)))
        (when *trace-frames* (format *error-output* "~&[arc-pre] isBlocklisted acct=~40,'0x cold=~A used=~D~%" acct cold used))
        (values used (arc-abi-bool (not (zerop v))) t)))))

(defun arc-native-blocklist (unblock caller kind input-ptr input-len gas is-static)
  "NativeCoinControl.blocklist / unBlocklist — native_coin_control.rs:100-178 /
   216-296, in `runBlocklist` order (Evm.Arc.Spec.NativeCoin). UNBLOCK stores 0
   instead of 1 and flips the revert string / event."
  (arc-with-meter (used remaining gas)
    (when is-static
      (return-from arc-meter (values gas (arc-revert-bytes "State change during static call") nil)))
    (let ((acct (arc-abi-address (arc-abi-word input-ptr input-len 0))))
      (unless acct (early "Execution reverted"))
      (unless (= caller +arc-native-fiat-token+)
        (early (if unblock "Not enabled for unblocklisting" "Not enabled for blocklisting")))
      (when (and *arc-zero8* (or (= kind 1) (= kind 2))) (early "Delegate call not allowed"))
      ;; check_gas_remaining(BLOCKLIST_GAS_COST − PRECOMPILE_SLOAD_GAS_COST) = 2900 + 1125
      (when (< remaining (+ (spec-arc-precompile-sstore-gas) (spec-arc-blocklist-event-gas))) (oog))
      (when (and (not *arc-zero8*) (or (= kind 1) (= kind 2))) (revert "Delegate call not allowed"))
      ;; write (helpers.rs:320-371): sentry, warmth probe (cold → 2100, warm → 0), sstore_base_cost
      (when (<= remaining (spec-arc-call-stipend)) (oog))
      (let ((slot (arc-blocklist-slot acct)) (new (if unblock 0 1)) (cold nil))
        (multiple-value-bind (c present) (arc-slot-read! +arc-native-coin-control+ slot)
          (declare (ignore present))
          (setf cold c)
          (charge (spec-arc-write-probe-gas (if cold 1 0))))
        (charge (arc-slot-write-gas! +arc-native-coin-control+ slot new))
        (arc-slot-store! +arc-native-coin-control+ slot new)
        ;; emit_event: Blocklisted(address indexed) / UnBlocklisted(address indexed), no data
        (charge (spec-arc-blocklist-event-gas))
        (observe-log! +arc-native-coin-control+
                      (list (if unblock +arc-unblocklisted-topic+ +arc-blocklisted-topic+) acct) #())
        (when *trace-frames*
          (format *error-output* "~&[arc-pre] ~A acct=~40,'0x cold=~A used=~D~%" (if unblock "unBlocklist" "blocklist") acct cold used))
        (values used (arc-abi-bool t) t)))))

(defconstant +arc-call-from+       #x1800000000000000000000000000000000000003)
(defconstant +arc-pq+              #x1800000000000000000000000000000000000004) ; PQSignatureVerify (SLH-DSA)
(defconstant +arc-memo+            #x5294E9927c3306DcBaDb03fe70b92e01cCede505) ; execution-config call_from.rs:24
(defconstant +arc-multicall3-from+ #x522fAf9A91c41c443c66765030741e4AaCe147D0) ; execution-config call_from.rs:27

(defun arc-abi-bool-bytes (ok data)
  "abi(bool success, bytes returnData): bool word, offset 64, length, padded data."
  (let* ((n (length data)) (padded (* 32 (ceiling n 32)))
         (o (make-array (+ 96 padded) :element-type '(unsigned-byte 8) :initial-element 0)))
    (when ok (setf (aref o 31) 1))
    (setf (aref o 63) 64)
    (loop for k below 32 do (setf (aref o (- 95 k)) (ldb (byte 8 (* 8 k)) n)))
    (loop for i below n do (setf (aref o (+ 96 i)) (aref data i)))
    o))

(defun arc-call-from (caller kind input-ptr input-len gas is-static value)
  "CallFrom — evm.rs frame_init/init_subcall/complete_subcall + call_from.rs, in
   `runCallFrom` order. The child is a real CALL frame: cb-call re-entered with
   *current-address* bound to the spoofed SENDER (cb-call seeds the child\'s
   caller from it), value 0, limit rem − rem/64. cb-call charges the target
   access itself (it is warm by then: 100, plus any EIP-7702 delegate load), so
   the 100 is netted out against the access we metered up front."
  (flet ((dispatch (msg)
           (let ((c (spec-arc-subcall-dispatch-cost)))
             (return-from arc-call-from (values (if (<= c gas) c gas) (arc-revert-bytes msg) nil))))
         (oog () (return-from arc-call-from (values gas #() nil))))
    (unless (or (= caller +arc-memo+) (= caller +arc-multicall3-from+))
      (dispatch "unauthorized caller"))
    (unless (= kind 0) (dispatch "subcall precompiles only support CALL scheme"))
    (when is-static
      (return-from arc-call-from
        (values gas (arc-revert-bytes "subcall precompiles cannot be invoked in static context") nil)))
    (when (plusp value) (dispatch "subcall precompiles do not support value transfers"))
    ;; callFrom(address sender, address target, bytes data): head = 3 words, bytes at
    ;; offset 96 (canonical), length word, then the payload.
    (let ((sender (arc-abi-address (arc-abi-word input-ptr input-len 0)))
          (target (arc-abi-address (arc-abi-word input-ptr input-len 1)))
          (off (arc-abi-word input-ptr input-len 2))
          (len (arc-abi-word input-ptr input-len 3)))
      (unless (and sender target off len (= off 96) (<= (+ 4 128 len) input-len))
        (dispatch "ABI decode error: callFrom: buffer overrun while deserializing"))
      (let* ((words (ceiling len 32))
             (overhead (spec-arc-abi-copy-gas words)))
        (when (< gas overhead) (dispatch "insufficient gas: gas limit below ABI decode overhead"))
        (unless (or (= sender caller) (= sender *tx-origin*))
          (dispatch "sender spoofing requires tx.origin as sender"))
        (fault-account! sender) (access-addr! sender)          ; unmetered pre-load (warms)
        (let ((used overhead) (remaining (- gas overhead)))
          (fault-account! target)
          (let ((access (spec-arc-account-load-gas (if (access-addr! target) 1 0))))
            (when (> access remaining) (oog))
            (incf used access) (decf remaining access))
          (let ((child-gas (- remaining (floor remaining 64)))
                (params (foreign-alloc :uint8 :count 128 :initial-element 0))
                (result (foreign-alloc :uint8 :count 64 :initial-element 0)))
            (unwind-protect
                 (progn
                   (setf (mem-ref params :int 0) 0)                       ; CALL
                   (u256-write (inc-pointer params 8) target)
                   (setf (mem-ref params :pointer 72) (inc-pointer input-ptr 132)
                         (mem-ref params :uint64 80) len
                         (mem-ref params :uint64 88) child-gas)
                   (let ((*current-address* sender))                    ; the spoof
                     (foreign-funcall-pointer (callback cb-call) ()
                                              :pointer (null-pointer) :pointer params
                                              :pointer result :int))
                   (let* ((ok (= 1 (mem-ref result :int 0)))
                          (out-ptr (mem-ref result :pointer 8))
                          (out-len (mem-ref result :uint64 16))
                          (sub-gas (mem-ref result :uint64 24))
                          (out (make-array out-len :element-type '(unsigned-byte 8))))
                     (loop for i below out-len do (setf (aref out i) (mem-aref out-ptr :uint8 i)))
                     (unless (null-pointer-p out-ptr) (foreign-free out-ptr))
                     (cond
                       ((eq *last-sub-outcome* :halt)
                        ;; complete_subcall: a halted child costs the whole limit,
                        ;; and the precompile still RETURNS (false, "") — unless the
                        ;; metered cost (overhead + access + the child's whole limit +
                        ;; encode) exceeds the limit, i.e. the encode overhead does not
                        ;; fit in the retained 1/64: then it is an OOG (evm.rs
                        ;; complete_subcall: gas_used = max(limit, metered), record fails).
                        (when (> (+ used child-gas (spec-arc-abi-copy-gas 0)) gas) (oog))
                        (values gas (arc-abi-bool-bytes nil #()) t))
                       (t
                        (let ((total (+ used (- sub-gas 100) (spec-arc-abi-copy-gas (ceiling out-len 32)))))
                          (when (> total gas) (oog))
                          (values total (arc-abi-bool-bytes ok out) t))))))
              (foreign-free params) (foreign-free result))))))))

;;; --- Block-level system state (arc-node crates/evm/src/executor.rs) -----------
;;; Two effects per block besides the txs, both applied by the block executor:
;;;   pre-block  EIP-2935: system call into the history contract with the parent
;;;              hash (apply_pre_execution_changes; Prague is at genesis on Arc).
;;;   post-block SystemAccounting.storeGasValues(n, {gasUsed, gasUsedSmoothed,
;;;              nextBaseFee}) — a system call into 0x1800…0002 that `write`s one
;;;              packed word into a 64-slot ring buffer (system_accounting.rs:
;;;              slot = keccak(pad32(n mod 64) ‖ pad32(1)); word[8..16]=nextBaseFee,
;;;              [16..24]=gasUsedSmoothed, [24..32]=gasUsed, big-endian u64s).
;;;              The values come from executor.rs compute_gas_values: fee params
;;;              via a system call to ProtocolConfig.feeParams() (defaults when
;;;              that call fails, e.g. at genesis), EMA smoothing
;;;              (gas_fee.rs determine_ema_parent_gas_used), the fixed-point
;;;              EIP-1559 variant (arc_calc_next_block_base_fee), the ProtocolConfig
;;;              min/max clamp and the chainspec absolute clamp. The client also
;;;              validates that the header's extra_data encodes that nextBaseFee —
;;;              so every header carries the value to gate against.
;;; Spec + pinned examples: lean/Evm/Arc/Spec/BlockSystem.lean.

(defconstant +arc-system-accounting+ #x1800000000000000000000000000000000000002)
(defconstant +arc-protocol-config+   #x3600000000000000000000000000000000000001)
(defconstant +arc-gas-values-key+ 1)         ; GAS_VALUES_STORAGE_KEY = [0..0, 1]
(defconstant +arc-gas-values-ring+ 64)
(defun arc-gas-values-slot (n)
  "keccak(pad32(n mod 64) ‖ pad32(1)) — system_accounting.rs compute_gas_values_storage_slot."
  (let ((buf (make-array 64 :element-type '(unsigned-byte 8) :initial-element 0))
        (k (mod n +arc-gas-values-ring+)))
    (loop for i below 8 do (setf (aref buf (+ 24 i)) (ldb (byte 8 (* 8 (- 7 i))) k)))
    (setf (aref buf 63) +arc-gas-values-key+)
    (loop with h = 0 for b across (keccak256-bytes buf) do (setf h (logior (ash h 8) b)) finally (return h))))

(defun arc-pack-gas-values (gas-used smoothed next-base-fee)
  (logior (ash next-base-fee 128) (ash smoothed 64) gas-used))
(defun arc-unpack-gas-values (word)
  (values (ldb (byte 64 0) word) (ldb (byte 64 64) word) (ldb (byte 64 128) word)))

;; compute_gas_values (executor.rs:291-348) — bounded parameter resolution, EMA, next base
;; fee, ProtocolConfig clamp, absolute clamp — is the Lean-emitted spec-arc-smoothed-gas-used
;; / spec-arc-next-base-fee (Evm.Arc.Spec.BlockSystem, proved equal to `computeGasValues`).
(defun arc-compute-gas-values (n gas-used gas-limit base-fee parent-smoothed fee-params)
  "FEE-PARAMS is the decoded feeParams() plist (:alpha :k-rate :inv-elasticity
   :min-base-fee :max-base-fee) or NIL when the system call failed (genesis).
   Returns (values smoothed next-base-fee)."
  (declare (ignore n))
  (let ((have (if fee-params 1 0))
        (alpha (or (getf fee-params :alpha) 0))
        (k (or (getf fee-params :k-rate) 0))
        (inv (or (getf fee-params :inv-elasticity) 0))
        (mn (or (getf fee-params :min-base-fee) 0))
        (mx (or (getf fee-params :max-base-fee) 0)))
    (values (spec-arc-smoothed-gas-used gas-used parent-smoothed alpha have)
            (spec-arc-next-base-fee gas-used gas-limit base-fee parent-smoothed have alpha k inv mn mx))))

(defun arc-read-gas-values (world n)
  "getGasValues(n) as a storage read of the ring slot: (values gas-used smoothed next-base-fee)."
  (let ((slot (arc-gas-values-slot n)))
    (fault-slot! +arc-system-accounting+ slot)
    (arc-unpack-gas-values (storage-of world +arc-system-accounting+ slot))))

(defun arc-store-gas-values! (world n gas-used smoothed next-base-fee)
  "storeGasValues(n, …): the precompile\'s single `write` of the packed word."
  (let ((slot (arc-gas-values-slot n)) (word (arc-pack-gas-values gas-used smoothed next-base-fee)))
    (fault-slot! +arc-system-accounting+ slot)
    ;; UNJOURNALED on purpose (a post-block write has no frame to revert into), so the
    ;; #237 dirty-set hooks in journal-push! cannot see it. Touch by hand, as every
    ;; non-journaled writer must. Without this, block 1
    ;; of Arc mainnet already diverges: the ring slot changes and the incremental
    ;; account trie never hears about it.
    (when *mpt-tracking* (mpt-touch! +arc-system-accounting+ slot))
    (setf (storage-of world +arc-system-accounting+ slot) word)))

(defun arc-decode-fee-params (out)
  "feeParams() returns the static 6-word struct (alpha, kRate, inverseElasticity,
   minBaseFee, maxBaseFee, blockGasLimit) — NIL unless exactly that shape."
  (when (and out (= (length out) 192))
    (flet ((w (i) (loop with v = 0 for k below 32 do (setf v (logior (ash v 8) (aref out (+ (* 32 i) k)))) finally (return v))))
      (list :alpha (w 0) :k-rate (w 1) :inv-elasticity (w 2)
            :min-base-fee (w 3) :max-base-fee (w 4) :block-gas-limit (w 5)))))

;;; --- PQ precompile 0x1800…0004 — SLH-DSA-SHA2-128s (FIPS 205) --------------
;;; Spec: lean/Evm/Arc/Spec/Pq.lean (`run`, kernel-checked examples), ported from
;;; arc-node crates/pq-precompile/src/lib.rs @6e76402. Gas is 230000 + 6 per
;;; 32-byte message word and does NOT depend on the verdict, so no gas gate can
;;; catch a wrong bool here — which is why the verification itself is not
;;; reimplemented: c/libeita_pq links the SAME `slh-dsa` crate (rust/pq) that
;;; arc-node calls. SPHINCS+ round-3.1 and FIPS 205 SLH-DSA are different
;;; functions (FIPS 205 prefixes the message with a domain separator and context
;;; length), so a lookalike C library would answer `false` where the chain says
;;; `true`, at identical cost.

(defconstant +arc-pq-selector+ #xbf4db8ba)  ; verifySlhDsaSha2128s(bytes,bytes,bytes)

(defcfun ("eita_slhdsa_sha2_128s_verify" %arc-slhdsa-verify) :int
  (vk :pointer) (vk-len :uint64) (msg :pointer) (msg-len :uint64)
  (sig :pointer) (sig-len :uint64))

(defcfun ("eita_slhdsa_sha2_128s_selftest" %arc-slhdsa-selftest) :int)

(defstartup *arc-pq-lib* nil "T once libeita_pq is open and its self-test passed (in this process).")

(defun arc-pq-ensure-lib! ()
  "Open libeita_pq on first use, found like every native library (native/libraries.lisp).
   Loud when absent: a replay that silently skipped PQ verification would produce a
   plausible wrong bool."
  (unless *arc-pq-lib*
    (let ((path (native-path "libeita_pq")))   ; not found: an error naming where it looked
      (load-foreign-library path)
      ;; A mid-run library load is exactly the event that can remap libeita and
      ;; leave every cached pointer (gas tables, handler addresses) dangling.
      (check-cached-foreign-pointers! "loading c/libeita_pq")
      (unless (= 1 (%arc-slhdsa-selftest))
        (error "c/libeita_pq is built for the wrong parameter set: a 32-byte key and ~
                7856-byte signature must parse and shorter ones must not"))
      (setf *arc-pq-lib* t))))

(defun arc-pq-decode (input-ptr input-len)
  "Strict ABI decode of `(bytes vk, bytes message, bytes sig)` — alloy's
   `abi_decode_raw_validate` (lib.rs:106). Returns six values: the BYTE OFFSET
   into the input buffer and the length of each argument, or NIL on a decode
   failure. Offsets, not copies: the bytes are handed to the verifier straight
   out of the frame's input buffer.

   Validated: a 96-byte head, each offset canonical (high 224 bits zero) and in
   bounds, each length canonical and its data inside the input, and the padding
   up to each 32-byte boundary zero. A residual difference from alloy would show
   up as a 200-gas early revert where the chain charged 230 000+ (or the reverse)
   — i.e. as a header gas mismatch, not as a silent divergence."
  (let ((body (- input-len 4)))
    (when (< body 96) (return-from arc-pq-decode nil))
    (flet ((word (off)                                  ; absolute offset
             (loop with v = 0 for k below 32
                   do (setf v (logior (ash v 8) (mem-aref input-ptr :uint8 (+ off k))))
                   finally (return v)))
           (padding-zero-p (off n)                      ; absolute data offset
             (loop for k from n below (* 32 (ceiling n 32))
                   always (zerop (mem-aref input-ptr :uint8 (+ off k))))))
      (let ((offs '()))
        (dotimes (i 3)
          (let ((o (word (+ 4 (* 32 i)))))
            (when (or (>= o body) (>= o (ash 1 32))) (return-from arc-pq-decode nil))
            (push o offs)))
        (setf offs (nreverse offs))
        (let ((out '()))
          (dolist (o offs)
            (let ((head (+ 4 o)))
              (when (> (+ head 32) input-len) (return-from arc-pq-decode nil))
              (let ((n (word head)))
                (when (>= n (ash 1 32)) (return-from arc-pq-decode nil))
                (let ((data (+ head 32)))
                  (when (> (+ data (* 32 (ceiling n 32))) input-len)
                    (return-from arc-pq-decode nil))
                  (unless (padding-zero-p data n) (return-from arc-pq-decode nil))
                  (push (cons data n) out)))))
          (setf out (nreverse out))
          (values (car (first out)) (cdr (first out))
                  (car (second out)) (cdr (second out))
                  (car (third out)) (cdr (third out))))))))

(defun arc-pq-verify (input-ptr input-len gas)
  "PQSignatureVerifier.verifySlhDsaSha2128s — pq-precompile/src/lib.rs:92-163,
   in the spec's step order (Evm.Arc.Spec.Pq.run)."
  (arc-with-meter (used remaining gas)
    (multiple-value-bind (vk-off vk-len msg-off msg-len sig-off sig-len)
        (arc-pq-decode input-ptr input-len)
      (unless vk-off (early "Execution reverted"))           ; L105-108
      (charge (spec-arc-pq-base-gas))                        ; L110-112
      (charge (* (spec-arc-pq-msg-word-gas) (ceiling msg-len 32)))  ; L114-119
      ;; Two SEPARATE typed reverts, both after the work is charged (L121-134).
      (unless (= vk-len  (spec-arc-pq-vk-len))  (revert "Invalid verifying key length"))
      (unless (= sig-len (spec-arc-pq-sig-len)) (revert "Invalid signature length"))
      ;; Cross-check the accumulated gas against the emitted total formula — the
      ;; two derived forms must agree on every success path.
      (let ((total (spec-arc-pq-verify-gas (ceiling msg-len 32))))
        (unless (= used total)
          (error "arc PQ gas disagrees with the emitted formula: stepwise ~D, formula ~D (msg-len ~D)"
                 used total msg-len)))
      (arc-pq-ensure-lib!)
      (let ((rc (%arc-slhdsa-verify (inc-pointer input-ptr vk-off)  vk-len
                                    (inc-pointer input-ptr msg-off) msg-len
                                    (inc-pointer input-ptr sig-off) sig-len)))
        (when *trace-frames*
          (format *error-output* "~&[arc-pre] verifySlhDsaSha2128s msg-len=~D rc=~D used=~D~%"
                  msg-len rc used))
        (case rc
          (-1 (revert "Failed to parse verifying key"))       ; L136-145
          (-2 (revert "Failed to parse signature"))           ; L147-155
          (-3 (error "arc PQ verifier got a null pointer (vk-off ~D msg-off ~D sig-off ~D)"
                     vk-off msg-off sig-off))
          (t (values used (arc-abi-bool (= rc 1)) t)))))))    ; L157-162

(defun arc-precompile-run (addr kind caller input-ptr input-len gas is-static value)
  "Chain-precompile hook entry: dispatch by address + selector (macros.rs:95-135).
   Returns (values gas-used output success)."
  (let ((sel (arc-selector input-ptr input-len)))
    (flet ((early (msg)
             (let ((pen (spec-arc-early-revert-penalty)))
               (if (<= pen gas) (values pen (arc-revert-bytes msg) nil) (values gas #() nil)))))
      (cond
        ((null sel) (early "Input too short"))
        ((= addr +arc-native-coin-authority+)
         (case sel
           (#xbeabacc8 (arc-native-transfer caller kind input-ptr input-len gas is-static))
           (#x18160ddd (arc-native-total-supply input-ptr input-len gas))
           (#x40c10f19 (arc-native-mint caller kind input-ptr input-len gas is-static))
           (#x9dc29fac (arc-native-burn caller kind input-ptr input-len gas is-static))
           (t (early "Invalid selector"))))
        ((= addr +arc-native-coin-control+)
         (case sel
           (#x8e204c43 (arc-native-is-blocklisted input-ptr input-len gas))
           (#xe5c7160b (arc-native-blocklist nil caller kind input-ptr input-len gas is-static))
           (#x31b23020 (arc-native-blocklist t   caller kind input-ptr input-len gas is-static))
           (t (early "Invalid selector"))))
        ((= addr +arc-call-from+)
         (arc-call-from caller kind input-ptr input-len gas is-static value))
        ((= addr +arc-pq+)
         (if (= sel +arc-pq-selector+)
             (arc-pq-verify input-ptr input-len gas)
             (early "Invalid selector")))
        (t (error "arc precompile ~40,'0x not ported yet (SystemAccounting)" addr))))))

(defun arc-precompile-p (addr)
  "Addresses the Arc client intercepts. NativeCoinAuthority/Control, SystemAccounting and
   PQ are in the provider's lookup from genesis (precompile_provider.rs:46-67); CallFrom is
   NOT — evm.rs:1672 registers it only once Zero7 is active. Before Zero7 the address holds
   the genesis 1-byte placeholder 0x01, so a call runs that code and halts exceptionally,
   burning the whole forwarded pool (Arc block 12998407: a Multicall3From batch whose first
   callFrom consumed all 265511 forwarded gas and reverted the batch — we executed the
   precompile instead and came out 142225 gas short)."
  (or (and (>= addr #x1800000000000000000000000000000000000000)
           (<= addr #x1800000000000000000000000000000000000002))
      (= addr +arc-pq+)
      (and *arc-zero7* (= addr +arc-call-from+))))

;;; --- Unmetered pre-execution / frame-init warming (arc-node crates/evm) ------
;;; handler.rs check_blocklist (L157-178): before execution the client reads the
;;; blocklist slot of tx.from — and of tx.to when tx value > 0 — through
;;; `journal.sload`, which (a) loads NativeCoinControl 0x1800…0001 into the warm
;;; set and (b) warms those slots. Unmetered ("blocklist SLOADs are unmetered",
;;; validate_initial_tx_gas). Later CALLs to 0x1800…0001 therefore cost 100, and
;;; the precompile's is_blocklisted(sender) read costs 100 — exactly the −2500 /
;;; −2000 residuals seen before this hook existed.
;;; evm.rs check_blocklist_and_create_log (L499-590): every value-bearing
;;; CALL/CREATE frame-init reads both parties' blocklist slots the same way
;;; (`meter_sloads = false`). The Zero7+ selfdestructed-target probe is
;;; checkpoint-reverted, so it does NOT warm the target account.
;;; That frame-init also REVERTS value moves involving the zero address, a
;;; blocklisted party or a selfdestructed target (`arc-value-transfer-prewarm!`
;;; below), at every call site: cb-call, cb-create and the top-level tx in
;;; apply-tx (the last one was missing until stop #15, Arc block 21 418 236).
(defun arc-tx-prewarm! (from to value)
  "handler.rs check_blocklist: warm NativeCoinControl + the sender's blocklist
   slot, and the recipient's when the tx carries value."
  (access-addr! +arc-native-coin-control+)
  (access-slot! +arc-native-coin-control+ (arc-blocklist-slot from))
  (when (and to (plusp value))
    (access-slot! +arc-native-coin-control+ (arc-blocklist-slot to))))

(defun arc-blocklisted-unmetered-p (acct)
  "evm.rs opcode.rs is_blocklisted: an UNMETERED host sload of the blocklist slot
   (it still warms the slot and the control contract)."
  ;; Ordinary revert-scoped warming, like any journal sload: arc-node reads this slot
  ;; through `journal.sload` (evm.rs is_address_blocklisted), so a revert un-warms it.
  ;; Forcing it to survive reverts makes block 21 150 901 tx 20 undercharge by 2000.
  (access-addr! +arc-native-coin-control+)
  (let ((slot (arc-blocklist-slot acct)))
    (access-slot! +arc-native-coin-control+ slot)
    (fault-slot! +arc-native-coin-control+ slot)    ; a lazy world starts empty
    (not (zerop (storage-of *current-world* +arc-native-coin-control+ slot)))))

(defun arc-value-transfer-prewarm! (from to value &optional (emit-log t))
  "evm.rs check_blocklist_and_create_log (L497-590) for a value-bearing CALL/CREATE
   frame init, mirrored by Evm.Arc.Spec.NativeCoin.runFrameInitCheck: zero address
   on either side → revert before any read; both parties' blocklist slots read
   UNMETERED (warming them) → \"Blocked address\"; a destructed target → \"Cannot
   increase…\" (Zero7+ probes inside a checkpoint, so no warming); self-transfer →
   no log; else the EIP-7708 log. Returns NIL (proceed) or (values :revert bytes)."
  (cond ((or (zerop from) (zerop to)) (values :revert (arc-revert-bytes "Zero address not allowed")))
        ((arc-blocklisted-unmetered-p from) (values :revert (arc-revert-bytes "Blocked address")))
        ((arc-blocklisted-unmetered-p to) (values :revert (arc-revert-bytes "Blocked address")))
        ((destroyed-p to)
         (values :revert (arc-revert-bytes "Cannot increase the balance of selfdestructed account")))
        ;; The Transfer log is NOT part of the early check. arc-node returns it from
        ;; `before_frame_init` but pushes it only once the frame init SUCCEEDS ("Execute
        ;; first, then push the log only if the result indicates success", evm.rs
        ;; checked_frame_init) — so a CALL that then fails on insufficient balance emits
        ;; nothing. cb-call therefore probes early with EMIT-LOG nil and logs at the
        ;; transfer point; cb-create and apply-tx still do both in one call.
        (t (when (and emit-log (/= from to)) (arc-7708-log! from to value)) nil)))

(defun arc-value-transfer-log! (from to value)
  "The EIP-7708 Transfer log for a frame-init value move, once it is going to happen."
  (unless (= from to) (arc-7708-log! from to value)))

(defun arc-selfdestruct-check (a b bal)
  "arc_network_selfdestruct_impl (evm.rs opcode.rs:64-175, check_selfdestruct_accounts
   :258-345), mirrored by Evm.Arc.Spec.NativeCoin.runSelfdestructCheck. Only a
   non-zero balance triggers the Arc rules; each failure is a REVERT that keeps the
   remaining gas (the opcode's 5000 was already charged): zero target → message;
   self target → bare revert; blocklisted target/source → \"Blocked address\";
   destructed target → \"Cannot increase…\". Otherwise the transfer gets its
   EIP-7708 log. Returns NIL or (values :revert bytes)."
  (when (plusp bal)
    (cond ((zerop b) (values :revert (arc-revert-bytes "Zero address not allowed")))
          ((= a b) (values :revert (make-array 0 :element-type '(unsigned-byte 8))))
          ((arc-blocklisted-unmetered-p b) (values :revert (arc-revert-bytes "Blocked address")))
          ((arc-blocklisted-unmetered-p a) (values :revert (arc-revert-bytes "Blocked address")))
          ((destroyed-p b)        ; every policy loads the target and checks it (opcode.rs:331, :370)
           (values :revert (arc-revert-bytes "Cannot increase the balance of selfdestructed account")))
          (t (arc-7708-log! a b bal) nil))))

;; Installed through the Arc chain-spec (chains/arc.lisp, chain-spec.lisp).
