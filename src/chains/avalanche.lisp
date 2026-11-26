;;;; chains/avalanche.lisp — Avalanche C-Chain (Etna -> Fortuna -> Granite -> Helicon/SAE).
;;;;
;;;; Every fork threshold, gas formula, SAE floor, Warp price, atomic gas formula, and
;;;; GasClock pricing formula is emitted from Lean (`lean/Evm/Avalanche/*.lean`) into
;;;; `src/generated/host.lisp` (`spec-avax-*`). This file holds only the thin seams:
;;;;   - fork/network dispatch (mainnet 43114, Fuji 43113; pre-Etna refused loudly)
;;;;   - Coreth Warp Messenger precompile (0x0200...0005): getBlockchainID, sendWarpMessage,
;;;;     getVerifiedWarpMessage, getVerifiedWarpBlockHash, access-list predicate withholding,
;;;;     and header.extraData predicate result decoding (`predicate.BlockResults`)
;;;;   - Coreth post-block atomic transactions (`blockExtraData`, codec v0 ImportTx/ExportTx)
;;;;   - Helicon / SAE GasClock state progression (`BeforeBlock`, `BaseFee`, `AfterBlock`)
;;;;     and receipt-derived base fee cross-check
;;;;   - Coreth no-refund charging and full coinbase fee routing (0x0100...0000)

(in-package #:eita.chain.avalanche)

;;; --- Network & Coreth protocol constants (non-gas; all gas formulas are spec-avax-*) -------

(defconstant +avax-mainnet-id+ 43114)
(defconstant +avax-fuji-id+    43113)
(defconstant +avax-mainnet-network-id+ 1)
(defconstant +avax-fuji-network-id+    5)

;;; Coreth special addresses
(defconstant +coreth-blackhole+     #x0100000000000000000000000000000000000000)
(defconstant +coreth-native-bal+    #x0100000000000000000000000000000000000001)
(defconstant +coreth-native-call+   #x0100000000000000000000000000000000000002)
(defconstant +coreth-warp+          #x0200000000000000000000000000000000000005)

;;; AVAX asset IDs (big-endian 32 bytes)
(defparameter +avax-mainnet-asset-id+
  (hex->bytes "21e67317cbc4be2aeb00677ad6462778a8f52274b9d605df2591b23027a87dff"))
(defparameter +avax-fuji-asset-id+
  (hex->bytes "dbcf890f77dfadb39e5d198a383260b88f132c0f08b90754984495c260454e92"))

;;; C-Chain blockchain IDs (CB58 decoded: 2q9e4r6M... / yH8D7ThN...)
(defparameter +avax-mainnet-blockchain-id+
  (hex->bytes "0427d4b22a2a78bcddd456742caf91b56badbff985ee19aef14573e7343fd652"))
(defparameter +avax-fuji-blockchain-id+
  (hex->bytes "7fc93d85c6d62c5b2ac0b519c87010ea5294012d1e407030d6acd0021cac10d5"))

;;; Warp Messenger ABI selectors, event topic, and codec bounds
(defconstant +warp-sent-topic+
  #x56600c567728a800c0aa927500f831cb451df66a7af570eb4df4dfbf4674887d
  "keccak256(\"SendWarpMessage(address,bytes32,bytes)\").")
(defconstant +warp-sel-send+             #xee5b48eb)
(defconstant +warp-sel-verified-msg+     #x6f825350)
(defconstant +warp-sel-verified-hash+    #xce7f5929)
(defconstant +warp-sel-blockchain-id+    #x4213cf78)
(defconstant +warp-delimiter+            #xff)
(defconstant +warp-bls-sig-len+          96)
(defconstant +warp-max-payload-size+     (* 24 1024))
(defconstant +warp-max-results-size+     (ash 1 20))
(defconstant +warp-max-index+            #x7fffffff)
(defconstant +x2c-rate+                  1000000000 "nAVAX (1e-9) -> wei (1e-18).")
(defconstant +nanoseconds-per-sec+       1000000000)
(defconstant +max-u64+                   #xffffffffffffffff)

(defstartup *avax-net* (or (sb-ext:posix-getenv "AVAX_CHAIN") "mainnet")
  "mainnet (43114) or fuji (43113).")

(defun avax-fuji-p (net) (string-equal net "fuji"))
(defun avax-chain-id (net) (if (avax-fuji-p net) +avax-fuji-id+ +avax-mainnet-id+))
(defun avax-network-id (net) (if (avax-fuji-p net) +avax-fuji-network-id+ +avax-mainnet-network-id+))
(defun avax-blockchain-id (net) (if (avax-fuji-p net) +avax-fuji-blockchain-id+ +avax-mainnet-blockchain-id+))
(defun avax-asset-id (net) (if (avax-fuji-p net) +avax-fuji-asset-id+ +avax-mainnet-asset-id+))

(defun avax-fork-ord (net ts)
  "Avalanche fork ord from Lean: 0=preEtna, 1=Etna, 2=Fortuna, 3=Granite, 4=Helicon."
  (if (avax-fuji-p net)
      (spec-avax-fuji-fork-ord ts)
      (spec-avax-mainnet-fork-ord ts)))

;;; --- Per-block & per-tx dynamic state ------------------------------------------------------

(defvar *avalanche-net* "mainnet")
(defvar *avalanche-fork-ord* 3 "Current block's AvaxFork ord (1=Etna..4=Helicon).")
(defvar *avalanche-sae-block* nil "T when the current block runs under Helicon/SAE.")
(defvar *avalanche-exec-base-fee* 0 "Executed base fee for the current block.")
(defvar *avalanche-block-gas-limits* 0 "Running sum of tx gas limits in an SAE block.")
(defvar *avalanche-block-difficulty* 1
  "Current block's header.difficulty: Coreth keeps difficulty=1 (not EIP-4399 mixHash=0) for opcode 0x44.")
(defvar *avalanche-warp-results* nil "Hash table: tx-hash-int -> failed-index bitset octets.")
(defvar *avalanche-tx-warp-messages* #() "Vector of parsed WARP-PRED structs for the current tx.")
(defvar *avalanche-tx-warp-failed* nil "Failed-index bitset octets for the current tx, or :UNRECORDED.")
(defvar *avalanche-gas-clock* nil "Active SAE AVAX-GASCLOCK across sequential Helicon blocks, or NIL.")
(defvar *avalanche-clock-block* nil "Block number after which *AVALANCHE-GAS-CLOCK* stands.")

;;; --- SAE GasClock (mirrors lean/Evm/Avalanche/GasClock.lean & vms/saevm/gastime) -----------

(defstruct (avax-gasclock (:conc-name gc-))
  (seconds 0)
  (fraction 0)
  (excess 0)
  (target 1000000)
  (min-price 1))

(defun gc-rate (gc) (* (gc-target gc) 2))

(defun gc-scaling (gc) (min (* (gc-target gc) 87) +max-u64+))

(defun gc-div-ceil (a b)
  (if (zerop b) 0 (floor (+ a b -1) b)))

(defun gasclock-base-fee (gc)
  "Block base fee at clock state GC (`Time.BaseFee`), via Lean-emitted spec-avax-gasclock-base-fee."
  (spec-avax-gasclock-base-fee (gc-excess gc) (gc-target gc) (gc-min-price gc)))

(defun gasclock-excess-for (target price)
  "Least excess whose price reaches PRICE, or greatest below it when skipped (`excessForPrice`)."
  (if (<= price 1)
      0
      (let ((lo 1) (hi 1))
        (loop while (and (< hi +max-u64+)
                         (< (spec-avax-gasclock-price-at hi target) price))
              do (setf lo hi
                       hi (min +max-u64+ (* hi 2))))
        (loop while (< lo hi) do
          (let ((mid (+ lo (ash (- hi lo) -1))))
            (if (>= (spec-avax-gasclock-price-at mid target) price)
                (setf hi mid)
                (setf lo (1+ mid)))))
        (if (> (spec-avax-gasclock-price-at lo target) price) (1- lo) lo))))

(defun gasclock-enforce-min-excess! (gc)
  (when (< (spec-avax-gasclock-price-at (gc-excess gc) (gc-target gc)) (gc-min-price gc))
    (setf (gc-excess gc) (max (gc-excess gc) (gasclock-excess-for (gc-target gc) (gc-min-price gc)))))
  gc)

(defun gasclock-from-settled (gas-unix gas-num excess target-exp min-price-exp)
  "Construct a GasClock from a block's settled marker and its own header parameter exponents."
  (let* ((target (spec-avax-gasclock-target target-exp))
         (min-price (spec-avax-gasclock-min-price min-price-exp))
         (rate (* target 2))
         (gc (make-avax-gasclock
              :seconds (+ gas-unix (floor gas-num rate))
              :fraction (mod gas-num rate)
              :excess excess
              :target target
              :min-price min-price)))
    (gasclock-enforce-min-excess! gc)))

(defun gasclock-before-block! (gc block-sec block-ms)
  "Advance GC to consensus wall time (BLOCK-SEC, BLOCK-MS mod 1000 ms) (`Time.BeforeBlock`)."
  (let* ((r (gc-rate gc))
         (t-gas (gc-target gc))
         (ns (* (mod (or block-ms 0) 1000) 1000000))
         (into-sec (gc-div-ceil (* ns r) +nanoseconds-per-sec+))
         (to-sec (min (+ block-sec (floor into-sec r)) +max-u64+))
         (to-frac (mod into-sec r))
         (ahead (if (= to-sec (gc-seconds gc))
                    (> to-frac (gc-fraction gc))
                    (> to-sec (gc-seconds gc)))))
    (when ahead
      (let* ((raw-sec (- to-sec (gc-seconds gc)))
             (skip-sec (if (> (gc-fraction gc) to-frac) (1- raw-sec) raw-sec))
             (skip-frac (if (> (gc-fraction gc) to-frac)
                            (- r (- (gc-fraction gc) to-frac))
                            (- to-frac (gc-fraction gc))))
             (e1 (max 0 (- (gc-excess gc) (* skip-sec t-gas))))
             (e2 (max 0 (- e1 (floor (* skip-frac t-gas) r)))))
        (setf (gc-seconds gc) to-sec
              (gc-fraction gc) to-frac
              (gc-excess gc) e2)
        (gasclock-enforce-min-excess! gc)))
    gc))

(defun gasclock-after-block! (gc charged target-exp min-price-exp)
  "Advance GC by CHARGED gas and switch to next block parameters (`Time.AfterBlock`)."
  (let* ((old-r (gc-rate gc))
         (old-t (gc-target gc))
         (old-k (gc-scaling gc))
         (new-t (spec-avax-gasclock-target target-exp))
         (new-mp (spec-avax-gasclock-min-price min-price-exp))
         (new-r (* new-t 2))
         (new-k (min (* new-t 87) +max-u64+))
         (frac1 (+ (gc-fraction gc) charged))
         (sec1 (+ (gc-seconds gc) (floor frac1 old-r)))
         (rem1 (mod frac1 old-r))
         (exc1 (min (+ (gc-excess gc) (floor (* charged (- old-r old-t)) old-r)) +max-u64+))
         (exc2 (if (zerop old-k) exc1 (min (gc-div-ceil (* exc1 new-k) old-k) +max-u64+)))
         (frac2 (gc-div-ceil (* rem1 new-r) old-r)))
    (if (and (plusp new-r) (>= frac2 new-r))
        (setf (gc-seconds gc) (1+ sec1)
              (gc-fraction gc) (- frac2 new-r))
        (setf (gc-seconds gc) sec1
              (gc-fraction gc) frac2))
    (setf (gc-excess gc) exc2
          (gc-target gc) new-t
          (gc-min-price gc) new-mp)
    (gasclock-enforce-min-excess! gc)))

;;; --- SAE executed base fee from receipts ---------------------------------------------------

(defun sae-executed-base-fee (txs receipts header-base-fee block-number)
  "Derive the executed base fee of an SAE block from its dynamic-fee receipts:
   any type >= 2 tx with effectiveGasPrice < maxFeePerGas paid exactly (baseFee + maxPriorityFeePerGas).
   Returns (values base-fee shown-p)."
  (let ((shown nil))
    (loop for tx in txs
          for r in receipts
          for typ = (or (tx-type tx) 0)
          for cap = (tx-max-fee tx)
          for tip = (or (tx-max-priority tx) 0)
          for egp = (getf r :effective-gas-price)
          when (and (>= typ 2) cap egp (< egp cap))
            do (let ((cand (- egp tip)))
                 (when (minusp cand)
                   (error "block ~D: receipt effectiveGasPrice ~D < maxPriorityFeePerGas ~D"
                          block-number egp tip))
                 (when (and shown (/= shown cand))
                   (error "block ~D: inconsistent SAE executed base fees ~D vs ~D"
                          block-number shown cand))
                 (setf shown cand)))
    (values (or shown header-base-fee 0) (not (null shown)))))

;;; --- Avalanche atomic transaction codec (v0) -----------------------------------------------

(defun decode-atomic-batch (bytes &optional (net *avalanche-net*))
  "Decode Avalanche C-Chain `blockExtraData` (codec v0 ImportTx / ExportTx batch).
   Returns (values effects atomic-gas), where EFFECTS is a list of
   (:credit addr wei) or (:debit addr wei nonce-after) and atomic-gas comes from
   Lean-emitted `spec-avax-atomic-tx-gas`."
  (if (or (null bytes) (zerop (length bytes)))
      (values nil 0)
      (let ((pos 0)
            (len (length bytes))
            (asset-id (avax-asset-id net))
            (effects '())
            (total-gas 0))
        (labels ((ensure-avail (n)
                   (when (> (+ pos n) len)
                     (error "atomic payload truncated: need ~D bytes at ~D/~D" n pos len)))
                 (read-u16 ()
                   (ensure-avail 2)
                   (prog1 (logior (ash (aref bytes pos) 8) (aref bytes (1+ pos)))
                     (incf pos 2)))
                 (read-u32 ()
                   (ensure-avail 4)
                   (prog1 (logior (ash (aref bytes pos) 24)
                                  (ash (aref bytes (+ pos 1)) 16)
                                  (ash (aref bytes (+ pos 2)) 8)
                                  (aref bytes (+ pos 3)))
                     (incf pos 4)))
                 (read-u64 ()
                   (ensure-avail 8)
                   (let ((v 0))
                     (dotimes (i 8) (setf v (logior (ash v 8) (aref bytes (+ pos i)))))
                     (incf pos 8)
                     v))
                 (read-addr ()
                   (ensure-avail 20)
                   (let ((v 0))
                     (dotimes (i 20) (setf v (logior (ash v 8) (aref bytes (+ pos i)))))
                     (incf pos 20)
                     v))
                 (skip (n) (ensure-avail n) (incf pos n))
                 (expect-avax-asset ()
                   (ensure-avail 32)
                   (dotimes (i 32)
                     (unless (= (aref bytes (+ pos i)) (aref asset-id i))
                       (error "atomic tx carries non-AVAX asset id at byte ~D" pos)))
                   (incf pos 32))
                 (skip-credentials ()
                   (let ((ncred (read-u32)))
                     (dotimes (_ ncred)
                       (let ((ctype (read-u32)))
                         (unless (= ctype 9)
                           (error "unsupported atomic credential type ~D" ctype))
                         (let ((nsigs (read-u32)))
                           (skip (* 65 nsigs)))))))
                 (decode-import ()
                   (skip (+ 4 32 32)) ; network id, blockchain id, source chain
                   (let ((n-in (read-u32)) (sigs 0))
                     (dotimes (_ n-in)
                       (skip (+ 32 4 32)) ; utxo id + asset id
                       (skip (+ 4 8))     ; input type + amount
                       (let ((ns (read-u32)))
                         (skip (* 4 ns))
                         (incf sigs ns)))
                     (let ((n-out (read-u32)))
                       (dotimes (_ n-out)
                         (let ((addr (read-addr))
                               (navax (read-u64)))
                           (expect-avax-asset)
                           (push (list :credit addr (* navax +x2c-rate+)) effects))))
                     sigs))
                 (decode-export ()
                   (skip (+ 4 32 32)) ; network id, blockchain id, destination chain
                   (let ((n-in (read-u32)))
                     (dotimes (_ n-in)
                       (let ((addr (read-addr))
                             (navax (read-u64)))
                         (expect-avax-asset)
                         (let ((nonce (read-u64)))
                           (push (list :debit addr (* navax +x2c-rate+) (1+ nonce)) effects))))
                     (let ((n-out (read-u32)))
                       (dotimes (_ n-out)
                         (skip (+ 32 4 8)) ; asset id, output type, amount
                         (skip (+ 8 4))    ; locktime, threshold
                         (let ((nowners (read-u32)))
                           (skip (* 20 nowners)))))
                     n-in)))
          (let ((version (read-u16)))
            (unless (zerop version)
              (error "unsupported atomic codec version ~D (expected 0)" version)))
          (let ((count (read-u32)))
            (dotimes (_ count)
              (let* ((unsigned-from pos)
                     (tx-type (read-u32))
                     (sigs (case tx-type
                             (0 (decode-import))
                             (1 (decode-export))
                             (otherwise (error "unknown atomic transaction type ~D" tx-type))))
                     (unsigned-bytes (- pos unsigned-from)))
                (incf total-gas (spec-avax-atomic-tx-gas unsigned-bytes sigs))
                (skip-credentials))))
          (unless (= pos len)
            (error "~D trailing bytes after atomic batch" (- len pos)))
          (values (nreverse effects) total-gas)))))

;;; --- Coreth Warp Messenger precompile (0x0200...0005) --------------------------------------
;;; Full support for getBlockchainID, sendWarpMessage, getVerifiedWarpMessage,
;;; getVerifiedWarpBlockHash, access-list predicate gas withholding, and header.extraData
;;; predicate results (`predicate.BlockResults`).

(defstruct (warp-pred (:conc-name wp-))
  (num-keys 0)
  (source-chain-id nil)  ; 32-byte octet vector
  (payload-kind nil)     ; :addressed-call or :hash
  (source-addr 0)        ; 20-byte integer (for :addressed-call)
  (payload nil)          ; octet vector (payload for :addressed-call, or 32B hash for :hash)
  (num-signers 0))

(defun sha256-octets (bytes)
  "SHA-256 of octet vector BYTES using libeita's native %sha256-hash."
  (let ((n (length bytes))
        (out (make-array 32 :element-type '(unsigned-byte 8))))
    (with-foreign-object (out-buf :uint8 32)
      (if (plusp n)
          (with-foreign-object (in-buf :uint8 n)
            (dotimes (i n) (setf (mem-aref in-buf :uint8 i) (aref bytes i)))
            (%sha256-hash in-buf n out-buf))
          (%sha256-hash (null-pointer) 0 out-buf))
      (dotimes (i 32 out)
        (setf (aref out i) (mem-aref out-buf :uint8 i))))))

(defun warp-bytes->addr (bytes)
  "common.BytesToAddress: last 20 bytes of BYTES, left-padded with zeros if shorter."
  (let* ((len (length bytes))
         (start (max 0 (- len 20)))
         (v 0))
    (loop for i from start below len do (setf v (logior (ash v 8) (aref bytes i))))
    v))

(defun warp-bytes< (a b)
  "Unsigned lexicographic comparison of equal-length octet vectors A and B."
  (dotimes (i (length a) nil)
    (let ((x (aref a i)) (y (aref b i)))
      (cond ((< x y) (return t))
            ((> x y) (return nil))))))

(defun warp-parse-block-results (extra-data offset)
  "Parse `predicate.BlockResults` from header EXTRA-DATA starting at OFFSET.
   Returns a hash-table mapping tx-hash (u256 int) -> failed-index bitset octets."
  (let ((tbl (make-hash-table :test 'eql)))
    (when (or (null extra-data) (<= (length extra-data) offset))
      (return-from warp-parse-block-results tbl))
    (let ((len (- (length extra-data) offset))
          (pos offset))
      (when (> len +warp-max-results-size+)
        (error "Warp predicate results exceed 1 MiB (~D bytes)" len))
      (let ((end (length extra-data)))
        (labels ((ensure (n)
                   (when (> (+ pos n) end) (error "Warp predicate results truncated")))
                 (rd-u16 ()
                   (ensure 2)
                   (prog1 (logior (ash (aref extra-data pos) 8) (aref extra-data (1+ pos)))
                     (incf pos 2)))
                 (rd-u32 ()
                   (ensure 4)
                   (prog1 (logior (ash (aref extra-data pos) 24)
                                  (ash (aref extra-data (+ pos 1)) 16)
                                  (ash (aref extra-data (+ pos 2)) 8)
                                  (aref extra-data (+ pos 3)))
                     (incf pos 4)))
                 (rd-len ()
                   (let ((n (rd-u32)))
                     (when (> n +warp-max-index+) (error "Warp predicate results length overflow"))
                     n))
                 (rd-bytes (n)
                   (ensure n)
                   (prog1 (subseq extra-data pos (+ pos n))
                     (incf pos n))))
          (let ((ver (rd-u16)))
            (unless (zerop ver) (error "Warp predicate results unknown codec version ~D" ver)))
          (let ((ntxs (rd-len))
                (prev-tx nil))
            (dotimes (_ ntxs)
              (let ((tx-bytes (rd-bytes 32)))
                (when (and prev-tx (not (warp-bytes< prev-tx tx-bytes)))
                  (error "Warp predicate results tx keys not strictly sorted"))
                (setf prev-tx tx-bytes)
                (let ((npre (rd-len))
                      (prev-addr nil)
                      (warp-bits (make-array 0 :element-type '(unsigned-byte 8))))
                  (dotimes (_ npre)
                    (let ((addr-bytes (rd-bytes 20)))
                      (when (and prev-addr (not (warp-bytes< prev-addr addr-bytes)))
                        (error "Warp predicate results precompile keys not strictly sorted"))
                      (setf prev-addr addr-bytes)
                      (let ((bits (rd-bytes (rd-len))))
                        (when (= (octets-int addr-bytes) +coreth-warp+)
                          (setf warp-bits bits)))))
                  (setf (gethash (octets-int tx-bytes) tbl) warp-bits)))))
          (unless (= pos end)
            (error "Warp predicate results have ~D trailing bytes" (- end pos)))
          tbl)))))

(defun warp-unpad-keys (keys)
  "Unpack storage keys of a Warp access-list tuple (`Predicate.Bytes`):
   concatenate 32B keys, strip trailing 0x00, require exact ceil(end/32)=nkeys and 0xff delimiter."
  (let* ((nkeys (length keys))
         (buf (make-array (* nkeys 32) :element-type '(unsigned-byte 8))))
    (loop for k in keys for idx from 0 do
      (let ((base (* idx 32)))
        (dotimes (b 32)
          (setf (aref buf (+ base (- 31 b))) (ldb (byte 8 (* 8 b)) k)))))
    (let ((end (length buf)))
      (loop while (and (plusp end) (zerop (aref buf (1- end)))) do (decf end))
      (when (zerop end) (error "Warp predicate missing delimiter"))
      (unless (= (ceiling end 32) nkeys) (error "Warp predicate excess zero padding"))
      (unless (= (aref buf (1- end)) +warp-delimiter+) (error "Warp predicate wrong delimiter"))
      (subseq buf 0 (1- end)))))

(defun warp-parse-predicate (keys)
  "Parse one Warp access-list predicate tuple into a WARP-PRED struct."
  (let* ((raw (warp-unpad-keys keys))
         (len (length raw))
         (pos 0))
    (labels ((ensure (n) (when (> (+ pos n) len) (error "Warp signed message truncated")))
             (rd-u16 () (ensure 2) (prog1 (logior (ash (aref raw pos) 8) (aref raw (1+ pos))) (incf pos 2)))
             (rd-u32 ()
               (ensure 4)
               (prog1 (logior (ash (aref raw pos) 24) (ash (aref raw (+ pos 1)) 16)
                              (ash (aref raw (+ pos 2)) 8) (aref raw (+ pos 3)))
                 (incf pos 4)))
             (rd-len ()
               (let ((n (rd-u32)))
                 (when (> n +warp-max-index+) (error "Warp codec length too large"))
                 n))
             (rd-bytes (n) (ensure n) (prog1 (subseq raw pos (+ pos n)) (incf pos n))))
      (unless (zerop (rd-u16)) (error "Warp signed message unknown codec version"))
      (rd-u32) ; networkId (verified by consensus)
      (let* ((source-chain-id (rd-bytes 32))
             (payload-raw (rd-bytes (rd-len)))
             (sig-type (rd-u32)))
        (unless (zerop sig-type) (error "Warp unsupported signature type ~D" sig-type))
        (let ((signers (rd-bytes (rd-len))))
          (when (and (plusp (length signers)) (zerop (aref signers 0)))
            (error "Warp signers bitset has leading zero byte"))
          (rd-bytes +warp-bls-sig-len+)
          (unless (= pos len) (error "Warp signed message has trailing bytes"))
          ;; Parse inner WarpPayload (Hash=0 or AddressedCall=1, <= 24 KiB)
          (when (> (length payload-raw) +warp-max-payload-size+)
            (error "Warp payload exceeds 24 KiB"))
          (let ((ppos 0) (plen (length payload-raw)))
            (labels ((p-ensure (n) (when (> (+ ppos n) plen) (error "Warp payload truncated")))
                     (p-u16 () (p-ensure 2) (prog1 (logior (ash (aref payload-raw ppos) 8) (aref payload-raw (1+ ppos))) (incf ppos 2)))
                     (p-u32 ()
                       (p-ensure 4)
                       (prog1 (logior (ash (aref payload-raw ppos) 24) (ash (aref payload-raw (+ ppos 1)) 16)
                                      (ash (aref payload-raw (+ ppos 2)) 8) (aref payload-raw (+ ppos 3)))
                         (incf ppos 4)))
                     (p-len ()
                       (let ((n (p-u32)))
                         (when (> n +warp-max-index+) (error "Warp payload length too large"))
                         n))
                     (p-bytes (n) (p-ensure n) (prog1 (subseq payload-raw ppos (+ ppos n)) (incf ppos n))))
              (unless (zerop (p-u16)) (error "Warp payload unknown codec version"))
              (let ((kind (p-u32))
                    (num-signers (loop for b across signers sum (logcount b))))
                (multiple-value-bind (pkind saddr pbytes)
                    (case kind
                      (0 (values :hash 0 (p-bytes 32)))
                      (1 (let* ((sa (p-bytes (p-len)))
                                (pl (p-bytes (p-len))))
                           (values :addressed-call (warp-bytes->addr sa) pl)))
                      (otherwise (error "Warp unknown payload type ~D" kind)))
                  (unless (= ppos plen) (error "Warp payload has trailing bytes"))
                  (make-warp-pred :num-keys (length keys)
                                  :source-chain-id source-chain-id
                                  :payload-kind pkind
                                  :source-addr saddr
                                  :payload pbytes
                                  :num-signers num-signers))))))))))

(defun warp-tx-prepare (access-list)
  "Split ACCESS-LIST into Warp predicates and remaining EIP-2930 tuples.
   Returns (values warp-pred-vector non-warp-access-list total-predicate-gas)."
  (let ((preds '()) (kept '()) (pred-gas 0))
    (dolist (entry access-list)
      (if (= (car entry) +coreth-warp+)
          (let ((p (warp-parse-predicate (cdr entry))))
            (push p preds)
            (incf pred-gas (spec-avax-warp-predicate-gas (wp-num-keys p) (wp-num-signers p))))
          (push entry kept)))
    (values (coerce (nreverse preds) 'vector) (nreverse kept) pred-gas)))

(defun warp-failed-p (bitset index)
  "T iff bit INDEX is set in big-endian bitset BITSET (`set.Bits`)."
  (let ((byte-idx (floor index 8))
        (len (length bitset)))
    (and (< byte-idx len)
         (logbitp (mod index 8) (aref bitset (- len 1 byte-idx))))))

(defun abi-decode-small-word (bytes off)
  "Read big-endian uint64 from 32-byte ABI word at OFF, or NIL if upper 24 bytes are non-zero."
  (when (<= (+ off 32) (length bytes))
    (dotimes (i 24)
      (unless (zerop (aref bytes (+ off i)))
        (return-from abi-decode-small-word nil)))
    (let ((v 0))
      (loop for i from 24 below 32 do (setf v (logior (ash v 8) (aref bytes (+ off i)))))
      v)))

(defun abi-decode-uint32-arg (args)
  (let ((v (abi-decode-small-word args 0)))
    (and v (<= v #xffffffff) v)))

(defun abi-decode-bytes-arg (args)
  "Decode a single dynamic `bytes` ABI argument from ARGS, or NIL if malformed."
  (let ((offset (abi-decode-small-word args 0)))
    (when (and offset (<= (+ offset 32) (length args)))
      (let ((len (abi-decode-small-word args offset)))
        (when (and len (<= (+ offset 32 len) (length args)))
          (subseq args (+ offset 32) (+ offset 32 len)))))))

(defun warp-encode-unsigned-message (caller payload net)
  "Encode avalanchego warp.UnsignedMessage wrapping payload.AddressedCall(caller, payload)."
  (let* ((caller-bytes (u256->octets caller 20))
         (ac-len (+ 2 4 4 20 4 (length payload))))
    (when (> ac-len +warp-max-payload-size+)
      (return-from warp-encode-unsigned-message nil))
    (let* ((ac (make-array ac-len :element-type '(unsigned-byte 8) :initial-element 0))
           (p 0))
      (flet ((put-u16 (buf idx v)
               (setf (aref buf idx) (ldb (byte 8 8) v)
                     (aref buf (1+ idx)) (ldb (byte 8 0) v)))
             (put-u32 (buf idx v)
               (setf (aref buf idx)       (ldb (byte 8 24) v)
                     (aref buf (+ idx 1)) (ldb (byte 8 16) v)
                     (aref buf (+ idx 2)) (ldb (byte 8 8) v)
                     (aref buf (+ idx 3)) (ldb (byte 8 0) v))))
        ;; AddressedCall: u16(0) || u32(1) || u32(20) || caller[20] || u32(len) || payload
        (put-u16 ac 0 0) (incf p 2)
        (put-u32 ac p 1) (incf p 4)
        (put-u32 ac p 20) (incf p 4)
        (replace ac caller-bytes :start1 p) (incf p 20)
        (put-u32 ac p (length payload)) (incf p 4)
        (replace ac payload :start1 p)
        ;; UnsignedMessage: u16(0) || u32(networkId) || blockchainId[32] || u32(ac-len) || ac
        (let ((msg (make-array (+ 2 4 32 4 ac-len) :element-type '(unsigned-byte 8) :initial-element 0))
              (q 0))
          (put-u16 msg 0 0) (incf q 2)
          (put-u32 msg q (avax-network-id net)) (incf q 4)
          (replace msg (avax-blockchain-id net) :start1 q) (incf q 32)
          (put-u32 msg q ac-len) (incf q 4)
          (replace msg ac :start1 q)
          msg)))))

(defun warp-abi-encode-bytes (raw)
  "ABI-encode RAW as a single `bytes` tuple: word(32) || word(len) || raw || zero-pad."
  (let* ((len (length raw))
         (padded (* 32 (ceiling len 32)))
         (out (make-array (+ 64 padded) :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref out 31) 32)
    (loop for i below 8 do (setf (aref out (- 63 i)) (ldb (byte 8 (* 8 i)) len)))
    (replace out raw :start1 64)
    out))

(defun warp-abi-encode-message-output (source-chain-id sender payload valid)
  "ABI-encode `(WarpMessage(bytes32,address,bytes), bool valid)`."
  (let* ((plen (length payload))
         (padded (* 32 (ceiling plen 32)))
         (out (make-array (+ 192 padded) :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref out 31) #x40)                             ; offset to WarpMessage tuple
    (setf (aref out 63) (if valid 1 0))                   ; valid bool
    (when source-chain-id (replace out source-chain-id :start1 64)) ; sourceChainID
    (replace out (u256->octets sender 20) :start1 108)    ; originSenderAddress (left-padded in word 3)
    (setf (aref out 159) #x60)                            ; offset to payload inside tuple
    (loop for i below 8 do (setf (aref out (- 191 i)) (ldb (byte 8 (* 8 i)) plen)))
    (replace out payload :start1 192)
    out))

(defun warp-abi-encode-block-hash-output (source-chain-id block-hash valid)
  "ABI-encode `(WarpBlockHash(bytes32,bytes32), bool valid)`."
  (let ((out (make-array 96 :element-type '(unsigned-byte 8) :initial-element 0)))
    (when source-chain-id (replace out source-chain-id :start1 0))
    (when block-hash (replace out block-hash :start1 32))
    (setf (aref out 95) (if valid 1 0))
    out))

(defun warp-handle-verified-read (want-kind args gas)
  "Execute getVerifiedWarpMessage (:addressed-call) or getVerifiedWarpBlockHash (:hash)."
  (let ((base-cost (spec-avax-warp-read-gas 0)))
    (when (> base-cost gas)
      (return-from warp-handle-verified-read (values gas #() nil)))
    (let ((idx (abi-decode-uint32-arg args)))
      (when (or (null idx) (> idx +warp-max-index+))
        (return-from warp-handle-verified-read (values gas #() nil)))
      (flet ((invalid-out ()
               (if (eq want-kind :addressed-call)
                   (warp-abi-encode-message-output nil 0 #() nil)
                   (warp-abi-encode-block-hash-output nil nil nil))))
        (when (>= idx (length *avalanche-tx-warp-messages*))
          (return-from warp-handle-verified-read (values base-cost (invalid-out) t)))
        (when (eq *avalanche-tx-warp-failed* :unrecorded)
          (error "Avalanche block ~D tx ~D: Warp message ~D has no recorded verification result in header.extraData"
                 *cur-block* *cur-tx* idx))
        (when (warp-failed-p *avalanche-tx-warp-failed* idx)
          (return-from warp-handle-verified-read (values base-cost (invalid-out) t)))
        (let* ((pred (aref *avalanche-tx-warp-messages* idx))
               (total-cost (spec-avax-warp-read-gas (wp-num-keys pred))))
          (when (> total-cost gas)
            (return-from warp-handle-verified-read (values gas #() nil)))
          (unless (eq (wp-payload-kind pred) want-kind)
            (return-from warp-handle-verified-read (values gas #() nil)))
          (values total-cost
                  (if (eq want-kind :addressed-call)
                      (warp-abi-encode-message-output (wp-source-chain-id pred)
                                                      (wp-source-addr pred)
                                                      (wp-payload pred) t)
                      (warp-abi-encode-block-hash-output (wp-source-chain-id pred)
                                                         (wp-payload pred) t))
                  t))))))

(defun run-warp-precompile (kind caller input-ptr input-len gas is-static)
  "Execute Avalanche Warp Messenger precompile (0x0200...0005): all 4 selectors."
  ;; Since Granite, DELEGATECALL (2) and CALLCODE (1) revert consuming all gas.
  (when (and *p256verify* (or (= kind 1) (= kind 2)))
    (return-from run-warp-precompile (values gas #() nil)))
  (when (< input-len 4)
    (return-from run-warp-precompile (values gas #() nil)))
  (let ((sel (logior (ash (mem-aref input-ptr :uint8 0) 24)
                     (ash (mem-aref input-ptr :uint8 1) 16)
                     (ash (mem-aref input-ptr :uint8 2) 8)
                     (mem-aref input-ptr :uint8 3))))
    (flet ((read-args ()
             (let* ((arg-len (- input-len 4))
                    (args (make-array arg-len :element-type '(unsigned-byte 8))))
               (dotimes (i arg-len args) (setf (aref args i) (mem-aref input-ptr :uint8 (+ 4 i)))))))
      (cond
        ((= sel +warp-sel-blockchain-id+)
         (let ((cost (spec-avax-warp-blockchain-id-gas)))
           (if (> cost gas)
               (values gas #() nil)
               (values cost (copy-seq (avax-blockchain-id *avalanche-net*)) t))))
        ((= sel +warp-sel-send+)
         (let* ((arg-len (- input-len 4))
                (cost (spec-avax-warp-send-gas arg-len)))
           (when (or (> cost gas) is-static)
             (return-from run-warp-precompile (values gas #() nil)))
           (let* ((payload (abi-decode-bytes-arg (read-args)))
                  (unsigned (and payload (warp-encode-unsigned-message caller payload *avalanche-net*))))
             (unless unsigned
               (return-from run-warp-precompile (values gas #() nil)))
             (let* ((id-bytes (sha256-octets unsigned))
                    (id-int (octets-int id-bytes))
                    (log-data (warp-abi-encode-bytes unsigned)))
               (observe-log! +coreth-warp+ (list +warp-sent-topic+ caller id-int) log-data)
               (values cost id-bytes t)))))
        ((= sel +warp-sel-verified-msg+)
         (warp-handle-verified-read :addressed-call (read-args) gas))
        ((= sel +warp-sel-verified-hash+)
         (warp-handle-verified-read :hash (read-args) gas))
        (t
         (values gas #() nil))))))

;;; --- Chain hooks ---------------------------------------------------------------------------

(defun avalanche-precompile-p (addr)
  "Coreth stateful precompiles: Warp (0x0200...0005) and legacy multi-coin (0x0100...0001/2)."
  (or (= addr +coreth-warp+)
      (= addr +coreth-native-bal+)
      (= addr +coreth-native-call+)))

(defun avalanche-precompile-run (addr kind caller input-ptr input-len gas is-static &optional value)
  (declare (ignore value))
  (if (= addr +coreth-warp+)
      (run-warp-precompile kind caller input-ptr input-len gas is-static)
      (error "Avalanche block ~D tx ~D: unsupported Coreth stateful precompile ~A"
             *cur-block* *cur-tx* (addr-hex addr))))

(defun avalanche-tx-prewarm! (from to value)
  "Warm Coreth's active native-asset precompiles at tx start (RulesExtra.ActivePrecompiles).
   Warp (0x0200...0005) is warmed ONLY if the transaction's access list named it.
   P-256 (0x100) is warmed automatically by Eita's precompile seed when *p256verify* is T."
  (declare (ignore from to value))
  (access-addr! +coreth-blackhole+)
  (access-addr! +coreth-native-bal+)
  (access-addr! +coreth-native-call+)
  (when (plusp (length *avalanche-tx-warp-messages*))
    (access-addr! +coreth-warp+)))

(defun avalanche-seed-gasclock-lookahead (target-height)
  "Attempt to seed *AVALANCHE-GAS-CLOCK* at TARGET-HEIGHT by looking ahead in *BLOCK-SOURCE*
   (up to 32 blocks) for a header whose settledHeight equals TARGET-HEIGHT. Returns T if seeded."
  (when (and *block-source* (>= target-height 0))
    (let ((fetch-fn (eita.input::block-source-block *block-source*)))
      (when fetch-fn
        (loop for k from (1+ target-height) to (+ target-height 32)
              for b = (ignore-errors (funcall fetch-fn k))
              while b
              for sh = (blk-settled-height b)
              do (cond ((eql sh target-height)
                        (when (and (blk-settled-gas-unix b) (blk-settled-gas-numerator b)
                                   (blk-settled-excess b) (blk-target-exponent b)
                                   (blk-min-price-exponent b))
                          (setf *avalanche-gas-clock*
                                (gasclock-from-settled
                                 (blk-settled-gas-unix b)
                                 (blk-settled-gas-numerator b)
                                 (blk-settled-excess b)
                                 (blk-target-exponent b)
                                 (blk-min-price-exponent b))
                                *avalanche-clock-block* target-height)
                          (format t "~&[avalanche] seeded SAE GasClock at block ~D from settled header ~D~%"
                                  target-height k)
                          (return t)))
                       ((and sh (> sh target-height))
                        (return nil))))))))

(defun avalanche-block-setup (net)
  (lambda (n blk ts)
    (let ((af (avax-fork-ord net ts)))
      (when (zerop af)
        (error "Avalanche block ~D (timestamp ~D) precedes Etna; Eita supports Etna onward" n ts))
      (let ((eth-fork (spec-avax-eth-analog-ord af)))
        (unless (= *fork-ord* eth-fork)
          (setf *fork-ord* eth-fork)
          (%set-fork eth-fork)))
      (setf *avalanche-net* net
            *avalanche-fork-ord* af
            *el-fork-ord* nil
            *p256verify* (= 1 (spec-avax-p256-active af)))
      (let* ((sae (or (= 1 (spec-avax-sae-active af))
                      (not (null (blk-settled-height blk)))))
             (ext-gas (or (blk-ext-data-gas-used blk) 0))
             (hdr-bf (or (blk-base-fee blk) 0))
             (receipts (when sae (or (blk-receipts blk) (and *block-source* (fetch-receipts n)))))
             ;; Auto-seed SAE GasClock on resume/first SAE block if settling header is available
             (_seeded (when (and sae (not (and *avalanche-gas-clock* (eql *avalanche-clock-block* (1- n)))))
                        (avalanche-seed-gasclock-lookahead (1- n))))
             ;; Advance active sequential SAE GasClock if continuous from block n-1
             (clock-bf
              (when (and sae *avalanche-gas-clock* (eql *avalanche-clock-block* (1- n)))
                (gasclock-before-block! *avalanche-gas-clock* ts (blk-timestamp-ms blk))
                (gasclock-base-fee *avalanche-gas-clock*))))
        (declare (ignore _seeded))
        (multiple-value-bind (rcpt-bf shown-p)
            (if sae
                (sae-executed-base-fee (blk-txs blk) receipts hdr-bf n)
                (values hdr-bf nil))
          (when (and clock-bf shown-p)
            (gate n :header "SAE GasClock baseFee" rcpt-bf clock-bf))
          (setf *avalanche-sae-block* sae
                *avalanche-block-gas-limits* 0
                *avalanche-block-difficulty* (if (plusp (blk-difficulty blk)) (blk-difficulty blk) (blk-mix-hash blk))
                *avalanche-warp-results* (warp-parse-block-results (blk-extra-data blk)
                                                                   (spec-avax-extradata-offset af))
                *avalanche-exec-base-fee* (cond (clock-bf clock-bf)
                                                (shown-p rcpt-bf)
                                                (t hdr-bf))
                *chain-header-foreign*
                (cond (sae
                       '("gasUsed" "logsBloom" "receiptsRoot" "withdrawalsRoot" "requestsHash" "blobGasUsed"))
                      ((plusp ext-gas)
                       '("gasUsed" "withdrawalsRoot" "requestsHash" "blobGasUsed"))
                      (t
                       '("withdrawalsRoot" "requestsHash" "blobGasUsed")))))))))

(defun avalanche-pre-block! (world n blk coinbase block-ctx)
  "No EIP-4788 or EIP-2935 system contracts are deployed on the Avalanche C-Chain."
  (declare (ignore world n blk coinbase block-ctx))
  nil)

(defun avalanche-post-block! (world n blk total-gas coinbase block-ctx)
  "Apply Avalanche atomic ImportTx/ExportTx effects, verify SAE / atomic header gas,
   and advance the active SAE GasClock."
  (declare (ignore coinbase block-ctx))
  (multiple-value-bind (effects atomic-gas) (decode-atomic-batch (blk-block-extra-data blk) *avalanche-net*)
    (when effects
      (observe-tx-begin!)
      (dolist (eff effects)
        (ecase (first eff)
          (:credit
           (destructuring-bind (_ addr wei) eff
             (declare (ignore _))
             (fault-account! addr)
             (balance-delta! world addr wei)))
          (:debit
           (destructuring-bind (_ addr wei nonce-after) eff
             (declare (ignore _))
             (fault-account! addr)
             (balance-delta! world addr (- wei))
             (setf (nonce-of world addr) nonce-after)))))
      (observe-tx-end! n +postblock-tx+ t))
    (cond (*avalanche-sae-block*
           (gate n :header "SAE gasUsed (limits + atomic)"
                 (blk-gas-used blk) (+ *avalanche-block-gas-limits* atomic-gas))
           (when (and *avalanche-gas-clock* (eql *avalanche-clock-block* (1- n))
                      (blk-target-exponent blk) (blk-min-price-exponent blk))
             (gasclock-after-block! *avalanche-gas-clock* (+ total-gas atomic-gas)
                                    (blk-target-exponent blk) (blk-min-price-exponent blk))
             (setf *avalanche-clock-block* n)))
          ((plusp (or (blk-ext-data-gas-used blk) 0))
           (gate n :header "pre-SAE gasUsed (txs + atomic)"
                 (blk-gas-used blk) (+ total-gas atomic-gas))))))

(defun avalanche-run-tx (world tx receipt block-ctx coinbase blk idx)
  "Execute one Avalanche C-Chain user transaction (Coreth + Warp + Helicon/SAE rules)."
  (declare (ignore world))
  (let* ((from (tx-sender tx))
         (gas-limit (tx-gas-limit tx))
         (to (tx-to tx))
         (value (tx-value tx))
         (base-fee *avalanche-exec-base-fee*)
         (tx-block-ctx (list* :base-fee base-fee :prev-randao *avalanche-block-difficulty* block-ctx))
         (egp (effective-gas-price tx base-fee))
         (block-gas-limit (getf block-ctx :gas-limit))
         (used-so-far (if *avalanche-sae-block* *avalanche-block-gas-limits* *receipt-cumulative-gas*))
         (left (- block-gas-limit used-so-far)))
    (when (> gas-limit left)
      (invalid! "gas allowance"
                "blk=~D tx=~D is invalid: gas limit ~D above the block's ~D left"
                blk idx gas-limit left))
    (when *avalanche-sae-block*
      (incf *avalanche-block-gas-limits* gas-limit))
    ;; Separate Warp access-list predicates from ordinary EIP-2930 entries.
    (multiple-value-bind (warp-preds non-warp-al pred-gas)
        (warp-tx-prepare (tx-access-list tx))
      (when (> pred-gas gas-limit)
        (invalid! "gas allowance"
                  "blk=~D tx=~D is invalid: Warp predicate gas ~D exceeds gas limit ~D"
                  blk idx pred-gas gas-limit))
      (let* ((has-warp (plusp (length warp-preds)))
             (exec-tx (if has-warp
                          (make-tx :type (tx-type tx) :sender from :to to :nonce (tx-nonce tx)
                                   :gas-limit (- gas-limit pred-gas) :gas-price (tx-gas-price tx)
                                   :max-fee (tx-max-fee tx) :max-priority (tx-max-priority tx)
                                   :value value :data (tx-data tx) :access-list non-warp-al
                                   :blob-hashes (tx-blob-hashes tx) :max-blob-fee (tx-max-blob-fee tx)
                                   :mint (tx-mint tx) :auth-count (tx-auth-count tx)
                                   :auth-list (tx-auth-list tx) :hash (tx-hash tx)
                                   :chain-id (tx-chain-id tx) :v (tx-v tx) :r (tx-r tx) :s (tx-s tx))
                          tx))
             (*avalanche-tx-warp-messages* warp-preds)
             (*avalanche-tx-warp-failed*
              (if (and has-warp *avalanche-warp-results*)
                  (multiple-value-bind (bits found) (gethash (tx-hash tx) *avalanche-warp-results*)
                    (if found bits :unrecorded))
                  #())))
        (observe-tx-begin!)
        (fault-account! from)
        (when (and receipt (getf receipt :effective-gas-price))
          (gate blk idx "effectiveGasPrice" (getf receipt :effective-gas-price) egp))
        (reset-tx-state (- gas-limit pred-gas))
        (when *chain-tx-prewarm-hook*
          (funcall *chain-tx-prewarm-hook*
                   from (or to (derive-create-address from (nonce-of *current-world* from))) value))
        (multiple-value-bind (success exec-used rej)
            (apply-tx exec-tx coinbase tx-block-ctx :egp egp :extra (* pred-gas egp))
          (unless (zerop rej)
            (invalid! (aref +tx-invalid-reasons+ (1- rej))
                      "blk=~D tx=~D is invalid: ~A (sender nonce ~D balance ~D)"
                      blk idx (aref +tx-invalid-reasons+ (1- rej))
                      (nonce-of *current-world* from) (balance-of *current-world* from)))
          ;; Lean-emitted Coreth / SAE tx gas charging (no refunds; SAE ceil(limit/2) floor).
          (let* ((spent (+ (intrinsic-gas exec-tx) exec-used))
                 (gas-used (spec-avax-tx-gas-used *avalanche-fork-ord* spent pred-gas gas-limit)))
            ;; Unused gas back to sender; full fee (base + tip) to coinbase.
            (spec-gas-refund-effect from gas-limit gas-used egp)
            (spec-coinbase-fee-effect coinbase gas-used egp 0)
            (spec-destroy-effect)
            (spec-sweep-effect)
            (observe-tx-end! blk idx success)
            (values gas-used (if success 1 0) egp)))))))

(defun avalanche-chain-spec (&optional (net *avax-net*))
  "Avalanche C-Chain as a chain-spec (mainnet 43114 or fuji 43113)."
  (let ((fuji (avax-fuji-p net)))
    (make-chain-spec
     :name (if fuji "Avalanche C-Chain Fuji" "Avalanche C-Chain Mainnet")
     :id (avax-chain-id net)
     :banner "Etna -> Fortuna -> Granite -> Helicon/SAE (Lean-emitted spec-avax-*)"
     :reorg-depth 0
     :rpc-url (or (sb-ext:posix-getenv "AVAX_RPC_URL")
                  (if fuji "https://api.avax-test.network/ext/bc/C/rpc"
                           "https://api.avax.network/ext/bc/C/rpc"))
     :fork-ord (lambda (n ts)
                 (declare (ignore n))
                 (spec-avax-eth-analog-ord (avax-fork-ord net ts)))
     :block-setup (avalanche-block-setup net)
     :pre-block #'avalanche-pre-block!
     :post-block #'avalanche-post-block!
     :run-tx #'avalanche-run-tx
     :tx-prewarm #'avalanche-tx-prewarm!
     :precompile-p #'avalanche-precompile-p
     :precompile-run #'avalanche-precompile-run
     :header-foreign '("withdrawalsRoot" "requestsHash" "blobGasUsed")
     :coreth-trie t
     :observe-kinds '(:storage_diff :account_diff :transfer :log :tx :block))))

(register-chain-spec "avalanche" (lambda () (avalanche-chain-spec "mainnet")))
(register-chain-spec "avalanche-fuji" (lambda () (avalanche-chain-spec "fuji")))

(defun main-avalanche (args &optional (net *avax-net*))
  "Install Avalanche C-Chain (mainnet or fuji), then run the generic driver."
  (setf *avax-net* net
        *avalanche-gas-clock* nil
        *avalanche-clock-block* nil)
  (install-chain-spec! (avalanche-chain-spec net))
  (replay-main args))
