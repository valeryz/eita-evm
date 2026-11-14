/-
  Evm.Optimism.Fjord.Spec.FastLz — the FastLZ compressed length of a byte string, the size
  input of the Fjord L1 cost function (`L1DataFeeFjord.estimatedSizeScaled`).

  Source: op-geth `core/types/rollup_cost.go` `FlzCompressLen` (op-geth@79e9d24, lines
  669-746), itself a port of solady `LibZip.flzCompress` (js/solady.js@5315d93); the Fjord
  spec (`specs/protocol/fjord/exec-engine.md` §"FastLZ") names it as the length function.
  It is applied to the full EIP-2718 encoding of the signed tx (op-geth
  `NewRollupCostData(tx.MarshalBinary())`).

  Clause by clause (Go variable names kept):
    * `ht` — an 8192-entry table of u32 positions, initially 0;
    * `hash(v) = ((2654435769 * v) >> 19) & 0x1fff` in u32 arithmetic (the product wraps);
    * `u24(i)` — three bytes little-endian;
    * `cmp(p, q, e)` — the match length from `p`/`q` up to `e`: on the first differing byte
      at offset `l` it returns `l + 1` (the Go loop sets `e = 0` and still increments);
    * `literals(r)` — `0x21` bytes per full 32-literal run, `r % 32 + 1` for the rest;
    * `match(l)` — `3` bytes per 262 of `l - 1`, plus `3` or `2`;
    * the scan from `ip = 2` while `ip < ipLimit = len - 13` (0 below 13 bytes): probe the
      table at `ip`, record `ip`, step; a hit within 0x1fff whose 3 bytes agree ends the
      probe; then the literals before it, the match, two table entries after it.

  The Lean function is total (fuel = the input length bounds both loops: every probe and
  every match advances `ip`). `flzCompressLenCL` is the same algorithm as Common Lisp,
  emitted to `src/generated/host.lisp` as `spec-flz-compress-len` (EmitHostCL), like
  `GasEmit.fakeExponentialCL`; the vectors below pin the Lean function on real Base
  transactions, and `tests/` pins the emitted CL on the same bytes and on op-geth's output.
-/

import Evm.BaseTypes

namespace Evm.Optimism.Fjord.Spec

/-- `hash(v)`: u32 product, then `>> 19`, `& 0x1fff`. -/
def flzHash (v : Nat) : Nat := (2654435769 * v) % 2 ^ 32 / 2 ^ 19 % 8192

/-- `u24(i)`: bytes `i, i+1, i+2`, little-endian (out-of-range bytes read as 0; the scan
    never reads past `len - 4`). -/
def flzU24 (b : Array UInt8) (i : Nat) : Nat :=
  (b.getD i 0).toNat + (b.getD (i + 1) 0).toNat * 256 + (b.getD (i + 2) 0).toNat * 65536

/-- `literals(r)`'s contribution to the output length. -/
def flzLiterals (r : Nat) : Nat :=
  0x21 * (r / 0x20) + (if r % 0x20 = 0 then 0 else r % 0x20 + 1)

/-- `match(l)`'s contribution (`l ≥ 1`). -/
def flzMatch (l : Nat) : Nat :=
  3 * ((l - 1) / 262) + (if (l - 1) % 262 ≥ 6 then 3 else 2)

/-- `cmp(p, q, e)` from offset `l` (fuel = the remaining span). -/
def flzCmp (b : Array UInt8) (p q : Nat) : Nat → Nat → Nat → Nat
  | 0, _, l => l
  | fuel + 1, span, l =>
    if l < span then
      (if b.getD (p + l) 0 ≠ b.getD (q + l) 0 then l + 1 else flzCmp b p q fuel span (l + 1))
    else l

/-- The table update `ht[h] = ip`. -/
def flzSet (ht : Nat → Nat) (h ip : Nat) : Nat → Nat := fun k => if k = h then ip else ht k

/-- The probe loop: returns the table, `ip` after it, and the candidate `r`. -/
def flzProbe (b : Array UInt8) (ipLimit : Nat) : Nat → (Nat → Nat) → Nat → (Nat → Nat) × Nat × Nat
  | 0, ht, ip => (ht, ip, 0)
  | fuel + 1, ht, ip =>
    let s := flzU24 b ip
    let h := flzHash s
    let r := ht h
    let ht := flzSet ht h ip
    let d := ip - r
    if ip ≥ ipLimit then (ht, ip, r)
    else if d ≤ 0x1fff ∧ s = flzU24 b r then (ht, ip + 1, r)
    else flzProbe b ipLimit fuel ht (ip + 1)

/-- The scan: returns `(a, n)` — the start of the trailing literals and the length so far. -/
def flzScan (b : Array UInt8) (ipLimit : Nat) : Nat → (Nat → Nat) → Nat → Nat → Nat → Nat × Nat
  | 0, _, _, a, n => (a, n)
  | fuel + 1, ht, ip, a, n =>
    if ip < ipLimit then
      let (ht, ip, r) := flzProbe b ipLimit b.size ht ip
      if ip ≥ ipLimit then (a, n)
      else
        let ip := ip - 1
        let n := if ip > a then n + flzLiterals (ip - a) else n
        let l := flzCmp b (r + 3) (ip + 3) b.size (ipLimit + 9 - (ip + 3)) 0
        let n := n + flzMatch l
        let ht := flzSet ht (flzHash (flzU24 b (ip + l))) (ip + l)
        let ht := flzSet ht (flzHash (flzU24 b (ip + l + 1))) (ip + l + 1)
        let ip := ip + l + 2
        flzScan b ipLimit fuel ht ip ip n
    else (a, n)

/-- `FlzCompressLen(ib)`. -/
def flzCompressLen (b : Array UInt8) : Nat :=
  let ipLimit := if b.size < 13 then 0 else b.size - 13
  let (a, n) := flzScan b ipLimit (b.size + 1) (fun _ => 0) 2 0 0
  n + flzLiterals (b.size - a)

/-- The same algorithm as Common Lisp (`(spec-flz-compress-len octets)`), emitted verbatim by
    EmitHostCL: the Go loops with `u32` products; `ht` a fresh 8192-word vector. -/
def flzCompressLenCL : String :=
  "(let* ((len (length ib)) (n 0) (ht (make-array 8192 :element-type '(unsigned-byte 32) :initial-element 0))\n" ++
  "         (ip-limit (if (< len 13) 0 (- len 13))) (a 0) (ip 2))\n" ++
  "    (declare (type (simple-array (unsigned-byte 8) (*)) ib) (type fixnum len n a ip ip-limit))\n" ++
  "    (labels ((u24 (i) (logior (aref ib i) (ash (aref ib (+ i 1)) 8) (ash (aref ib (+ i 2)) 16)))\n" ++
  "             (hsh (v) (logand (ash (logand (* 2654435769 v) #xffffffff) -19) #x1fff))\n" ++
  "             (literals (r) (incf n (* #x21 (floor r #x20))) (setf r (mod r #x20)) (unless (zerop r) (incf n (+ r 1))))\n" ++
  "             (match (l) (decf l) (incf n (* 3 (floor l 262))) (incf n (if (>= (mod l 262) 6) 3 2)))\n" ++
  "             (cmp (p q e) (let ((l 0) (e (- e q))) (loop while (< l e) do (when (/= (aref ib (+ p l)) (aref ib (+ q l))) (setf e 0)) (incf l)) l))\n" ++
  "             (set-next-hash (i) (setf (aref ht (hsh (u24 i))) i) (+ i 1)))\n" ++
  "      (loop while (< ip ip-limit)\n" ++
  "            do (let ((r 0))\n" ++
  "                 (loop (let* ((s (u24 ip)) (h (hsh s)))\n" ++
  "                         (setf r (aref ht h) (aref ht h) ip)\n" ++
  "                         (let ((d (- ip r)))\n" ++
  "                           (when (>= ip ip-limit) (return))\n" ++
  "                           (incf ip)\n" ++
  "                           (when (and (<= d #x1fff) (= s (u24 r))) (return)))))\n" ++
  "                 (when (>= ip ip-limit) (return))\n" ++
  "                 (decf ip)\n" ++
  "                 (when (> ip a) (literals (- ip a)))\n" ++
  "                 (let ((l (cmp (+ r 3) (+ ip 3) (+ ip-limit 9))))\n" ++
  "                   (match l)\n" ++
  "                   (setf ip (set-next-hash (set-next-hash (+ ip l))) a ip))))\n" ++
  "      (literals (- len a))\n" ++
  "      n))"

/-! ## Vectors

Short inputs are all literals; the Base vector is a real transaction (FastLZ length from
op-geth's `FlzCompressLen`, `tests/op-fastlz.lisp`). -/

example : flzCompressLen #[] = 0 := by decide
example : flzCompressLen #[1, 2, 3] = 4 := by decide
/-- 40 zero bytes: two literal runs around one match. -/
example : flzCompressLen (Array.replicate 40 0) = 12 := by decide +kernel

end Evm.Optimism.Fjord.Spec
