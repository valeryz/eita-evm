/-
  Evm.Arc.Spec.Pq — Arc's PQ precompile (0x1800…0004), clause by clause.

  SOURCE OF TRUTH: arc-node `crates/pq-precompile/src/lib.rs` at 6e76402
  (`run_pq_precompile`, L86-163). Line refs below are that file. The precompile
  verifies an SLH-DSA-SHA2-128s (FIPS 205) signature and returns an ABI-encoded
  bool; it is in the provider's lookup from genesis on mainnet (Zero6-gated).

    verifySlhDsaSha2128s(bytes vk, bytes message, bytes sig) → bool

  Gas is independent of the verification RESULT: 230 000 base + 6 per 32-byte
  message word, charged before the key and signature are parsed. That is what
  makes a wrong verdict so dangerous here — it costs exactly the same gas as the
  right one, so no gas gate can catch it; only the returned bool (and whatever
  the caller does with it) diverges. Hence `Evm.Arc.Spec.Pq.isValid` is an
  OBSERVED input in the view, and the obligation it carries is discharged by
  linking the same `slh-dsa` crate arc-node uses (rust/pq), not by a second
  implementation of SPHINCS+.

  Ported against the real chain call, which is also pinned as an example below:
  block 21 452 605 tx 17, a STATICCALL at depth 4 into 0x1800…0004 with 8 132
  bytes of input, `gasUsed = 230 006`, output `0x…01`. That block is where the
  continuous replay stopped (stop #14) — the address was in `arc-precompile-p`
  but had no implementation, so the seam raised instead of guessing.
-/

import Evm.Arc.Spec.NativeCoin
import Evm.CL.GasEmit

namespace Evm.Arc.Spec.Pq

open Evm.Arc.Spec.NativeCoin (Outcome step earlyRevert)
open Evm.CL.GasEmit (Expr mkEnv)

/-- PQ precompile address (`PQ_ADDRESS`, L25). -/
def pqAddress : Nat := 0x1800000000000000000000000000000000000004

/-- `verifySlhDsaSha2128s(bytes,bytes,bytes)` — the first four bytes of its
    keccak256, i.e. alloy's `IPQ::verifySlhDsaSha2128sCall::SELECTOR` (L102). -/
def selVerifySlhDsaSha2128s : Nat := 0xbf4db8ba

/-- `VERIFY_BASE_GAS` (L33): priced against the SHA-256 precompile's per-word
    work anchor, see `crates/precompiles/benches/pq.rs`. -/
def verifyBaseGas : Nat := 230000

/-- `GAS_PER_MSG_WORD` (L40) = `KECCAK256WORD`: SLH-DSA-SHA2-128s hashes the
    message once through H_msg (SHA-256 + MGF1), comparable to KECCAK256. -/
def gasPerMsgWord : Nat := 6

/-- `VK_LEN` / `SIG_LEN` (L42-43) for the SHA2-128s parameter set. These are
    checked as SEPARATE, typed reverts, so they must not collapse into one. -/
def vkLen  : Nat := 32
def sigLen : Nat := 7856

/-- `(message.len() as u64).div_ceil(32) * GAS_PER_MSG_WORD` (L115). -/
def msgWordGas (msgLen : Nat) : Nat := ((msgLen + 31) / 32) * gasPerMsgWord

/-- What the host observes, in source order. `decodeOk` is the strict ABI decode
    (`abi_decode_raw_validate`, L106) — three `bytes` at canonical offsets with
    zero padding — exactly as `argsOk` is an observed flag for `transfer`.
    `keyParseOk`/`sigParseOk` are the two `try_from`s (L136, L147); with the
    length checks already passed they can only fail on a parameter-set
    mismatch, which `eita_slhdsa_sha2_128s_selftest` rules out at load time. -/
structure PqView where
  gas        : Nat      -- forwarded gas
  inputLen   : Nat      -- total calldata length
  selectorOk : Bool
  decodeOk   : Bool
  vkLenObs   : Nat
  msgLen     : Nat
  sigLenObs  : Nat
  keyParseOk : Bool
  sigParseOk : Bool
  isValid    : Bool     -- SLH-DSA-SHA2-128s verification (rust/pq → slh-dsa)
  deriving Repr

/-- The precompile, clause by clause (L92-163).

    Order is load-bearing twice over: the three early paths charge only the
    200-gas penalty and must precede any base charge (so probing is not free
    yet a short input does not burn 230 000), and the base + per-word charges
    must precede the length checks (so a wrong-length key still pays for the
    work the node did decoding it). -/
def run (v : PqView) : Outcome :=
  let s0 : Nat × Nat := (0, v.gas)
  if v.inputLen < 4 then
    earlyRevert s0 "Input too short"                      -- L96-98
  else if !v.selectorOk then
    earlyRevert s0 "Invalid selector"                     -- L100-103
  else if !v.decodeOk then
    earlyRevert s0 "Execution reverted"                   -- L105-108
  else
    match step s0 verifyBaseGas with                      -- L110-112
    | none => .oog
    | some s1 =>
      match step s1 (msgWordGas v.msgLen) with            -- L114-119
      | none => .oog
      | some s2 =>
        if v.vkLenObs ≠ vkLen then
          .revert s2.1 "Invalid verifying key length"     -- L121-127
        else if v.sigLenObs ≠ sigLen then
          .revert s2.1 "Invalid signature length"         -- L128-134
        else if !v.keyParseOk then
          .revert s2.1 "Failed to parse verifying key"    -- L136-145
        else if !v.sigParseOk then
          .revert s2.1 "Failed to parse signature"        -- L147-155
        else
          .success s2.1 v.isValid                         -- L157-162

/-! ## The host's gas expression (emitted to `src/generated/host.lisp`) -/

/-- Success-path gas as a `GasEmit.Expr` over the message word count. -/
def verifyGas : Expr := .add (.lit verifyBaseGas) (.mul (.lit gasPerMsgWord) (.var "msg-words"))

def verifyBaseGasExpr : Expr := .lit verifyBaseGas
def gasPerMsgWordExpr : Expr := .lit gasPerMsgWord
def vkLenExpr  : Expr := .lit vkLen
def sigLenExpr : Expr := .lit sigLen

/-! ## What the chain says

The real call is the test: anything that drifts from it changes a bool whose
cost is identical either way. -/

/-- Block 21 452 605 tx 17: one 32-byte message word, a valid signature. -/
def arcBlock21452605Tx17 : PqView :=
  { gas := 358134, inputLen := 8132, selectorOk := true, decodeOk := true,
    vkLenObs := 32, msgLen := 32, sigLenObs := 7856,
    keyParseOk := true, sigParseOk := true, isValid := true }

example : run arcBlock21452605Tx17 = .success 230006 true := by decide
example : verifyGas.eval (mkEnv [("msg-words", 1)]) = 230006 := by decide

/-- The gas does NOT move with the verdict — the whole reason the verifier has
    to be the same implementation and not a lookalike. -/
example : run { arcBlock21452605Tx17 with isValid := false } = .success 230006 false := by decide

/-- A message of 0 words costs the base only; 33 bytes costs two words. -/
example : msgWordGas 0 = 0 := by decide
example : msgWordGas 1 = 6 := by decide
example : msgWordGas 32 = 6 := by decide
example : msgWordGas 33 = 12 := by decide

/-- One gas short of the base: halt, not revert, and the whole pool is gone. -/
example : run { arcBlock21452605Tx17 with gas := verifyBaseGas - 1 } = .oog := by decide
/-- Enough for the base, one short of the message word. -/
example : run { arcBlock21452605Tx17 with gas := verifyBaseGas + 5 } = .oog := by decide
example : run { arcBlock21452605Tx17 with gas := verifyBaseGas + 6 } = .success 230006 true := by decide

/-- The early paths charge 200 and nothing else. -/
example : run { arcBlock21452605Tx17 with inputLen := 3 } = .revert 200 "Input too short" := by decide
example : run { arcBlock21452605Tx17 with selectorOk := false } = .revert 200 "Invalid selector" := by decide
example : run { arcBlock21452605Tx17 with decodeOk := false } = .revert 200 "Execution reverted" := by decide
/-- …and if even the penalty does not fit, it is a halt. -/
example : run { arcBlock21452605Tx17 with inputLen := 3, gas := 199 } = .oog := by decide

/-- The length reverts come AFTER the work is charged, and are distinguishable. -/
example : run { arcBlock21452605Tx17 with vkLenObs := 31 }
        = .revert 230006 "Invalid verifying key length" := by decide
example : run { arcBlock21452605Tx17 with sigLenObs := 7855 }
        = .revert 230006 "Invalid signature length" := by decide
example : run { arcBlock21452605Tx17 with keyParseOk := false }
        = .revert 230006 "Failed to parse verifying key" := by decide
example : run { arcBlock21452605Tx17 with sigParseOk := false }
        = .revert 230006 "Failed to parse signature" := by decide

/-- Gas of an outcome, `none` for a halt (which consumes the whole pool). -/
def gasOf : Outcome → Option Nat
  | .success g _ => some g
  | .revert  g _ => some g
  | .oog         => none

/-- Charging order, as a theorem rather than a comment: once the three early
    paths are past and the pool covers base + words, the gas used is exactly
    base + words on EVERY remaining path — independent of the observed lengths,
    of the parse results, and of the verdict. A regression that moved a length
    check above the base charge, or made the verdict cost anything, breaks
    this. -/
theorem gas_is_base_plus_words (v : PqView)
    (h4 : 4 ≤ v.inputLen) (hs : v.selectorOk = true) (hd : v.decodeOk = true)
    (hg : verifyBaseGas + msgWordGas v.msgLen ≤ v.gas) :
    gasOf (run v) = some (verifyBaseGas + msgWordGas v.msgLen) := by
  unfold run
  simp only [hs, hd, Bool.not_true]
  rw [if_neg (show ¬ v.inputLen < 4 by omega)]
  have hb : verifyBaseGas ≤ v.gas := by omega
  have hw : msgWordGas v.msgLen ≤ v.gas - verifyBaseGas := by omega
  unfold step
  simp only [hb, hw, if_true, Nat.zero_add]
  -- Every remaining branch carries the SAME gas, so take them one by one.
  by_cases h1 : v.vkLenObs = vkLen
  · by_cases h2 : v.sigLenObs = sigLen
    · cases hk : v.keyParseOk
      · simp [h1, h2, gasOf]
      · cases v.sigParseOk <;> simp [h1, h2, gasOf]
    · simp [h1, h2, gasOf]
  · simp [h1, gasOf]

end Evm.Arc.Spec.Pq
