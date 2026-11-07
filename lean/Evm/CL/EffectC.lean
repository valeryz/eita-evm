import Evm.CL.EffectSload

/-! # CL/EffectC — the effect IR printed as C, for the native storage path

`Stmt.toCL` (Evm.CL.EffectIR) prints a callback's effect as Common Lisp; this prints the same
term as C, for the subset the native SLOAD path runs (docs/native-storage.md, owner note 6). The
term, its meaning (`Stmt.run`) and its proofs (`Evm.CL.EffectSloadProof`) are untouched: only the
printing is new, so the trusted part is this printer (the same class as `toCL`) and the
primitives it prints to (`c/storage_host.h`, `c/generated/limb_ops.h`; docs/trusted-surface.md).

The printed function runs on the native fast path of a callback: inputs `self` (the frame's
account) and `key` live in the storage host `h`; it returns the gas, or `EITA_SH_MISS` when the
slot is not in the native table — before any effect, so the Lisp effect then runs the whole term
(the slow path: the fault-in, the hooks). Each primitive is one call:

| IR | C |
|---|---|
| `faultSlot self key` | `if (!eita_sh_hit(h)) return EITA_SH_MISS;` (a present key is live: nothing to fault) |
| `letW x (sload self key)` | `uint64_t x[4]; eita_sh_sload(h, x);` |
| `warmSlot g self key x` | `int x = (g) && eita_sh_access_slot(h);` |
| `origRecord self key w` | `eita_sh_orig_record(h, w);` |
| `ret w` | `limb_copy(out, w);` |
| `charge g` | `gas += g;` |
| `forkGe n` | `(h->fork >= n)` |

Anything outside the subset is an emitter error (`Except.error`), never a silent omission. -/

namespace Evm.CL.EffectC

open Evm.CL.EffectIR

abbrev E := Except String

def selfKey (a : AExp) (k : WExp) : E Unit :=
  match a, k with
  | .var "self", .var "key" => pure ()
  | _, _ => throw "EffectC: storage primitives on (self, key) only"

def word : WExp → E String
  | .var x => pure x
  | _ => throw "EffectC: a word operand must be a bound word"

def bC : BExp → E String
  | .lit b => pure (if b then "1" else "0")
  | .var x => pure x
  | .not p => return s!"!{← bC p}"
  | .and p q => return s!"({← bC p} && {← bC q})"
  | .or p q => return s!"({← bC p} || {← bC q})"
  | .forkGe n => pure s!"(h->fork >= {n})"
  | _ => throw "EffectC: condition outside the subset"

def gC : GExp → E String
  | .lit n => pure s!"UINT64_C({n})"
  | .ite p t e => return s!"({← bC p} ? {← gC t} : {← gC e})"
  | .add a b => return s!"({← gC a} + {← gC b})"
  | _ => throw "EffectC: gas outside the subset"

/-- The C statements of `s`, at indentation `i`. -/
def sC (i : String) : Stmt → E (List String)
  | .skip => pure []
  | .seq s t => return (← sC i s) ++ (← sC i t)
  | .faultSlot a k => do selfKey a k; pure [s!"{i}if (!eita_sh_hit(h)) return EITA_SH_MISS;"]
  | .letW x (.sload a k) s => do
      selfKey a k
      return [s!"{i}uint64_t {x}[4];", s!"{i}eita_sh_sload(h, {x});"] ++ (← sC i s)
  | .warmSlot g a k x s => do
      selfKey a k
      return [s!"{i}const int {x} = {← bC g} && eita_sh_access_slot(h);"] ++ (← sC i s)
  | .origRecord a k w => do selfKey a k; return [s!"{i}eita_sh_orig_record(h, {← word w});"]
  | .ret w => return [s!"{i}limb_copy(out, {← word w});"]
  | .charge g => return [s!"{i}gas += {← gC g};"]
  | _ => throw "EffectC: statement outside the subset"

/-- A word-returning callback (SLOAD's) as a C function: `uint64_t name(eita_sh *h, uint64_t *out)`. -/
def toFnRet (name : String) (s : Stmt) : E String := do
  let body ← sC "  " s
  return s!"uint64_t {name}(eita_sh *h, uint64_t *out) \{\n  uint64_t gas = 0;\n" ++
    String.intercalate "\n" body ++ "\n  return gas;\n}\n"

/-- `c/generated/storage_effect.c`. -/
def file : E String := do
  let sload ← toFnRet "eita_spec_sload_effect" Evm.CL.EffectSload.term
  return "/* c/generated/storage_effect.c — EMITTED by `lake exe emitStorageC` from the effect IR\n" ++
    "   (lean/Evm/CL/EffectC.lean); do not edit. The terms and their proofs: Evm.CL.EffectSload\n" ++
    "   (sload_refines). The Lisp printing of the same terms: spec-sload-effect in\n" ++
    "   src/generated/host.lisp. */\n" ++
    "#include \"../storage_host.h\"\n#include \"limb_ops.h\"\n\n" ++
    "/* SLOAD (Evm.CL.EffectSload.term) */\n" ++ sload

end Evm.CL.EffectC
