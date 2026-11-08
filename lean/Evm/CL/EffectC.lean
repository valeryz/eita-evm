import Evm.CL.EffectSload
import Evm.CL.EffectSstore

/-! # CL/EffectC — the effect IR printed as C, for the native storage path

`Stmt.toCL` (Evm.CL.EffectIR) prints the other callbacks' effects as Common Lisp; this prints the
SLOAD and SSTORE terms as C, their one execution path (docs/native-storage.md, owner note 6 and
its addendum 2: there is no Lisp printing of these terms). The terms, their meaning (`Stmt.run`)
and their proofs (`Evm.CL.EffectSloadProof`, `EffectSstoreProof`) are untouched: the trusted part
is this printer (the same class as `toCL`) and the primitives it prints to (`c/storage_host.h`,
`c/generated/limb_ops.h`; docs/trusted-surface.md).

The printed function is the SLOAD/SSTORE callback's effect: inputs `self` (the frame's account)
and `key` live in the storage host `h`; it returns the gas. `faultSlot` is the host's fault: a
key absent from the native table is loaded through the world's fault hook first (a lazy world),
and then reads as its value or zero. Each primitive is one call:

| IR | C |
|---|---|
| `faultSlot self key` | `eita_sh_fault(h);` (a present key is live: nothing to fault) |
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

/-- A word input's C name (`new` is SSTORE's new value, `h->val`). -/
def cname : String → String
  | "new" => "new_val"
  | x => x

def word : WExp → E String
  | .var x => pure (cname x)
  | _ => throw "EffectC: a word operand must be a bound word"

def bC : BExp → E String
  | .lit b => pure (if b then "1" else "0")
  | .var x => pure x
  | .not p => return s!"!{← bC p}"
  | .and p q => return s!"({← bC p} && {← bC q})"
  | .or p q => return s!"({← bC p} || {← bC q})"
  | .forkGe n => pure s!"(h->fork >= {n})"
  | .weq a b => return s!"limb_eq({← word a}, {← word b})"
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
  | .faultSlot a k => do selfKey a k; pure [s!"{i}eita_sh_fault(h);"]
  | .letW x (.sload a k) s => do
      selfKey a k
      return [s!"{i}uint64_t {x}[4];", s!"{i}eita_sh_sload(h, {x});"] ++ (← sC i s)
  | .letW x (.orig a k fb) s => do
      selfKey a k
      return [s!"{i}uint64_t {x}[4];", s!"{i}eita_sh_orig_get(h, {← word fb}, {x});"] ++ (← sC i s)
  | .warmSlot g a k x s => do
      selfKey a k
      return [s!"{i}const int {x} = {← bC g} && eita_sh_access_slot(h);"] ++ (← sC i s)
  | .origRecord a k w => do selfKey a k; return [s!"{i}eita_sh_orig_record(h, {← word w});"]
  | .sstoreGas o c n cold =>
      return [s!"{i}gas += eita_sh_sstore_gas(h, {← word o}, {← word c}, {← word n}, {← bC cold});"]
  | .setStorage a k w => do selfKey a k; return [s!"{i}eita_sh_set_storage(h, {← word w});"]
  | .ite p s .skip => do
      return [s!"{i}if ({← bC p}) \{"] ++ (← sC (i ++ "  ") s) ++ [s!"{i}}"]
  | .ret w => return [s!"{i}limb_copy(out, {← word w});"]
  | .charge g => return [s!"{i}gas += {← gC g};"]
  | _ => throw "EffectC: statement outside the subset"

/-- A word-returning callback (SLOAD's) as a C function: `uint64_t name(eita_sh *h, uint64_t *out)`. -/
def toFnRet (name : String) (s : Stmt) : E String := do
  let body ← sC "  " s
  return s!"uint64_t {name}(eita_sh *h, uint64_t *out) \{\n  uint64_t gas = 0;\n" ++
    String.intercalate "\n" body ++ "\n  return gas;\n}\n"

/-- A gas-returning callback with the word input `new` (SSTORE's): `uint64_t name(eita_sh *h)`. -/
def toFn (name : String) (s : Stmt) : E String := do
  let body ← sC "  " s
  return s!"uint64_t {name}(eita_sh *h) \{\n  uint64_t gas = 0;\n  const uint64_t *new_val = h->val.limb;\n" ++
    String.intercalate "\n" body ++ "\n  return gas;\n}\n"

/-- The SSTORE schedule dispatch in C, from `SstoreSched.ofFork` (THE one copy): each fork
    ordinal to its native routine. -/
def sstoreDispatchC : String :=
  let all := [SstoreSched.legacy, .eip1283, .eip2200, .berlin, .london]
  let ords (s : SstoreSched) := (List.range (maxForkOrd + 1)).filter (fun k => SstoreSched.ofFork k = s)
  let call (s : SstoreSched) := s!"eita_sstore_gas_{s.name}(out, refund, orig, cur, nv, cold); return;"
  let decl (s : SstoreSched) :=
    s!"void eita_sstore_gas_{s.name}(uint64_t *out, uint64_t refund, const u256_t *orig, const u256_t *cur, const u256_t *nv, uint64_t cold);"
  let arms := (all.filter (· ≠ SstoreSched.ofFork (maxForkOrd + 1))).map fun s =>
    String.join ((ords s).map fun k => s!"  case {k}: ") ++ call s
  "\n".intercalate (all.map decl) ++ "\n" ++
  "void eita_spec_sstore_plan(uint64_t fork, uint64_t *out, uint64_t refund, const u256_t *orig,\n" ++
  "                           const u256_t *cur, const u256_t *nv, uint64_t cold) {\n" ++
  "  switch (fork) {\n" ++ "\n".intercalate arms ++ "\n" ++
  s!"  default: {call (SstoreSched.ofFork (maxForkOrd + 1))}\n" ++ "  }\n}\n"

/-- `c/generated/storage_effect.c`. -/
def file : E String := do
  let sload ← toFnRet "eita_spec_sload_effect" Evm.CL.EffectSload.term
  let sstore ← toFn "eita_spec_sstore_effect" Evm.CL.EffectSstore.term
  return "/* c/generated/storage_effect.c — EMITTED by `lake exe emitStorageC` from the effect IR\n" ++
    "   (lean/Evm/CL/EffectC.lean); do not edit. The terms and their proofs: Evm.CL.EffectSload\n" ++
    "   (sload_refines), Evm.CL.EffectSstore (sstore_refines), the SSTORE dispatch\n" ++
    "   Evm.CL.EffectIR.SstoreSched.ofFork. The one execution path of SLOAD and SSTORE. */\n" ++
    "#include \"../storage_host.h\"\n#include \"limb_ops.h\"\n\n" ++
    "/* SLOAD (Evm.CL.EffectSload.term) */\n" ++ sload ++
    "\n/* SSTORE (Evm.CL.EffectSstore.term) */\n" ++ sstore ++
    "\n/* The SSTORE schedule of each fork (Evm.CL.EffectIR.SstoreSched.ofFork) */\n" ++ sstoreDispatchC

end Evm.CL.EffectC
