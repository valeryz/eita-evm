import Lean
import Velvet
import Slots.Mem

/-!
# A C printer for Velvet methods (prototype)

Velvet is a shallow embedding: a `method` elaborates to an ordinary Lean definition in a monad
(`Option` by default) built from `bind`/`pure`, `ite`/`dite`, `let`/`have`, `Prod` tuples,
`Option` matches, and the loop gadgets `Loop.Gadget.whileLoopTotal(Returning)` (both are
`forIn Lean.Loop.mk init body`). This printer walks that elaborated `Expr` (a MetaM pass, no
deep embedding needed) and emits C for a small subset:

* scalars: `Nat`, `UInt64` → `uint64_t`, `UInt8` → `uint8_t`, `Bool` → `bool`;
* arrays: `Array UInt64` / `Array UInt8` → pointers. Indexing is proof-carrying only: `a[i]'h`
  → `a[i]`, `a.set i v h` → in-place store (checked linear: the old array value may not be used
  after it is consumed); `a[i]!` and `a.set! i v` are rejected by name. The bound proofs come
  from `if h : i < a.size then … else oob` (Slots/Mem.lean: `rd`, `wr`): the printer emits the
  `then` branch only, and only in a method whose proved contract (`<name>.spec`) forbids
  failure, so the `else` is dead and every index is in bounds by proof;
  `Array.replicate n 0` → zeroed allocation;
* `wsAbort "msg"` → `fputs("msg\n", stderr); abort();` (the contract's `signals` says when);
* tuples and `Option` are scalarized into C variables; a method returning a tuple returns a
  struct;
* `+ * &&& >>>` on `UInt64`, `+ * &&&` on `Nat`, Nat `-` as saturating `nat_sub`, comparisons,
  `==` (only at types whose `BEq` instance is `LawfulBEq`), `&&`/`||`/`!`;
* calls to other emitted methods; non-method definitions (`setKV`, `hashIdx`, `golden`, ...) are
  unfolded (delta + beta);
* `whileLoopTotal(Returning)` → `for (;;)` with `ForInStep.done` → `break`, `yield` → `continue`.

Anything else is rejected with an error naming the construct. The side condition the printer does
not discharge (reported, not hidden): `Nat` values fit in 64 bits (`+`/`*` do not wrap).
Each emitted function carries a comment listing the array parameters it may write in place.
-/

open Lean Meta Elab Command

namespace VelvetC

inductive CTy | u64 | u8 | bool | p64 | p8 | unit
  deriving BEq, Inhabited, Repr

def CTy.decl : CTy → String
  | .u64 => "uint64_t" | .u8 => "uint8_t" | .bool => "bool"
  | .p64 => "uint64_t *" | .p8 => "uint8_t *" | .unit => "int"

def CTy.zero : CTy → String
  | .p64 | .p8 => "NULL" | .bool => "false" | _ => "0"

inductive Shape | leaf (t : CTy) | pair (a b : Shape) | opt (v : Shape)
  deriving Inhabited

/-- A scalarized C value: leaves are C expressions. `opt tag v`: `tag` is a C bool. -/
inductive CVal | leaf (c : String) (t : CTy) | pair (a b : CVal) | opt (tag : String) (v : CVal)
  deriving Inhabited

def CVal.leaves : CVal → List (String × CTy)
  | .leaf c t => [(c, t)]
  | .pair a b => a.leaves ++ b.leaves
  | .opt g v => (g, .bool) :: v.leaves

def Shape.leaves : Shape → List CTy
  | .leaf t => [t] | .pair a b => a.leaves ++ b.leaves | .opt v => .bool :: v.leaves

/-- Rebuild a value of shape `sh` from a list of leaf expressions. -/
partial def Shape.fill : Shape → List String → CVal × List String
  | .leaf t, c :: cs => (.leaf c t, cs)
  | .pair a b, cs => let (va, cs) := a.fill cs; let (vb, cs) := b.fill cs; (.pair va vb, cs)
  | .opt v, g :: cs => let (vv, cs) := v.fill cs; (.opt g vv, cs)
  | _, cs => (.leaf "/*?*/0" .u64, cs)

structure MethInfo where
  cname : String
  ret : Shape
  /-- Indices of array parameters (passed as pointers; a call consumes them if the method
  returns arrays). -/
  consumes : Bool

structure St where
  out : Array String := #[]
  ind : Nat := 1
  fresh : Nat := 0
  env : Std.HashMap FVarId CVal := {}
  consumed : Std.HashSet FVarId := {}
  /-- Array fvars bound outside the innermost loop body (consuming them inside is rejected). -/
  outer : Std.HashSet FVarId := {}
  meths : Std.HashMap Name MethInfo := {}
  /-- The current method's proved contract forbids `Option` failure (so `oob` is dead). -/
  noFail : Bool := false
  /-- Array fvars consumed anywhere in the current method (for the "writes" comment). -/
  written : Std.HashSet FVarId := {}

abbrev CM := StateRefT St MetaM

def emit (s : String) : CM Unit := modify fun st =>
  { st with out := st.out.push ("".pushn ' ' (2 * st.ind) ++ s) }

def indent (k : CM α) : CM α := do
  modify fun st => { st with ind := st.ind + 1 }
  let r ← k
  modify fun st => { st with ind := st.ind - 1 }
  return r

def sanitize (n : String) : String :=
  n.foldl (fun acc c => if c.isAlphanum || c == '_' then acc.push c else if c == '\'' then acc ++ "_p" else acc) ""

/-- `if (c)`, without doubling the parentheses of an already parenthesized condition. -/
def ifHead (c : String) : String := if c.startsWith "(" then s!"if {c}" else s!"if ({c})"

def freshName (base : String) : CM String := do
  let st ← get; set { st with fresh := st.fresh + 1 }
  let b := sanitize base
  return s!"{if b.isEmpty then "t" else b}_{st.fresh}"

/-! ## Types -/

partial def shapeOf (ty : Expr) : MetaM Shape := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Nat, #[]) | (``UInt64, #[]) => return .leaf .u64
  | (``UInt8, #[]) => return .leaf .u8
  | (``Bool, #[]) => return .leaf .bool
  | (``Unit, #[]) | (``PUnit, _) => return .leaf .unit
  | (``Prod, #[a, b]) => return .pair (← shapeOf a) (← shapeOf b)
  | (``Option, #[a]) => return .opt (← shapeOf a)
  | (``Array, #[a]) =>
    match (← whnfR a).getAppFnArgs with
    | (``UInt64, #[]) => return .leaf .p64
    | (``UInt8, #[]) => return .leaf .p8
    | _ => throwError "C printer: unsupported array element type {a}"
  | _ => throwError "C printer: unsupported type {ty}"

def leafTy (ty : Expr) : MetaM CTy := do
  match ← shapeOf ty with
  | .leaf t => return t
  | _ => throwError "C printer: expected a scalar type, got {ty}"

/-- Declare fresh C variables for a value of shape `sh`. -/
def declVars (base : String) (sh : Shape) : CM CVal := do
  let mut names := #[]
  for t in sh.leaves do
    let n ← freshName base
    emit s!"{t.decl} {n} = {t.zero};"
    names := names.push n
  return (sh.fill names.toList).1

/-- Assign `v` to the variables `vars` (via temporaries: a parallel assignment). -/
def assignVals (vars v : CVal) : CM Unit := do
  let ls := v.leaves; let ds := vars.leaves
  if ls.length != ds.length then throwError "C printer: shape mismatch in assignment"
  let mut tmps := #[]
  for (c, t) in ls do
    let n ← freshName "tmp"
    emit s!"{t.decl} {n} = {c};"
    tmps := tmps.push n
  for ((d, _), tmp) in ds.zip tmps.toList do
    if d != tmp then emit s!"{d} = {tmp};"

/-- Materialize a value into fresh variables (fixes evaluation order). -/
def materialize (base : String) (v : CVal) : CM CVal := do
  let mut names := #[]
  for (c, t) in v.leaves do
    let n ← freshName base
    emit s!"{t.decl} {n} = {c};"
    names := names.push n
  let sh : Shape := shapeOfVal v
  return (sh.fill names.toList).1
where
  shapeOfVal : CVal → Shape
    | .leaf _ t => .leaf t | .pair a b => .pair (shapeOfVal a) (shapeOfVal b)
    | .opt _ v => .opt (shapeOfVal v)

partial def litOf? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => litOf? n
    | (``instOfNatNat, #[n]) => litOf? n
    | _ => none

def isPrimitive (n : Name) : Bool :=
  n ∈ [``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HAnd.hAnd, ``HShiftRight.hShiftRight, ``HMod.hMod,
       ``UInt64.toNat, ``BEq.beq, ``and, ``or, ``not, ``GetElem.getElem, ``Array.set, ``Array.replicate,
       ``Prod.mk, ``Prod.fst, ``Prod.snd, ``ite, ``dite, ``decide, ``Option.some, ``Option.none,
       ``OfNat.ofNat, ``Bool.true, ``Bool.false, ``Unit.unit, ``PUnit.unit]

def useVar (fv : FVarId) : CM CVal := do
  let st ← get
  if st.consumed.contains fv then
    throwError "C printer: array {← fv.getUserName} used after it was consumed (not linear)"
  match st.env.get? fv with
  | some v => return v
  | none => throwError "C printer: unbound variable {← fv.getUserName}"

def consume (e : Expr) : CM Unit := do
  if let .fvar fv := e then
    if (← get).outer.contains fv then
      throwError "C printer: array {← fv.getUserName} from outside the loop is consumed inside it"
    modify fun st => { st with consumed := st.consumed.insert fv, written := st.written.insert fv }

def isArrayTy (e : Expr) : MetaM Bool := do
  match ← (shapeOf (← inferType e) |>.run' |> fun x => (try (some <$> x) catch _ => pure none)) with
  | some (.leaf .p64) | some (.leaf .p8) => return true
  | _ => return false

/-- Beta-normalize the head, looking through metadata. -/
partial def nb (e : Expr) : Expr :=
  let e := e.consumeMData
  let f := e.getAppFn.consumeMData
  if f.isLambda && e.getAppNumArgs > 0 then nb (f.betaRev e.getAppRevArgs) else mkAppN f e.getAppArgs

mutual

/-- Compile a pure term. -/
partial def cexp (e : Expr) : CM CVal := do
  let e := nb e
  if let some n := litOf? e then
    let t ← leafTy (← inferType e)
    return .leaf (if t == .u64 then s!"{n}ULL" else toString n) t
  match e with
  | .fvar fv => useVar fv
  | .letE n _ v b _ => cexpLet n v b cexp
  | .mdata _ b => cexp b
  | _ =>
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    let bin (op : String) : CM CVal := do
      let a ← cexp args[4]!; let b ← cexp args[5]!
      let t ← leafTy (← inferType e)
      match a, b with
      | .leaf a _, .leaf b _ => return .leaf s!"({a} {op} {b})" t
      | _, _ => throwError "C printer: tuple operand"
    match c, args.size with
    | ``HAdd.hAdd, 6 => bin "+"
    | ``HMul.hMul, 6 => bin "*"
    | ``HAnd.hAnd, 6 => bin "&"
    | ``HMod.hMod, 6 => bin "%"
    | ``HSub.hSub, 6 => do
      let t ← leafTy (← inferType e)
      let .leaf a _ ← cexp args[4]! | throwError "tuple"
      let .leaf b _ ← cexp args[5]! | throwError "tuple"
      let isNat := (← whnfR (← inferType e)).isConstOf ``Nat
      return .leaf (if isNat then s!"nat_sub({a}, {b})" else s!"({a} - {b})") t
    | ``HShiftRight.hShiftRight, 6 => do
      let .leaf a _ ← cexp args[4]! | throwError "tuple"
      let .leaf b _ ← cexp args[5]! | throwError "tuple"
      return .leaf s!"({a} >> (({b}) & 63))" .u64
    | ``UInt64.toNat, 1 => cexp args[0]!
    | ``BEq.beq, 4 => do
      let inst ← mkAppOptM ``LawfulBEq #[args[0]!, args[1]!]
      unless (← synthInstance? inst).isSome do
        throwError "C printer: `==` at {args[0]!} without a LawfulBEq instance"
      let .leaf a _ ← cexp args[2]! | throwError "tuple"
      let .leaf b _ ← cexp args[3]! | throwError "tuple"
      return .leaf s!"({a} == {b})" .bool
    | ``and, 2 => boolBin "&&" args[0]! args[1]!
    | ``or, 2 => boolBin "||" args[0]! args[1]!
    | ``not, 1 => do
      let .leaf a _ ← cexp args[0]! | throwError "tuple"
      return .leaf s!"(!{a})" .bool
    | ``decide, 2 => return .leaf (← cprop args[0]!) .bool
    | ``Bool.true, 0 => return .leaf "true" .bool
    | ``Bool.false, 0 => return .leaf "false" .bool
    | ``Unit.unit, 0 | ``PUnit.unit, _ => return .leaf "0" .unit
    | ``getElem!, _ => throwError "C printer: `a[i]!` is not accepted (unchecked index); use `a[i]'h` under `if h : i < a.size` (Slots/Mem.lean `rd`)"
    | ``Array.set!, _ => throwError "C printer: `a.set! i v` is not accepted (unchecked index); use `a.set i v h` (Slots/Mem.lean `wr`)"
    | ``getElem?, _ => throwError "C printer: `a[i]?` is not accepted; use `a[i]'h`"
    | ``GetElem.getElem, 8 => do
      let .leaf a _ ← cexp args[5]! | throwError "tuple"
      let .leaf i _ ← cexp args[6]! | throwError "tuple"
      return .leaf s!"{a}[{i}]" (← leafTy (← inferType e))
    | ``Array.set, 5 => do
      let .leaf a t ← cexp args[1]! | throwError "tuple"
      let .leaf i _ ← cexp args[2]! | throwError "tuple"
      let .leaf v _ ← cexp args[3]! | throwError "tuple"
      emit s!"{a}[{i}] = {v};"
      consume args[1]!
      return .leaf a t
    | ``Array.replicate, 3 => do
      let t ← leafTy (← inferType e)
      let .leaf n _ ← cexp args[1]! | throwError "tuple"
      unless litOf? args[2]! == some 0 do throwError "C printer: Array.replicate of a non-zero value"
      let x ← freshName "arr"
      emit s!"{t.decl}{x} = {if t == .p64 then "alloc_zero64" else "alloc_zero8"}({n});"
      return .leaf x t
    | ``Prod.mk, 4 => return .pair (← cexp args[2]!) (← cexp args[3]!)
    | ``Prod.fst, 3 => do
      match ← cexp args[2]! with
      | .pair a _ => return a
      | _ => throwError "C printer: Prod.fst of a non-pair"
    | ``Prod.snd, 3 => do
      match ← cexp args[2]! with
      | .pair _ b => return b
      | _ => throwError "C printer: Prod.snd of a non-pair"
    | ``Option.some, 2 => return .opt "true" (← cexp args[1]!)
    | ``Option.none, 1 => do
      let sh ← shapeOf args[0]!
      return .opt "false" (sh.fill (sh.leaves.map CTy.zero)).1
    | ``ite, 5 => do
      let c ← cprop args[1]!
      let sh ← shapeOf args[0]!
      let r ← declVars "ite" sh
      emit s!"{ifHead c} \{"
      indent (do assignVals r (← branch (cexp args[3]!)))
      emit "} else {"
      indent (do assignVals r (← branch (cexp args[4]!)))
      emit "}"
      return r
    | _, _ =>
      if isPrimitive c then throwError "C printer: unsupported use of {c} in {e}"
      if (← get).meths.contains c then throwError "C printer: method call {c} in pure position"
      match ← unfoldDefinition? e with
      | some e' => cexp e'
      | none => throwError "C printer: cannot unfold {c}"
  | _ => throwError "C printer: unsupported term {e}"

partial def boolBin (op : String) (a b : Expr) : CM CVal := do
  let .leaf a _ ← cexp a | throwError "tuple"
  let .leaf b _ ← cexp b | throwError "tuple"
  return .leaf s!"({a} {op} {b})" .bool

/-- Compile a branch with the consumed set restored afterwards (branches are alternatives). -/
partial def branch (k : CM α) : CM α := do
  let saved := (← get).consumed
  let r ← k
  modify fun st => { st with consumed := saved }
  return r

partial def cexpLet (n : Name) (v b : Expr) (k : Expr → CM α) : CM α := do
  if v.headBeta.isLambda then
    -- join points (`__do_jp`) and other local functions: inline at the uses
    k (b.instantiate1 v)
  else
    let cv ← materialize n.eraseMacroScopes.toString (← cexp v)
    withLetDecl n (← inferType v) v fun x => do
      modify fun st => { st with env := st.env.insert x.fvarId! cv }
      k (b.instantiate1 x)

/-- Compile a decidable proposition used as a condition. -/
partial def cprop (p : Expr) : CM String := do
  let p ← instantiateMVars p
  let leaf (e : Expr) : CM String := do
    let .leaf c _ ← cexp e | throwError "tuple in condition"
    return c
  match p.getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return s!"({← leaf a} < {← leaf b})"
  | (``LE.le, #[_, _, a, b]) => return s!"({← leaf a} <= {← leaf b})"
  | (``GT.gt, #[_, _, a, b]) => return s!"({← leaf a} > {← leaf b})"
  | (``GE.ge, #[_, _, a, b]) => return s!"({← leaf a} >= {← leaf b})"
  | (``Eq, #[ty, a, b]) =>
    if (← whnfR ty).isConstOf ``Bool && b.isConstOf ``Bool.true then leaf a
    else if (← whnfR ty).isConstOf ``Bool && b.isConstOf ``Bool.false then return s!"(!{← leaf a})"
    else return s!"({← leaf a} == {← leaf b})"
  | (``Not, #[a]) => return s!"(!{← cprop a})"
  | (``And, #[a, b]) => return s!"({← cprop a} && {← cprop b})"
  | (``Or, #[a, b]) => return s!"({← cprop a} || {← cprop b})"
  | _ => throwError "C printer: unsupported condition {p}"

end

/-- `wsAbort "msg"`: its message. -/
def abortMsg? (e : Expr) : MetaM (Option String) := do
  let e := nb e
  if e.isAppOfArity ``wsAbort 2 then
    match (← instantiateMVars e.appArg!) with
    | .lit (.strVal m) => return some m
    | _ => throwError "C printer: wsAbort needs a string literal"
  return none

def isOob (e : Expr) : Bool := (nb e).isAppOf ``oob

def cString (m : String) : String :=
  "\"" ++ m.foldl (fun acc c => if c == '"' || c == '\\' then (acc.push '\\').push c else acc.push c) "" ++ "\\n\""

def emitAbort (msg : String) : CM Unit := do
  emit s!"fputs({cString msg}, stderr); abort();"

/-- The values of the `Named.mk` clauses inside `e`. -/
partial def namedVals (e : Expr) : Array Expr :=
  if e.isAppOfArity ``Named.mk 4 then #[e.appArg!] else
  match e with
  | .app f a => namedVals f ++ namedVals a
  | .lam _ t b _ | .forallE _ t b _ => namedVals t ++ namedVals b
  | .letE _ t v b _ => namedVals t ++ namedVals v ++ namedVals b
  | .mdata _ b | .proj _ _ b => namedVals b
  | _ => #[]

/-- The method's proved contract forbids `Option` failure: every `Named` clause of the failure
postcondition of `<n>.spec` is `False`. -/
def noFailure (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? (n ++ `spec) | throwError "C printer: {n} has no proved contract `{n}.spec`"
  forallTelescope ci.type fun _ b => do
    let b ← whnfR b
    unless b.isAppOf ``Std.WP.Triple do throwError "C printer: {n}.spec is not a Triple"
    let ep := b.appArg!
    let nameds := namedVals ep
    return !nameds.isEmpty && nameds.all (·.isConstOf ``False)

/-- Where the value of a monadic computation goes. -/
inductive Ret
  | ret (sh : Shape) (fn : String)
  | assign (vars : CVal)
  | loop (state : CVal)

def deliver (r : Ret) (v : CVal) : CM Unit := do
  match r with
  | .ret sh fn =>
    match sh with
    | .leaf _ => match v with
      | .leaf c _ => emit s!"return {c};"
      | _ => throwError "shape"
    | _ =>
      let ls := v.leaves.map (·.1)
      emit s!"return (struct ret_{fn})\{{", ".intercalate ls}};"
  | .assign vars => assignVals vars v
  | .loop _ => throwError "C printer: loop body must end in ForInStep.done/yield"

mutual

/-- Compile a monadic (`Option`) computation, sending its value to `r`. -/
partial def cstm (e : Expr) (r : Ret) : CM Unit := do
  let e := nb e
  match e with
  | .letE n _ v b _ => cexpLet n v b (cstm · r)
  | .mdata _ b => cstm b r
  | _ =>
  let args := e.getAppArgs
  match e.getAppFn with
  | .const c _ =>
    match c, args.size with
    | ``Pure.pure, 4 => do
      match r with
      | .loop st =>
        let v := args[3]!.headBeta
        match v.getAppFnArgs with
        | (``ForInStep.done, #[_, x]) => do assignVals st (← cexp x); emit "break;"
        | (``ForInStep.yield, #[_, x]) => do assignVals st (← cexp x); emit "continue;"
        | _ => throwError "C printer: loop step {v}"
      | _ => deliver r (← cexp args[3]!)
    | ``Bind.bind, 6 => do
      if let some msg ← abortMsg? args[4]! then
        emitAbort msg
        return
      let v ← cmonadic args[4]!
      let f := args[5]!
      match f.headBeta with
      | .lam n ty b _ =>
        let v ← materialize n.eraseMacroScopes.toString v
        withLocalDeclD n ty fun x => do
          modify fun st => { st with env := st.env.insert x.fvarId! v }
          cstm (b.instantiate1 x) r
      | _ => throwError "C printer: bind continuation is not a lambda"
    | ``ite, 5 => do
      let cnd ← cprop args[1]!
      emit s!"{ifHead cnd} \{"
      indent (branch (cstm args[3]! r))
      emit "} else {"
      indent (branch (cstm args[4]! r))
      emit "}"
    | ``dite, 5 => do
      if isOob (nb (args[4]!.headBeta.bindingBody!.instantiate1 (mkConst ``True.intro))) then
        unless (← get).noFail do
          throwError "C printer: an `oob` bound check in a method whose contract allows failure (the else branch is not proved dead)"
        withLocalDeclD `h args[1]! fun h => cstm (mkApp args[3]! h) r
        return
      let cnd ← cprop args[1]!
      emit s!"{ifHead cnd} \{"
      indent (branch (withLocalDeclD `h args[1]! fun h => cstm (mkApp args[3]! h) r))
      emit "} else {"
      indent (branch (withLocalDeclD `h (mkNot args[1]!) fun h => cstm (mkApp args[4]! h) r))
      emit "}"
    | ``Option.rec, n => do
      if n < 5 then throwError "C printer: partial Option.rec"
      -- Option.rec {α} {motive} none some t, then extra arguments
      let extra := args.extract 5 n
      let d := args[4]!
      let alt0 := mkAppN args[2]! extra
      let alt1 := args[3]!
      match ← cexp d with
      | .opt tag v =>
        emit s!"{ifHead tag} \{"
        indent (branch do
          withLocalDeclD `val (← shapeTyOfAlt alt1) fun x => do
            modify fun st => { st with env := st.env.insert x.fvarId! v }
            cstm (mkAppN (mkApp alt1 x) extra) r)
        emit "} else {"
        indent (branch (cstm alt0 r))
        emit "}"
      | _ => throwError "C printer: match on a non-Option"
    | ``oob, _ => throwError "C printer: `oob` outside an `if h : i < a.size` bound check"
    | ``wsAbort, 2 => do
      let some msg ← abortMsg? e | throwError "C printer: wsAbort needs a string literal"
      emitAbort msg
    | _, _ =>
      if (← get).meths.contains c then
        let v ← cmonadic e
        deliver r v
      else if ← isMatcher c then
        let e' ← deltaExpand e (· == c)
        cstm e'.headBeta r
      else if let some e' ← unfoldDefinition? e then
        -- matchers (`match __r with ...`) and other definitions
        cstm (← whnfCore e') r
      else throwError "C printer: unsupported monadic term {e} (head {c}, {args.size} args)"
  | _ => throwError "C printer: unsupported monadic term {e}"

/-- The binder type of a `some` alternative. -/
partial def shapeTyOfAlt (alt : Expr) : CM Expr := do
  match ← whnfR (← inferType alt) with
  | .forallE _ ty _ _ => return ty
  | t => throwError "C printer: some-alternative of type {t}"

/-- A monadic computation in a `bind`: a method call, a loop, or a nested block. -/
partial def cmonadic (m : Expr) : CM CVal := do
  let m := nb m
  let args := m.getAppArgs
  match m.getAppFn with
  | .const c _ =>
    if let some mi := (← get).meths.get? c then
      let mut cs := #[]
      for a in args do
        match ← cexp a with
        | .leaf s _ => cs := cs.push s
        | _ => throwError "C printer: tuple argument to {c}"
      if mi.consumes then
        for a in args do
          if ← isArrayTy a then consume a
      let res ← freshName c.toString
      match mi.ret with
      | .leaf t =>
        emit s!"{t.decl} {res} = {mi.cname}({", ".intercalate cs.toList});"
        return .leaf res t
      | sh =>
        emit s!"struct ret_{mi.cname} {res} = {mi.cname}({", ".intercalate cs.toList});"
        let fields := (List.range sh.leaves.length).map (fun i => s!"{res}.f{i}")
        return (sh.fill fields).1
    if c == ``Loop.Gadget.whileLoopTotal || c == ``Loop.Gadget.whileLoopTotalReturning then
      let off := if c == ``Loop.Gadget.whileLoopTotal then 4 else 5
      let init := args[off]!
      let body := args[off + 1]!
      let sh ← shapeOf (← inferType init)
      let st ← declVars "st" sh
      assignVals st (← cexp init)
      emit "for (;;) {"
      let saved ← get
      -- arrays bound so far are "outer" for this loop
      modify fun s => { s with outer := s.env.fold (fun acc k _ => acc.insert k) s.outer }
      indent do
        withLocalDeclD `u (mkConst ``Unit) fun u => do
          withLocalDeclD `s (← inferType init) fun sv => do
            modify fun s => { s with env := (s.env.insert u.fvarId! (.leaf "0" .unit)).insert sv.fvarId! st }
            cstm (mkApp2 body u sv) (.loop st)
      modify fun s => { s with outer := saved.outer, consumed := saved.consumed }
      emit "}"
      return st
    -- a nested monadic block
    let sh ← shapeOf (← monadValueType m)
    let vars ← declVars "blk" sh
    cstm m (.assign vars)
    return vars
  | _ =>
    let sh ← shapeOf (← monadValueType m)
    let vars ← declVars "blk" sh
    cstm m (.assign vars)
    return vars

partial def monadValueType (m : Expr) : CM Expr := do
  let ty ← whnfR (← inferType m)
  match ty.getAppFnArgs with
  | (``Option, #[a]) => return a
  | _ => throwError "C printer: expected an Option computation, got {ty}"

end

/-- Emit one method as a C function. -/
def emitMethod (n : Name) : CM Unit := do
  let ci ← getConstInfo n
  let some val := ci.value? | throwError "{n} has no body"
  let cname := "vv_" ++ sanitize n.toString
  lambdaTelescope val fun xs body => do
    let mut ps := #[]
    for x in xs do
      let t ← leafTy (← inferType x)
      let pn := sanitize (← x.fvarId!.getUserName).toString
      ps := ps.push s!"{t.decl}{if t == .p64 || t == .p8 then "" else " "}{pn}"
      modify fun st => { st with env := st.env.insert x.fvarId! (.leaf pn t) }
    let rty ← monadValueType body
    let sh ← shapeOf rty
    let mut consumes := false
    for t in sh.leaves do if t == .p64 || t == .p8 then consumes := true
    modify fun st => { st with meths := st.meths.insert n ⟨cname, sh, consumes⟩ }
    let retDecl ← match sh with
      | .leaf t => pure t.decl
      | _ => do
        let fs := sh.leaves.zipIdx.map fun (t, i) => s!"{t.decl} f{i};"
        modify fun st => { st with out := st.out.push s!"struct ret_{cname} \{ {" ".intercalate fs} };" }
        pure s!"struct ret_{cname}"
    let nf ← noFailure n
    let hdr := (← get).out.size
    modify fun st => { st with out := st.out.push s!"static {retDecl} {cname}({", ".intercalate ps.toList}) \{",
                                ind := 1, consumed := {}, outer := {}, written := {}, noFail := nf }
    cstm body (.ret sh cname)
    let st ← get
    let mut ws := #[]
    for x in xs do
      if st.written.contains x.fvarId! then ws := ws.push (sanitize (← x.fvarId!.getUserName).toString)
    let note := s!"/* {n}: contract {if nf then "forbids failure" else "may abort (signals)"}; " ++
      (if ws.isEmpty then "consumes no array parameter */" else s!"consumes (may store into or return): {", ".intercalate ws.toList} */")
    modify fun st => { st with out := ((st.out.insertIdx! hdr note).push "}").push "" }

/-- The emitted file's header. -/
def header (methods : List String) : String :=
  "/* world_slots_emit.c: GENERATED, do not edit. Printed by Eita's Velvet C printer from the slot
   table's Velvet methods, each proved (in Lean, with Velvet) against the slot-table model for every
   capacity: " ++ ", ".intercalate methods ++ ".
   The proofs and the printer: verify/velvet-slots/ (its own Lake package); scripts/verify-velvet-slots.sh
   regenerates this file and fails if it differs. Glue: world_slots.c. */\n"

def prelude : String := "#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Printer temporaries, unused parameters and functions are expected: silence them here only. */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored \"-Wunused-variable\"
#pragma GCC diagnostic ignored \"-Wunused-parameter\"
#pragma GCC diagnostic ignored \"-Wunused-function\"
static inline uint64_t nat_sub(uint64_t a, uint64_t b) { return a < b ? 0 : a - b; }
static void *vv_zeroed(void *p, uint64_t bytes) {
  if (!p) { fputs(\"eita_ws: out of memory\\n\", stderr); abort(); }
  memset(p, 0, bytes);
  return p;
}
static inline uint64_t *alloc_zero64(uint64_t n) { return vv_zeroed(malloc(n * sizeof(uint64_t)), n * sizeof(uint64_t)); }
static inline uint8_t *alloc_zero8(uint64_t n) { return vv_zeroed(malloc(n * sizeof(uint8_t)), n * sizeof(uint8_t)); }
"

/-- `#emit_c "path.c" [m₁, m₂, …]`: print the methods, in order, to a C file. -/
elab "#emit_c " path:str " [" ns:ident,* "]" : command => do
  let names ← ns.getElems.mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let out ← liftTermElabM do
    let (_, st) ← (names.forM emitMethod).run {}
    return st.out
  let txt := header (names.toList.map (·.toString (escape := false))) ++ prelude ++ "\n" ++ "\n".intercalate out.toList ++ "\n#pragma GCC diagnostic pop\n"
  IO.FS.writeFile path.getString txt
  logInfo m!"wrote {path.getString} ({out.size} lines)"

end VelvetC
