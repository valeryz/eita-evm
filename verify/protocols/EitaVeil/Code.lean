/-! # The models' code citations, checked against the Lisp they cite

A model action names the code it abstracts with `@code` and a tag:

* a defun: `@code freeze!` — exactly one `(defun freeze! …)` in the cited files;
* a step in a defun: `@code freeze!/push` — the line holding that step carries the comment
  `; @veil freeze!/push`, inside `(defun freeze! …)` (several lines may carry one tag; a
  `defstruct`'s slot is marked the same way, `tail/through`);
* historical code an OLD model describes: `@code snapshot-world.lisp@0a9f2c0:315` — a row
  of `Config.history` gives the fragment that line holds at that commit (`git show`).

`check` fails when a cited tag is missing, a marker has left its defun, a marker is cited by
no model, or a historical line no longer holds its fragment. Markers survive edits that only
move code (no line numbers); a change to a marked line is in sight of its marker. The
orderings the proofs rest on are structural checks over the forms (`Src`, `Form`), written
per repository in its `CheckCode.lean`. -/

namespace EitaVeil.Code

inductive Kind | atom | str | list
  deriving BEq, Inhabited

/-- A form of a Lisp source: `[start, stop)` in its characters. -/
structure Form where
  start : Nat
  stop : Nat
  kind : Kind
  kids : Array Form := #[]
  deriving Inhabited

structure Src where
  path : String
  cs : Array Char
  forms : Array Form
  /-- where each line starts -/
  lines : Array Nat
  deriving Inhabited

def strOf (cs : Array Char) (a b : Nat) : String := String.ofList (cs.extract a b).toList

/-- A small reader: lists, atoms and strings; comments, `#\x` and `#|…|#` skipped. -/
def readForms (cs : Array Char) : Array Form := Id.run do
  let n := cs.size
  let mut i := 0
  let mut stack : Array (Array Form) := #[#[]]
  let mut starts : Array Nat := #[]
  let mut fuel := n + 1
  while i < n && fuel > 0 do
    fuel := fuel - 1
    let c := cs[i]!
    if c == ';' then
      while i < n && cs[i]! != '\n' do i := i + 1
    else if c == '"' then
      let st := i
      i := i + 1
      while i < n && cs[i]! != '"' do
        i := i + (if cs[i]! == '\\' then 2 else 1)
      i := i + 1
      stack := stack.modify (stack.size - 1) (·.push { start := st, stop := i, kind := .str })
    else if c == '#' && i + 1 < n && cs[i + 1]! == '\\' then
      i := i + 3
      while i < n && cs[i]!.isAlphanum do i := i + 1
    else if c == '#' && i + 1 < n && cs[i + 1]! == '|' then
      i := i + 2
      while i + 1 < n && !(cs[i]! == '|' && cs[i + 1]! == '#') do i := i + 1
      i := i + 2
    else if c == '(' then
      starts := starts.push i
      stack := stack.push #[]
      i := i + 1
    else if c == ')' then
      if stack.size > 1 then
        let kids := stack.back!
        stack := stack.pop
        let st := starts.back!
        starts := starts.pop
        stack := stack.modify (stack.size - 1) (·.push { start := st, stop := i + 1, kind := .list, kids })
      i := i + 1
    else if c.isWhitespace || "'`,#@".contains c then
      i := i + 1
    else
      let st := i
      while i < n && !cs[i]!.isWhitespace && !"()\";".contains cs[i]! do i := i + 1
      stack := stack.modify (stack.size - 1) (·.push { start := st, stop := i, kind := .atom })
  return stack[0]!

def lineStarts (cs : Array Char) : Array Nat := Id.run do
  let mut out := #[0]
  for i in [0:cs.size] do
    if cs[i]! == '\n' then out := out.push (i + 1)
  return out

def Src.ofString (path text : String) : Src :=
  let cs := text.toList.toArray
  { path, cs, forms := readForms cs, lines := lineStarts cs }

def Src.load (root : System.FilePath) (path : String) : IO Src :=
  return Src.ofString path (← IO.FS.readFile (root / path))

def Src.text (s : Src) (f : Form) : String := strOf s.cs f.start f.stop

def collapse (t : String) : String :=
  " ".intercalate ((t.toList.splitBy (fun a b => a.isWhitespace == b.isWhitespace)).filterMap
    fun w => if w.head?.any Char.isWhitespace then none else some (String.ofList w))

/-- The characters `[a, b)` without their `;` comments (strings kept as they are). -/
def codeOf (cs : Array Char) (a b : Nat) : String := Id.run do
  let mut out : Array Char := #[]
  let mut i := a
  let mut inStr := false
  while i < b do
    let c := cs[i]!
    if inStr then
      out := out.push c
      if c == '\\' && i + 1 < b then
        out := out.push cs[i + 1]!
        i := i + 1
      else if c == '"' then inStr := false
      i := i + 1
    else if c == '"' then
      inStr := true
      out := out.push c
      i := i + 1
    else if c == ';' then
      while i < b && cs[i]! != '\n' do i := i + 1
    else
      out := out.push c
      i := i + 1
  return String.ofList out.toList

/-- The form's code (comments dropped), whitespace collapsed, lower case. -/
def Src.flat (s : Src) (f : Form) : String := (collapse (codeOf s.cs f.start f.stop)).toLower

partial def walk (f : Form) : Array Form :=
  f.kids.foldl (fun acc k => acc ++ walk k) #[f]

def walkAll (fs : Array Form) : Array Form := fs.foldl (fun acc f => acc ++ walk f) #[]

def Src.head (s : Src) (f : Form) : Option String :=
  if f.kind == .list then
    match f.kids[0]? with
    | some k => if k.kind == .atom then some (s.text k).toLower else none
    | none => none
  else none

def Src.atoms (s : Src) (f : Form) : Array String :=
  (walk f).filterMap fun a => if a.kind == .atom then some (s.text a).toLower else none

def Src.findDefun (s : Src) (name : String) : Option Form :=
  (walkAll s.forms).find? fun f =>
    s.head f == some "defun" && (f.kids[1]?.map (fun k => (s.text k).toLower)) == some name

/-- The forms below `f` whose head is `h`, in source order. -/
def Src.within (s : Src) (f : Form) (h : String) : Array Form :=
  (walk f).filter fun g => s.head g == some h

/-- The sibling right before `f` in its parent, if any. -/
def Src.prevSibling (s : Src) (f : Form) : Option Form := do
  let p ← (walkAll s.forms).find? fun p => p.kids.any fun k => k.start == f.start && k.stop == f.stop
  let k ← p.kids.findIdx? fun k => k.start == f.start
  if k == 0 then none else p.kids[k - 1]?

/-- The line (from 1) holding position `pos`. -/
def Src.lineOf (s : Src) (pos : Nat) : Nat :=
  (s.lines.findIdx? (· > pos)).getD s.lines.size

/-- The position of `needle` in `hay` (characters), if present. -/
def indexOf (hay needle : String) : Option Nat :=
  match hay.splitOn needle with
  | p :: _ :: _ => some p.length
  | _ => none

/-- `needles` all present in `hay`, in this order. -/
def inOrder (hay : String) (needles : List String) : Bool :=
  let ix := needles.map (indexOf hay)
  ix.all Option.isSome && (ix.filterMap id |>.zip (ix.filterMap id |>.drop 1)).all fun (a, b) => a < b

/-- Is `(barrier (:write))` the form right before `f`? -/
def Src.barrierBefore (s : Src) (f : Form) : Bool :=
  (s.prevSibling f).any fun p => s.flat p == "(sb-thread:barrier (:write))"

/-! ## Markers and citations -/

def tagChar (c : Char) : Bool := !c.isWhitespace && !"),;`'\"".contains c

/-- Every `word` occurrence followed by a space, and the token after it. -/
def tokensAfter (text word : String) : Array (Nat × String) := Id.run do
  let cs := text.toList.toArray
  let w := word.toList.toArray
  let mut out := #[]
  let mut i := 0
  while i + w.size < cs.size do
    if cs.extract i (i + w.size) == w && cs[i + w.size]! == ' ' then
      let st := i + w.size + 1
      let mut j := st
      while j < cs.size && tagChar cs[j]! do j := j + 1
      -- a citation may end a clause: `@code freeze!:` or `@code freeze!.`
      let mut k := j
      while k > st && (cs[k - 1]! == ':' || cs[k - 1]! == '.') do k := k - 1
      if k > st then out := out.push (i, strOf cs st k)
      i := j
    else i := i + 1
  return out

/-- The top-level defun on whose lines position `pos` is, by name (a marker may follow the
defun's last parenthesis). -/
def Src.defunAt (s : Src) (pos : Nat) : Option String := do
  let l := s.lineOf pos
  let f ← s.forms.find? fun f => s.lineOf f.start ≤ l && l ≤ s.lineOf (f.stop - 1)
  unless s.head f == some "defun" || s.head f == some "defstruct" do none
  -- `(defstruct (tail (:constructor …)) …)` is named by its first atom
  let k ← f.kids[1]?
  let k ← if k.kind == .list then k.kids[0]? else some k
  return (s.text k).toLower

structure Marker where
  tag : String
  src : String
  line : Nat
  defun : Option String

def Src.markers (s : Src) : Array Marker :=
  (tokensAfter (strOf s.cs 0 s.cs.size) "; @veil").map fun (pos, tag) =>
    { tag, src := s.path, line := s.lineOf pos, defun := s.defunAt pos }

structure Config where
  /-- the repository root -/
  root : System.FilePath
  /-- the Lisp files the models cite (repository-relative) -/
  files : Array String
  /-- the model files -/
  models : Array System.FilePath
  /-- historical lines the OLD models cite: (file name, commit, line, fragment) -/
  history : Array (String × String × Nat × String) := #[]

def baseName (p : String) : String := (p.splitOn "/").getLast!

/-- Check every citation; returns (errors, notes, citations checked). -/
def check (cfg : Config) : IO (Array String × Array String × Nat) := do
  let srcs ← cfg.files.mapM (Src.load cfg.root)
  let markers := srcs.foldl (fun acc s => acc ++ s.markers) #[]
  let mut errs := #[]
  let mut notes := #[]
  let mut cited : Array String := #[]
  let mut nCites := 0
  for m in markers do
    let d := (m.tag.splitOn "/").head!
    unless m.defun == some d do
      errs := errs.push s!"{m.src}:{m.line}: marker {m.tag} is not inside (defun {d} …)"
  for mp in cfg.models do
    let text ← IO.FS.readFile mp
    for (_, tag) in tokensAfter text "@code" do
      nCites := nCites + 1
      cited := cited.push tag
      if (tag.splitOn "@").length == 2 then
        let (file, rest) := ((tag.splitOn "@")[0]!, (tag.splitOn "@")[1]!)
        match rest.splitOn ":" with
        | [rev, ln] =>
          unless cfg.history.any (fun (f, r, l, _) => f == file && r == rev && toString l == ln) do
            errs := errs.push s!"{mp}: cites {tag}, which has no history row (fragment) in CheckCode.lean"
        | _ => errs := errs.push s!"{mp}: cites {tag}: expected FILE@REV:LINE"
      else if tag.contains '/' then
        unless markers.any (·.tag == tag) do
          errs := errs.push s!"{mp}: cites {tag}: no `; @veil {tag}` marker in {cfg.files.toList}"
      else
        let n := (srcs.filter fun s => (s.findDefun tag).isSome).size
        unless n == 1 do
          errs := errs.push s!"{mp}: cites {tag}: {n} (defun {tag} …) in the cited files, expected one"
  for m in markers do
    unless cited.contains m.tag do
      errs := errs.push s!"{m.src}:{m.line}: marker {m.tag} is cited by no model"
  for (file, rev, ln, frag) in cfg.history do
    let tag := s!"{file}@{rev}:{ln}"
    unless cited.contains tag do
      errs := errs.push s!"history row {tag} is cited by no model"
    let some path := cfg.files.find? (baseName · == file)
      | errs := errs.push s!"history row {tag}: {file} is not among the cited files"
    let out ← IO.Process.output { cmd := "git", args := #["-C", cfg.root.toString, "show", s!"{rev}:{path}"] }
    if out.exitCode != 0 then
      notes := notes.push s!"skipped {path}@{rev} (no commit {rev} in this clone)"
    else
      let lines := out.stdout.splitOn "\n"
      let got := lines.getD (ln - 1) ""
      unless (indexOf got frag).isSome do
        errs := errs.push s!"{path}@{rev}:{ln}: expected {repr frag}, found {repr got}"
  return (errs, notes, nCites)

end EitaVeil.Code
