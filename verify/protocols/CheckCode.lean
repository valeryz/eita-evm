import EitaVeil.Code

/-! # The protocol models' citations and orderings, against core's code

    lake env lean --run CheckCode.lean      (from verify/protocols; scripts/verify-protocols.sh)

1. Every `@code` citation in `EitaVeil/*.lean` (`EitaVeil.Code.check`): a defun, a marked step
   (`; @veil defun/step`) or a historical line (the rows below, checked with `git show`).
2. The orderings the safety proofs rest on, as structural checks over the forms:
   * `live-components` reads `*layers*` and `*base*` exactly once, inside
     `(with-mutex (*stack-lock*))` (LayerGcFixed: one atomic pin action);
   * every `(setf … *layers* …)` in snapshot-world.lisp directly follows
     `(sb-thread:barrier (:write))` (the lock-free readers' publication order);
   * both `(setf (snap-…-fence s) …)` in `snap-open` directly follow the barrier, and
     `snap-close` joins the fence thread before it unmaps (Compaction f_pub / close);
   * `close-retired!` closes only under `(not *writer-busy*)` and `(null *compactor*)`;
   * `write-layer!` sets `*writer-busy*` with `stack-below`, and clears it with the swap, each
     in one locked form;
   * `rollback-to!`: `writer-drain!`, then the compactor joined, then the kept stack; after
     the below-the-base error, `(kill-root-check!)` of a check above TOP, then
     `(discard-compacting-base!)` of a pending base above TOP, then the kept stack, then the
     rm (CompactionDeepReorg); `rollback-chain!` kills no check itself (one owner);
   * `compaction-swap!` refuses unless a layer at M is in the stack, before it installs.
-/

open EitaVeil.Code

def root : System.FilePath := "../.."

def files : Array String :=
  #["src/state/snapshot-world.lisp", "src/state/snapshot.lisp", "src/state/anchors.lisp",
    "src/state/recovery.lisp", "src/chains/driver.lisp"]

/-- The historical code the OLD models describe: (file, commit, line, fragment). -/
def history : Array (String × String × Nat × String) := #[
  ("snapshot-world.lisp", "0a9f2c0", 315, "(remove-if-not #'eita.state.snapshot:snap-p (cons *base* *layers*))"),
  ("snapshot-world.lisp", "807f8f5", 312, "(loop for l in *layers* when (ram-layer-p l)"),
  ("snapshot-world.lisp", "807f8f5", 314, "(remove-if-not #'eita.state.snapshot:snap-p (cons *base* *layers*))"),
  ("snapshot-world.lisp", "f1d29c6", 472, "(gone (cons *base* (member m *layers* :key #'layer-block)))"),
  ("snapshot-world.lisp", "f1d29c6", 473, "(keep (ldiff *layers* (member m *layers* :key #'layer-block)))"),
  ("snapshot-world.lisp", "f1d29c6", 496, "(defun rollback-to!"),
  ("snapshot-world.lisp", "f1d29c6", 500, "(writer-drain!)"),
  ("snapshot-world.lisp", "f1d29c6", 503, "(when *compactor* (sb-thread:join-thread *compactor*"),
  ("snapshot-world.lisp", "f1d29c6", 504, "(when (and *compactor-job* (> (layer-block (first (second *compactor-job*))) b))"),
  ("snapshot-world.lisp", "f1d29c6", 507, "(keep (member-if (lambda (l) (<= (layer-block l) b)) *layers*))"),
  ("snapshot-world.lisp", "f1d29c6", 509, "(top (if keep"),
  ("snapshot-world.lisp", "f1d29c6", 510, "(when (and (null keep) (> (eita.state.snapshot:snap-block *base*) b))"),
  ("snapshot-world.lisp", "f1d29c6", 512, "(setf *layers* keep)"),
  ("snapshot-world.lisp", "f1d29c6", 514, "(eita.state.snapshot:snap-close l)"),
  ("snapshot-world.lisp", "f1d29c6", 515, "(sb-ext:run-program \"rm\" (list \"-rf\""),
  ("driver.lisp", "f1d29c6", 224, "(defun rollback-chain!"),
  ("driver.lisp", "f1d29c6", 228, "(rollback-to! world fork)"),
  ("driver.lisp", "f1d29c6", 231, "(when (and *pending-root* (> (first *pending-root*) top))"),
  ("driver.lisp", "f1d29c6", 232, "(sb-ext:process-kill (third *pending-root*) 9)"),
  ("driver.lisp", "f1d29c6", 234, "(setf *pending-root* nil)")]

/-- The `setf` places of `f` (its odd arguments), as text. -/
def places (s : Src) (f : Form) : List String :=
  (List.range f.kids.size).filter (· % 2 == 1) |>.filterMap fun i => f.kids[i]?.map fun k => (s.text k).toLower

def orderings : IO (Array String) := do
  let sw ← Src.load root "src/state/snapshot-world.lisp"
  let sn ← Src.load root "src/state/snapshot.lisp"
  let dr ← Src.load root "src/chains/driver.lisp"
  let mut errs : Array String := #[]
  let count (a : Array String) (v : String) := (a.filter (· == v)).size
  -- live-components: one locked read
  match sw.findDefun "live-components" with
  | none => errs := errs.push "snapshot-world.lisp: no (defun live-components"
  | some lc =>
    let a := sw.atoms lc
    let locks := (sw.within lc "sb-thread:with-mutex").filter fun f =>
      (f.kids[1]?.bind (·.kids[0]?)).any fun x => (sw.text x).toLower == "*stack-lock*"
    let inside := if locks.size == 1 then sw.atoms locks[0]! else #[]
    for v in ["*layers*", "*base*"] do
      unless count a v == 1 && count inside v == 1 do
        errs := errs.push s!"live-components reads {v} {count a v} time(s), {count inside v} under one (with-mutex (*stack-lock*)): LayerGcFixed models exactly one locked read"
  -- every publication of *layers* right after the write barrier
  for f in walkAll sw.forms do
    if sw.head f == some "setf" && (places sw f).contains "*layers*" && !sw.barrierBefore f then
      errs := errs.push s!"snapshot-world.lisp:{sw.lineOf f.start}: (setf … *layers* …) without (sb-thread:barrier (:write)) right before it (the replay thread reads *layers* without the lock)"
  -- the fences: built, barrier, pointer; snap-close joins before it unmaps
  match sn.findDefun "snap-open" with
  | none => errs := errs.push "snapshot.lisp: no (defun snap-open"
  | some so =>
    let sets := (sn.within so "setf").filter fun f =>
      (places sn f).any fun p => p.startsWith "(snap-" && (indexOf p "fence s)").isSome
    unless sets.size == 2 do
      errs := errs.push s!"snap-open: {sets.size} (setf (snap-…-fence s) …), Compaction models two"
    for f in sets do
      unless sn.barrierBefore f do
        errs := errs.push s!"snapshot.lisp:{sn.lineOf f.start}: a fence published without (sb-thread:barrier (:write)) right before it (Compaction f_build before f_pub)"
  match sn.findDefun "snap-close" with
  | none => errs := errs.push "snapshot.lisp: no (defun snap-close"
  | some sc =>
    unless inOrder (sn.flat sc) ["sb-thread:join-thread", "(unmap"] do
      errs := errs.push "snap-close must join the fence thread before it unmaps (Compaction: snap-close waits for f_pub)"
  -- close-retired!
  match sw.findDefun "close-retired!" with
  | none => errs := errs.push "snapshot-world.lisp: no (defun close-retired!"
  | some cr =>
    let ok := match (sw.within cr "when")[0]? with
      | some w =>
        let c := (w.kids[1]?.map sw.flat).getD ""
        (indexOf c "(not *writer-busy*)").isSome && (indexOf c "(null *compactor*)").isSome &&
          (sw.atoms w).any fun x => (indexOf x "snap-close").isSome
      | none => false
    unless ok do
      errs := errs.push "close-retired!: snap-close only under (not *writer-busy*) and (null *compactor*) (Compaction close_retired)"
  -- write-layer!
  match sw.findDefun "write-layer!" with
  | none => errs := errs.push "snapshot-world.lisp: no (defun write-layer!"
  | some wl =>
    let a := (sw.within wl "sb-thread:with-mutex").map sw.atoms
    unless a.size == 2 && a[0]!.contains "*writer-busy*" && a[0]!.contains "stack-below" &&
        a[1]!.contains "*writer-busy*" && a[1]!.contains "substitute" do
      errs := errs.push "write-layer!: *writer-busy* T with stack-below, and NIL with the swap, each in one (with-mutex (*stack-lock*)) (Compaction w_take / w_swap)"
  -- rollback-to!
  match sw.findDefun "rollback-to!" with
  | none => errs := errs.push "snapshot-world.lisp: no (defun rollback-to!"
  | some rb =>
    let t := sw.flat rb
    unless inOrder t ["(writer-drain!)", "(sb-thread:join-thread *compactor*", "(setf *layers* keep)"] do
      errs := errs.push "rollback-to!: writer-drain!, then join the compactor, then publish the kept stack (Compaction rollback)"
    unless inOrder t ["(error \"rollback to ~d: below the base",
        "(when (and *pending-root* (> (first *pending-root*) top)) (kill-root-check!))",
        "(when (and *compacting-base* (> (eita.state.snapshot:snap-block *compacting-base*) top)) (discard-compacting-base!",
        "(setf *layers* keep)", "(dolist (l drop)"] do
      errs := errs.push "rollback-to!: the base error, then (kill-root-check!) of a check above TOP, then (discard-compacting-base!) of a pending base above TOP, then the kept stack, then the rm (CompactionDeepReorg rollback)"
  -- compaction-swap!
  match sw.findDefun "compaction-swap!" with
  | none => errs := errs.push "snapshot-world.lisp: no (defun compaction-swap!"
  | some cs =>
    unless inOrder (sw.flat cs) ["(unless (and s (eql m (eita.state.snapshot:snap-block s)) (member m *layers* :key #'layer-block))",
        "(return-from compaction-swap! nil)", "(setf *base* s *layers* keep)"] do
      errs := errs.push "compaction-swap!: refuse (return NIL) unless a layer at M is in the stack, before it installs the base (CompactionDeepReorg rc_pass_base_nomember)"
  -- one owner: rollback-to! kills the check; rollback-chain! does not
  match dr.findDefun "rollback-chain!" with
  | none => errs := errs.push "driver.lisp: no (defun rollback-chain!"
  | some rc =>
    let a := dr.atoms rc
    unless a.contains "rollback-to!" && !a.contains "sb-ext:process-kill" && !a.contains "*pending-root*" do
      errs := errs.push "rollback-chain!: calls rollback-to! and touches no root check itself (one owner of the kill)"
  return errs

def main : IO UInt32 := do
  let models := ((← System.FilePath.readDir "EitaVeil").map (·.path)).filter (fun p =>
    p.extension == some "lean" && p.fileName != some "Code.lean") |>.qsort (·.toString < ·.toString)
  let (errs, notes, n) ← check { root, files, models, history }
  let errs := errs ++ (← orderings)
  for x in notes do IO.println s!"note: {x}"
  for x in errs do IO.println s!"STALE: {x}"
  IO.println s!"check-code: {n} citations in {models.size} model files, 9 orderings: {if errs.isEmpty then "OK" else s!"{errs.size} problem(s)"}"
  return if errs.isEmpty then 0 else 1
