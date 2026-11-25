module

public import Veil

/-! # State GC vs the layer writer: the parts the three variants share

`LayerGcOld`, `LayerGcSwapped` and `LayerGcFixed` differ only in how `live-components` pins
the stack (their own files); this file holds the rest once, as commands each variant splices
into its `veil module` (macros, hygiene off: the names are the module's own).

Code: `src/state/snapshot-world.lisp` (`freeze!`, `write-layer!`, `live-components`),
`src/state/snapshot.lisp` (`snap-publish`), `src/state/recovery.lisp` (`run-gc`),
`src/state/anchors.lisp` (`prune-dumps!`). The `@code` citations name the code an action
abstracts: a defun (`freeze!`), or a step in it (`freeze!/push`) marked `; @veil freeze!/push`
on its line in the Lisp; `CheckCode.lean` checks every citation against the code.

Per layer component `l` = layer-P-N:
  `ram l`   a RAM-LAYER for l is in `*layers*`;   `snap l`  its open snap is in `*layers*`;
  `disk l`  the directory layer-P-N/ exists (initially arbitrary: a previous life's copy);
  `wpc l`   the writer's progress on l.  `.tmp-layer-P-N/` and `.old-layer-P-N` are not
  modelled: `component-of-dir` (recovery.lisp) parses neither, so GC never touches them.
The replay thread runs `freeze!` and `prune-dumps!`, so they never interleave (gpc = GIdle
guards freeze). GC = `live-components` (the pin) then `run-gc` (scan + rm -rf each victim).
GC may delete ANY unpinned on-disk component: `gc-files` (the resume-point rule, proved in
lean/Evm/Persist) is abstracted away; it did name layer-117-118 in the incident.
-/

open Veil

public section

-- the macros splice commands into the variant's module: its names, not fresh ones
set_option hygiene false

/-- The state, `freeze!` and the layer writer. -/
macro "layer_gc_writer" : command => `(
type layer

enum WPC = { WNone, WQueued, WWriting, WProbedYes, WProbedNo, WRenamed, WOpened, WDone, WFailed }
enum GPC = { GIdle, GPin1, GPin2, GDel }

relation ram : layer → Bool
relation snap : layer → Bool
relation disk : layer → Bool
relation pinned : layer → Bool
function wpc : layer → WPC
individual gpc : GPC
individual werr : Bool      -- *writer-error*: "layer writer failed: rename/open: No such file"
individual bad : Bool       -- GC deleted the directory of a layer in the running stack

#gen_state

after_init {
  ram L := false
  snap L := false
  disk L := *
  pinned L := false
  wpc L := WNone
  gpc := GIdle
  werr := false
  bad := false
}

/-! ## Replay thread: freeze! (@code freeze!) -/
action freeze (l : layer) {
  require gpc = GIdle
  require wpc l = WNone ∧ ¬ ram l ∧ ¬ snap l
  ram l := true                    -- @code freeze!/push (cons l *layers*) under *stack-lock*
  wpc l := WQueued                 -- @code freeze!/pipe pipe-put
}

/-! ## Writer thread: @code write-layer!, @code write-ram-tables, @code snap-publish -/
action w_take (l : layer) {        -- @code write-layer!/take *writer-busy*, stack-below under the lock
  require wpc l = WQueued
  wpc l := WWriting
}
action w_probe (l : layer) {       -- tmp written (merge-finish); @code snap-publish/probe (probe-file final)
  require wpc l = WWriting
  if disk l then wpc l := WProbedYes else wpc l := WProbedNo
}
action w_aside (l : layer) {       -- @code snap-publish/aside (sb-posix:rename fin old)
  require wpc l = WProbedYes
  if disk l then
    disk l := false
    wpc l := WProbedNo
  else
    werr := true                   -- the incident: "rename: No such file"
    wpc l := WFailed
}
action w_rename (l : layer) {      -- @code snap-publish/rename (sb-posix:rename tmp fin)
  require wpc l = WProbedNo
  if disk l then
    werr := true                   -- rename onto a non-empty directory
    wpc l := WFailed
  else
    disk l := true
    wpc l := WRenamed
}
action w_open (l : layer) {        -- @code write-ram-tables/open (snap-open final)
  require wpc l = WRenamed
  if disk l then wpc l := WOpened
  else
    werr := true
    wpc l := WFailed
}
action w_swap (l : layer) {        -- @code write-layer!/swap (substitute snap l *layers*) under *stack-lock*
  require wpc l = WOpened
  ram l := false
  snap l := true
  wpc l := WDone
}
)

/-- `prune-dumps!` starts: the pins are reset; `pc` is the first pin step of the variant. -/
macro "layer_gc_start" pc:term : command => `(
/-! ## Replay thread: @code prune-dumps! → @code live-components → @code run-gc -/
action g_start {
  require gpc = GIdle
  pinned L := false
  gpc := $pc
}
)

/-- `run-gc`'s deletions, and the safety properties. -/
macro "layer_gc_delete" : command => `(
action g_delete (l : layer) {      -- @code run-gc/scan read-view, @code run-gc/victims set-difference, @code run-gc/rm rm -rf
  require gpc = GDel
  require disk l ∧ ¬ pinned l
  if ram l ∨ snap l then bad := true
  disk l := false
}
action g_done {
  require gpc = GDel
  gpc := GIdle
}

safety [writer_ok] werr = false
safety [gc_spares_stack] bad = false
safety [stack_on_disk] snap L → disk L
)

end
