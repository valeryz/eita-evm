module

public import EitaVeil.LayerGc

/-! # State GC vs the layer writer — OLD live-components (core 0a9f2c0)

`live-components` pinned only the stack's snaps (one read of `*layers*`): GC deletes a frozen
layer's directory under its writer. The incident (Arc stress, 2026-11-08): "rename: No such
file", the replay died. The shared state, writer and GC are in `EitaVeil/LayerGc.lean`.
-/

veil module LayerGcOld

layer_gc_writer
layer_gc_start GPin2

action g_pin_snap {               -- @code snapshot-world.lisp@0a9f2c0:315 (the only read of *layers*)
  require gpc = GPin2
  pinned L := pinned L ∨ snap L
  gpc := GDel
}

layer_gc_delete

#gen_spec

set_option veil.violationIsError false in
#model_check { layer := Fin 2 } { }

-- the incident's exact interleaving (layer-117-118 left by the previous life, resumed at 112)
sat trace [incident] {
  freeze
  w_take
  w_probe
  g_start
  g_pin_snap
  g_delete
  g_done
  w_aside
  assert (werr = true)
}

-- the other window: published (renamed, opened) but not yet swapped in — no error, the stack
-- then holds a snap whose directory is gone (a later resume or root check fails)
sat trace [published_window] {
  freeze
  w_take
  w_probe
  w_rename
  w_open
  g_start
  g_pin_snap
  g_delete
  g_done
  w_swap
  assert (∃ l, snap l ∧ ¬ disk l)
}

-- a kernel-checked counterexample (evaluation on Fin n, no solver in the proof)
#updr (expect := unsafe) certify
#gen_theorems
#print axioms ic3_unsafe
#check @ic3_unsafe

end LayerGcOld
