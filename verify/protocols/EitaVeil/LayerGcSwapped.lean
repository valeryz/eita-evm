module

public import EitaVeil.LayerGc

/-! # State GC vs the layer writer — core 807f8f5 with its two reads of *layers* swapped (hypothetical)

At 807f8f5 `live-components` read `*layers*` twice, the RAM layers first, then the snaps
(`append` evaluates in that order): safe. In the other order the writer's swap of layer N
between the two reads drops N from both: a violation in 10 steps. The shared state, writer
and GC are in `EitaVeil/LayerGc.lean`.
-/

veil module LayerGcSwapped

layer_gc_writer
layer_gc_start GPin1

action g_pin_snap {               -- @code snapshot-world.lisp@807f8f5:314 (HYPOTHETICAL first read of *layers*)
  require gpc = GPin1
  pinned L := pinned L ∨ snap L
  gpc := GPin2
}
action g_pin_ram {                -- @code snapshot-world.lisp@807f8f5:312 (HYPOTHETICAL second read)
  require gpc = GPin2
  pinned L := pinned L ∨ ram L
  gpc := GDel
}

layer_gc_delete

#gen_spec

set_option veil.violationIsError false in
#model_check { layer := Fin 2 } { }

end LayerGcSwapped
