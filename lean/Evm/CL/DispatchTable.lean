/-
  Evm.CL.DispatchTable — the 256-entry opcode table, checked.

  Stage 1 of #238. With every per-op handler now structured and the gas-bearing
  gadgets denoted, the remaining hand-written asm in `ARM64.lean` is the
  threading machinery and this DATA table:

      _eita_dispatch_table:
          .quad   _eita_handler_<name>     -- 256 of these
          …

  and `_eita_next` indexes it with the opcode byte:

      ldrb w14, [x26, x21]          ; code[pc]
      add  x21, x21, #1             ; pc++
      ldr  x14, [x25, x14, lsl #3]  ; dispatch_table[op]
      br   x14

  Nothing about that indexing is checked by a handler proof: it is the step
  BEFORE any handler runs. Three things can go wrong, all silently —

    * the table is not exactly 256 entries, so some byte indexes past its end
      and `br` jumps to whatever follows in .data;
    * `opcodeNameMap` lists a byte twice, and `find?` silently takes the first,
      so one of the two opcodes runs the other's handler;
    * an opcode the registry implements maps to `_eita_handler_invalid` (or the
      reverse: an opcode with no handler maps to a real one).

  The first two are properties of the emitter's data, decidable by evaluation.
  The third is the agreement between `opcodeNameMap` and the handler registry.
  All of them are below as `native_decide`, so a hand edit to either list that
  breaks the correspondence fails the build rather than the chain.
-/

import Evm.CL.ARM64
import Evm.CL.ARM64.Interp
import Evm.IR.Compile

namespace Evm.CL.DispatchTable

open Evm.CL.ARM64

/-- Bytes the opcode map names, in order. -/
def mappedBytes : List Nat := opcodeNameMap.map (·.1)

/-- Names the opcode map uses. -/
def mappedNames : List String := opcodeNameMap.map (·.2)

/-! ## The table is total and well-formed -/

/-- Every byte 0..255 gets exactly one `.quad`. `dispatchTableNamed` builds it
    with `List.range 256`, so this is really a check that the emitter's shape is
    what the `ldr x14, [x25, x14, lsl #3]` indexing assumes. -/
theorem table_has_256_entries :
    ((dispatchTableNamed "_t" (fun n => n)).splitOn ".quad").length = 257 := by
  native_decide

/-- **No byte is listed twice.** `opcodeNameMap.find?` takes the FIRST match, so
    a duplicate would silently give one opcode the other's handler — and with
    256 hand-written rows, this is exactly the edit that goes unnoticed. -/
theorem mappedBytes_nodup : mappedBytes.Nodup := by native_decide

/-- No name is used for two different opcodes either. (Two bytes legitimately
    sharing a handler would be a design choice; today none do, and a surprise
    duplicate is far more likely to be a copy-paste slip.) -/
theorem mappedNames_nodup : mappedNames.Nodup := by native_decide

/-- Every mapped byte is a byte. -/
theorem mappedBytes_lt_256 : mappedBytes.all (· < 256) = true := by native_decide

/-! ## The table agrees with the handler registry

`dispatchTable` resolves each name against the registry and falls back to
`_eita_handler_invalid`; `allHandlers` is the Cancun-pinned registry the
threaded interpreter emits. -/

/-- Names in the registry. -/
def registryNames : List String := Evm.CL.ARM64.Interp.allHandlers.map (·.1)

/-- **Every opcode the map names has a handler in the registry.** A name in the
    map with no handler silently becomes `_eita_handler_invalid`, i.e. the
    opcode faults at run time with nothing at build time to say so. -/
theorem every_mapped_opcode_has_a_handler :
    mappedNames.all (fun n => registryNames.contains n) = true := by native_decide

/-- …and the table entry for every mapped byte really is that handler, not the
    invalid stub. This is the composition of the two lists as the emitter does
    it, so it catches a mismatch in either. -/
def entryFor (b : Nat) : String :=
  match opcodeNameMap.find? (fun (op, _) => op == b) with
  | some (_, nm) =>
      match Evm.CL.ARM64.Interp.allHandlers.find? (fun (n, _) => n == nm) with
      | some _ => s!"_eita_handler_{nm}"
      | none   => "_eita_handler_invalid"
  | none => "_eita_handler_invalid"

/-- Every mapped byte resolves to its own handler — EXCEPT 0xfe, whose opcode
    IS `INVALID` and whose handler therefore legitimately is the invalid stub.
    (First version of this theorem omitted the exception and failed; the code was
    right.) -/
theorem mapped_bytes_resolve_to_real_handlers :
    (mappedBytes.filter (· ≠ 0xfe)).all
      (fun b => entryFor b ≠ "_eita_handler_invalid") = true := by
  native_decide

/-- 0xfe and an undefined byte are INDISTINGUISHABLE in the table, which is
    exactly right: the designated INVALID opcode and an undefined one must fault
    identically. So the table cannot encode the difference, and does not try. -/
theorem invalid_opcode_and_undefined_byte_agree :
    entryFor 0xfe = entryFor 0x0c := by native_decide

/-- **And an unmapped byte resolves to the invalid stub** — the other direction,
    which is what makes an undefined opcode fault instead of running whatever
    handler happens to sit at that index. -/
theorem unmapped_bytes_resolve_to_invalid :
    ((List.range 256).filter (fun b => ¬ mappedBytes.contains b)).all
      (fun b => entryFor b = "_eita_handler_invalid") = true := by
  native_decide

/-- The two directions together cover all 256 bytes, so the table is a total
    function with no byte unaccounted for. -/
theorem every_byte_is_classified :
    ((List.range 256).filter (fun b => mappedBytes.contains b)).length
      + ((List.range 256).filter (fun b => ¬ mappedBytes.contains b)).length = 256 := by
  native_decide

/-- How much of the byte space is actually implemented — a fact worth having
    written down, since the rest is `_eita_handler_invalid` by construction. -/
theorem implemented_opcode_count : mappedBytes.length = 150 := by native_decide

/-- …of which 149 have a handler of their own; 0xfe shares the invalid stub. -/
theorem distinct_handler_count :
    (mappedBytes.filter (· ≠ 0xfe)).length = 149 := by native_decide

/-! ## Fork gating

`dispatchTable` takes a `present` predicate and maps an absent opcode to the
invalid stub, which is how PUSH0 faults before Shanghai rather than executing.
The gating is a function of that predicate, so what is checkable here is that it
is applied at all — i.e. that a `present` which rejects a name really does
remove it from the table. -/

def entryForGated (present : String → Bool) (b : Nat) : String :=
  match opcodeNameMap.find? (fun (op, _) => op == b) with
  | some (_, nm) =>
      match Evm.CL.ARM64.Interp.allHandlers.find? (fun (n, _) => n == nm) with
      | some _ => if present nm then s!"_eita_handler_{nm}" else "_eita_handler_invalid"
      | none   => "_eita_handler_invalid"
  | none => "_eita_handler_invalid"

/-- With PUSH0 absent (pre-Shanghai), byte 0x5f dispatches to the invalid stub
    — not to the PUSH0 handler, and not past the end of the table. -/
theorem push0_gated_off_is_invalid :
    entryForGated (fun n => n ≠ "push0") 0x5f = "_eita_handler_invalid" := by
  native_decide

/-- …and with it present it is the real handler, so the gate is the only thing
    that moved. -/
theorem push0_present_is_handler :
    entryForGated (fun _ => true) 0x5f = "_eita_handler_push0" := by
  native_decide

/-- The same for an opcode gated by a later fork (MCOPY, Cancun). -/
theorem mcopy_gated_off_is_invalid :
    entryForGated (fun n => n ≠ "mcopy") 0x5e = "_eita_handler_invalid" := by
  native_decide

/-! ## The JIT compiler admits exactly the interp's opcodes, per fork

Opcode admission has two homes: the interp's tables gate a name by
`Interp.handlerSymbol` (the `Op.metadata` rows), the IR compiler by the
`fork.atLeast` arms of `IR.compileLoop`, whose default arm compiles any other
byte to `.invalid`. A byte the metadata admits but `compileLoop` has no arm for
is silently an exceptional halt on the JIT tier only — CLZ (0x1e, Osaka) was
exactly that until mainnet block 24,538,111. -/

/-- The table the host selects for fork `f` (`forkTablesInstrs`): its own below
    Cancun, the default (Cancun registry) for Cancun/Prague, the Osaka table for
    Osaka and after. -/
def interpTableFork : Evm.Fork → Evm.Fork
  | .cancun | .prague => .cancun
  | .osaka | .bpo1 | .bpo2 | .amsterdam => .osaka
  | f => f

/-- Byte `b` dispatches to a real handler in fork `f`'s interp table. -/
def interpAdmits (f : Evm.Fork) (b : Nat) : Bool :=
  match opcodeNameMap.find? (fun (op, _) => op == b) with
  | some (_, nm) => Interp.handlerSymbol (interpTableFork f) nm != "_eita_handler_invalid"
  | none => false

/-- Byte `b` compiles, at fork `f`, to something other than the `.invalid`
    terminator (alone, at pc 0 of a one-byte code). -/
def jitAdmits (f : Evm.Fork) (b : Nat) : Bool :=
  match Evm.IR.compileLoop f ⟨#[b.toUInt8]⟩ 0 with
  | .ok ([], _, .invalid, _) => false
  | .ok _ => true
  | .error _ => false

def allForks : List Evm.Fork :=
  [.frontier, .homestead, .daoFork, .tangerineWhistle, .spuriousDragon, .byzantium,
   .constantinople, .petersburg, .istanbul, .muirGlacier, .berlin, .london,
   .arrowGlacier, .grayGlacier, .paris, .shanghai, .cancun, .prague, .osaka,
   .bpo1, .bpo2, .amsterdam]

/-- **The two tiers admit the same opcodes**, every fork, every byte. -/
theorem jit_admits_exactly_interp_opcodes :
    allForks.all (fun f => (List.range 256).all (fun b => interpAdmits f b == jitAdmits f b))
      = true := by native_decide

/-- …and the theorem has teeth: CLZ is admitted from Osaka (both tiers), not before. -/
theorem clz_admitted_from_osaka :
    jitAdmits .bpo2 0x1e = true ∧ interpAdmits .bpo2 0x1e = true ∧
    jitAdmits .prague 0x1e = false ∧ interpAdmits .prague 0x1e = false := by native_decide

end Evm.CL.DispatchTable
