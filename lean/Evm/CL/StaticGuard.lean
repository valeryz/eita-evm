/-
  Evm.CL.StaticGuard — EIP-214 write protection, as a theorem.

  Last item of stage 1 (#238). `AsmCore.staticGuard` emits

      ldrb w14, [x20, #130]            ; EvmState.is_static
      cbnz w14, _eita_static_violation

  and denoted `m` — "coarse: static-context check (no static flag modelled)".
  With nothing modelled, no proof could tell a handler that checks the flag from
  one that does not, which is the whole content of EIP-214: inside a STATICCALL,
  every state-modifying op must fault.

  `Mach.isStatic` now carries byte #130 and `staticGuard` traps on it, so the
  question becomes which bodies carry the guard — and that is checkable both
  ways: every write op faults, and no read-only op does (a spurious guard would
  break ordinary execution, which is the failure mode a "just add the guard
  everywhere" fix would produce).
-/

import Evm.CL.AsmCore

namespace Evm.CL.StaticGuard

open Evm.CL.AsmCore

/-- A frame inside a STATICCALL, otherwise unconstrained. -/
def staticMach (m : Mach) : Mach := { m with isStatic := true }

/-! ## The guard itself -/

theorem guard_traps_in_static (m : Mach) :
    ((Op.staticGuard).denote (staticMach m)).trap = true := by
  simp [Op.denote, staticMach]

theorem guard_is_transparent_outside_static (m : Mach) (h : m.isStatic = false) :
    (Op.staticGuard).denote m = m := by
  simp [Op.denote, h]

/-! ## Every state-modifying op faults in a static context

Each of these bodies BEGINS with `.staticGuard`, so the trap is set before
anything else runs — before any gas is charged and before any journal entry is
pushed, which is what makes the fault clean. The argument is the same for all
six, so it is made once: `trap` is monotone (no op clears it), hence a program
whose first op traps, traps. -/

/-- No single op clears `trap`. -/
theorem trap_monotone (o : Op) (m : Mach) (h : m.trap = true) :
    (o.denote m).trap = true := by
  cases o <;> simp_all [Op.denote] <;> (repeat' split) <;> simp_all

/-- …so neither does a program. -/
theorem prog_trap_monotone (p : Prog) (m : Mach) (h : m.trap = true) :
    (p.denote m).trap = true := by
  induction p generalizing m with
  | nil => simpa [Prog.denote] using h
  | cons o rest ih =>
    have := trap_monotone o m h
    simpa [Prog.denote] using ih (o.denote m) this

/-- A program that starts with the guard faults in a static frame. -/
theorem guarded_faults (rest : Prog) (m : Mach) :
    (Prog.denote (Op.staticGuard :: rest) (staticMach m)).trap = true := by
  have h : ((Op.staticGuard).denote (staticMach m)).trap = true := by
    simp [Op.denote, staticMach]
  simpa [Prog.denote] using prog_trap_monotone rest _ h

theorem sstore_faults (m : Mach) (sentry : Nat) :
    ((sstoreBody sentry).denote (staticMach m)).trap = true := by
  cases sentry <;> exact guarded_faults _ m

theorem tstore_faults (m : Mach) :
    (tstoreBody.denote (staticMach m)).trap = true := guarded_faults _ m

theorem log_faults (m : Mach) (n cost : Nat) :
    ((logBody n cost).denote (staticMach m)).trap = true := guarded_faults _ m

theorem create_faults (m : Mach) :
    (createBody.denote (staticMach m)).trap = true := guarded_faults _ m

theorem create2_faults (m : Mach) :
    (create2Body.denote (staticMach m)).trap = true := guarded_faults _ m

theorem selfdestruct_faults (m : Mach) (cost : Nat) :
    ((selfdestructBody cost).denote (staticMach m)).trap = true := guarded_faults _ m

/-! ## …and no read-only op does

The other direction matters just as much: a guard added where EIP-214 does not
ask for one would fault ordinary execution inside every STATICCALL. These are
the ops a static frame must still be able to run. -/

/-- MSTORE has no static guard at all, so a static frame can still write
    memory — stated structurally, which is stronger than any single run. -/
theorem mstore_has_no_static_guard :
    (mstoreBody 3).all (fun o => decide (o ≠ Op.staticGuard)) = true := by native_decide

theorem mload_has_no_static_guard :
    (mloadBody 3).all (fun o => decide (o ≠ Op.staticGuard)) = true := by native_decide

theorem sload_has_no_static_guard :
    (sloadBody).all (fun o => decide (o ≠ Op.staticGuard)) = true := by native_decide

theorem return_has_no_static_guard :
    returnBody.all (fun o => decide (o ≠ Op.staticGuard)) = true := by native_decide

/-! ## The guard set, against EIP-214's list

EIP-214 forbids SSTORE, LOG0-4, CREATE, CREATE2, SELFDESTRUCT and a CALL with
nonzero value; Cancun adds TSTORE. CALL is the one that is NOT a plain guard: its
restriction is value-conditional, `staticValueGuard`. (Until 2026-10-24 this file
said the call-gas plan handled it; nothing did, and a value CALL inside STATICCALL
moved wei — ethereum/tests static_CheckOpcodes2/3, Byzantium+.) -/

/-- Bodies that must carry the guard, and do. -/
theorem guarded_bodies_carry_it :
    [sstoreBody 0, tstoreBody, logBody 0 375, createBody, create2Body,
     selfdestructBody 5000].all (fun b => b.any (fun o => decide (o = Op.staticGuard))) = true := by
  native_decide

/-- CALL carries the value-conditional guard and no plain one; CALLCODE, DELEGATECALL
    and STATICCALL carry neither (they move no value to another account). -/
theorem call_carries_value_guard :
    (callFamilyBody "call" 0 0 true).contains Op.staticValueGuard ∧
    (callFamilyBody "call" 0 0 true).all (fun o => decide (o ≠ Op.staticGuard)) ∧
    ([callFamilyBody "callcode" 1 0 true, callFamilyBody "delegatecall" 2 0 false,
      callFamilyBody "staticcall" 3 1 false].all (fun b => !b.contains Op.staticValueGuard)) = true := by
  native_decide

/-- A value CALL in a static frame faults; zero value, or a non-static frame, passes. -/
theorem value_guard_traps (m : Mach) (hv : m.mem (m.sp - 3) ≠ U256.ofScalar 0) :
    ((Op.staticValueGuard).denote (staticMach m)).trap = true := by
  simp [Op.denote, staticMach, hv]
theorem value_guard_transparent (m : Mach) (h : m.isStatic = false ∨ m.mem (m.sp - 3) = U256.ofScalar 0) :
    (Op.staticValueGuard).denote m = m := by
  rcases h with h | h <;> simp [Op.denote, h]

end Evm.CL.StaticGuard
