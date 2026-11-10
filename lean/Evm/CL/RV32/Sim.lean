/-
  Evm.CL.RV32.Sim — the relation a lowering simulation for rv32 is stated over.

  `Items` builds the sequences, `Sem` executes them, `Carry` proves their
  arithmetic. What remains is the statement that ties them to the ARM-flavoured
  machine the handlers are written against — the rv32 counterpart of `X86Sem`'s
  simulation. This module carries the relation; the per-form theorems are the
  next stage and are named at the bottom.

  The relation is the interesting part, because it is what lets a 32-bit machine
  stand in for a 64-bit one.
-/

import Evm.CL.RV32.Items
import Evm.CL.AsmRun

namespace Evm.CL.RV32.Sim

open Evm.CL.AsmCore Evm.CL.RV32 Evm.CL.RV32.Asm Evm.CL.RV32.Items Evm.CL.RV32.Sem

/-- **A 64-bit `AsmCore.Reg` is held by its rv32 pair**, high half first.

    For the roles whose high half is `zero` (`Regs`: the `EvmState` pointer, the
    stack and code bases, `pc`, `sp`, and `gas`) this same definition *states
    their invariant* rather than assuming it: `0 ++ lo` can equal the ARM value
    only when that value fits 32 bits. So the narrowing decision taken in
    `Regs` — gas in one register, guarded at frame entry — appears here as a
    proof obligation wherever gas is held, not as a side comment. -/
def holds (s : AsmRun.RS) (t : RS) (r : Reg) : Prop :=
  (t.get (hiR r)) ++ (t.get (loR r)) = s.regs r

/-- The flag, whose polarity depends on provenance exactly as on x86-64
    (`X86Sem`'s `FlagsRel`): after an add the carry register is ARM's `C`;
    after a subtract ARM's `C` is the NO-borrow (`subFlags`: `c := b ≤ a`)
    while the register holds the borrow. A lowering proved under the wrong
    provenance would be a mis-lowered consumer, which is why the relation
    names which is in force. -/
inductive Prov where
  | add
  | sub
  deriving DecidableEq, Repr

def flagHolds (p : Prov) (s : AsmRun.RS) (t : RS) : Prop :=
  match p with
  | .add => t.get carryR = (if s.flags.c then 1#32 else 0#32)
  | .sub => t.get carryR = (if s.flags.c then 0#32 else 1#32)

/-- The carry register always holds a bit, which `Sem.addc32I_correct` needs as
    a hypothesis and every `sltu`/`sltiu` establishes. -/
def carryIsABit (t : RS) : Prop := (t.get carryR).ule 1#32 = true

/-! ## What is proved, and what is not

Proved so far, and all sorry-free:

* `Carry` — the arithmetic: the two carries are mutually exclusive, their `or`
  is the true carry out, and the two-half sequence IS 64-bit `BitVec` add/sub.
* `Sem.addc32I_correct` — the carry-in-and-carry-out sequence, executed on this
  machine, computes `p + q + c` and leaves the true carry, given register
  distinctness and `carryIsABit`.
* `Items.items_match_the_emitted_text` — where a form is structured, it prints
  exactly the text the production path prints, over every instruction the
  interpreter emits. So those proofs are about the file that ships.
* `Lower.no_carry_clobber_hazards` — no handler destroys a live flag, which is
  what licenses using `carry` as a scratch in the flag-neutral forms.

**Not proved: the per-form simulation**, e.g.

    sim_addReg : holds s t a → holds s t b → <register distinctness> →
      (exec _ (add64I n d a b false false) t).map (pairOf d)
        = some ((AsmRun.step s (.addReg d a b)).get.regs d)

The statement is settled; the proof is not. The obstacle is mechanical rather
than mathematical: `Sem.exec` recurses on a cons list, so it does not step until
`add64I`'s two appended `addc32I` blocks are unfolded to explicit items, and
their shape guards (`D == P && D == Q`, `D == Q`) have to be discharged from the
distinctness hypotheses first. `Carry.pair_add` already supplies the arithmetic
content, so what is missing is the unfolding script, per form. -/

end Evm.CL.RV32.Sim
