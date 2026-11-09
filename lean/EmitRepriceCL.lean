import Evm.CL.RepriceEmit

/-! Emit the re-costing tool's per-charge prices (Evm.CL.RepriceEmit) as Common Lisp:

      lake exe emitRepriceCL > ../scripts/generated/reprice-amsterdam.lisp

    Loaded by scripts/reprice.lisp only; the replay never loads it. -/

def main : IO Unit := IO.print Evm.CL.RepriceEmit.emit
