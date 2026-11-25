/-
  Evm.Optimism.Denim.Fork — Base's Denim (2026-11-05 18:00 UTC, timestamp 1793901600):
  200 ms blocks.

  Source: base/base @ v1.5.6 (a9f6cc9d). Delta on Cobalt in the execution layer:

    * the timestamp schedule (Spec.BaseTime): from the activation block (53,556,127 on Base
      mainnet) blocks are 200 ms apart; the header's `timestamp` stays in seconds and may
      repeat, so the parent check allows equal timestamps between two Denim blocks;
    * every block's tx[1] is the BaseTime metadata deposit writing the block's millisecond
      part into the BaseTime predeploy (0x4200…0030), which the activation block installs
      before its transactions (Spec.BaseTime.ensurePredeploy);
    * the third version of the asset, stablecoin and policy logic (versions.rs).

  Denim's other features (the six-hour sequencer drift, one-shot payload building, singular
  batches only, the gas parameters divided by ten in the derived system config) are the
  rollup node's and the sequencer's: the execution layer reads the resulting gas limit and
  EIP-1559 parameters from the header as before (consensus/derive/src/attributes/
  stateful.rs:170-180). Fork activation stays by header seconds against the activation
  times (Evm.Optimism.OpFork.baseMainnetAt); the schedule's activation block is the first
  whose seconds reach Denim's time.
-/

import Evm.Optimism.Cobalt.Fork
import Evm.Optimism.Denim.Spec.BaseTime

namespace Evm.Optimism.Denim

open Evm.Optimism (OpFork)

/-- The schedule's activation block is the first by header seconds: its seconds are at or
    past Denim's time and its parent's are not. -/
theorem activation_by_seconds :
    OpFork.baseMainnetAt (Spec.baseMainnet.seconds 53556127) = .denim ∧
    OpFork.baseMainnetAt (Spec.baseMainnet.seconds 53556126) = .cobalt := by
  decide

/-- Five blocks share each Denim second. -/
example : (List.range 5).map (fun i => Spec.baseMainnet.seconds (53556127 + i)) =
    List.replicate 5 1793901601 := by decide

end Evm.Optimism.Denim
