/-
  Evm.Optimism.Forks — OP Stack fork enumeration + ordinal.

  Parallel to `Evm.Forks` (the Ethereum mainnet enum). OP Stack
  hardforks are named distinctly even when they track an Ethereum
  upgrade (Canyon ↔ Shanghai, Ecotone ↔ Cancun, Isthmus ↔ Prague),
  because some forks introduce OP-only deltas (Fjord's RIP-7212;
  Granite's bn256 cap; Holocene's per-chain EIP-1559 params).

  Mapping (as of 2026-01):

    Bedrock   2023-06-06   pre-Shanghai baseline + deposited tx +
                            L1 fee accounting + L1Block predeploy
    Canyon    2024-01-11   ~Shanghai (PUSH0, withdrawals-shaped)
    Delta    *no Base*     batcher format, no EL delta
    Ecotone   2024-03-14   ~Cancun (TLOAD/TSTORE/MCOPY/EIP-6780/EIP-4844
                            blob-base-fee on L1 only)
    Fjord     2024-07-10   RIP-7212 secp256r1 at 0x100; FastLZ L1 fee
    Granite   2024-09-11   bn256 pairing input cap (1536 bytes)
    Holocene  2025-01-09   EIP-1559 params per chain (overridable)
    Isthmus   2025-05-09   ~Prague (BLS, EIP-2935, EIP-7702, ...)
                            + EIP-7685 requests-root in header
    Jovian    2025-12-02   operator-fee fix, DA footprint in blobGasUsed,
                            minimum base fee (extraData v1)
    Azul      2026-05-28   ~Osaka, Base only

  Activation timestamps below are Base mainnet's (chain id 8453), from the
  superchain-registry `superchain/configs/mainnet/base.toml` (@5b055be, the
  last revision before Base left the registry) and, for Azul, base/base
  `crates/common/chains/src/config.rs`; each one is MEASURED on chain (the
  first block at or after it is the first with the fork's L1-attributes
  selector or header format: Ecotone 11,792,527, Holocene 24,828,128 (9-byte
  extraData), Isthmus 30,008,527, Jovian 38,950,927 (extraData v1), Azul
  46,600,927). Until 2026-11-14 Holocene was recorded as 1740484801
  (2025-02-25); Base's extraData carries the Holocene parameters from
  block 24,828,128 (2025-01-09).
  Optimism Mainnet (chain id 10) uses slightly different timestamps;
  callers needing OP Mainnet should use a different table.
-/

import Evm.Forks

namespace Evm.Optimism

/-- All OP Stack execution-layer hardforks. We model only the ones
    that change EL semantics (Delta was a batcher-only upgrade, not
    listed). -/
inductive OpFork where
  | bedrock
  | canyon
  | ecotone
  | fjord
  | granite
  | holocene
  | isthmus
  | jovian
  | azul
  deriving Repr, DecidableEq, Inhabited

namespace OpFork

/-- Linear ordinal in fork-sequence order. Pair with `≥` to write
    "active at fork X+" spec conditions. -/
def ord : OpFork → Nat
  | .bedrock   => 0
  | .canyon    => 1
  | .ecotone   => 2
  | .fjord     => 3
  | .granite   => 4
  | .holocene  => 5
  | .isthmus   => 6
  | .jovian    => 7
  | .azul      => 8

/-- `f.atLeast g` — is `f` the same OP fork as `g` or newer? -/
def atLeast (f g : OpFork) : Bool := decide (f.ord ≥ g.ord)

/-- Base mainnet activation timestamps. Bedrock activated by *block
    number* not timestamp; we record it as 0 in the timestamp table
    since Base genesis is Bedrock. -/
def baseMainnetActivations : List (OpFork × Nat) :=
  [ (.bedrock,  0)            -- Base genesis 2023-06-06
  , (.canyon,   1704992401)   -- 2024-01-11 17:00:01 UTC
  , (.ecotone,  1710374401)   -- 2024-03-14 00:00:01 UTC
  , (.fjord,    1720627201)   -- 2024-07-10 16:00:01 UTC
  , (.granite,  1726070401)   -- 2024-09-11 16:00:01 UTC
  , (.holocene, 1736445601)   -- 2025-01-09 18:00:01 UTC
  , (.isthmus,  1746806401)   -- 2025-05-09 16:00:01 UTC
  , (.jovian,   1764691201)   -- 2025-12-02 16:00:01 UTC
  , (.azul,     1779991200)   -- 2026-05-28 18:00:00 UTC (Base only)
  ]

/-- Base mainnet dispatcher: which OP fork is active at `timestamp`?
    All Base mainnet forks (except Bedrock) activate by timestamp. -/
def baseMainnetAt (timestamp : Nat) : OpFork :=
  if timestamp ≥ 1779991200 then .azul
  else if timestamp ≥ 1764691201 then .jovian
  else if timestamp ≥ 1746806401 then .isthmus
  else if timestamp ≥ 1736445601 then .holocene
  else if timestamp ≥ 1726070401 then .granite
  else if timestamp ≥ 1720627201 then .fjord
  else if timestamp ≥ 1710374401 then .ecotone
  else if timestamp ≥ 1704992401 then .canyon
  else .bedrock

/-- The Ethereum mainnet fork that an OP fork's *EL semantics* tracks
    (modulo OP-specific deltas in `Spec/` files of each OP fork). -/
def ethereumAnalog : OpFork → Evm.Fork
  | .bedrock  => .london     -- pre-Shanghai
  | .canyon   => .shanghai
  | .ecotone  => .cancun
  | .fjord    => .cancun     -- no Ethereum-side delta; OP-only changes
  | .granite  => .cancun
  | .holocene => .cancun
  | .isthmus  => .prague
  | .jovian   => .prague     -- OP fee/DA rules only: Upgrade 17 left Osaka off on L2
  | .azul     => .osaka      -- Base-only Osaka activation

end OpFork

end Evm.Optimism
