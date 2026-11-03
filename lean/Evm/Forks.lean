/-
  Evm.Forks — fork enumeration and block/timestamp → fork dispatcher.

  Mirrors `src/evm/forks.lisp` in this repo. The activation table follows
  ethereum/execution-specs/network-upgrades/mainnet-upgrades/*.md.

  Constantinople and Petersburg both activate at block 7,280,000 on
  mainnet; Constantinople was reverted before activation, so the mainnet
  dispatcher resolves block 7,280,000 to Petersburg. Constantinople is
  still kept as a distinct fork because EELS retains it as a separate
  module and Ropsten / older testnets briefly ran it.
-/

namespace Evm

/-- All Ethereum execution-layer forks from Frontier through Amsterdam. -/
inductive Fork where
  | frontier
  | homestead
  | daoFork
  | tangerineWhistle
  | spuriousDragon
  | byzantium
  | constantinople
  | petersburg
  | istanbul
  | muirGlacier
  | berlin
  | london
  | arrowGlacier
  | grayGlacier
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  /-- EIP-7892 blob-parameter-only forks: EELS `forks/bpo1`, `forks/bpo2` — full fork
      modules whose only change over Osaka is the blob schedule (target, max, base-fee
      update fraction; `bpo{1,2}/vm/gas.py`). EELS also has `bpo3`..`bpo5` as
      `Unscheduled` placeholders carrying BPO2's parameters; they are not modelled until
      a mainnet schedule exists. -/
  | bpo1
  | bpo2
  | amsterdam
  deriving Repr, DecidableEq, Inhabited

namespace Fork

/-- The first block under Paris (The Merge) on mainnet: the first proof-of-stake block,
    EELS `forks/paris/__init__.py` `FORK_CRITERIA = ByBlockNumber(15537394)`. Block 15537393
    is the terminal proof-of-work block: Gray Glacier rules, difficulty > 0, a 2 ETH reward. -/
def mergeTransitionBlock : Nat := 15537394

/-- The timestamp at which Paris activated (block 15537394's timestamp). -/
def mergeTransitionTimestamp : Nat := 1663224179

/-- Pre-merge activation block numbers on Ethereum mainnet. -/
def premergeActivations : List (Fork × Nat) :=
  [ (.frontier,         0)
  , (.homestead,        1150000)
  , (.daoFork,          1920000)
  , (.tangerineWhistle, 2463000)
  , (.spuriousDragon,   2675000)
  , (.byzantium,        4370000)
  , (.constantinople,   7280000)  -- reverted; see module note
  , (.petersburg,       7280000)
  , (.istanbul,         9069000)
  , (.muirGlacier,      9200000)
  , (.berlin,           12244000)
  , (.london,           12965000)
  , (.arrowGlacier,     13773000)
  , (.grayGlacier,      15050000)
  , (.paris,            15537394)
  ]

/-- Post-merge activation timestamps on Ethereum mainnet. Amsterdam is
    `Unscheduled` on mainnet at time of writing (EELS
    `forks/amsterdam/__init__.py`); we omit it from the table and the
    dispatcher resolves it only via explicit selection. -/
def postmergeActivations : List (Fork × Nat) :=
  [ (.paris,    1663224162)
  , (.shanghai, 1681338455)
  , (.cancun,   1710338135)
  , (.prague,   1746612311)
  , (.osaka,    1764798551)  -- EELS forks/osaka/__init__.py (2025-12-03 21:49:11 UTC)
  , (.bpo1,     1765290071)  -- EELS forks/bpo1/__init__.py  (2025-12-09 14:21:11 UTC); geth
                             -- params/chainspecs/mainnet.json `bpo1Time`
  , (.bpo2,     1767747671)  -- EELS forks/bpo2/__init__.py  (2026-01-07 01:01:11 UTC); geth
                             -- `bpo2Time`
  ]

/-- Mainnet dispatcher: which fork is active at `(blockNumber, timestamp)`? -/
def ofBlock (blockNumber timestamp : Nat) : Fork :=
  if blockNumber ≥ mergeTransitionBlock then
    if timestamp ≥ 1767747671 then .bpo2
    else if timestamp ≥ 1765290071 then .bpo1
    else if timestamp ≥ 1764798551 then .osaka
    else if timestamp ≥ 1746612311 then .prague
    else if timestamp ≥ 1710338135 then .cancun
    else if timestamp ≥ 1681338455 then .shanghai
    else .paris
  else
    if blockNumber ≥ 15050000 then .grayGlacier
    else if blockNumber ≥ 13773000 then .arrowGlacier
    else if blockNumber ≥ 12965000 then .london
    else if blockNumber ≥ 12244000 then .berlin
    else if blockNumber ≥ 9200000  then .muirGlacier
    else if blockNumber ≥ 9069000  then .istanbul
    else if blockNumber ≥ 7280000  then .petersburg
    else if blockNumber ≥ 4370000  then .byzantium
    else if blockNumber ≥ 2675000  then .spuriousDragon
    else if blockNumber ≥ 2463000  then .tangerineWhistle
    else if blockNumber ≥ 1920000  then .daoFork
    else if blockNumber ≥ 1150000  then .homestead
    else .frontier

/-- Linear ordinal in fork-sequence order. Use with `≥` /  `<` to
    state "active from fork X onwards" in spec files.

    `daoFork` slots in between Homestead and Tangerine Whistle to
    match the mainnet activation table; specs that care only about
    semantic deltas can ignore it (its ordinal differs by a non-load-
    bearing 1). -/
def ord : Fork → Nat
  | .frontier         =>  0
  | .homestead        =>  1
  | .daoFork          =>  2
  | .tangerineWhistle =>  3
  | .spuriousDragon   =>  4
  | .byzantium        =>  5
  | .constantinople   =>  6
  | .petersburg       =>  7
  | .istanbul         =>  8
  | .muirGlacier      =>  9
  | .berlin           => 10
  | .london           => 11
  | .arrowGlacier     => 12
  | .grayGlacier      => 13
  | .paris            => 14
  | .shanghai         => 15
  | .cancun           => 16
  | .prague           => 17
  | .osaka            => 18
  | .bpo1             => 19
  | .bpo2             => 20
  | .amsterdam        => 21

/-- `f.atLeast g` — is `f` the same fork as `g` or newer? Reads
    naturally in spec sites: `f.atLeast .shanghai` ↔ "EIP-3651 is in
    effect at fork `f`". -/
def atLeast (f g : Fork) : Bool := decide (f.ord ≥ g.ord)

/-- The fork immediately preceding `f`. `frontier` returns `frontier`
    (no predecessor). Useful when describing one fork in terms of its
    delta from its parent. -/
def predecessor : Fork → Fork
  | .frontier         => .frontier
  | .homestead        => .frontier
  | .daoFork          => .homestead
  | .tangerineWhistle => .daoFork
  | .spuriousDragon   => .tangerineWhistle
  | .byzantium        => .spuriousDragon
  | .constantinople   => .byzantium
  | .petersburg       => .constantinople
  | .istanbul         => .petersburg
  | .muirGlacier      => .istanbul
  | .berlin           => .muirGlacier
  | .london           => .berlin
  | .arrowGlacier     => .london
  | .grayGlacier      => .arrowGlacier
  | .paris            => .grayGlacier
  | .shanghai         => .paris
  | .cancun           => .shanghai
  | .prague           => .cancun
  | .osaka            => .prague
  | .bpo1             => .osaka
  | .bpo2             => .bpo1
  | .amsterdam        => .bpo2

end Fork

end Evm
