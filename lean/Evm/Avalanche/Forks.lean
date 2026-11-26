/-
  Evm.Avalanche.Forks — Avalanche C-Chain hardfork enumeration and schedule (Etna .. Helicon).

  Source: avalanchego d38de7e0 / v1.15.3
    upgrade/upgrade.go               Mainnet / Fuji activation timestamps
    graft/coreth/params/extras       RulesExtra (ActivePrecompiles, P256, Warp)
    graft/coreth/plugin/evm/customtypes/extra.go  predicateBytesOffset (ACP-176 / Helicon)

  Scope: Etna through Helicon (the modern Cancun+ snapshot-import era). Blocks before
  Etna are represented explicitly by `preEtna` and refused by the replay driver, matching
  Arc's pre-Zero6 policy: no unmodelled historical fork is executed silently.

  Fork summary (Mainnet chainId 43114):
    Etna     2024-12-16 16:00 UTC (1734364800)  ~Cancun (TLOAD/TSTORE/MCOPY/BLOBBASEFEE),
                                                 AP3 fee window (80 bytes in header extraData)
    Fortuna  2025-04-08 15:00 UTC (1744124400)  ACP-176 dynamic fee state (24 bytes in extraData)
    Granite  2025-11-19 16:00 UTC (1763568000)  EIP-7951 P256VERIFY at 0x100 (6900 gas),
                                                 Warp Granite gas config & DELEGATECALL ban
    Helicon  2026-09-22 15:00 UTC (1790089200)  ACP-194 SAE: minimum gas floor ceil(limit/2),
                                                 gas clock pricing, deferred stateRoot at
                                                 settledHeight, extraData predicate offset = 0
-/

import Evm.Forks

namespace Evm.Avalanche

/-- Avalanche C-Chain hardforks modelled by Eita (Etna through Helicon, plus `preEtna` sentinel). -/
inductive AvaxFork where
  | preEtna
  | etna
  | fortuna
  | granite
  | helicon
  deriving Repr, DecidableEq, Inhabited

namespace AvaxFork

/-- Linear ordinal in fork-sequence order. -/
def ord : AvaxFork → Nat
  | .preEtna => 0
  | .etna    => 1
  | .fortuna => 2
  | .granite => 3
  | .helicon => 4

/-- Is `f` at least fork `g`? -/
def atLeast (f g : AvaxFork) : Bool := decide (f.ord ≥ g.ord)

/-- Avalanche Mainnet (chainId 43114) activation timestamps (`upgrade/upgrade.go`). -/
def mainnetEtnaTime    : Nat := 1734364800
def mainnetFortunaTime : Nat := 1744124400
def mainnetGraniteTime : Nat := 1763568000
def mainnetHeliconTime : Nat := 1790089200

/-- Avalanche Fuji testnet (chainId 43113) activation timestamps (`upgrade/upgrade.go`). -/
def fujiEtnaTime    : Nat := 1732550400
def fujiFortunaTime : Nat := 1741276800
def fujiGraniteTime : Nat := 1761750000
def fujiHeliconTime : Nat := 1788274800

/-- Active Avalanche fork on Mainnet at `timestamp`. -/
def mainnetAt (timestamp : Nat) : AvaxFork :=
  if timestamp ≥ mainnetHeliconTime then .helicon
  else if timestamp ≥ mainnetGraniteTime then .granite
  else if timestamp ≥ mainnetFortunaTime then .fortuna
  else if timestamp ≥ mainnetEtnaTime then .etna
  else .preEtna

/-- Active Avalanche fork on Fuji at `timestamp`. -/
def fujiAt (timestamp : Nat) : AvaxFork :=
  if timestamp ≥ fujiHeliconTime then .helicon
  else if timestamp ≥ fujiGraniteTime then .granite
  else if timestamp ≥ fujiFortunaTime then .fortuna
  else if timestamp ≥ fujiEtnaTime then .etna
  else .preEtna

/-- Ethereum EL analog fork. Etna through Helicon all execute Cancun opcodes and gas
    (no EIP-7623 calldata floor, no EIP-7702 delegation). -/
def ethereumAnalog : AvaxFork → Evm.Fork
  | .preEtna => .shanghai
  | .etna    => .cancun
  | .fortuna => .cancun
  | .granite => .cancun
  | .helicon => .cancun

/-- Whether EIP-7951 P256VERIFY (0x100, 6900 gas) is active (Granite+). -/
def p256Active (f : AvaxFork) : Bool := f.atLeast .granite

/-- Whether ACP-194 Streaming Asynchronous Execution (SAE) is active (Helicon+). -/
def saeActive (f : AvaxFork) : Bool := f.atLeast .helicon

/-- Whether Warp rejects DELEGATECALL / CALLCODE (Granite+). -/
def warpDelegateDisallowed (f : AvaxFork) : Bool := f.atLeast .granite

/-- Byte offset in `header.extraData` where Warp `predicate.BlockResults` begins
    (`customtypes/extra.go` `predicateBytesOffset`):
    80 bytes (AP3 window) under Etna, 24 bytes (ACP-176 fee state) under Fortuna/Granite,
    0 bytes under Helicon (SAE moves fee state into dedicated header fields). -/
def extraDataResultsOffset : AvaxFork → Nat
  | .preEtna => 80
  | .etna    => 80
  | .fortuna => 24
  | .granite => 24
  | .helicon => 0

theorem mainnet_activations_ordered :
    mainnetEtnaTime < mainnetFortunaTime ∧
    mainnetFortunaTime < mainnetGraniteTime ∧
    mainnetGraniteTime < mainnetHeliconTime := by
  decide

theorem fuji_activations_ordered :
    fujiEtnaTime < fujiFortunaTime ∧
    fujiFortunaTime < fujiGraniteTime ∧
    fujiGraniteTime < fujiHeliconTime := by
  decide

theorem ethereumAnalog_cancun_from_etna (f : AvaxFork) (h : f.atLeast .etna = true) :
    f.ethereumAnalog = .cancun := by
  cases f <;> simp_all [atLeast, ord, ethereumAnalog]

theorem p256Active_iff_granite (f : AvaxFork) :
    f.p256Active = decide (f.ord ≥ 3) := by
  cases f <;> rfl

theorem saeActive_iff_helicon (f : AvaxFork) :
    f.saeActive = decide (f.ord ≥ 4) := by
  cases f <;> rfl

end AvaxFork
end Evm.Avalanche
