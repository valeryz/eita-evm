/- Evm.Testnets — the fork schedules of Ethereum's public testnets: mainnet's fork modules,
   other activation points. -/

import Evm.Forks

namespace Evm.Fork

/-- Hoodi (chain id 560048), eth-clients/hoodi `metadata/genesis.json` @2a7efb3: through Cancun
    at genesis (no DAO fork, TTD 0), then `pragueTime`, `osakaTime`, `bpo1Time`, `bpo2Time`;
    Amsterdam unscheduled. Its `blobSchedule` is mainnet's, so the forks keep their parameters. -/
def ofHoodi (timestamp : Nat) : Fork :=
  if timestamp ≥ 1762955544 then .bpo2
  else if timestamp ≥ 1762365720 then .bpo1
  else if timestamp ≥ 1761677592 then .osaka
  else if timestamp ≥ 1742999832 then .prague
  else .cancun

/-- A network on mainnet's rules scheduled by timestamp from Cancun on, its activation times
    its own data — a devnet's genesis.json `pragueTime`, `osakaTime`, `bpo1Time`, `bpo2Time`
    (geth `--dev`, Kurtosis): Cancun before `prague`, then each fork from its time. The order
    of the forks is this table's; a network that schedules them otherwise is refused where
    the times are read (src/chains/ethereum.lisp). -/
def ofTimes (prague osaka bpo1 bpo2 timestamp : Nat) : Fork :=
  if timestamp ≥ bpo2 then .bpo2
  else if timestamp ≥ bpo1 then .bpo1
  else if timestamp ≥ osaka then .osaka
  else if timestamp ≥ prague then .prague
  else .cancun

end Evm.Fork
