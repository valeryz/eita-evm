/-
  Evm.Frontier.Vm.Gas — Frontier gas table.

  EELS reference: ethereum/frontier/vm/gas.py. Constants below mirror the
  original Yellow Paper schedule; many are repriced at later forks:
    - EXP byte cost (10 → 50 at Spurious Dragon, EIP-160).
    - SLOAD (50 → 200 at TangerineWhistle, 800 at Berlin warm).
    - BALANCE, EXTCODE*, CALL (20 → 700 at TangerineWhistle).
    - Calldata non-zero (68 → 16 at Istanbul, EIP-2028).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions

namespace Evm.Frontier.Vm.Gas

abbrev Gas : Type := Nat

-- Tier costs (Yellow Paper G_*).
def zero          : Gas := 0
def base          : Gas := 2
def veryLow       : Gas := 3
def low           : Gas := 5
def mid           : Gas := 8
def high          : Gas := 10

-- State-access costs (Frontier values; repriced at TangerineWhistle).
def balance       : Gas := 20
def sLoad         : Gas := 50
def sSet          : Gas := 20000
def sReset        : Gas := 5000
def sClearRefund  : Gas := 15000
def selfDestruct  : Gas := 0
def selfDestructRefund : Gas := 24000
def selfDestructNewAccount : Gas := 0  -- Frontier; 25000 at TangerineWhistle (EIP-150 has +25k under EIP-161; effective from SpuriousDragon)
def extCode       : Gas := 20
def call          : Gas := 40
def callValue     : Gas := 9000
def callStipend   : Gas := 2300
def newAccount    : Gas := 25000

-- Computation costs.
def jumpDest      : Gas := 1
def exp           : Gas := 10
def expByte       : Gas := 10   -- 50 at SpuriousDragon (EIP-160)
def memory        : Gas := 3
def keccak256     : Gas := 30
def keccak256Word : Gas := 6
def copy          : Gas := 3
def blockHash     : Gas := 20

-- Logs.
def logTopic      : Gas := 375
def log           : Gas := 375
def logData       : Gas := 8

-- Contract creation / transactions.
def create        : Gas := 32000
def codeDeposit   : Gas := 200   -- per byte of deployed code
def transaction   : Gas := 21000
def txCreate      : Gas := 0     -- 32000 at Homestead (EIP-2)
def txDataZero    : Gas := 4
def txDataNonZero : Gas := 68    -- 16 at Istanbul (EIP-2028)

/-- Cost of allocating `words` × 32 bytes of memory.
    `C_mem(a) = 3·a + ⌊a²/512⌋`. -/
def memoryCost (words : Nat) : Gas :=
  3 * words + (words * words) / 512

/-- Charged on a memory expansion from `oldWords` to `newWords`. -/
def memoryExpansionCost (oldWords newWords : Nat) : Gas :=
  if newWords ≤ oldWords then 0
  else memoryCost newWords - memoryCost oldWords

/-- Charge `n` gas, signalling `outOfGas` if insufficient. -/
def charge (remaining : Gas) (n : Gas) : Except Exception Gas :=
  if remaining < n then .error .outOfGas
  else .ok (remaining - n)

end Evm.Frontier.Vm.Gas
