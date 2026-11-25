/-
  Evm.Optimism.Canyon.Spec.Create2Deployer — the state change of Canyon's activation block.

  Source: optimism-specs `specs/protocol/canyon/overview.md` ("Deploys the create2Deployer
  to 0x13b0D85CcB8bf860b6b79AF3029fCA081AE9beF2"), `specs/protocol/predeploys.md`
  §create2Deployer; op-geth@79e9d24 `consensus/misc/create2deployer.go` (lines 20-41,
  `EnsureCreate2Deployer`), called from `core/state_processor.go:81` before the block's
  pre-execution system calls.

  The rule: in the block whose timestamp EQUALS the chain's Canyon time (not every block
  after it), before anything else runs, the account's code is set to the create2Deployer
  runtime code (`create2deployer.bin`, whose keccak op-geth checks at init); nonce,
  balance and storage are untouched. The bytes are `chains/op/create2deployer.hex`
  (op-geth's file); the Lisp replay checks their hash against `codeHash` before use.
-/

import Evm.BaseTypes

namespace Evm.Optimism.Canyon.Spec

def create2DeployerAddress : Evm.Address := Evm.Address.ofNat 0x13b0D85CcB8bf860b6b79AF3029fCA081AE9beF2

/-- keccak256 of the create2Deployer runtime code (op-geth `create2DeployerCodeHash`). -/
def create2DeployerCodeHash : Nat :=
  0xb0550b5b431e30d38000efb7107aaa0ade03d48a7198a140edda9d27134468b2

/-- Canyon's activation time on Base mainnet (= OP Mainnet's and World Chain's). -/
def canyonTime : Nat := 1704992401

/-- The code is installed in exactly one block: the one at the Canyon time. -/
def installsCreate2Deployer (timestamp : Nat) : Bool := timestamp == canyonTime

theorem installs_only_at_canyon (ts : Nat) :
    installsCreate2Deployer ts = true ↔ ts = canyonTime := by
  simp [installsCreate2Deployer]

end Evm.Optimism.Canyon.Spec
