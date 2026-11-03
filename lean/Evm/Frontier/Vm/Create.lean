/-
  Evm.Frontier.Vm.Create — CREATE / CREATE2 for every fork, once.

  EELS `vm/instructions/system.py` `create` / `create2` / `generic_create`, then
  `vm/interpreter.py` `process_create_message` / `process_message`, then
  `vm/__init__.py` `incorporate_child_on_{success,error}` — the same clauses at every fork,
  switched by the fork's ordinal (`Rules.ofOrd`):

    * EIP-150 (TW, ord 3): forward all but 1/64 of the gas left after the charge
      (`max_message_call_gas`); before it, all of it.
    * EIP-2 (Homestead, ord 1): a code deposit the child cannot pay fails the creation;
      at Frontier the code is dropped and the creation succeeds with the child's gas.
    * EIP-161 (SD, ord 4): the new account starts at nonce 1 (`increment_nonce` in
      `process_create_message`); EIP-170: deployed code above 24576 bytes fails.
    * EIP-140 (Byzantium, ord 5): a REVERTing child returns its gas and its output
      becomes the creator's return data.
    * EIP-2929 (Berlin, ord 10): the new address joins the accessed set before the
      collision check, and stays there whatever happens next.
    * EIP-3541 (London, ord 11): deployed code starting with 0xEF fails.
    * EIP-3860 (Shanghai, ord 15): init code above 49152 bytes is an exceptional halt
      of the creator, and costs 2 gas per word.
    * EIP-6780 (Cancun, ord 16): the new address joins `createdAccounts` (EELS
      `mark_account_created`, from London; nothing before Cancun reads it).

  Every fork's `doCreate`/`doCreate2` is `opcode` (the pops, the static check from
  Byzantium, the memory charge, the address) then `start`; every fork's `.createLike`
  arm is `resume` on the child `runSub` returns. The derived host callback
  (`Evm.CL.EffectCreate`) is proved against `start`/`resume`
  (`Evm.CL.EffectCreateProof.create_refines`).

  EIP-7610 is not applied (EELS master: execution-specs #3417, merged 2026-08-25, commit
  2ce2191562, EIP-7610 declined per EIP-7773): the collision rule is EIP-684's nonce and
  code only (`account_deployable`, `forks/*/state_tracker.py`), and a creation over an
  account that holds storage wipes it before the init code runs (`process_create_message`'s
  `destroy_storage`, `forks/*/vm/interpreter.py` — Frontier line 159, Cancun line 167;
  #3508, merged 2026-09-23, commit faf6637766, made the Cancun+ trackers honour it: their
  reads no longer fall back to the pre-state). The slots' original values are then 0, as
  EELS's `get_storage_original` answers for a created account (the child's
  `originalState`; the Berlin+ cache records the wiped zeros at first touch). No mainnet
  creation can reach such an address (EIP-8253 bumps the 28 pre-Spurious ones).

  One deliberate choice, unobservable on any chain we replay:

    * A failed creation's `createdAccounts` mark is rolled back with the rest of the
      child (EELS never rolls the set back): an address whose creation failed carries
      no code, so no SELFDESTRUCT can run there before a later creation marks it again.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Utils.Address
import Evm.Petersburg.Utils.Address
import Evm.SpuriousDragon.Vm.Gas

namespace Evm.Frontier.Vm.Create

open Evm.Frontier (State Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions (chargeMemory)

/-- The fork rules the create family distinguishes. -/
structure Rules where
  homestead : Bool   -- EIP-2: deposit failure fails the creation
  eip150    : Bool   -- 63/64 forwarding
  eip161    : Bool   -- new account nonce 1; EIP-170 code size limit
  eip2929   : Bool   -- warm the new address
  eip3541   : Bool   -- reject code starting with 0xEF
  eip3860   : Bool   -- init code cap and word cost
  deriving DecidableEq, Repr

def Rules.ofOrd (k : Nat) : Rules :=
  { homestead := decide (k ≥ 1), eip150 := decide (k ≥ 3), eip161 := decide (k ≥ 4),
    eip2929 := decide (k ≥ 10), eip3541 := decide (k ≥ 11), eip3860 := decide (k ≥ 15) }

/-- EELS `STACK_DEPTH_LIMIT`. -/
def maxDepth : Nat := 1024
/-- EIP-2681's bound, the third leg of `generic_create`'s fail-fast. -/
def maxNonce : Nat := 2 ^ 64 - 1
/-- EIP-3860 `MAX_INIT_CODE_SIZE = 2 · MAX_CODE_SIZE`. -/
def maxInitCodeSize : Nat := 2 * Evm.SpuriousDragon.Vm.Gas.maxCodeSize
/-- EIP-3860 `init_code_cost`: 2 per word. -/
def initCodeCost (len : Nat) : Nat := 2 * ((len + 31) / 32)

/-- The opcode's own charge (memory aside): `GAS_CREATE`, the EIP-3860 word cost, and for
    CREATE2 the hashing cost `GAS_KECCAK256_WORD` per word. -/
def baseOf (r : Rules) (create2 : Bool) (len : Nat) : Nat :=
  Gas.create + (if r.eip3860 then initCodeCost len else 0)
    + (if create2 then Gas.keccak256Word * ((len + 31) / 32) else 0)

/-- EELS `not account_deployable`: a nonce or code at the address (EIP-684; no storage
    leg — EIP-7610 is not applied, execution-specs #3417). -/
def collides (s : State) (a : Evm.Address) : Bool :=
  decide ((s.getAccount a).nonce ≠ 0) || decide ((s.getAccount a).code.size ≠ 0)

/-- EELS `evm.accessed_addresses.add` on the tx's accessed set. -/
def warm (env : Environment) (a : Evm.Address) : Environment :=
  if env.accessedAddresses.contains a then env
  else { env with accessedAddresses := env.accessedAddresses ++ [a] }

/-- The world the init code starts in, from the creator's (nonce already bumped):
    `process_create_message`'s `destroy_storage` and `increment_nonce` (SD+), then
    `process_message`'s `touch_account` and `move_ether` (only a non-zero value moves). -/
def childState (r : Rules) (s : State) (sender newAddr : Evm.Address) (value : Evm.U256) : State :=
  let s := s.destroyStorage newAddr
  let s := if r.eip161 then s.setAccount newAddr
              { (s.getAccount newAddr) with nonce := (s.getAccount newAddr).nonce + 1 } else s
  let s := s.touchAccount newAddr
  if value = 0 then s else (s.subBalance sender value).addBalance newAddr value

/-- What happens after the charge. -/
inductive Start where
  /-- An exceptional halt of the creator (out of gas: the charge, or EIP-3860's cap). -/
  | halt
  /-- The creation fails before any code runs (fail-fast, collision): push 0 on this
      frame and continue. -/
  | done (evm : Evm)
  /-- Run the init code: the creator as it waits (`parent`), the child's message, and the
      world it starts in. -/
  | run (parent : Evm) (msg : Message) (st : State)

/-- `generic_create` from the charge to `process_create_message`. `evm` is the creator
    after the pops, the memory charge (and from Byzantium the static check): its gas is
    what is left after memory, its memory expanded, its stack popped, its pc at the
    opcode. -/
def start (r : Rules) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes)
    (newAddr : Evm.Address) (base : Nat) : Start :=
  if evm.gasLeft < base then .halt
  else if r.eip3860 ∧ initCode.size > maxInitCodeSize then .halt
  else
  let g := evm.gasLeft - base
  let fwd := if r.eip150 then g - g / 64 else g
  let sender := evm.message.currentTarget
  let acc := evm.env.state.getAccount sender
  let e0 : Evm := { evm with gasLeft := g, returnData := Evm.Bytes.empty }
  if evm.message.depth ≥ maxDepth ∨ acc.balance.toNat < value.toNat ∨ acc.nonce = maxNonce then
    .done e0
  else
  let env1 := if r.eip2929 then warm evm.env newAddr else evm.env
  let env2 := { env1 with state := env1.state.setAccount sender { acc with nonce := acc.nonce + 1 } }
  let e2 : Evm := { e0 with env := env2, gasLeft := g - fwd }
  if collides evm.env.state newAddr then .done e2
  else
  .run e2
    { caller := sender, target := none, currentTarget := newAddr, value := value,
      data := Evm.Bytes.empty, code := initCode, gas := fwd,
      depth := evm.message.depth + 1 }
    (childState r env2.state sender newAddr value)

/-- The child frame: the creator's tx environment with the child's world, the new
    address marked created (`mark_account_created`) and its original storage values 0
    (`get_storage_original` of a created account: the tx-start snapshot without its
    storage). -/
def child (parent : Evm) (msg : Message) (st : State) : Evm :=
  let created := parent.env.createdAccounts
  Evm.fresh msg { parent.env with
    state := st,
    originalState := parent.env.originalState.destroyStorage msg.currentTarget,
    createdAccounts := if created.contains msg.currentTarget then created
                       else msg.currentTarget :: created }

/-- Push the opcode's result and step past it. -/
def push (evm : Evm) (w : Evm.U256) : Except Exception Evm := do
  let s ← Stack.push evm.stack w
  return { evm with stack := s, pc := evm.pc + 1 }

/-- `process_create_message`'s end and `incorporate_child_on_*`, on the child's result:
    an exceptional halt or a REVERT keeps nothing of the child (a REVERT returns its gas
    and output); otherwise the code deposit — EIP-3541's prefix, the 200/byte charge,
    EIP-170's size — and on success the child's world with the code, the new address
    pushed. -/
def resume (r : Rules) (parent : Evm) (newAddr : Evm.Address) (res : Except Exception Evm) :
    Except Exception Evm :=
  let fail (g : Nat) (rd : Evm.Bytes) : Except Exception Evm :=
    push { parent with gasLeft := parent.gasLeft + g, returnData := rd } 0
  match res with
  | .error _ => fail 0 Evm.Bytes.empty
  | .ok sub =>
    if sub.reverted then fail sub.gasLeft sub.output
    else
    let code := sub.output
    let d := Gas.codeDeposit * code.size
    if r.eip3541 ∧ 0 < code.size ∧ code.get! 0 = (0xEF : UInt8) then fail 0 Evm.Bytes.empty
    else if sub.gasLeft < d then
      if r.homestead then fail 0 Evm.Bytes.empty
      else push { parent with env := sub.env, gasLeft := parent.gasLeft + sub.gasLeft,
                              returnData := Evm.Bytes.empty } (Evm.U256.ofNat newAddr.toNat)
    else if r.eip161 ∧ code.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize then fail 0 Evm.Bytes.empty
    else
      let st := sub.env.state.setAccount newAddr { (sub.env.state.getAccount newAddr) with code := code }
      push { parent with env := { sub.env with state := st },
                         gasLeft := parent.gasLeft + (sub.gasLeft - d),
                         returnData := Evm.Bytes.empty } (Evm.U256.ofNat newAddr.toNat)

/-- The whole of CREATE after the memory charge, with `runSub` the child's run. -/
def run (r : Rules) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes)
    (newAddr : Evm.Address) (base : Nat) (runSub : Evm → Except Exception Evm) :
    Except Exception Evm :=
  match start r evm value initCode newAddr base with
  | .halt => .error .outOfGas
  | .done e => push e 0
  | .run p m st => resume r p newAddr (runSub (child p m st))

/-- What the opcode hands the callback: the creator after the pops and the memory charge,
    the value, the init code, the address, the opcode's own charge, the creator's nonce. -/
structure Native where
  frame    : Evm
  value    : Evm.U256
  initCode : Evm.Bytes
  newAddr  : Evm.Address
  base     : Nat
  nonce    : Nat

/-- The opcode's part before `start` (the native handler's, in the replay): the static check
    (`static`: Byzantium+, EIP-214), the pops (CREATE2 adds the salt), the memory charge, the
    init code, the address (from the creator's nonce; CREATE2 from the salt and the init
    code, EIP-1014) and the charge. -/
def native (r : Rules) (static create2 : Bool) (evm : Evm) : Except Exception Native := do
  if static ∧ evm.message.isStatic then throw .writeInStaticContext
  let (value, offset, len, salt, s) ←
    if create2 then do
      let (a, s) ← Stack.pop evm.stack
      let (b, s) ← Stack.pop s
      let (c, s) ← Stack.pop s
      let (d, s) ← Stack.pop s
      pure (a, b, c, d, s)
    else do
      let (a, b, c, s) ← Stack.pop3 evm.stack
      pure (a, b, c, (0 : Evm.U256), s)
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory offset.toNat len.toNat
  let initCode := Evm.Bytes.sliceZeroPad mem offset.toNat len.toNat
  let sender := evm.message.currentTarget
  let nonce := (evm.env.state.getAccount sender).nonce
  let newAddr :=
    if create2 then Evm.Petersburg.Utils.computeCreate2Address sender salt initCode
    else Evm.Frontier.Utils.computeContractAddress sender nonce
  return { frame := { evm with gasLeft := gasLeft, memory := mem, stack := s }, value := value,
           initCode := initCode, newAddr := newAddr, base := baseOf r create2 len.toNat, nonce := nonce }

/-- The opcode, for a fork's step: `native`, then `start`. The continuations build the
    fork's own step result. -/
def opcode {R : Type} (r : Rules) (static create2 : Bool) (evm : Evm)
    (err : Exception → R) (cont : Evm → R)
    (yld : Evm → Message → State → Evm.Address → Nat → Evm.U256 → R) : R :=
  match native r static create2 evm with
  | .error e => err e
  | .ok n =>
  match start r n.frame n.value n.initCode n.newAddr n.base with
  | .halt => err .outOfGas
  | .done e =>
    match push e 0 with
    | .error x => err x
    | .ok e' => cont e'
  | .run p m st => yld p m st n.frame.message.currentTarget n.nonce n.value

end Evm.Frontier.Vm.Create
