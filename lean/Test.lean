import Evm.Crypto.Hash
import Evm.Crypto.Sha256
import Evm.Crypto.Ripemd160
import Evm.Crypto.P256Verify
import Evm.Trie
import Evm.BaseTypes
import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Replay.Dispatch

open Evm.Crypto

private def hexOfNibble (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 0x30)
  else Char.ofNat (n - 10 + 0x61)

private def hexOfByte (b : UInt8) : String :=
  String.ofList [hexOfNibble ((b.toNat >>> 4) &&& 0xf), hexOfNibble (b.toNat &&& 0xf)]

private def hexOfBytes (b : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0:b.size] do
    out := out ++ hexOfByte (b.get! i)
  pure out

def main : IO Unit := do
  -- Empty trie root.
  let r := Evm.Trie.emptyRootBytes
  IO.println s!"emptyRoot: 0x{hexOfBytes r}"
  let expected := "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
  IO.println s!"expected:  0x{expected}"
  IO.println s!"match:     {hexOfBytes r == expected}"

  -- Trie with one entry: key="\x42", value="\x42".
  -- Per the well-known test vector: keccak256(rlp([hexPrefix([4,2], leaf), "\x42"]))
  let single := Evm.Trie.rootBytes [(ByteArray.mk #[0x42], ByteArray.mk #[0x42])]
  IO.println s!"single-entry trie root: 0x{hexOfBytes single}"

  -- Smoke test: Optimism Bedrock deposited tx.
  --   sender   : 0x1111...
  --   recipient: 0x2222...
  --   mint = 100, value = 30, data = empty, gas = 21000
  -- Expect post: sender = 70, recipient = 30. No fee accounting.
  let sender    : Evm.Address := Evm.Address.ofNat 0x1111
  let recipient : Evm.Address := Evm.Address.ofNat 0x2222
  let depTx : Evm.Optimism.Bedrock.DepositedTx :=
    { sourceHash := 0
      from_      := sender
      to         := some recipient
      mint       := (100 : Evm.U256)
      value      := (30  : Evm.U256)
      gas        := (21000 : Evm.U256)
      isSystemTx := false
      data       := Evm.Bytes.empty }
  let coinbase : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000011
  match Evm.Optimism.Bedrock.processDepositedTx
          (state := Evm.Frontier.State.empty)
          (blockHashes := [])
          (coinbase := coinbase)
          (number := 1) (gasLimit := 30_000_000) (timestamp := 0)
          (baseFeePerGas := 0)
          (prevRandao := 0)
          (tx := depTx) with
  | .ok r =>
    let sB := (r.state.getAccount sender).balance
    let rB := (r.state.getAccount recipient).balance
    IO.println s!"deposited tx: sender={sB.toNat} recipient={rB.toNat} success={r.success}"
    IO.println s!"deposited tx OK: {sB.toNat == 70 && rB.toNat == 30 && r.success}"
  | .error e =>
    IO.println s!"deposited tx FAILED: {e}"

  -- Smoke test: Bedrock.applyBlock with one user tx.
  --   sender starts with 1 ETH; pays gasPrice=100, l1Fee=500,
  --   sends 10 wei to recipient.
  -- Expect post:
  --   sender = 1e18 - 10 - (21000*100) - 500
  --   recipient = 10
  --   SequencerFeeVault = (100 - baseFee) * gasUsed
  --   BaseFeeVault = baseFee * gasUsed
  --   L1FeeVault = 500
  let baseFee := 50
  let sender2 : Evm.Address := Evm.Address.ofNat 0xa11ce
  let recip2  : Evm.Address := Evm.Address.ofNat 0xb0b
  let preState : Evm.Frontier.State := Id.run do
    let mut st := Evm.Frontier.State.empty
    st := st.setAccount sender2 { Evm.Frontier.Account.empty with
      balance := Evm.U256.ofNat (10 ^ 18), nonce := 0 }
    pure st
  let userTx : Evm.Optimism.Bedrock.UserTxInputs :=
    { sender := sender2
      effectiveGasPrice := 100
      gas               := 21000
      to                := some recip2
      value             := (10 : Evm.U256)
      data              := Evm.Bytes.empty
      nonce             := 0
      l1FeeWei          := 500 }
  let coinbase2 : Evm.Address := Evm.Address.ofNat 0x4200000000000000000000000000000000000011
  match Evm.Optimism.Bedrock.applyBlock
          (state := preState)
          (blockHashes := [])
          (coinbase := coinbase2)
          (number := 1) (gasLimit := 30_000_000) (timestamp := 0)
          (baseFeePerGas := baseFee)
          (prevRandao := 0)
          (txs := [.user userTx]) with
  | .ok br =>
    let sBal := (br.state.getAccount sender2).balance.toNat
    let rBal := (br.state.getAccount recip2).balance.toNat
    let seqV := (br.state.getAccount
                   (Evm.Address.ofNat 0x4200000000000000000000000000000000000011)).balance.toNat
    let baseV := (br.state.getAccount
                    (Evm.Address.ofNat 0x4200000000000000000000000000000000000019)).balance.toNat
    let l1V := (br.state.getAccount
                  (Evm.Address.ofNat 0x420000000000000000000000000000000000001a)).balance.toNat
    let exp_sender   := (10 ^ 18) - 10 - (21000 * 100) - 500
    let exp_seq      := (100 - baseFee) * 21000
    let exp_base     := baseFee * 21000
    let exp_l1       := 500
    IO.println s!"\nOP block: sender={sBal} recip={rBal} seqV={seqV} baseV={baseV} l1V={l1V}"
    IO.println s!"  expected: sender={exp_sender} recip=10 seqV={exp_seq} baseV={exp_base} l1V={exp_l1}"
    IO.println s!"  match: {sBal == exp_sender && rBal == 10 && seqV == exp_seq && baseV == exp_base && l1V == exp_l1}"
  | .error e =>
    IO.println s!"\nOP block FAILED: {e}"

  -- Smoke test: P-256 verifier (RFC 6979 deterministic test vector).
  -- Message: SHA-256("sample"); known-valid signature under the
  -- supplied public key.
  let msgHash : Evm.U256 :=
    Evm.U256.ofNat 0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF
  let qx : Evm.U256 :=
    Evm.U256.ofNat 0x60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6
  let qy : Evm.U256 :=
    Evm.U256.ofNat 0x7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299
  let r  : Evm.U256 :=
    Evm.U256.ofNat 0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716
  let s  : Evm.U256 :=
    Evm.U256.ofNat 0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8
  let ok := Evm.Crypto.isValidP256Signature msgHash r s qx qy
  IO.println s!"\nP-256 verify (RFC 6979 'sample' vector): {ok}"
  IO.println s!"  expected: true"
  -- Tamper with s; should fail.
  let sBad : Evm.U256 := s + 1
  let bad := Evm.Crypto.isValidP256Signature msgHash r sBad qx qy
  IO.println s!"P-256 verify (tampered s):                  {bad}"
  IO.println s!"  expected: false"
