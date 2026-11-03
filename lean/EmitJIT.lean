/-
  EmitJIT — emit a per-chunk JIT .S for one program's bytecode.

  Usage: `lake exe emitJIT <hex-bytecode> [fork-ord]` (hex with or
  without 0x prefix; fork-ord is `Evm.Fork.ord`, default 16 = Cancun);
  prints the assembly to stdout. Link the result against the handlers
  dylib that `emitARM64` produced.
-/

import Evm.CL.ARM64.JIT
import Evm.CL.X86JIT

/-! ## Unix-domain-socket emit server (#235)

A persistent `emitJIT serve <sock>` daemon: the replay connects once and streams
`(fork, code)` requests, getting back the serialized loader blob — no per-contract
process spawn. Wire framing (little-endian u32):
  request  = forkOrd | codeLen | code
  response = status  | blobLen | blob     (status 0 = blob, 1 = error message) -/

@[extern "lean_uds_listen"] private opaque udsListen : @& String → IO UInt32
@[extern "lean_uds_accept"] private opaque udsAccept : UInt32 → IO UInt32
@[extern "lean_fd_read"]    private opaque udsRead  : UInt32 → UInt32 → IO ByteArray
@[extern "lean_fd_write"]   private opaque udsWrite : UInt32 → @& ByteArray → IO UInt32
@[extern "lean_fd_close"]   private opaque udsClose : UInt32 → IO Unit

private def rdU32 (b : ByteArray) (o : Nat) : UInt32 :=
  (b.get! o).toUInt32 ||| ((b.get! (o+1)).toUInt32 <<< 8) |||
  ((b.get! (o+2)).toUInt32 <<< 16) ||| ((b.get! (o+3)).toUInt32 <<< 24)

private def pushU32 (b : ByteArray) (v : UInt32) : ByteArray :=
  let b := b.push (v &&& 0xff).toUInt8
  let b := b.push ((v >>> 8) &&& 0xff).toUInt8
  let b := b.push ((v >>> 16) &&& 0xff).toUInt8
  b.push ((v >>> 24) &&& 0xff).toUInt8

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private partial def hexBytesLoop : List Char → ByteArray → Option ByteArray
  | [],             acc => some acc
  | [_],            _   => none
  | h :: l :: rest, acc =>
    match hexDigit? h, hexDigit? l with
    | some hi, some lo => hexBytesLoop rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
    | _, _ => none

private def hexToBytes (s : String) : Option ByteArray :=
  let s := if s.startsWith "0x" ∨ s.startsWith "0X"
           then String.ofList (s.toList.drop 2) else s
  let s := if s.length % 2 = 1 then "0" ++ s else s
  hexBytesLoop s.toList ByteArray.empty

/-- `Fork.ord` → `Fork`, the inverse the replay host dispatches with.
    Out-of-range ords are a hard error — no silent Cancun fallback. -/
private def forkOfOrd? (n : Nat) : Option Evm.Fork :=
  [Evm.Fork.frontier, .homestead, .daoFork, .tangerineWhistle,
   .spuriousDragon, .byzantium, .constantinople, .petersburg,
   .istanbul, .muirGlacier, .berlin, .london, .arrowGlacier,
   .grayGlacier, .paris, .shanghai, .cancun, .prague, .osaka,
   .bpo1, .bpo2, .amsterdam].find? (fun f => f.ord == n)

/-- Build a response frame: status word, length, body. -/
private def respFrame (status : UInt32) (body : ByteArray) : ByteArray :=
  (pushU32 (pushU32 ByteArray.empty status) (UInt32.ofNat body.size)) ++ body

/-- The image for the host (or `EITA_JIT_ARCH=x86|arm64`). -/
private def x86Host : IO Bool := do
  match (← IO.getEnv "EITA_JIT_ARCH") with
  | some "x86" | some "x86_64" | some "x86-64" => return true
  | some "arm64" | some "aarch64"              => return false
  | _ => return (System.Platform.target.splitOn "x86_64").length > 1

/-- The JIT tier's size budget, in chunk ops summed over the program. Chunks
    overlap — each runs through interior JUMPDESTs to its terminator
    (`IR.Compile`) — so a contract of N JUMPDESTs with no terminator between
    them compiles to N chunks of O(N) ops: stQuadraticComplexityTest's
    Call20KbytesContract50 is 21 126 chunks, 223 M ops, minutes per fork in
    the daemon. Over budget is a loud refusal: the replay counts it (`no-jit`)
    and runs the frame on the interpreter tier. -/
private def maxProgramOps : Nat := 4_000_000

/-- `compileProgram`, refused over the budget BEFORE its chunk table exists: the chunks
    (`compileChunkAt` at `compileProgram`'s entries) are first compiled one at a time, only
    their op counts kept, and the count gives up as soon as it passes `maxProgramOps`. The
    table is quadratic in a run of JUMPDESTs: stStaticCall's static_Call50000bytesContract50_3
    (60 001 chunks, 1.8e9 ops) had the daemon at ~30 GB before a check on the finished table
    could refuse it. An in-budget program is compiled twice (the count, then the table). -/
private def compileWithin (f : Evm.Fork) (code : ByteArray) : Except String Evm.IR.Program := Id.run do
  let mut ops := 0
  for e in 0 :: Evm.IR.chunkEntries code 0 do
    if let .ok ch := Evm.IR.compileChunkAt f code e then ops := ops + ch.ops.length
    if ops > maxProgramOps then
      return .error s!"image: over the JIT tier's budget: more than {maxProgramOps} chunk ops (counted up to the chunk at pc {e})"
  match Evm.IR.compileProgram f code with
  | .ok p    => .ok p
  | .error e => .error s!"compile error: {repr e}"

private def imageFor (x86 : Bool) (f : Evm.Fork) (p : Evm.IR.Program) : Except String ByteArray :=
  if x86 then Evm.CL.X86JIT.emitProgramImageX86 f p
  else .ok (Evm.CL.ARM64.JIT.emitProgramImage f p)

/-- Emit the blob (or an error message) for one `(fork, code)` request. -/
private def emitResponse (x86 : Bool) (forkOrd : UInt32) (code : ByteArray) : ByteArray :=
  match forkOfOrd? forkOrd.toNat with
  | none => respFrame 1 (s!"bad fork ord {forkOrd}").toUTF8
  | some f =>
    match compileWithin f code with
    | .error e => respFrame 1 e.toUTF8
    | .ok p    =>
      match imageFor x86 f p with
      | .ok b    => respFrame 0 b
      | .error e => respFrame 1 (s!"image: {e}").toUTF8

/-- Serve one accepted connection: read framed requests until the peer closes. -/
private partial def serveConn (x86 : Bool) (cfd : UInt32) : IO Unit := do
  let hdr ← udsRead cfd 8
  if hdr.size < 8 then return ()        -- peer closed
  let forkOrd := rdU32 hdr 0
  let codeLen := rdU32 hdr 4
  let code ← udsRead cfd codeLen
  if code.size < codeLen.toNat then return ()
  let _ ← udsWrite cfd (emitResponse x86 forkOrd code)
  serveConn x86 cfd

private partial def serveLoop (x86 : Bool) (lfd : UInt32) : IO Unit := do
  let cfd ← udsAccept lfd
  if cfd == (0xffffffff : UInt32) then return ()
  serveConn x86 cfd
  udsClose cfd
  serveLoop x86 lfd

def main (args : List String) : IO Unit := do
  -- Modes:
  --   emitJIT <hex> [ord]            → per-chunk .S text to stdout (clang path)
  --   emitJIT bin <hex> <ord> <out>  → serialized in-process loader blob to <out>
  --   emitJIT serve <sock>           → persistent UDS emit server (#235)
  let x86 ← x86Host
  match args with
  | ["serve", sock] =>
    let lfd ← udsListen sock
    if lfd == (0xffffffff : UInt32) then throw (IO.userError s!"uds listen failed: {sock}")
    serveLoop x86 lfd
    return
  | _ => pure ()
  -- `emitJIT chunks <hex> [ord]`: compile only, print the chunk count (profiling)
  let (chunksOnly, args) := match args with
    | "chunks" :: rest => (true, rest)
    | _ => (false, args)
  let (binOut, hex, ordStr) ← match args with
    | [hex]                  => pure (none, hex, "16")
    | [hex, ord]             => pure (none, hex, ord)
    | ["bin", hex, ord, out] => pure (some out, hex, ord)
    | _ => throw (IO.userError
            "usage: emitJIT <hex> [ord] | emitJIT bin <hex> <ord> <out>")
  let some code := hexToBytes hex
    | throw (IO.userError s!"invalid hex bytecode: {hex}")
  let some f := ordStr.toNat? >>= forkOfOrd?
    | throw (IO.userError s!"invalid fork ord: {ordStr}")
  -- Compiling at the replay fork decides opcode admission (PUSH0,
  -- SHL/SHR, REVERT, ...) and routes op/terminator sites to the
  -- fork's handler variants; static chunk gas is fork-invariant.
  match Evm.IR.compileProgram f code with
  | .error e => throw (IO.userError s!"compile error: {repr e}")
  | .ok p =>
    if chunksOnly then
      let lens := p.chunks.map (fun (_, c) => c.ops.length)
      IO.println s!"chunks: {p.chunks.length} (dedup {(Evm.CL.ARM64.JIT.dedupByPc p.chunks).length}) ops total {lens.sum} max {lens.foldl max 0}"
      return
    match binOut with
    | none     => IO.println (Evm.CL.ARM64.JIT.emitProgram f p)
    | some out =>
      match compileWithin f code >>= fun p => (imageFor x86 f p).mapError (s!"image: {·}") with
      | .ok b    => IO.FS.writeBinFile out b
      | .error e => throw (IO.userError e)
