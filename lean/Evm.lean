/-
  Evm — Lean specification of the Ethereum Virtual Machine.

  Tracks ethereum/execution-specs (EELS). Goal: a faithful Lean port that
  can replay every Ethereum mainnet block from Frontier (block 0) through
  Prague.

  Top-level module re-exports the public surface.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash
import Evm.Trie
import Evm.Forks

-- Per-fork modules. Each fork is a self-contained namespace mirroring the
-- corresponding EELS package; pre-Prague forks currently expose only a
-- header file pending build-out.
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.DaoFork.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Constantinople.Fork
import Evm.Petersburg.Fork
import Evm.Istanbul.Fork
import Evm.MuirGlacier.Fork
import Evm.Berlin.Fork
import Evm.London.Fork
import Evm.ArrowGlacier.Fork
import Evm.GrayGlacier.Fork
import Evm.Paris.Fork
import Evm.Shanghai.Fork
import Evm.Cancun.Fork
import Evm.Prague.Fork
import Evm.Osaka.Fork
import Evm.CL.ARM64.ChunkGas
import Evm.CL.ARM64.CallGasDenote
import Evm.CL.ARM64.PredFold
import Evm.CL.ARM64.RunProgramDenote
import Evm.CL.ARM64.SstoreGasDenote
import Evm.CL.AsmSem
import Evm.CL.ARM64.CallGasSem
import Evm.CL.ARM64.SstoreGasSem
import Evm.CL.X86CallGas
import Evm.CL.X86CallGasSem
import Evm.CL.EffectSelfdestructProof  -- the derived cb-selfdestruct = every fork's SELFDESTRUCT
import Evm.CL.EffectSettleProof        -- the derived fee settlement = every fork's settleFees
import Evm.CL.EffectEndTxProof         -- the derived end-of-tx deletions = every fork's finishTx
import Evm.CL.EffectSstoreProof        -- the derived cb-sstore = every fork's SSTORE
import Evm.CL.EffectSloadProof         -- the derived cb-sload = every fork's SLOAD
import Evm.CL.EffectCreateProof        -- the derived cb-create = every fork's CREATE/CREATE2
import Evm.CL.EffectCallProof          -- the derived cb-call = every fork's CALL family
import Evm.CL.EffectTxProof            -- the derived apply-tx = every fork's processTransaction (Evm.Frontier.Vm.Tx)
import Evm.CL.EffectSystemProof        -- the derived system call = every fork's system transaction (Evm.Frontier.Vm.System)
import Evm.CL.EffectBlockProof         -- the derived block credits = every fork's rewards + withdrawals (Evm.Frontier.Vm.Block)
import Evm.CL.X86SstoreGas
import Evm.CL.X86SstoreGasSem
import Evm.CL.X86Interp
import Evm.CL.X86Alias
import Evm.CL.ChunkMemExpand
import Evm.CL.DispatchTable
import Evm.CL.JumpDest
import Evm.CL.BlobEnv
import Evm.CL.GasEmitCancun
import Evm.CL.GasEmitLondon
import Evm.CL.StackOps
import Evm.CL.PushWide
import Evm.CL.Target
import Evm.Arc.Spec.NativeCoin
import Evm.Arc.Spec.Pq
import Evm.Arc.Spec.BlockSystem
import Evm.Trie.CheckpointSchedule
import Evm.Trie.Stack
import Evm.Amsterdam.Fork
import Evm.Frontier.Vm.Effect

-- Spec layer (property-flavored relations, refinement obligations).
import Evm.Frontier.Spec.Step
import Evm.Frontier.Spec.Invariants
import Evm.Frontier.Spec.Refinement
import Evm.Frontier.Spec.CallStep
import Evm.Frontier.Spec.MemStep
import Evm.Frontier.Spec.StorageStep
import Evm.Frontier.Spec.FrameRun
import Evm.Frontier.Spec.SelfdestructStep
import Evm.Frontier.Spec.SelfdestructRefinement
import Evm.Frontier.Spec.HeaderValidity
import Evm.Constantinople.Spec.BitwiseStep
import Evm.Shanghai.Spec.Push0Step
import Evm.Shanghai.Spec.InitcodeCap
import Evm.Shanghai.Spec.WarmCoinbase
import Evm.Cancun.Spec.TransientStorageStep
import Evm.Cancun.Spec.McopyStep
import Evm.Cancun.Spec.BlobhashStep
import Evm.Cancun.Spec.BlobbasefeeStep
import Evm.Cancun.Spec.BlobTx
import Evm.Cancun.Spec.KzgStep
import Evm.Cancun.Spec.Selfdestruct
import Evm.Cancun.Spec.PrecompileWarm
import Evm.Optimism.Forks
import Evm.Optimism.Bedrock.Spec.DepositedTx
import Evm.Optimism.Bedrock.Spec.L1Block
import Evm.Optimism.Bedrock.Spec.FeeVaults
import Evm.Optimism.Bedrock.Spec.L1DataFee
import Evm.Optimism.Canyon.Spec.ShanghaiInheritance
import Evm.Optimism.Ecotone.Spec.L1DataFeeEcotone
import Evm.Optimism.Fjord.Spec.L1DataFeeFjord
import Evm.Optimism.Fjord.Spec.P256Verify
import Evm.Optimism.Granite.Spec.Bn256PairingCap
import Evm.Optimism.Holocene.Spec.Eip1559Params
import Evm.Optimism.Isthmus.Spec.PragueInheritance
import Evm.Optimism.Bedrock.Transactions
import Evm.Optimism.Bedrock.Fork
import Evm.Optimism.Replay.L1Fee
import Evm.Optimism.Replay.FeeRouting
import Evm.Optimism.Canyon.Fork
import Evm.Optimism.Ecotone.Fork
import Evm.Optimism.Fjord.Fork
import Evm.Optimism.Fjord.P256VerifyImpl
import Evm.Optimism.Granite.Fork
import Evm.Optimism.Isthmus.Fork
import Evm.Optimism.Replay.Dispatch
import Evm.Optimism.Isthmus.Spec.Soundness
import Evm.Optimism.Fjord.Spec.Soundness
import Evm.Optimism.Granite.Spec.Soundness
import Evm.Optimism.Holocene.Spec.Soundness
import Evm.Prague.Spec.Bls12381Step
import Evm.Prague.Spec.CalldataCost
import Evm.Prague.Spec.BlobSchedule
import Evm.Prague.Spec.Requests
import Evm.Prague.Spec.SetCodeStep
import Evm.Osaka.Spec.ClzStep
import Evm.Osaka.Spec.P256VerifyStep
import Evm.Osaka.Spec.GasCap
import Evm.Osaka.Spec.ModexpGas
import Evm.Osaka.Spec.BlobSchedule
import Evm.Amsterdam.Spec.SlotNumberStep
import Evm.Amsterdam.Spec.StackAccessStep
import Evm.Amsterdam.Spec.CodeSizeCap
import Evm.Amsterdam.Spec.BlockAccessList
import Evm.Amsterdam.Spec.IntrinsicGasFloor

-- IR pipeline (bytecode → IR.Op chunks; under refactor per
-- toward shared interp/JIT infra).
import Evm.IR.Types
import Evm.IR.Compile
import Evm.IR.Emit
import Evm.IR.Execute
import Evm.IR.Soundness
import Evm.IR.Trampoline
import Evm.IR.Dispatch

-- CL backend (Form IR + ARM64 emission for the threaded interpreter
-- handlers compiled into c/libeita.dylib via `lake exe emitARM64`).
import Evm.CL.Journal
import Evm.CL.StorageCache
import Evm.CL.MacroSpec
import Evm.CL.Extract

-- Block-STM spec (#255): never imported before, so `lake build Evm` never compiled it.
import Evm.Parallel.BlockSTM
import Evm.Parallel.Reads
import Evm.Parallel.Scheduler
