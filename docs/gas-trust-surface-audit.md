# Gas/semantics trust-surface audit (src/evm/)

> **Status: historical** (written 2026-06). Accurate as of then; the current system is described in `docs/replay-architecture.md` and the code.

Triggered by #260 (Byzantium precompile-gas divergence at block 4,466,928): the CL
executable hand-wrote a fork-blind precompile gas table that silently diverged from
the verified Lean spec. This audit enumerates every other site where `src/evm/`
computes a consensus gas/refund/reward with a HAND-WRITTEN literal instead of DERIVING
it from the Lean spec (via an emitted native or `EmitHostCL`). Each hand-written site
is a latent #260 — it currently matches the spec but is a parallel copy that can drift.

Spec source of truth: `lean/Evm/<Fork>/...`. Emit pipeline: `lean/EmitHostCL.lean`
(`lake exe emitHostCL > src/generated/host.lisp`), the #230 model.

## Correctly DERIVED (spec-emitted — already safe)
- **CALL-family gas** — `%call-gas{,-tangerine,-frontier}` ← `CL/ARM64/CallGas.lean` ←
  `Berlin.Vm.Effect.callGasPlan`. base / 63-64 cap / stipend 2300 / value 9000.
  Differentially audited by `tests/audit-call-gas.lisp`.
- **CALL new-account 25000 flag** — the derived `spec-call-effect` ←
  `Evm.CL.EffectCall.term` (proved against `Evm.Frontier.Vm.Call` in EffectCallProof).
- **SSTORE gas + refund** — `%sstore-gas-{legacy,eip1283,eip2200,berlin,london}` ←
  `CL/ARM64/SstoreGas.lean` (#230).
- **Account-access cost table** — `eita_access_costs[ord][kind]{cold,warm}` ←
  `SstoreGas.lean:360` → `c/handlers.S`. Drives SLOAD/BALANCE/EXTCODE*.
- **Opcode gas inside frames** (memexp, copy-word, arithmetic) — native ARM64 handlers/JIT.

## HAND-WRITTEN trust surface — ranked #260-class risk
1. **`intrinsic-gas` (3216-3235) — HIGHEST.** Every tx. base 21000 / txCreate 32000 /
   calldata 4·zero, 68→16 nonzero @Istanbul / EIP-3860 2·word @Shanghai / AL 2400+1900.
   Fork-gated but duplicates `Berlin/Fork.lean:101`, `Homestead/Fork.lean:37`,
   `Frontier/Vm/Gas.lean:62`. Boundary risk: Istanbul, Shanghai.
2. **`run-precompile` (1683-1706)** — the #260 file. bn254 now fork-gated (interim);
   ECRECOVER 3000 / SHA256 / RIPEMD / IDENTITY / BLAKE2F still bare literals (fork-constant,
   lower risk). Spec: `*/Vm/PrecompiledContracts/Bn256.lean`.
3. **`modexp-gas` (1651-1681)** — #260 site, now fork-gated (interim). Intricate formula
   reimplemented in CL while a full spec sits unused at `{Byzantium,Berlin}/Vm/PrecompiledContracts/Modexp.lean`.
4. **`cb-selfdestruct` (2540-2541)** — new-account **25000 bare literal** + cold 2600,
   while `cb-call` DERIVES the same new-account quantity (site B). ASYMMETRY → drift trap.
5. **`cb-create` base (2259-2261) + code-deposit 200/byte (2421, 3078)** — code-deposit
   hand-written in TWO places (must stay equal). Spec `Berlin/Vm/Effect.lean:651`,
   `Frontier/Vm/Gas.lean:59`. Boundary: Shanghai (3860).
6. **block/uncle reward (3397-3408)** — 5/3/2 ETH + uncle formulas, every pre-Merge block.
   Spec `Byzantium/Fork.lean:37-47`. Boundary: Byzantium (EIP-649), Constantinople (EIP-1234).
7. **refund cap (3379-3382) + SELFDESTRUCT refund 24000 (2508)** — EIP-3529 /2→/5. Boundary: London.
8. **EIP-150 63/64 in CREATE (2309-2313, 2347-2351)** — hand-coded `x - x/64`, duplicated;
   CALL derives this, CREATE does not. ASYMMETRY. Boundary: TangerineWhistle.

## Migration order (→ #261)
intrinsic-gas → modexp (spec exists) → precompile table → unify selfdestruct/CREATE 63-64
onto cb-call's derived helpers (kill asymmetry) → dedupe code-deposit → block reward.
Each migration ships with a refinement vector (emitted == spec), like `SstoreGasVectors`.

All values currently MATCH spec; the risk is structural (parallel literals), exactly the
mechanism that produced #260.
