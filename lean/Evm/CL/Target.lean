/-
  Evm.CL.Target — the register allocation, as roles rather than register names.

  Stage 0 of the x86-64 backend (#238). Today's emitters name ARM64 registers
  directly (`AsmCore.Reg` is `x6 | x7 | … | x24`, `AInstr` is an ARM64
  instruction subset), so there is nothing a second target could instantiate.
  The first thing that has to become target-parametric is not the instruction
  encoding — it is the ROLE ASSIGNMENT, because that is what decides whether a
  target can afford the register caches the handlers assume.

  The question this module settles: ARM64 pins 20 registers (TOS 4, NOS 4,
  scratch 4, and 8 singletons), and x86-64 has 16 GPRs of which one is the
  hardware stack pointer. So something has to go.

  ## Two registers found, so only NOS has to go

  * `cont` — ARM64 threads through `br x27`, an explicit continuation register,
    because `adr`+`br` is how you get a computed return on that ISA. x86-64 has
    `call`/`ret` and a return-stack-buffer predictor, so subroutine threading
    uses the hardware stack and needs NO register at all. (It is also likely
    FASTER than the indirect branch: `ret` is predicted, an indirect `br` to a
    varying target often is not.)
  * `dispatch` — ARM64 keeps the 256-entry table base in x25 since it cannot
    address it otherwise. x86-64 can: `jmp *table(,%rax,8)` reaches the table
    RIP-relatively, with no base register live.

  That frees 2 of the 8 singletons, which is exactly enough for TOS to stay
  cached with a comfortable 5 scratch registers. Keeping NOS as well would
  leave ONE scratch register, and x86-64's two-operand destructive forms (`add
  dst, src` writes dst) need more scratch than ARM64's three-operand forms, not
  less. Hence: `x86_64` pins TOS and drops NOS — reading the second stack item
  from memory at `[stackBase + 32·(sp-2)]`.

  ## What dropping NOS costs, and the bug it retires

  The ARM64 handlers may read NOS registers only under the invariant "if sp ≥ 2
  then stack memory at sp-2 equals x10-x13". A target without the NOS cache has
  nothing to keep in step, so a whole class of divergence cannot arise there —
  including #272, where the interpreter's speculative `stack[depth-2]`
  register-cache read went one slot BELOW the live stack and faulted the guard
  arena. Note the direction: the register cache is an optimisation that must be
  PROVED equivalent to the memory read, so the memory form is the specification
  and the cache is the refinement. Writing the roles down this way makes the
  x86-64 backend the simpler instantiation, not a second special case.
-/

namespace Evm.CL.Target

/-- A register's JOB in the threaded interpreter and the JIT, independent of any
    ISA. `tos`/`nos` are the 4-limb u256 caches of the top two stack items. -/
inductive RegRole where
  | tos     (i : Fin 4)     -- TOS limb i (0 = least significant)
  | nos     (i : Fin 4)     -- NOS limb i
  | scratch (i : Fin 5)     -- clobberable within one handler
  | state                   -- EvmState *
  | pc                      -- cached program counter
  | gas                     -- cached gas_left
  | sp                      -- cached EVM stack depth
  | stackBase               -- u256_t[1024]
  | dispatch                -- 256 × function pointer
  | codeBase                -- the frame's bytecode
  | cont                    -- continuation (next / sync_and_ret)
  deriving DecidableEq, Repr

/-- A code generation target: which concrete register plays each role, and which
    registers the ISA/ABI keeps for itself. A role mapped to `none` is one this
    target does NOT pin — it must reach that datum another way, and the comment
    at the top of this file says how for each. -/
structure Target where
  name     : String
  reg      : RegRole → Option String
  /-- Registers that exist but may not be allocated (hardware stack pointer). -/
  reserved : List String
  /-- Every general-purpose register the ISA has, including `reserved`. -/
  allGpr   : List String
  deriving Inhabited

namespace Target

/-- Every role, for the injectivity and budget checks below. -/
def allRoles : List RegRole :=
  (List.finRange 4).map RegRole.tos ++
  (List.finRange 4).map RegRole.nos ++
  (List.finRange 5).map RegRole.scratch ++
  [.state, .pc, .gas, .sp, .stackBase, .dispatch, .codeBase, .cont]

/-- The concrete registers this target pins, in role order. -/
def pinned (t : Target) : List String := allRoles.filterMap t.reg

/-- Registers left over: neither pinned nor reserved. On a target that pins its
    scratch registers explicitly this should be empty; it is the slack. -/
def unused (t : Target) : List String :=
  t.allGpr.filter (fun r => !(t.pinned.contains r) && !(t.reserved.contains r))

/-- Does this target pin a role? -/
def pins (t : Target) (r : RegRole) : Bool := (t.reg r).isSome

/-- How many scratch registers the target actually has. -/
def scratchCount (t : Target) : Nat :=
  ((List.finRange 5).filterMap (fun i => t.reg (.scratch i))).length

/-- Registers committed to a NAMED job — everything but the scratch pool. This
    is the number that competes with the ISA's register count. -/
def pinnedNonScratch (t : Target) : Nat := t.pinned.length - t.scratchCount

end Target

/-! ## ARM64 — today's assignment (see the header of `Evm.CL.ARM64`) -/

def arm64 : Target where
  name := "arm64"
  reserved := ["sp"]                                  -- x31/sp; x18 is platform-reserved on Darwin
  allGpr := (List.range 29).map (fun i => s!"x{i}") ++ ["sp"]
  reg := fun
    | .tos i => some s!"x{6 + i.val}"                 -- x6-x9
    | .nos i => some s!"x{10 + i.val}"                -- x10-x13
    | .scratch i => if i.val < 4 then some s!"x{14 + i.val}" else none  -- x14-x17
    | .state => some "x20" | .pc => some "x21" | .gas => some "x22"
    | .sp => some "x23" | .stackBase => some "x24" | .dispatch => some "x25"
    | .codeBase => some "x26" | .cont => some "x27"

/-! ## x86-64 — the proposed assignment -/

/-- x86-64 integer registers. `rsp` is the hardware stack pointer, and the
    subroutine-threading scheme WANTS it (that is what retires `cont`). -/
def x86Gpr : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
   "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

/-- TOS cached, NOS NOT (see the header). `dispatch` is reached RIP-relatively
    and `cont` through `call`/`ret`, so neither takes a register.

    Baseline is x86-64-v3 (Haswell and later): BMI2 gives `shlx/shrx/sarx`, so a
    variable shift does not have to route its count through `cl`, and `mulx`
    takes its operands without the implicit `rdx`. Without v3 the scratch set
    would have to reserve `rcx` and `rdx` for those two instruction families. -/
def x86_64 : Target where
  name := "x86-64"
  reserved := ["rsp"]
  allGpr := x86Gpr
  reg := fun
    | .tos i => some (["r8", "r9", "r10", "r11"].getD i.val "")
    | .nos _ => none                                   -- read from [stackBase + 32*(sp-2)]
    | .scratch i => some (["rax", "rcx", "rdx", "rsi", "rdi"].getD i.val "")
    | .state => some "rbx" | .pc => some "rbp" | .gas => some "r15"
    | .sp => some "r13" | .stackBase => some "r12" | .codeBase => some "r14"
    | .dispatch => none                                -- jmp *table(,%rax,8), RIP-relative
    | .cont => none                                    -- call / ret

/-- The same assignment but insisting on the NOS cache, to show why it does not
    fit. It must steal four of the five scratch registers. -/
def x86_64_withNos : Target :=
  { x86_64 with
    name := "x86-64 (+NOS)"
    reg := fun
      | .nos i => some (["rax", "rcx", "rdx", "rsi"].getD i.val "")
      | .scratch i => if i.val = 0 then some "rdi" else none
      | r => x86_64.reg r }

/-! ## The budget, machine-checked

These are the claims the design rests on, as `decide` rather than as the
comment above. A future edit that double-books a register fails here. -/

/-- No register plays two roles, on either target. -/
example : arm64.pinned.Nodup := by native_decide
example : x86_64.pinned.Nodup := by native_decide

/-- Neither target allocates a reserved register. -/
example : arm64.reserved.all (fun r => !arm64.pinned.contains r) := by native_decide
example : x86_64.reserved.all (fun r => !x86_64.pinned.contains r) := by native_decide

/-- ARM64 pins 20 registers: 4 TOS, 4 NOS, 4 scratch, 8 singletons. -/
example : arm64.pinned.length = 20 := by native_decide
example : arm64.scratchCount = 4 := by native_decide

/-- ARM64 commits 16 registers to named jobs (4 TOS, 4 NOS, 8 singletons). -/
example : arm64.pinnedNonScratch = 16 := by native_decide

/-- x86-64 commits 10 and keeps 5 scratch: 15 allocated + `rsp` is exactly the
    16 registers the ISA has, with nothing left over. -/
example : x86_64.pinnedNonScratch = 10 := by native_decide
example : x86_64.pinned.length = 15 := by native_decide
example : x86_64.scratchCount = 5 := by native_decide
example : x86_64.unused = [] := by native_decide
example : x86_64.pinned.length + x86_64.reserved.length = x86Gpr.length := by native_decide

/-- The two roles x86-64 does not need a register for. -/
example : x86_64.pins .dispatch = false := by native_decide
example : x86_64.pins .cont = false := by native_decide
example : arm64.pins .dispatch = true := by native_decide
example : arm64.pins .cont = true := by native_decide

/-- And the reason NOS is dropped: keeping it leaves ONE scratch register, on
    the ISA whose two-operand forms need scratch MORE than ARM64's do. -/
example : x86_64_withNos.scratchCount = 1 := by native_decide
example : x86_64.pins (.nos 0) = false := by native_decide
example : arm64.pins (.nos 0) = true := by native_decide

/-- Minimum scratch a handler body needs: the 4-limb chains keep a carry temp, a
    loaded operand and an address temp live at once (`memExpandEmit` already
    uses three — x14, x15, x16 — and its docstring warns that aliasing the
    accumulator with any of them doubles the result). -/
def minScratch : Nat := 3

example : minScratch ≤ x86_64.scratchCount := by native_decide
example : ¬ (minScratch ≤ x86_64_withNos.scratchCount) := by native_decide

end Evm.CL.Target
