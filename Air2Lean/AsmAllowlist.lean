/-! # Reviewed inline-asm allowlist (L13, A01, C03)

The single reviewed list of inline assembly the translator accepts outside a device contract
(`docs/volatile-effects.md` §Inline asm). Data only: `Check.lean` reads it, nothing else does.

An M21 `opaque` asm op is a function of its inputs: two executions with equal inputs are equal
in Lean. That is sound only for an instruction whose outputs are determined by its register
inputs, whether or not the asm is `volatile` (a non-volatile asm is not a promise of
determinism: LLVM *may* merge two of them, but need not, so a native run can still observe two
different `rdtsc` values). Every asm the checker accepts therefore matches one entry exactly:
the template, the ordered constraint list (outputs, then inputs), the clobbers and the target
architecture. A legacy profile without a target (`legacy-abi64-le`) is the x86_64 reference
model (premise PRF-01). Any other asm is `ASM_VOLATILE_EFFECT`, unless the device contract
declares it as a device event (`Zig.vasm`).

Every entry also states when the instruction faults (`AsmFault`, S7). An opaque is a total
function, so without that condition the model of a trapping instruction would return a value:
`Emit.lean` guards the call with `Zig.asmTrap`, which throws `Zig.Error.trap` exactly on the
entry's fault condition. `never` is a reviewed claim, not a default.

To add an entry: show that the instruction's outputs depend only on its inputs on the target
(no flags, memory, counters, entropy, privileged or I/O state is read), that it writes nothing
outside its outputs and clobbers, state every input on which it faults (#DE, #UD, ...), and name
the committed fixture that needs it. -/
namespace Air2Lean

inductive AsmSemantics where
  /-- An M21 `opaque` function of the inputs (`Emit.lean`'s `emitAsmDef`). -/
  | opaque
  /-- `Zig.spinLoopHintC`: a scheduling point, no memory effect (C03, `Op.isSpinHint`). -/
  | spinHint
  /-- An environment read (`rdtsc`, `rdrand`; A01, premise ASM-05): each output is a fresh query
  of the explicit oracle (`Zig.Asm.envWord`), never a repeatable value. No input, no memory
  effect. -/
  | envRead
  deriving BEq, Repr

/-- A region's byte length: integer operand `k` (AIR order: outputs, then inputs; for a
read-write output, its old value) times `scale`. -/
structure AsmLen where
  operand : Nat
  scale : Nat := 1
  deriving BEq, Repr

inductive AsmAccess where
  | read | write
  deriving BEq, Repr

/-- A memory region that the instructions access through a pointer operand (A01, premise
ASM-06): the pointer operand `base` (AIR order; for a read-write output, its old value), the
length, and whether the bytes are read or written. -/
structure AsmRegion where
  base : Nat
  len : AsmLen
  access : AsmAccess
  deriving BEq, Repr

/-- When an allowlisted instruction faults (a CPU exception, delivered as a signal), as a
condition on its inputs (AIR order). The model throws `Zig.Error.trap` exactly when it holds. -/
inductive AsmFault where
  /-- The instruction faults on no input (reviewed for each entry, see `reason`). -/
  | never
  /-- The instruction faults (#DE) exactly when input `k` is zero. -/
  | zeroInput (k : Nat)
  deriving BEq, Repr

/-- The Lean `Prop` under which the instruction faults, over its rendered input operands `args`;
`none` for an instruction that never faults, or for an input index that does not exist. -/
def AsmFault.condition? (fault : AsmFault) (args : List String) : Option String :=
  match fault with
  | .never => none
  | .zeroInput k => args[k]?.map fun a => s!"{a} = 0"

structure AsmAllowEntry where
  template : String
  /-- Outputs, then inputs, in AIR order. -/
  constraints : List String
  clobbers : List String
  /-- The `target_triple` architecture (`x86_64`, `aarch64`). -/
  target : String
  semantics : AsmSemantics
  /-- When the instruction faults (`.never` for a spin hint: it has no inputs). -/
  fault : AsmFault
  /-- The memory regions that the instructions access through pointer operands (ASM-06). An
  entry with a region declares every memory access of the block: only such an entry may have a
  pointer operand or a `"memory"` clobber (besides `asmPureRegistry`'s barrier). -/
  regions : List AsmRegion := []
  reason : String
  reviewerNote : String
  deriving Repr

def asmAllowlist : List AsmAllowEntry := [
  { template := "bswap %[ret]", constraints := ["=r", "0"], clobbers := [], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "byte swap of one register: the output is a function of the input; bswap faults \
      on no input",
    reviewerNote := "examples/asm bswap32 (tests/golden/asm/air/asm.bswap32.json); non-volatile" },
  { template := "xorl %%edx, %%edx\n\tdivl %[b]", constraints := ["={eax}", "=&{edx}", "{eax}", "r"],
    clobbers := [], target := "x86_64", semantics := .opaque, fault := .zeroInput 1,
    reason := "unsigned 32-bit divide: quotient and remainder are functions of the inputs. \
      divl raises #DE (SIGFPE) for a zero divisor and for a quotient above 2^32 - 1; the xorl \
      makes the dividend edx:eax = eax < 2^32, so the quotient always fits and the divisor \
      (input 1) being zero is the only fault",
    reviewerNote := "examples/asm divmod (tests/golden/asm/air/asm.divmod.json); non-volatile" },
  { template := "lzcnt %[x], %[ret]", constraints := ["=r", "r"], clobbers := ["cc"],
    target := "x86_64", semantics := .opaque, fault := .never,
    reason := "leading-zero count: a function of the input; it only clobbers flags and faults \
      on no input (a zero input gives the operand size). On a CPU without LZCNT the encoding \
      runs as bsr: a target-CPU premise (ASM-04), not an input condition",
    reviewerNote := "examples/asm lzcnt64 (tests/golden/asm/air/asm.lzcnt64.json); volatile in \
      the source, but input-determined" },
  { template := "popcnt %[x], %[ret]", constraints := ["=r", "r"], clobbers := [],
    target := "x86_64", semantics := .opaque, fault := .never,
    reason := "population count: a function of the input; it faults on no input on a CPU \
      with POPCNT (on one without it every execution is #UD: a target-CPU premise, ASM-04)",
    reviewerNote := "examples/asm popcnt64 (tests/golden/asm/air/asm.popcnt64.json); non-volatile" },
  -- A01's effect-contract forms (`Air2Lean/AsmContract.lean`, premise ASM-03): the new value of
  -- each read-write or memory output is a function of the register inputs and the old values.
  -- None faults on an input: the generated wrapper reads and writes each memory operand through
  -- the model's checked accesses before and after the opaque, and the arithmetic cannot trap.
  { template := "incl %[x]", constraints := ["+m"], clobbers := ["cc"], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "increment of a memory operand: the new value is a function of the old one; it \
      only clobbers flags",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.incm.json; volatile" },
  { template := "incl %[y]", constraints := ["+m"], clobbers := ["cc"], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "increment of a memory operand (a local): the new value is a function of the old one",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.incLocal.json; volatile" },
  { template := "movq %[v], %[x]", constraints := ["=m", "r"], clobbers := [], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "store of a register input to a memory output: the output is the input",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.setm.json; non-volatile" },
  { template := "movl %[a], %%eax\n\txchgl %%eax, %[b]\n\tmovl %%eax, %[a]",
    constraints := ["+m", "+m"], clobbers := ["rax"], target := "x86_64", semantics := .opaque, fault := .never,
    reason := "swap of two memory operands through eax: each new value is the other old value \
      (xchg with memory is atomic natively; the model has no other thread on these locations)",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.swapm.json; volatile" },
  { template := "addq %[v], %[x]", constraints := ["+r", "r"], clobbers := ["cc"],
    target := "x86_64", semantics := .opaque, fault := .never,
    reason := "64-bit add into a read-write register: a function of both inputs; it only clobbers flags",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.addr.json; non-volatile" },
  { template := "", constraints := [], clobbers := [], target := "x86_64", semantics := .opaque, fault := .never,
    reason := "an empty template executes no instruction: the opaque is a constant",
    reviewerNote := "A01 tests/roadmap/asm-effects/test_cli.py (`plain`, the barrier without its \
      clobber: one hash, two opaques)" },
  { template := "", constraints := [], clobbers := ["memory"], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "A01's compiler barrier (`asmPureRegistry`): no instruction, so no effect in a model \
      that runs accesses in program order; the checker also requires `volatile` and the registry",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.16.0/asm_effects.barrier.json and L13 \
      tests/roadmap/volatile-effects/air-asm/0.16.0/device_asm.barrier.json; volatile" },
  { template := "pause", constraints := [], clobbers := [], target := "x86_64",
    semantics := .spinHint, fault := .never,
    reason := "std.atomic.spinLoopHint on x86_64: no output, no memory effect",
    reviewerNote := "C03 tests/roadmap/idle-loops/air/progress.idle.json; volatile, operand-free" },
  { template := "isb", constraints := [], clobbers := [], target := "aarch64",
    semantics := .spinHint, fault := .never,
    reason := "std.atomic.spinLoopHint on aarch64: no output, no memory effect",
    reviewerNote := "C03 docs/progress-hints.md; volatile, operand-free" },
  -- A01's environment reads (premise ASM-05): no input, no memory effect; each output is a
  -- fresh oracle query (`Zig.Asm.envWord`), so two reads are never one repeatable value.
  { template := "rdtsc\n\tshlq $32, %%rdx\n\torq %%rdx, %%rax", constraints := ["={rax}"],
    clobbers := ["cc", "rdx"], target := "x86_64", semantics := .envRead, fault := .never,
    reason := "time-stamp counter read, combined into rax: the value comes from outside the \
      model (an environment read, not a function of inputs); it writes rdx and the flags, both \
      clobbered. rdtsc faults (#GP) only when the OS sets CR4.TSD: a target premise (ASM-05)",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.ticks.json; L13 \
      device_asm.elapsed/ticksPlain (a device contract that declares it keeps it a device event)" },
  { template := "rdrand %[ret]", constraints := ["=r"], clobbers := ["cc"], target := "x86_64",
    semantics := .envRead, fault := .never,
    reason := "hardware random number: an environment read. A failed rdrand (CF = 0) writes 0, \
      which is one of the oracle's values; only the flags are clobbered. #UD without RDRAND: a \
      target-CPU premise (ASM-04)",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.random.json; L13 \
      device_asm.random" },
  { template := "rdrand %[v]\n\tsetc %[ok]", constraints := ["=r", "=r"], clobbers := ["cc"],
    target := "x86_64", semantics := .envRead, fault := .never,
    reason := "rdrand with its success flag: both outputs are environment reads (the flag is any \
      byte in the model, a superset of setc's 0 or 1); only the flags are clobbered",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.rand64.json; two lvalue outputs" },
  -- A01's memory input: an integer `m` input is the value, spilled by the compiler to a private
  -- stack slot (`codegen/llvm/FuncGen.zig` `airAssembly`: a non-by-ref operand under a
  -- memory-only constraint is stored to a fresh alloca), so it is a value input.
  { template := "movq %[x], %[ret]", constraints := ["=r", "m"], clobbers := [], target := "x86_64",
    semantics := .opaque, fault := .never,
    reason := "load of a memory input operand into a register: the output is the input value \
      (the compiler's private copy of it)",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.loadm.json; non-volatile" },
  -- A01's memory-region contracts (premise ASM-06): the block reads and writes memory through
  -- pointer operands only within its declared regions; the `"memory"` clobber is then accounted
  -- for by the regions.
  { template := "rep stosb", constraints := ["+{rdi}", "+{rcx}", "{al}"], clobbers := ["memory"],
    target := "x86_64", semantics := .opaque, fault := .never,
    regions := [{ base := 0, len := { operand := 1 }, access := .write }],
    reason := "string store (DF = 0, the ABI's state at every call): writes rcx bytes at rdi \
      and nothing else; the new rdi and rcx are functions of the old ones (rdi moves by rcx, \
      rcx becomes 0). A bad address faults natively and is `.illegal` in the model's checked \
      access",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.fill.json; volatile" },
  { template := "rep movsb", constraints := ["+{rdi}", "+{rsi}", "+{rcx}"], clobbers := ["memory"],
    target := "x86_64", semantics := .opaque, fault := .never,
    regions := [{ base := 1, len := { operand := 2 }, access := .read },
                { base := 0, len := { operand := 2 }, access := .write }],
    reason := "string copy (DF = 0): reads rcx bytes at rsi, writes rcx bytes at rdi, nothing \
      else; for disjoint regions the written bytes are a function of the read ones (an \
      overlapping forward copy depends on the distance, so the wrapper's guard makes overlap \
      `.unspecified`), the new pointers move by rcx and rcx becomes 0",
    reviewerNote := "A01 tests/roadmap/asm-effects/air/0.17.0/asm_env.copy.json; volatile" }]

/-- The entry for an asm op on the target `arch` (empty: a legacy profile, the x86_64
reference model), if any. -/
def asmAllowed? (arch template : String) (constraints clobbers : List String) :
    Option AsmAllowEntry :=
  let arch := if arch.isEmpty then "x86_64" else arch
  asmAllowlist.find? fun e => e.template == template && e.constraints == constraints &&
    e.clobbers == clobbers && e.target == arch

end Air2Lean
