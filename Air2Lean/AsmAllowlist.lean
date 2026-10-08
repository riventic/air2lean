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
      runs as bsr: a target-CPU premise (ASM-03), not an input condition",
    reviewerNote := "examples/asm lzcnt64 (tests/golden/asm/air/asm.lzcnt64.json); volatile in \
      the source, but input-determined" },
  { template := "popcnt %[x], %[ret]", constraints := ["=r", "r"], clobbers := [],
    target := "x86_64", semantics := .opaque, fault := .never,
    reason := "population count: a function of the input; it faults on no input on a CPU \
      with POPCNT (on one without it every execution is #UD: a target-CPU premise, ASM-03)",
    reviewerNote := "examples/asm popcnt64 (tests/golden/asm/air/asm.popcnt64.json); non-volatile" },
  { template := "pause", constraints := [], clobbers := [], target := "x86_64",
    semantics := .spinHint, fault := .never,
    reason := "std.atomic.spinLoopHint on x86_64: no output, no memory effect",
    reviewerNote := "C03 tests/roadmap/idle-loops/air/progress.idle.json; volatile, operand-free" },
  { template := "isb", constraints := [], clobbers := [], target := "aarch64",
    semantics := .spinHint, fault := .never,
    reason := "std.atomic.spinLoopHint on aarch64: no output, no memory effect",
    reviewerNote := "C03 docs/progress-hints.md; volatile, operand-free" }]

/-- The entry for an asm op on the target `arch` (empty: a legacy profile, the x86_64
reference model), if any. -/
def asmAllowed? (arch template : String) (constraints clobbers : List String) :
    Option AsmAllowEntry :=
  let arch := if arch.isEmpty then "x86_64" else arch
  asmAllowlist.find? fun e => e.template == template && e.constraints == constraints &&
    e.clobbers == clobbers && e.target == arch

end Air2Lean
