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

To add an entry: show that the instruction's outputs depend only on its inputs on the target
(no flags, memory, counters, entropy, privileged or I/O state is read), that it writes nothing
outside its outputs and clobbers, and name the committed fixture that needs it. -/
namespace Air2Lean

inductive AsmSemantics where
  /-- An M21 `opaque` function of the inputs (`Emit.lean`'s `emitAsmDef`). -/
  | opaque
  /-- `Zig.spinLoopHintC`: a scheduling point, no memory effect (C03, `Op.isSpinHint`). -/
  | spinHint
  deriving BEq, Repr

structure AsmAllowEntry where
  template : String
  /-- Outputs, then inputs, in AIR order. -/
  constraints : List String
  clobbers : List String
  /-- The `target_triple` architecture (`x86_64`, `aarch64`). -/
  target : String
  semantics : AsmSemantics
  reason : String
  reviewerNote : String
  deriving Repr

def asmAllowlist : List AsmAllowEntry := [
  { template := "bswap %[ret]", constraints := ["=r", "0"], clobbers := [], target := "x86_64",
    semantics := .opaque,
    reason := "byte swap of one register: the output is a function of the input",
    reviewerNote := "examples/asm bswap32 (tests/golden/asm/air/asm.bswap32.json); non-volatile" },
  { template := "xorl %%edx, %%edx\n\tdivl %[b]", constraints := ["={eax}", "=&{edx}", "{eax}", "r"],
    clobbers := [], target := "x86_64", semantics := .opaque,
    reason := "unsigned 32-bit divide: quotient and remainder are functions of the inputs \
      (a zero divisor is #DE, which the opaque does not model; the caller's proof states it)",
    reviewerNote := "examples/asm divmod (tests/golden/asm/air/asm.divmod.json); non-volatile" },
  { template := "lzcnt %[x], %[ret]", constraints := ["=r", "r"], clobbers := ["cc"],
    target := "x86_64", semantics := .opaque,
    reason := "leading-zero count: a function of the input; it only clobbers flags",
    reviewerNote := "examples/asm lzcnt64 (tests/golden/asm/air/asm.lzcnt64.json); volatile in \
      the source, but input-determined" },
  { template := "popcnt %[x], %[ret]", constraints := ["=r", "r"], clobbers := [],
    target := "x86_64", semantics := .opaque,
    reason := "population count: a function of the input",
    reviewerNote := "examples/asm popcnt64 (tests/golden/asm/air/asm.popcnt64.json); non-volatile" },
  { template := "pause", constraints := [], clobbers := [], target := "x86_64",
    semantics := .spinHint,
    reason := "std.atomic.spinLoopHint on x86_64: no output, no memory effect",
    reviewerNote := "C03 tests/roadmap/idle-loops/air/progress.idle.json; volatile, operand-free" },
  { template := "isb", constraints := [], clobbers := [], target := "aarch64",
    semantics := .spinHint,
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
