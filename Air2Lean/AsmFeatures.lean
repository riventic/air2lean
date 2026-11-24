/-! # CPU features of inline-asm instructions (A02, premise ASM-09)

The single table from an instruction mnemonic to the CPU features it needs, for every target with
inline asm (`x86_64`, `aarch64`). Data and a statement scanner only: `Check.lean`'s
`checkAsmCpuFeatures` compares the features of every instruction of every asm block (allowlisted
or declared by a device contract) with the `features` of the profile the program is translated
for, which are the features of the CPU the compiler targeted (`zig-patch/air-json/json.zig`
writes `target.cpu.features`).

Why it matters: an instruction's encoding on a CPU without its feature is another instruction
or a fault. `lzcnt` (`F3 0F BD`) on a CPU without LZCNT executes as `bsr` (Intel SDM vol. 2A,
LZCNT: the `F3` prefix is ignored), so `lzcnt(1)` is 0 there, not 63; `tzcnt` without BMI1
executes as `bsf`; `popcnt` and `rdrand` are #UD. A model of the instruction is therefore sound
only on a CPU with the feature.

**Fail closed.** An instruction that is not in the table is rejected, never taken as needing no
feature. So is every statement that is not an instruction of the table: a directive (`.byte`), a
label, a comment, an upper-case mnemonic.

**Feature names** are Zig's `std.Target.<arch>.Feature` names (`lib/std/Target/x86.zig`,
`aarch64.zig`), which are LLVM's `SubtargetFeature` names (`llvm/lib/Target/X86/X86.td`,
`AArch64/AArch64Features.td`) and the spelling of `profile.features`.

**Sources.**
* x86_64: the feature column of the Zig compiler's own encoding table,
  `src/codegen/x86_64/encodings.zon` (0.17.1; its rows over general registers, memory and
  immediates), which agrees with the CPUID feature flag of each instruction's entry in the Intel
  SDM vol. 2. Two rows are stricter than that file: `cmpxchg16b` needs `cx16` (LLVM `X86.td`
  `HasCX16`, CPUID.01H:ECX[13]; the file says none), and `rdtscp` is left out (CPUID.80000001H:
  EDX[27]; no Zig/LLVM feature names it, so the profile cannot show it).
* The **x86-64 base** is not listed as a requirement: every CPU that runs 64-bit code has CMOV,
  CX8, FXSR, MMX, SSE, SSE2 and the TSC (System V x86-64 psABI, micro-architecture level
  x86-64-v1; AMD64 APM vol. 1). So `cmov`, `pause`, `mfence` and `rdtsc` need nothing here,
  although the encoding table marks `cmov`. ASM-09 is about the CPU that runs the program;
  `-mcpu=x86_64-cmov` changes what the compiler emits, not what an x86-64 CPU has. The levels
  x86-64-v2 (`cx16`, `sahf`, `popcnt`, `crc32`) and x86-64-v3 (`bmi`, `bmi2`, `lzcnt`, `movbe`)
  are not base.
* aarch64: the Arm ARM (DDI 0487) base A64 instructions (section C6.2: no `FEAT_` condition;
  `src/codegen/aarch64/instructions.zon` gives them no `.requires`) and `FEAT_CRC32` for the
  `crc32*` family (Zig/LLVM `crc`). An instruction over a system register (`mrs`, `msr`) is not
  in the table: its requirement depends on the register operand.

`tests/roadmap/asm-semantics/feature_table.py` compares `air2lean --print-asm-feature-table`
with both Zig files.

The table is by mnemonic, for instructions over general registers, memory and immediates. It
does not decode operands: `movq` with an `%xmm` operand is the SSE2 instruction, which is base
too. Vector, x87 and system instructions are not in the table. -/
namespace Air2Lean

/-- Instructions with one feature requirement. -/
structure AsmFeatureRow where
  /-- Lower-case mnemonics, as the template spells them. -/
  mnemonics : List String
  /-- AT&T (x86_64): the mnemonic may carry one operand-size suffix `b`, `w`, `l` or `q`. -/
  sized : Bool := false
  /-- A prefix (`rep`, `lock`): the rest of its statement is the prefixed instruction. -/
  isPrefix : Bool := false
  /-- The CPU features the instructions need beyond the target's base ISA. -/
  features : List String
  deriving Repr

/-- The x86 condition codes of `setcc` and `cmovcc`. -/
private def x86Conditions : List String :=
  ["a", "ae", "b", "be", "c", "e", "g", "ge", "l", "le", "na", "nae", "nb", "nbe", "nc", "ne",
   "ng", "nge", "nl", "nle", "no", "np", "ns", "nz", "o", "p", "pe", "po", "s", "z"]

/-- x86_64, AT&T syntax (see the module comment for the sources). -/
def asmFeaturesX86_64 : List AsmFeatureRow := [
  -- 8086 to 80486 integer instructions: in every x86-64 CPU.
  { mnemonics := ["adc", "add", "and", "bsf", "bsr", "bswap", "bt", "btc", "btr", "bts", "cmp",
      "cmpxchg", "dec", "div", "idiv", "imul", "in", "inc", "lea", "mov", "mul", "neg", "not",
      "or", "out", "pop", "push", "rcl", "rcr", "rol", "ror", "sal", "sar", "sbb", "shl", "shld",
      "shr", "shrd", "sub", "test", "xadd", "xchg", "xor",
      -- string instructions (`stosb`, `movsq`)
      "cmps", "lods", "movs", "scas", "stos"],
    sized := true, features := [] },
  { mnemonics := ["clc", "cld", "cmc", "cpuid", "nop", "stc", "std"], features := [] },
  { mnemonics := ["rep", "repe", "repz", "repne", "repnz", "lock"], isPrefix := true, features := [] },
  { mnemonics := x86Conditions.map ("set" ++ ·), features := [] },
  -- x86-64 base (x86-64-v1): CMOV, CX8, SSE (`sfence`), SSE2 (`lfence`, `mfence`; `pause` is
  -- `rep nop` on an older CPU), TSC.
  { mnemonics := x86Conditions.map ("cmov" ++ ·), sized := true, features := [] },
  { mnemonics := ["cmpxchg8b", "lfence", "mfence", "sfence", "pause", "rdtsc"], features := [] },
  -- Not base: each needs its CPUID feature.
  { mnemonics := ["lzcnt"], sized := true, features := ["lzcnt"] },       -- else runs as `bsr`
  { mnemonics := ["popcnt"], sized := true, features := ["popcnt"] },     -- else #UD
  { mnemonics := ["tzcnt", "andn", "bextr", "blsi", "blsmsk", "blsr"], sized := true,
    features := ["bmi"] },                                                -- `tzcnt` else runs as `bsf`
  { mnemonics := ["bzhi", "mulx", "pdep", "pext", "rorx", "sarx", "shlx", "shrx"], sized := true,
    features := ["bmi2"] },
  { mnemonics := ["adcx", "adox"], sized := true, features := ["adx"] },
  { mnemonics := ["movbe"], sized := true, features := ["movbe"] },
  { mnemonics := ["crc32"], sized := true, features := ["crc32"] },
  { mnemonics := ["rdrand"], sized := true, features := ["rdrnd"] },
  { mnemonics := ["rdseed"], sized := true, features := ["rdseed"] },
  { mnemonics := ["rdfsbase", "rdgsbase", "wrfsbase", "wrgsbase"], sized := true,
    features := ["fsgsbase"] },
  { mnemonics := ["rdpid"], features := ["rdpid"] },
  { mnemonics := ["lahf", "sahf"], features := ["sahf"] },                -- absent in early 64-bit CPUs
  { mnemonics := ["cmpxchg16b"], features := ["cx16"] }]

/-- aarch64 (see the module comment for the sources). -/
def asmFeaturesAarch64 : List AsmFeatureRow := [
  -- Armv8.0-A base A64 instructions over general registers.
  { mnemonics := ["nop", "yield", "isb", "rev", "rev16", "rev32", "clz", "cls", "rbit", "udiv",
      "sdiv"], features := [] },
  -- FEAT_CRC32 (optional in Armv8.0-A).
  { mnemonics := ["crc32b", "crc32h", "crc32w", "crc32x", "crc32cb", "crc32ch", "crc32cw",
      "crc32cx"], features := ["crc"] }]

/-- The feature table of each target architecture with inline asm. -/
def asmFeatureTable : List (String × List AsmFeatureRow) :=
  [("x86_64", asmFeaturesX86_64), ("aarch64", asmFeaturesAarch64)]

/-- The architecture of the asm tables for a dialect's `arch` (empty: a legacy profile without a
target, the x86_64 reference model, premise PRF-01). -/
def asmTargetArch (arch : String) : String := if arch.isEmpty then "x86_64" else arch

/-- Every feature name that a row of some table requires: the names
`--assume-asm-cpu-features` accepts. -/
def asmKnownFeatures : List String :=
  (asmFeatureTable.flatMap fun (_, rows) => rows.flatMap (·.features)).eraseDups

/-- The row of `mnemonic` on `arch`: the exact mnemonic, else (a `sized` row) the mnemonic
without one AT&T size suffix. -/
def asmFeatureRow? (arch mnemonic : String) : Option AsmFeatureRow := do
  let rows ← asmFeatureTable.lookup (asmTargetArch arch)
  match rows.find? (·.mnemonics.contains mnemonic) with
  | some row => some row
  | none =>
    match mnemonic.toList.reverse with
    | suffix :: stem =>
      if ['b', 'w', 'l', 'q'].contains suffix then
        rows.find? fun row => row.sized && row.mnemonics.contains (String.ofList stem.reverse)
      else none
    | [] => none

/-- `s` cut at every character that satisfies `p`; empty pieces are dropped. -/
private def splitNonEmpty (p : Char → Bool) (s : String) : List String :=
  let (pieces, last) := s.toList.foldl (init := (([] : List (List Char)), ([] : List Char)))
    fun (pieces, piece) c => if p c then (piece :: pieces, []) else (pieces, c :: piece)
  ((last :: pieces).reverse.filter (!·.isEmpty)).map fun piece => String.ofList piece.reverse

/-- The instructions of one statement, given as its words: the first word is the mnemonic, and
after a prefix the next word is one too. -/
private def asmStatementInstrs (arch : String) :
    List String → Except String (List (String × List String))
  | [] => pure []
  | word :: rest => do
    let some row := asmFeatureRow? arch word
      | throw s!"instruction '{word}' is not in the CPU-feature table of target \
          '{asmTargetArch arch}' (Air2Lean/AsmFeatures.lean)"
    let prefixed ← if row.isPrefix then asmStatementInstrs arch rest else pure []
    pure ((word, row.features) :: prefixed)

/-- The instructions of an asm template on `arch`, in order, each with the features it needs.
Statements end at a newline or `;`. An empty template has no instruction. An error names the
first word that is not an instruction of the table (fail closed). -/
def asmTemplateInstrs (arch template : String) : Except String (List (String × List String)) := do
  let statements := splitNonEmpty (fun c => c == '\n' || c == ';') template
  let instrs ← statements.mapM fun statement =>
    asmStatementInstrs arch (splitNonEmpty Char.isWhitespace statement)
  pure instrs.flatten

end Air2Lean
