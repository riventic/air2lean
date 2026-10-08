import Air2Lean.Air.Op

/-!
# Inline asm effect contract (A01)

The operand grammar that `Check.lean` accepts for an `assembly` instruction and that `Emit.lean`
lowers (`docs/generated-code.md` §Inline asm, `ZigLean/Asm.lean`, premise ASM-03):

| Constraint | Operand | Lowering |
|---|---|---|
| `=r`, `=&r`, `={reg}`, `=&{reg}` | the result (`-> T`) or an lvalue (pointer `ref`) | opaque output; an lvalue is stored after the call |
| `+r`, `+{reg}` | an lvalue | old value loaded before, passed to the opaque, new value stored after |
| `=m` | an lvalue | opaque output stored to the pointee (the memory operand) |
| `+m` | an lvalue | as `+r`, through the memory operand |
| input `r`, `{reg}` | an integer value | opaque input |
| input digit `k` | an integer value | opaque input tied to the write-only register output `k` |

Clobbers name registers and flags (`cc`, `rax`, `eax`, …): none is Lean-visible state, but a
clobbered register may not also be a pinned (`{reg}`) operand. A `"memory"` clobber is rejected
unless the whole block is an `asmPureRegistry` entry.
-/

namespace Air2Lean

/-- One parsed output constraint. -/
structure AsmOutput where
  /-- `+`: the asm reads the old value too. -/
  readWrite : Bool
  /-- `&`: written before every input is read (cannot share an input's register). -/
  earlyClobber : Bool
  /-- `m`: a memory operand (the pointee itself), not a register. -/
  memory : Bool
  /-- The pinned register name of `{reg}`. -/
  pin : Option String
  deriving BEq, Repr

/-- Is `body` a register constraint body: the class `r` or a named register `{reg}`? Returns the
pin. -/
def asmRegBody? (body : String) : Option (Option String) :=
  if body == "r" then some none
  else if body.startsWith "{" && body.endsWith "}" && body.length > 2 then
    some (some ((body.drop 1).dropEnd 1).toString)
  else none

/-- Parse an output constraint: `=r`, `=&r`, `={reg}`, `=&{reg}`, `+r`, `+{reg}`, `=m`, `+m`.
Anything else (`=&m`, `+&r`, `rm`, an immediate class, several alternatives) is `none`. -/
def parseAsmOutput (c : String) : Option AsmOutput :=
  if c.startsWith "=&" then
    (asmRegBody? (c.drop 2).toString).map fun pin =>
      { readWrite := false, earlyClobber := true, memory := false, pin }
  else if c.startsWith "=" || c.startsWith "+" then
    let rw := c.startsWith "+"
    let body := (c.drop 1).toString
    if body == "m" then some { readWrite := rw, earlyClobber := false, memory := true, pin := none }
    else (asmRegBody? body).map fun pin =>
      { readWrite := rw, earlyClobber := false, memory := false, pin }
  else none

/-- Is this output read-write (`+r`, `+{reg}`, `+m`)? -/
def AsmOperand.isReadWrite (o : AsmOperand) : Bool :=
  ((parseAsmOutput o.constraint).map (·.readWrite)).getD false

/-- Does the output need the Lean effect wrapper beyond plain register outputs (a read of the old
value, or a memory operand)? -/
def AsmOutput.isEffect (o : AsmOutput) : Bool := o.readWrite || o.memory

/-- The x86_64 general-purpose register family (0 = `rax` … 15 = `r15`) of a register name, at
any width (`rax`, `eax`, `ax`, `al`, `ah`, `r8`, `r8d`, `r8w`, `r8b`). Clobber names and `{reg}`
pins of one family are the same physical register. -/
def x86RegFamily (name : String) : Option Nat :=
  let legacy : List (List String) := [
    ["rax", "eax", "ax", "al", "ah"], ["rcx", "ecx", "cx", "cl", "ch"],
    ["rdx", "edx", "dx", "dl", "dh"], ["rbx", "ebx", "bx", "bl", "bh"],
    ["rsp", "esp", "sp", "spl"], ["rbp", "ebp", "bp", "bpl"],
    ["rsi", "esi", "si", "sil"], ["rdi", "edi", "di", "dil"]]
  match legacy.findIdx? (·.contains name) with
  | some k => some k
  | none =>
    (List.range 8).findSome? fun k =>
      let r := s!"r{k + 8}"
      if [r, r ++ "d", r ++ "w", r ++ "b"].contains name then some (k + 8) else none

/-- A reviewed asm block whose `"memory"` clobber has no effect on the model state. The whole
block must match: template, volatility, constraint list and clobber set. -/
structure AsmPureEntry where
  name : String
  source : String
  isVolatile : Bool
  constraints : Array String
  clobbers : Array String
  /-- Why the block has no model-visible effect (`docs/premises.md` ASM-03). -/
  reason : String

/-- The reviewed registry of `"memory"`-clobber blocks with no model-visible effect. -/
def asmPureRegistry : Array AsmPureEntry := #[
  { name := "compiler-barrier", source := "", isVolatile := true, constraints := #[],
    clobbers := #["memory"],
    reason := "an empty template executes no instruction: the clobber only stops the compiler \
      from moving memory accesses across it. The model runs accesses in program order, so it \
      has no effect there (it adds no synchronization either: THR/ORD premises are unchanged)." }]

/-- The registry entry that covers this block, if any. -/
def asmPureEntry? (source : String) (isVolatile : Bool) (clobbers : Array String)
    (outputs inputs : Array AsmOperand) : Option AsmPureEntry :=
  let constraints := outputs.map (·.constraint) ++ inputs.map (·.constraint)
  let sameSet (a b : Array String) := a.all b.contains && b.all a.contains
  asmPureRegistry.find? fun e =>
    e.source == source && e.isVolatile == isVolatile && e.constraints == constraints &&
      sameSet e.clobbers clobbers

/-- Does this block lower to the effect form (`airAsmFx_<hash>`, ASM-03): a read-write or memory
output, or a registry-approved `"memory"` clobber? Every other accepted block is register-only
(`airAsm_<hash>`, ASM-01) and keeps its exact earlier lowering. -/
def asmIsEffect (clobbers : Array String) (outputs : Array AsmOperand) : Bool :=
  clobbers.contains "memory" ||
    outputs.any fun o => ((parseAsmOutput o.constraint).map (·.isEffect)).getD false

end Air2Lean
