import Air2Lean.AsmAllowlist
import Air2Lean.AsmContract
import ZigLean.Isa.X86

/-!
# Inline asm as a defined function (A02 decision 1, premise ASM-07)

An allowlist entry with `AsmSemantics.isa` is not an `opaque`: its template is decoded into the
instructions of the ISA model (`ZigLean/Isa/X86.lean`) and the translator emits a *defined*
function over that model (`Emit.lean`'s `emitAsmDef`). A fact about the block is then a theorem
about the instruction semantics, not a hypothesis (ASM-02).

**One emission rule** (`asmIsaBlock`), for every template:

1. The statements come from the one statement scanner (`asmTemplateStmts`,
   `Air2Lean/AsmFeatures.lean`). A prefix (`rep`, `lock`) is not modelled.
2. Each operand of the block gets a location from its constraint (`asmIsaLocs`): a `{reg}` pin is
   that register, a register class `r` is the operand's own register (`vreg k`), `m` is the
   operand's memory (`mem k`), a digit is the location of the output it ties to.
3. Each instruction operand is `%[name]` (that operand's location, at the width of the
   operand's type: the register name the compiler prints), `%%reg` (a named register at the
   width of the name) or `$n` (an immediate that the instruction can encode). A modifier
   (`%[x:q]`), an address (`(%%rax)`), a symbol or a high-byte register is not modelled.
4. The mnemonic's AT&T size suffix and the register operands give the operand size; they must
   agree.
5. The declared footprint is checked against the instructions (`Zig.Isa.X86.Block.check`): a
   write to a register that is neither an output nor a clobber, a read of bits that nothing
   defined (an unbound register, the upper bits of a narrower input), a read of an input after a
   write to an output that may share its register, a memory operand accessed at another width,
   an output that is never written. Each is a rejection that names the instruction, never a
   guess.

A template outside the model (step 1 to 4) is *uncovered*; a block that the model can run but
whose declaration is wrong (step 5) is a *violation*. For an `isa` entry both reject the
program. An `opaque` entry is never decoded: `air2lean --print-asm-isa-table` shows that each
of them is uncovered, so no covered entry stays an opaque.
-/

namespace Air2Lean

open Zig.Isa.X86

inductive AsmIsaError where
  /-- The template is outside the ISA model. -/
  | uncovered (why : String)
  /-- The model runs the block, and the declared operands or clobbers do not match it. -/
  | violation (why : String)
  deriving Repr

def AsmIsaError.message : AsmIsaError → String
  | .uncovered why => s!"not covered by the instruction model (ZigLean/Isa/X86.lean): {why}"
  | .violation why => s!"the declared operands do not match the instructions: {why}"

def isaWidth? : Nat → Option Width
  | 8 => some .w8
  | 16 => some .w16
  | 32 => some .w32
  | 64 => some .w64
  | _ => none

/-- A general register name: its number (0 = `rax` … 15 = `r15`, the numbering of
`x86RegFamily`) and the width of the name. A high-byte register (`ah`) has none. -/
def x86Gpr? (name : String) : Option (Fin 16 × Width) :=
  let legacy : List (List String × Width) := [
    (["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"], .w64),
    (["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"], .w32),
    (["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"], .w16),
    (["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"], .w8)]
  let extended : Option (Nat × Width) := (List.range 8).findSome? fun k =>
    let r := s!"r{k + 8}"
    if name == r then some (k + 8, Width.w64)
    else if name == r ++ "d" then some (k + 8, .w32)
    else if name == r ++ "w" then some (k + 8, .w16)
    else if name == r ++ "b" then some (k + 8, .w8)
    else none
  let found := (legacy.findSome? fun (names, w) => (names.idxOf? name).map (·, w)) <|> extended
  found.bind fun (n, w) => if h : n < 16 then some (⟨n, h⟩, w) else none

/-- The location of each operand (AIR order: outputs, then inputs). -/
def asmIsaLocs (outputs inputs : Array AsmOperand) : Except AsmIsaError (Array Loc) := do
  let pin (name : String) : Except AsmIsaError Loc :=
    match x86Gpr? name with
    | some (r, _) => pure (.reg r)
    | none => throw (.uncovered s!"the pinned register '{name}' is not a general register")
  let mut locs : Array Loc := #[]
  for (o, k) in outputs.zipIdx do
    let some po := parseAsmOutput o.constraint
      | throw (.uncovered s!"output constraint '{o.constraint}'")
    let loc ← if po.memory then pure (Loc.mem k) else
      match po.pin with
      | some name => pin name
      | none => pure (.vreg k)
    locs := locs.push loc
  for (i, j) in inputs.zipIdx do
    let k := outputs.size + j
    let loc ← match i.constraint.toNat? with
      | some d =>
        match if d < outputs.size then locs[d]? else none with
        | some l => pure l
        | none => throw (.uncovered s!"input constraint '{i.constraint}' ties to no output")
      | none =>
        if i.constraint == "m" then pure (Loc.mem k) else
        match asmRegBody? i.constraint with
        | some (some name) => pin name
        | some none => pure (.vreg k)
        | none => throw (.uncovered s!"input constraint '{i.constraint}'")
    locs := locs.push loc
  return locs

/-- One operand of an instruction. -/
inductive AsmIsaArg where
  | loc (l : Loc) (w : Width) (isRegister : Bool)
  | imm (v : Int)

/-- A decimal or `0x` integer, with an optional sign. -/
def asmIsaInt? (s : String) : Option Int :=
  let (neg, digits) := match s.toList with
    | '-' :: rest => (true, rest)
    | cs => (false, cs)
  let value? : Option Nat := match digits with
    | '0' :: 'x' :: hex =>
      if hex.isEmpty then none else
      hex.foldlM (init := 0) fun acc c =>
        if c.isDigit then some (acc * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c && c ≤ 'f' then some (acc * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c && c ≤ 'F' then some (acc * 16 + (c.toNat - 'A'.toNat + 10))
        else none
    | ds => if ds.isEmpty || !ds.all Char.isDigit then none else (String.ofList ds).toNat?
  value?.map fun n => if neg then -(n : Int) else n

/-- The operand text `text` of an instruction: `%[name]`, `%%reg` or `$n`. -/
def asmIsaArg (names : Array String) (locs : Array Loc) (widths : Array Width) (text : String) :
    Except AsmIsaError AsmIsaArg :=
  match text.toList with
  | '%' :: '[' :: rest =>
    let name := String.ofList (rest.takeWhile (· != ']'))
    if rest.dropWhile (· != ']') != [']'] || name.any (· == ':') then
      throw (.uncovered s!"operand '{text}' (a modifier or trailing text)")
    else match names.idxOf? name with
      | none => throw (.uncovered s!"operand '{text}' names no operand of the block")
      | some k =>
        match locs[k]?, widths[k]? with
        | some l, some w => pure (.loc l w !l.isMem)
        | _, _ => throw (.uncovered s!"operand '{text}' has no location")
  | '%' :: '%' :: rest =>
    match x86Gpr? (String.ofList rest) with
    | some (r, w) => pure (.loc (.reg r) w true)
    | none => throw (.uncovered s!"operand '{text}' is not a general register of the model")
  | '$' :: rest =>
    match asmIsaInt? (String.ofList rest) with
    | some v => pure (.imm v)
    | none => throw (.uncovered s!"immediate '{text}' is not an integer literal")
  | _ => throw (.uncovered s!"operand '{text}' (an address, a symbol or another form)")

/-- Can the instruction encode the immediate `v` at width `w`? 8 and 16 bits: any value of the
width, signed or unsigned; 32 bits likewise; 64 bits: a sign-extended 32-bit immediate. -/
def asmIsaImmFits (w : Width) (v : Int) : Bool :=
  match w with
  | .w8 => -128 ≤ v && v < 256
  | .w16 => -32768 ≤ v && v < 65536
  | .w32 => -2147483648 ≤ v && v < 4294967296
  | .w64 => -2147483648 ≤ v && v < 2147483648

/-- The mnemonics (without size suffix) of the modelled instructions (`Zig.Isa.X86.Instr`). -/
def asmIsaStems : List String :=
  ["mov", "add", "sub", "and", "or", "xor", "inc", "dec", "neg", "not", "bswap", "lzcnt", "tzcnt",
   "popcnt", "bsr", "bsf", "xchg", "div"]

/-- The statements of a template that the model covers as a whole: an x86_64 template without
memory regions whose statements are all modelled instructions, none a prefix. This is the
coverage of an allowlist entry, whatever its operands are (`air2lean --print-asm-isa-table`). -/
def asmIsaStmts (arch source : String) (regions : List AsmRegion) :
    Except AsmIsaError (List AsmStmt) := do
  unless asmTargetArch arch == "x86_64" do
    throw (.uncovered s!"there is no instruction model for target '{asmTargetArch arch}'")
  unless regions.isEmpty do
    throw (.uncovered "memory regions through pointer operands (ASM-06) are not modelled")
  let stmts ← match asmTemplateStmts arch source with
    | .ok stmts => pure stmts
    | .error e => throw (.uncovered e)
  for stmt in stmts do
    if stmt.isPrefix then
      throw (.uncovered s!"the prefix '{stmt.mnemonic}' is not modelled")
    unless asmIsaStems.contains stmt.stem do
      throw (.uncovered s!"instruction '{stmt.mnemonic}' is not modelled")
  return stmts

/-- One statement as an instruction of the model. -/
def asmIsaInstr (names : Array String) (locs : Array Loc) (widths : Array Width)
    (stmt : AsmStmt) : Except AsmIsaError Instr := do
  let args ← stmt.operands.mapM (asmIsaArg names locs widths)
  let suffix? : Option Width ← match (stmt.mnemonic.toList.drop stmt.stem.length) with
    | [] => pure none
    | ['b'] => pure (some .w8)
    | ['w'] => pure (some .w16)
    | ['l'] => pure (some .w32)
    | ['q'] => pure (some .w64)
    | _ => throw (.uncovered s!"mnemonic '{stmt.mnemonic}'")
  -- The operand size: the suffix, else the register operands'. Every register operand has it
  -- (the assembler rejects a mismatch); a memory operand is checked by `Block.check`.
  let regWidths := args.filterMap fun
    | .loc _ w true => some w
    | _ => none
  let some w := suffix? <|> regWidths.head?
    | throw (.uncovered s!"'{stmt.mnemonic}': no suffix and no register operand gives the \
        operand size")
  unless regWidths.all (· == w) do
    throw (.violation s!"'{stmt.mnemonic} {", ".intercalate stmt.operands}': the operand sizes \
      differ (the register that the compiler prints for an operand has the width of its type)")
  let src (a : AsmIsaArg) : Except AsmIsaError Src :=
    match a with
    | .loc l _ _ => pure (.loc l)
    | .imm v =>
      if asmIsaImmFits w v then pure (.imm (BitVec.ofInt 64 v))
      else throw (.uncovered s!"'{stmt.mnemonic}': the immediate {v} has no encoding at \
        {w.bits} bits")
  let bin (op : BinOp) : Except AsmIsaError Instr :=
    match args with
    | [a, .loc d _ _] => return .bin op w (← src a) d
    | _ => throw (.uncovered s!"'{stmt.mnemonic}' with operands {stmt.operands}")
  let un (op : UnOp) : Except AsmIsaError Instr :=
    match args with
    | [.loc d _ _] => pure (.un op w d)
    | _ => throw (.uncovered s!"'{stmt.mnemonic}' with operands {stmt.operands}")
  let cnt (op : CntOp) : Except AsmIsaError Instr :=
    match args with
    | [.loc s _ _, .loc d _ _] => pure (.cnt op w s d)
    | _ => throw (.uncovered s!"'{stmt.mnemonic}' with operands {stmt.operands}")
  match stmt.stem with
  | "mov" => bin .mov
  | "add" => bin .add
  | "sub" => bin .sub
  | "and" => bin .and
  | "or" => bin .or
  | "xor" => bin .xor
  | "inc" => un .inc
  | "dec" => un .dec
  | "neg" => un .neg
  | "not" => un .not
  | "bswap" => un .bswap
  | "lzcnt" => cnt .lzcnt
  | "tzcnt" => cnt .tzcnt
  | "popcnt" => cnt .popcnt
  | "bsr" => cnt .bsr
  | "bsf" => cnt .bsf
  | "xchg" =>
    match args with
    | [.loc a _ _, .loc b _ _] => pure (.xchg w a b)
    | _ => throw (.uncovered s!"'{stmt.mnemonic}' with operands {stmt.operands}")
  | "div" =>
    match args with
    | [.loc s _ _] => pure (.div w s)
    | _ => throw (.uncovered s!"'{stmt.mnemonic}' with operands {stmt.operands}")
  | _ => throw (.uncovered s!"instruction '{stmt.mnemonic}' is not modelled")

def asmIsaLocName : Loc → String
  | .reg r => (["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"][r.val]?).getD s!"r{r.val}"
  | .vreg k => s!"operand {k} (a register)"
  | .mem k => s!"operand {k} (memory)"

def asmIsaViolation (stmts : List AsmStmt) (v : Violation) : String :=
  let at_ (i : Nat) : String := match stmts[i]? with
    | some s => s!"instruction {i} ('{s.mnemonic} {", ".intercalate s.operands}')"
    | none => s!"instruction {i}"
  match v with
  | .declaration => "an operand location is declared twice, or a clobbered register carries an \
      operand"
  | .noEncoding i => s!"{at_ i} has no encoding or an undefined result at this operand size or \
      operand kind"
  | .memWidth i l => s!"{at_ i} accesses {asmIsaLocName l} at another size than the operand's type"
  | .undefinedRead i l => s!"{at_ i} reads bits of {asmIsaLocName l} that no input and no earlier \
      instruction of the block defines (an unbound register, or the bits above a narrower input)"
  | .staleRead i l => s!"{at_ i} reads the input {asmIsaLocName l} after a write to an output \
      that the compiler may place in the same register (declare the output early-clobber, '=&')"
  | .staleAddress i l => s!"{at_ i} accesses {asmIsaLocName l} after a write to a register output \
      that the compiler may place in the register of its address (declare the output \
      early-clobber, '=&')"
  | .undeclaredWrite i l => s!"{at_ i} writes {asmIsaLocName l}, which is neither an output nor \
      a clobber of the block"
  | .outputUndefined k => s!"output {k} is not written by the block at the width of its type"

/-- The decoded and checked block of an asm op (the module comment's rule). `outBits`/`inBits`
are the bit widths of the operand types; `regions` are the allowlist entry's memory regions
(a block with one is not covered: the model has no memory beyond its `m` operands). -/
def asmIsaBlock (arch source : String) (outputs inputs : Array AsmOperand)
    (outBits inBits : Array Nat) (clobbers : Array String) (regions : List AsmRegion) :
    Except AsmIsaError Block := do
  let stmts ← asmIsaStmts arch source regions
  let operands := outputs ++ inputs
  let mut widths : Array Width := #[]
  for (o, bits) in operands.zip (outBits ++ inBits) do
    let some w := isaWidth? bits
      | throw (.uncovered s!"operand '{o.name}' is {bits} bits wide, not 8, 16, 32 or 64")
    widths := widths.push w
  unless widths.size == operands.size do
    throw (.uncovered "an operand has no known width")
  let locs ← asmIsaLocs outputs inputs
  let names := operands.map (·.name)
  let instrs ← stmts.mapM (asmIsaInstr names locs widths)
  let at_ (k : Nat) : Loc × Width := (locs[k]?.getD (.vreg k), widths[k]?.getD .w64)
  let outs := (List.range outputs.size).map at_
  let rw := (outputs.toList.zipIdx.filter (·.1.isReadWrite)).map fun (_, k) => at_ k
  let early := outputs.toList.zipIdx.filterMap fun (o, k) =>
    if ((parseAsmOutput o.constraint).map (·.earlyClobber)).getD false then some (at_ k).1 else none
  let block : Block := {
    instrs
    inputs := (List.range inputs.size).map (fun j => at_ (outputs.size + j)) ++ rw
    outputs := outs
    early
    clobbers := (clobbers.toList.filterMap fun c => (x86Gpr? c).map (·.1)).eraseDups }
  match block.check with
  | some v => throw (.violation (asmIsaViolation stmts v))
  | none => pure block

/-! ## Rendering (the generated `airIsa_<hash>_block`) -/

def asmIsaRenderLoc : Loc → String
  | .reg r => s!"(.reg {r.val})"
  | .vreg k => s!"(.vreg {k})"
  | .mem k => s!"(.mem {k})"

def asmIsaRenderWidth : Width → String
  | .w8 => ".w8"
  | .w16 => ".w16"
  | .w32 => ".w32"
  | .w64 => ".w64"

def asmIsaRenderInstr : Instr → String
  | .bin op w src dst =>
    let o := match op with
      | .mov => ".mov" | .add => ".add" | .sub => ".sub" | .and => ".and" | .or => ".or"
      | .xor => ".xor"
    let s := match src with
      | .loc l => s!"(.loc {asmIsaRenderLoc l})"
      | .imm v => s!"(.imm {v.toNat}#64)"
    s!".bin {o} {asmIsaRenderWidth w} {s} {asmIsaRenderLoc dst}"
  | .un op w dst =>
    let o := match op with
      | .inc => ".inc" | .dec => ".dec" | .neg => ".neg" | .not => ".not" | .bswap => ".bswap"
    s!".un {o} {asmIsaRenderWidth w} {asmIsaRenderLoc dst}"
  | .cnt op w src dst =>
    let o := match op with
      | .lzcnt => ".lzcnt" | .tzcnt => ".tzcnt" | .popcnt => ".popcnt" | .bsr => ".bsr"
      | .bsf => ".bsf"
    s!".cnt {o} {asmIsaRenderWidth w} {asmIsaRenderLoc src} {asmIsaRenderLoc dst}"
  | .xchg w a b => s!".xchg {asmIsaRenderWidth w} {asmIsaRenderLoc a} {asmIsaRenderLoc b}"
  | .div w src => s!".div {asmIsaRenderWidth w} {asmIsaRenderLoc src}"

/-- The block as a Lean structure instance body (the fields, one per line). -/
def asmIsaRenderBlock (b : Block) : List String :=
  let list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
  let bare (l : Loc) : String := ((asmIsaRenderLoc l).drop 1).dropEnd 1 |>.toString
  let operand (lw : Loc × Width) : String := s!"({bare lw.1}, {asmIsaRenderWidth lw.2})"
  [s!"  instrs := {list (b.instrs.map asmIsaRenderInstr)}",
   s!"  inputs := {list (b.inputs.map operand)}",
   s!"  outputs := {list (b.outputs.map operand)}",
   s!"  early := {list (b.early.map bare)}",
   s!"  clobbers := {list (b.clobbers.map fun r => toString r.val)}"]

end Air2Lean
