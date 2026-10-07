/-!
# Test-only executable interpretation of register-only inline asm (A03)

Never imported by `ZigLean`, `Proofs` or `Air2Lean`; it is not a module of any Lake library.
`harness.py` pastes this file into a standalone `lake env lean --run` program after the real
generated wrappers' opaques have been rebound to it. Nothing here is a proof premise: ASM-01/02
keep every `airAsm_<hash>` opaque in the proof environment (`audit.py` checks this).

The interpretation is a small x86_64 register machine. One `Spec` is one AIR `assembly`
instruction (source template, constraints, operand widths). `exec`:

1. allocates registers from the constraints (`{reg}` pins, `r` takes the next free register of
   an allocation pool, a digit reuses that output's register);
2. fills every register with a junk pattern, then writes each input into the low bits of its
   register, so a template that reads unspecified upper bits or an unbound register sees junk;
3. expands `%%`, `%[name]` and `%<n>` and runs the AT&T instructions `bswap`, `popcnt`,
   `lzcnt`, `xor` and `div` (optional `l`/`q` width suffix);
4. rejects a write to any register that is neither an output nor a named clobber, and reads
   each output from the low `width` bits of its register.

`run` executes under three allocations (two pools, and one where an `r` input shares a plain
`=r` output's register) and rejects a result that depends on the allocation.
A fault (`#DE`, an unsupported instruction or constraint, an undeclared write) panics; the
harness runs with `LEAN_ABORT_ON_PANIC=1`.
-/

namespace AsmHarness.Interp

/-- One asm operand: its AIR constraint, its `[name]` and its bit width. -/
structure Operand where
  constraint : String
  name : String
  width : Nat

/-- One AIR `assembly` instruction. -/
structure Spec where
  source : String
  outputs : List Operand
  inputs : List Operand
  clobbers : List String

def names64 : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
   "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

def names32 : List String :=
  ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
   "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]

/-- Register index and width of an AT&T register name (without `%`). -/
def lookupReg (s : String) : Option (Nat × Nat) :=
  match names64.idxOf? s, names32.idxOf? s with
  | some i, _ => some (i, 64)
  | none, some i => some (i, 32)
  | none, none => none

def regName (r w : Nat) : Except String String :=
  match w, names64[r]?, names32[r]? with
  | 64, some n, _ => pure n
  | 32, _, some n => pure n
  | _, _, _ => throw s!"no register name for index {r} at width {w}"

/-- Two allocation pools for `r`: neither contains `rsp` or `rbp`. -/
def poolA : List Nat := [1, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 2]
def poolB : List Nat := poolA.reverse

/-- The register named by a `{reg}` constraint body, if any. -/
def pinned (c : String) : Except String (Option Nat) :=
  match c.toList.dropWhile (· != '{') with
  | [] => pure none
  | _ :: rest =>
    let name := String.ofList (rest.takeWhile (· != '}'))
    match lookupReg name with
    | some (r, _) => pure (some r)
    | none => throw s!"unknown pinned register {name}"

def stripOutput (c : String) : Except String String :=
  match c.toList with
  | '=' :: '&' :: rest => pure (String.ofList rest)
  | '=' :: rest => pure (String.ofList rest)
  | _ => throw s!"unsupported output constraint {c}"

def pick (pool used : List Nat) : Except String Nat :=
  match pool.find? (!used.contains ·) with
  | some r => pure r
  | none => throw "register pool exhausted"

/-- Registers of outputs then inputs. An `r` operand gets a pool register no constraint pins and
no other operand uses. With `share`, an `r` input instead reuses the register of a plain `=r`
output (not early-clobber) that no other input took, as a compiler may. -/
def allocate (spec : Spec) (pool : List Nat) (share : Bool) : Except String (List Nat) := do
  let mut pins : List Nat := []
  for o in spec.outputs ++ spec.inputs do
    if let some r ← pinned o.constraint then pins := r :: pins
  let mut regs : List Nat := []
  for o in spec.outputs do
    let c ← stripOutput o.constraint
    match ← pinned c with
    | some r => regs := regs ++ [r]
    | none =>
      if c != "r" then throw s!"unsupported output constraint {o.constraint}"
      regs := regs ++ [← pick pool (pins ++ regs)]
  let outRegs := regs
  for i in spec.inputs do
    match ← pinned i.constraint, i.constraint.toNat? with
    | some r, _ => regs := regs ++ [r]
    | none, some k =>
      match outRegs[k]? with
      | some r => regs := regs ++ [r]
      | none => throw s!"matching constraint {k} names no output"
    | none, none =>
      if i.constraint != "r" then throw s!"unsupported input constraint {i.constraint}"
      let shareable := (outRegs.zip spec.outputs).find? fun (r, o) =>
        o.constraint == "=r" && !(regs.drop outRegs.length).contains r
      match share, shareable with
      | true, some (r, _) => regs := regs ++ [r]
      | _, _ => regs := regs ++ [← pick pool (pins ++ regs)]
  return regs

def operands (spec : Spec) : List Operand := spec.outputs ++ spec.inputs

partial def expandChars (ops : List Operand) (rename : Nat → Except String String) :
    List Char → Except String (List Char)
  | '%' :: '%' :: rest => return '%' :: (← expandChars ops rename rest)
  | '%' :: '[' :: rest => do
    let name := String.ofList (rest.takeWhile (· != ']'))
    match ops.findIdx? (·.name == name) with
    | some k => return (← rename k).toList ++
        (← expandChars ops rename ((rest.dropWhile (· != ']')).drop 1))
    | none => throw s!"template names unknown operand [{name}]"
  | '%' :: d :: rest =>
    if d.isDigit then return (← rename (d.toNat - '0'.toNat)).toList ++ (← expandChars ops rename rest)
    else throw s!"unsupported template escape %{d}"
  | c :: rest => return c :: (← expandChars ops rename rest)
  | [] => return []

/-- Expand `%%`, `%[name]` and `%<digit>` with the allocated register names. -/
def expand (spec : Spec) (regs : List Nat) : Except String String := do
  let ops := operands spec
  let rename (k : Nat) : Except String String := do
    match ops[k]?, regs[k]? with
    | some o, some r => return "%" ++ (← regName r o.width)
    | _, _ => throw s!"template operand {k} out of range"
  return String.ofList (← expandChars ops rename spec.source.toList)

def isSpace (c : Char) : Bool := c == ' ' || c == '\t'

def trim (cs : List Char) : List Char :=
  ((cs.dropWhile isSpace).reverse.dropWhile isSpace).reverse

def splitOn (sep : Char → Bool) (cs : List Char) : List (List Char) :=
  let (cur, done) := cs.foldl (init := ([], []))
    fun (cur, done) c => if sep c then ([], cur.reverse :: done) else (c :: cur, done)
  (cur.reverse :: done).reverse

/-- Machine state: sixteen 64-bit registers and the registers written so far. -/
structure Machine where
  regs : Array Nat
  written : List Nat

def junk (r : Nat) : Nat := 0xA5C3_0F96_0000_0000 + 0x0101_0101 * (r + 1)

def Machine.read (m : Machine) (r w : Nat) : Nat := m.regs.getD r 0 % 2 ^ w

/-- A 32-bit write zero-extends into the 64-bit register, as on x86_64. -/
def Machine.write (m : Machine) (r w v : Nat) : Machine :=
  { regs := m.regs.set! r (v % 2 ^ w), written := r :: m.written }

def byteSwap (w v : Nat) : Nat :=
  (List.range (w / 8)).foldl (fun acc k => acc * 256 + (v / 256 ^ k) % 256) 0

def popCount (w v : Nat) : Nat := (List.range w).countP (v.testBit ·)

def bitLength (v : Nat) : Nat := if v = 0 then 0 else v.log2 + 1

/-- Mnemonic base and width suffix (`l` = 32, `q` = 64). -/
def mnemonic (m : String) : Except String (String × Option Nat) := do
  for base in ["bswap", "popcnt", "lzcnt", "xor", "div"] do
    if m == base then return (base, none)
    if m == base ++ "l" then return (base, some 32)
    if m == base ++ "q" then return (base, some 64)
  throw s!"unsupported instruction {m}"

def parseReg (cs : List Char) : Except String (Nat × Nat) :=
  match trim cs with
  | '%' :: name => match lookupReg (String.ofList name) with
    | some r => pure r
    | none => throw s!"unknown register {String.ofList name}"
  | other => throw s!"unsupported operand {String.ofList other}"

def step (m : Machine) (line : List Char) : Except String Machine := do
  let line := trim line
  let mn := String.ofList (line.takeWhile (!isSpace ·))
  let (base, suffix) ← mnemonic mn
  let rest := trim (line.dropWhile (!isSpace ·))
  let args ← (if rest.isEmpty then [] else splitOn (· == ',') rest).mapM parseReg
  let w ← match args with
    | [] => throw s!"{mn} needs an operand"
    | (_, w) :: more =>
      if more.any (·.2 != w) then throw s!"{mn}: mixed operand widths"
      else if suffix.any (· != w) then throw s!"{mn}: suffix disagrees with operand width"
      else if w != 32 && w != 64 then throw s!"{mn}: unsupported width {w}"
      else pure w
  match base, args with
  | "bswap", [(d, _)] => return m.write d w (byteSwap w (m.read d w))
  | "popcnt", [(s, _), (d, _)] => return m.write d w (popCount w (m.read s w))
  | "lzcnt", [(s, _), (d, _)] => return m.write d w (w - bitLength (m.read s w))
  | "xor", [(s, _), (d, _)] => return m.write d w (m.read s w ^^^ m.read d w)
  | "div", [(s, _)] =>
    let divisor := m.read s w
    let dividend := m.read 2 w * 2 ^ w + m.read 0 w
    if divisor = 0 then throw "#DE: division by zero"
    if dividend / divisor ≥ 2 ^ w then throw "#DE: quotient overflow"
    return (m.write 0 w (dividend / divisor)).write 2 w (dividend % divisor)
  | _, _ => throw s!"{mn}: wrong operand count"

/-- Execute `spec` on `args` (one natural number per input) under one allocation. -/
def exec (spec : Spec) (pool : List Nat) (share : Bool) (args : List Nat) :
    Except String (List Nat) := do
  if args.length != spec.inputs.length then throw "argument count differs from inputs"
  let regs ← allocate spec pool share
  let inRegs := regs.drop spec.outputs.length
  let mut m : Machine := { regs := Array.ofFn (n := 16) (junk ·.val), written := [] }
  for ((r, o), x) in (inRegs.zip spec.inputs).zip args do
    let old := m.regs.getD r 0
    m := { m with regs := m.regs.set! r (old - old % 2 ^ o.width + x % 2 ^ o.width) }
  let text ← expand spec regs
  for line in splitOn (fun c => c == '\n' || c == ';') text.toList do
    if !(trim line).isEmpty then m ← step m line
  let outRegs := regs.take spec.outputs.length
  let clobbered := spec.clobbers.filterMap fun c => (lookupReg c).map (·.1)
  for r in m.written do
    if !(outRegs.contains r || clobbered.contains r) then
      throw s!"writes undeclared register {names64.getD r "?"}"
  return (outRegs.zip spec.outputs).map fun (r, o) => m.read r o.width

/-- The interpretation the harness binds to an opaque: three allocations must agree. -/
def run (spec : Spec) (args : List Nat) : List Nat :=
  match [(poolA, false), (poolB, false), (poolA, true)].mapM fun (p, s) => exec spec p s args with
  | .ok (a :: rest) =>
    if rest.all (· == a) then a
    else panic! s!"asm result depends on register allocation: {spec.source}"
  | .ok [] => []
  | .error e => panic! s!"asm fault in {spec.source}: {e}"

end AsmHarness.Interp
