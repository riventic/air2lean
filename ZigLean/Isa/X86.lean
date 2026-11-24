import ZigLean.Permutation
import ZigLean.SimpAttr

/-!
# x86_64 instruction semantics for inline asm (A02, premise ASM-07)

The translator turns an inline-asm block whose instructions are all in this file into a
*defined* function (`airIsa_<hash>`, `Air2Lean/AsmIsa.lean`): the block's decoded instruction
list, run on a small machine state. A fact about such a block (`bswap` is an involution, `divl`
gives quotient and remainder) is a theorem about this file's definitions, not a hypothesis.

What this file is: a hand-written reading of the Intel SDM vol. 2 and the AMD APM vol. 3 for the
general-register instructions below, at every operand width. It is trusted (premise ASM-07,
`docs/premises.md`); its evidence is `ZigLean/Isa/X86Vectors.lean` (the native observations of
`tests/roadmap/asm-semantics`, kernel-checked against these definitions) and the differential
test of `examples/asm` on x86_64 hardware.

## Machine state

A location (`Loc`) is a general register, or an operand of the block:

* `reg r`: the general register `r` (0 = `rax`, 1 = `rcx`, 2 = `rdx`, 3 = `rbx`, 4 = `rsp`, …),
  named by a `{reg}` constraint or by the template itself (`%%edx`);
* `vreg k`: operand `k` (AIR order: outputs, then inputs) under a register-class constraint
  (`r`). The compiler chooses its register, so the model gives it a location of its own; the
  footprint check (`Block.check`) admits only blocks whose result does not depend on that choice;
* `mem k`: operand `k` under a memory constraint (`m`): the operand's own bytes. The generated
  wrapper loads them before the block and stores them after it (`ZigLean/Asm.lean`).

Every location holds 64 bits. A 32-bit write to a register zero-extends, an 8- or 16-bit write
keeps the upper bits (Intel SDM vol. 1, 3.4.1.1); a write to memory changes only its own bytes.

Flags are not state: no instruction of this file reads a flag (`adc`, `setcc`, `cmovcc` and the
conditional jumps are not modelled, so a block with one is not covered). The qualified backend
declares the flags clobbered for every x86 asm block (`src/codegen/llvm/FuncGen.zig`
`airAssembly` appends `~{dirflag},~{fpsr},~{flags}`), so an instruction's flag writes need no
`cc` clobber.

## Faults

`Instr.fault` is the instruction's own fault condition on the current state: `div` raises #DE
(`Fault.trap`) for a zero divisor and for a quotient that does not fit. `bsr`/`bsf` of zero
leave the destination undefined (Intel) or unchanged (AMD): the model chooses neither
(`Fault.unspecified`, a conservative `Zig.Error.unspecified` in the wrapper).
-/

namespace Zig.Isa.X86

/-- An operand size. -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited

@[reducible] def Width.bits : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/-- A location of the machine state (see the module comment). -/
inductive Loc where
  | reg (r : Fin 16)
  | vreg (k : Nat)
  | mem (k : Nat)
  deriving DecidableEq, Repr, Inhabited

def Loc.isMem : Loc → Bool
  | .mem _ => true
  | _ => false

def Loc.isReg : Loc → Bool
  | .reg _ => true
  | _ => false

def rax : Loc := .reg 0
def rdx : Loc := .reg 2
def rsp : Loc := .reg 4

abbrev State := Loc → BitVec 64

/-- The low `w` bits of a location. -/
def State.get (s : State) (w : Width) (l : Loc) : BitVec w.bits := (s l).setWidth w.bits

/-- A `w`-bit write: a 64-bit write, or a 32-bit write to a register (which zero-extends),
replaces the location; any other write keeps the bits above `w`. -/
def State.set (s : State) (w : Width) (l : Loc) (v : BitVec w.bits) : State := fun l' =>
  if l' = l then
    if w = .w64 || (w = .w32 && !l.isMem) then v.setWidth 64
    else (s l &&& ~~~ (BitVec.allOnes w.bits).setWidth 64) ||| v.setWidth 64
  else s l'

/-- A source operand: a location or an immediate (already sign-extended to 64 bits). -/
inductive Src where
  | loc (l : Loc)
  | imm (v : BitVec 64)
  deriving DecidableEq, Repr

inductive BinOp where
  | mov | add | sub | and | or | xor
  deriving DecidableEq, Repr

inductive UnOp where
  | inc | dec | neg | not | bswap
  deriving DecidableEq, Repr

inductive CntOp where
  | lzcnt | tzcnt | popcnt | bsr | bsf
  deriving DecidableEq, Repr

/-- The modelled instructions, in AT&T operand order (source, then destination). -/
inductive Instr where
  /-- `mov`, `add`, `sub`, `and`, `or`, `xor`. -/
  | bin (op : BinOp) (w : Width) (src : Src) (dst : Loc)
  /-- `inc`, `dec`, `neg`, `not`, `bswap`. -/
  | un (op : UnOp) (w : Width) (dst : Loc)
  /-- `lzcnt`, `tzcnt`, `popcnt`, `bsr`, `bsf`. -/
  | cnt (op : CntOp) (w : Width) (src dst : Loc)
  | xchg (w : Width) (a b : Loc)
  /-- Unsigned divide of `rdx:rax` (8-bit: of `ax`) by the operand. -/
  | div (w : Width) (src : Loc)
  deriving DecidableEq, Repr

def Src.val (s : State) (w : Width) : Src → BitVec w.bits
  | .loc l => s.get w l
  | .imm v => v.setWidth w.bits

/-- Source value, then the old destination value, at the operand width. -/
def BinOp.eval {n : Nat} : BinOp → BitVec n → BitVec n → BitVec n
  | .mov, a, _ => a
  | .add, a, b => b + a
  | .sub, a, b => b - a
  | .and, a, b => b &&& a
  | .or, a, b => b ||| a
  | .xor, a, b => b ^^^ a

def UnOp.eval {n : Nat} : UnOp → BitVec n → BitVec n
  | .inc, a => a + 1
  | .dec, a => a - 1
  | .neg, a => -a
  | .not, a => ~~~a
  | .bswap, a => Zig.byteSwap a

/-- `lzcnt` and `tzcnt` of zero are the operand size. `bsr` is the index of the highest set
bit, `bsf` of the lowest one; both are meaningful only for a nonzero source (`Instr.fault`). -/
def CntOp.eval {n : Nat} : CntOp → BitVec n → BitVec n
  | .lzcnt, a => a.clz
  | .tzcnt, a => a.ctz
  | .popcnt, a => a.cpop
  | .bsr, a => BitVec.ofNat n (n - 1) - a.clz
  | .bsf, a => a.ctz

/-- The dividend and the divisor of `div`. -/
def divOperands (s : State) (w : Width) (src : Loc) : Nat × Nat :=
  (match w with
    | .w8 => (s.get .w16 rax).toNat
    | _ => (s.get w rdx).toNat * 2 ^ w.bits + (s.get w rax).toNat,
   (s.get w src).toNat)

def Instr.step : Instr → State → State
  | .bin op w src dst, s => s.set w dst (op.eval (src.val s w) (s.get w dst))
  | .un op w dst, s => s.set w dst (op.eval (s.get w dst))
  | .cnt op w src dst, s => s.set w dst (op.eval (s.get w src))
  | .xchg w a b, s => (s.set w a (s.get w b)).set w b (s.get w a)
  | .div w src, s =>
    let nd := divOperands s w src
    match w with
    -- `al` is the quotient, `ah` the remainder.
    | .w8 => s.set .w16 rax (BitVec.ofNat _ (nd.1 % nd.2 * 256 + nd.1 / nd.2))
    | _ => (s.set w rax (BitVec.ofNat _ (nd.1 / nd.2))).set w rdx (BitVec.ofNat _ (nd.1 % nd.2))

inductive Fault where
  /-- A CPU exception (#DE), delivered as a signal. -/
  | trap
  /-- The architecture leaves the result open. -/
  | unspecified
  deriving DecidableEq, Repr

/-- The instruction's fault on the state it runs in, if any. -/
def Instr.fault : Instr → State → Option Fault
  | .div w src, s =>
    let nd := divOperands s w src
    if nd.2 = 0 ∨ 2 ^ w.bits ≤ nd.1 / nd.2 then some .trap else none
  | .cnt .bsr w src _, s => if s.get w src = 0 then some .unspecified else none
  | .cnt .bsf w src _, s => if s.get w src = 0 then some .unspecified else none
  -- `bswap` of a 16-bit register is undefined (Intel SDM vol. 2A, BSWAP); `Block.check`
  -- rejects it and the 8-bit form, which has no encoding.
  | .un .bswap .w16 _, _ => some .unspecified
  | .un .bswap .w8 _, _ => some .unspecified
  | _, _ => none

/-- Can the instruction fault on some state? The translator emits a block's fault function and
the wrapper's guard only for a block with such an instruction. (`bswap` at 8 or 16 bits is not
listed: `Block.check` rejects it.) -/
def Instr.mayFault : Instr → Bool
  | .div _ _ => true
  | .cnt .bsr _ _ _ => true
  | .cnt .bsf _ _ _ => true
  | _ => false

def runInstrs : List Instr → State → State
  | [], s => s
  | i :: rest, s => runInstrs rest (i.step s)

/-- The first fault of the instructions, run in order. -/
def faultInstrs : List Instr → State → Option Fault
  | [], _ => none
  | i :: rest, s => (i.fault s).or (faultInstrs rest (i.step s))

/-! ## Blocks -/

/-- One decoded asm block with its declared operands. -/
structure Block where
  instrs : List Instr
  /-- The locations that hold a value on entry, with the operand's width, in the order of the
  generated function's parameters: the inputs, then the read-write outputs. -/
  inputs : List (Loc × Width)
  /-- The outputs, in output order. -/
  outputs : List (Loc × Width)
  /-- The early-clobber (`&`) outputs: no input shares their register. -/
  early : List Loc := []
  /-- The clobbered general registers. -/
  clobbers : List (Fin 16) := []
  deriving Repr

/-- The state on entry: each input location holds its value, cut to the operand's width. Every
other bit is 0 here and is never read by a block that passes `Block.check`. -/
def initState : List (Loc × Width) → List (BitVec 64) → State
  | (l, w) :: ins, v :: vs => fun l' =>
    if l' = l then (v.setWidth w.bits).setWidth 64 else initState ins vs l'
  | _, _ => fun _ => 0

namespace Block

/-- Output `k` after the block, on the input values `vals`. -/
def out (b : Block) (vals : List (BitVec 64)) (k : Nat) : BitVec 64 :=
  match b.outputs[k]? with
  | some (l, w) => ((runInstrs b.instrs (initState b.inputs vals)).get w l).setWidth 64
  | none => 0

/-- The block's fault on the input values `vals`, if any. -/
def fault (b : Block) (vals : List (BitVec 64)) : Option Fault :=
  faultInstrs b.instrs (initState b.inputs vals)

end Block

/-! ## Footprint check

`Block.check` compares what the instructions read and write with what the block declares. It is
what makes one function a model of the block under *every* register assignment the compiler may
choose and whatever the registers held before:

* a write goes only to an output or to a clobbered register, never to `rsp`;
* a read sees only bits that an input or an earlier instruction of the block defined: an input
  defines the bits of its operand's type (the bits above them are whatever the caller left), a
  32- or 64-bit register write defines the whole register;
* an output without `&` may get the register of an input (the compiler assumes that every input
  is read before any output is written), so after a write to such an output no other input may
  be read;
* a memory operand is accessed at exactly its own width;
* every output holds defined bits at the end.

The translator runs it and rejects a block with a `Violation`; the generated module states the
result as a theorem (`airIsa_<hash>_wf`, by `decide`). -/

inductive Violation where
  /-- The declared operands are inconsistent (a location twice, a clobbered operand register). -/
  | declaration
  /-- Instruction `i` has no encoding or an undefined result at this width or operand kind. -/
  | noEncoding (i : Nat)
  /-- Instruction `i` accesses the memory operand `l` at another width than the operand's. -/
  | memWidth (i : Nat) (l : Loc)
  /-- Instruction `i` reads bits of `l` that neither an input nor the block defined. -/
  | undefinedRead (i : Nat) (l : Loc)
  /-- Instruction `i` reads the input `l` after a write to an output that may share its
  register. -/
  | staleRead (i : Nat) (l : Loc)
  /-- Instruction `i` writes `l`, which is neither an output nor a clobber (or is `rsp`). -/
  | undeclaredWrite (i : Nat) (l : Loc)
  /-- Output `k` does not hold defined bits at the end of the block. -/
  | outputUndefined (k : Nat)
  deriving DecidableEq, Repr

/-- Does the instruction exist in this form? -/
def Instr.encodable : Instr → Bool
  | .bin _ _ (.loc l) dst => !(l.isMem && dst.isMem)
  | .bin _ _ (.imm _) _ => true
  | .un .bswap w dst => (w = .w32 || w = .w64) && !dst.isMem
  | .un _ _ _ => true
  | .cnt _ w _ dst => w != .w8 && !dst.isMem
  | .xchg _ a b => !(a.isMem && b.isMem)
  | .div _ _ => true

def Src.reads (w : Width) : Src → List (Loc × Width)
  | .loc l => [(l, w)]
  | .imm _ => []

/-- The locations whose value the instruction's result depends on. `xor` and `sub` of a
location with itself give 0 whatever it held (the zeroing idiom). -/
def Instr.reads : Instr → List (Loc × Width)
  | .bin .mov w src _ => src.reads w
  | .bin op w src dst =>
    if (op = .xor || op = .sub) && src = .loc dst then [] else src.reads w ++ [(dst, w)]
  | .un _ w dst => [(dst, w)]
  | .cnt _ w src _ => [(src, w)]
  | .xchg w a b => [(a, w), (b, w)]
  | .div .w8 src => [(src, .w8), (rax, .w16)]
  | .div w src => [(src, w), (rax, w), (rdx, w)]

def Instr.writes : Instr → List (Loc × Width)
  | .bin _ w _ dst => [(dst, w)]
  | .un _ w dst => [(dst, w)]
  | .cnt _ w _ dst => [(dst, w)]
  | .xchg w a b => [(a, w), (b, w)]
  | .div .w8 _ => [(rax, .w16)]
  | .div w _ => [(rax, w), (rdx, w)]

/-- The check's state: how many low bits of each location are defined, and the inputs whose
register an output write may have reused. -/
structure Track where
  defined : Loc → Nat
  stale : List Loc

/-- No element twice. -/
def distinct : List Loc → Bool
  | [] => true
  | l :: rest => !rest.contains l && distinct rest

namespace Block

def inputLocs (b : Block) : List Loc := b.inputs.map (·.1)

def outputLocs (b : Block) : List Loc := b.outputs.map (·.1)

/-- A memory operand is a declared operand and is accessed at its own width. -/
def memWidthOk (b : Block) (l : Loc) (w : Width) : Bool :=
  !l.isMem || ((b.inputs ++ b.outputs).any (·.1 == l) &&
    (b.inputs ++ b.outputs).all fun lw => lw.1 != l || lw.2 == w)

def writable (b : Block) (l : Loc) : Bool :=
  l != rsp && (b.outputLocs.contains l ||
    match l with
    | .reg r => b.clobbers.contains r
    | _ => false)

/-- May the compiler give the input `i` and the output `o` one register? Not a register and a
memory operand, and not two different named registers. -/
def mayShare (i o : Loc) : Bool := i.isMem == o.isMem && !(i.isReg && o.isReg)

def declared (b : Block) : Bool :=
  distinct b.inputLocs && distinct b.outputLocs &&
    b.clobbers.all (fun r => !(b.inputLocs ++ b.outputLocs).contains (.reg r)) &&
    b.early.all (fun l => b.outputLocs.contains l && !b.inputLocs.contains l)

def checkReads (b : Block) (n : Nat) (t : Track) : List (Loc × Width) → Option Violation
  | [] => none
  | (l, w) :: rest =>
    if !b.memWidthOk l w then some (.memWidth n l)
    else if t.defined l < w.bits then some (.undefinedRead n l)
    else if t.stale.contains l then some (.staleRead n l)
    else checkReads b n t rest

def applyWrites (b : Block) (n : Nat) : List (Loc × Width) → Track → Except Violation Track
  | [], t => .ok t
  | (l, w) :: rest, t =>
    if !b.memWidthOk l w then .error (.memWidth n l)
    else if !b.writable l then .error (.undeclaredWrite n l)
    else applyWrites b n rest
      { defined := fun l' =>
          if l' = l then
            if l.isMem then w.bits
            else if w = .w32 || w = .w64 then 64
            else Nat.max (t.defined l) w.bits
          else t.defined l'
        stale :=
          if b.outputLocs.contains l && !b.early.contains l then
            t.stale ++ b.inputLocs.filter fun i => !b.outputLocs.contains i && mayShare i l
          else t.stale }

def checkOutputs (t : Track) : Nat → List (Loc × Width) → Option Violation
  | _, [] => none
  | k, (l, w) :: rest =>
    if t.defined l < w.bits then some (.outputUndefined k) else checkOutputs t (k + 1) rest

def checkFrom (b : Block) : Nat → List Instr → Track → Option Violation
  | _, [], t => checkOutputs t 0 b.outputs
  | n, i :: rest, t =>
    if !i.encodable then some (.noEncoding n)
    else match checkReads b n t i.reads with
      | some v => some v
      | none =>
        match applyWrites b n i.writes t with
        | .error v => some v
        | .ok t' => checkFrom b (n + 1) rest t'

/-- The first violation of the footprint rules, or `none` (see the section comment). -/
def check (b : Block) : Option Violation :=
  if !b.declared then some .declaration
  else checkFrom b 0 b.instrs
    { defined := fun l => ((b.inputs.find? (·.1 == l)).map (·.2.bits)).getD 0, stale := [] }

end Block

/-! ## A block without a faulting instruction never faults

The generic half of the fault guard: the translator omits the guard for a block that passed
`Block.check` and has no `Instr.mayFault` instruction. -/

theorem Instr.fault_eq_none {i : Instr} (he : i.encodable = true) (hf : i.mayFault = false)
    (s : State) : i.fault s = none := by
  cases i with
  | bin op w src dst => rfl
  | un op w dst =>
    cases op <;> first | rfl | (cases w <;> first | rfl | simp [Instr.encodable] at he)
  | cnt op w src dst => cases op <;> first | rfl | simp [Instr.mayFault] at hf
  | xchg w a b => rfl
  | div w src => simp [Instr.mayFault] at hf

theorem faultInstrs_eq_none {is : List Instr} (he : is.all Instr.encodable = true)
    (hf : is.any Instr.mayFault = false) (s : State) : faultInstrs is s = none := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at he
    simp only [List.any_cons, Bool.or_eq_false_iff] at hf
    simp [faultInstrs, Instr.fault_eq_none he.1 hf.1, ih he.2 hf.2]

/-! ## The simp set of a block

A generated `airIsa_<hash>` is `Block.out` of a literal block. `simp [zig_unfold]` runs the
block: the definitions above unfold (they are in `zig_unfold`), the state is a function that
is applied to literal locations, and the lemmas below remove the cuts and the `Nat` round trip
of `div` for operands that came from narrower `BitVec`s. What is left is a `BitVec` term over
the function's parameters. -/

attribute [zig_unfold] Block.out Block.fault runInstrs faultInstrs Instr.step Instr.fault
  initState State.get State.set Src.val BinOp.eval UnOp.eval CntOp.eval divOperands
  Width.bits Loc.isMem rax rdx

/-- A `BitVec n` as a number is below every `k ≥ 2 ^ n`: the cuts of a read vanish. -/
@[zig_unfold] theorem toNat_mod_of_pow_le {n : Nat} (v : BitVec n) {k : Nat} (h : 2 ^ n ≤ k) :
    v.toNat % k = v.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt h)

/-- The quotient of `div` with a zero upper half is `BitVec` division. -/
@[zig_unfold] theorem ofNat_toNat_div {n : Nat} (a b : BitVec n) :
    BitVec.ofNat n (a.toNat / b.toNat) = a / b := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)]

/-- The remainder of `div` with a zero upper half is `BitVec` remainder. -/
@[zig_unfold] theorem ofNat_toNat_mod {n : Nat} (a b : BitVec n) :
    BitVec.ofNat n (a.toNat % b.toNat) = a % b := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)]

/-- A quotient of an `n`-bit dividend fits `n` bits: no #DE for overflow. -/
@[zig_unfold] theorem pow_le_toNat_div {n : Nat} (a : BitVec n) (d : Nat) {k : Nat}
    (h : 2 ^ n ≤ k) : (k ≤ a.toNat / d) = False :=
  eq_false (Nat.not_le.mpr
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt) h))

@[zig_unfold] theorem toNat_eq_zero {n : Nat} (a : BitVec n) : (a.toNat = 0) = (a = 0) := by
  apply propext
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa using h
  · intro h
    simp [h]

end Zig.Isa.X86
