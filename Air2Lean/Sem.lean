import ZigLean.Mem
import Air2Lean.Air.Op
import Air2Lean.SemAttr

/-!
# Formal semantics of canonical AIR (fragment)

A definitional interpreter for the decoded, canonical AIR that the translator reads
(`Air2Lean.Func`, the output of `Air2Lean.normalize`). It is stated over the translator's own
input datatypes, not over the generated Lean, so a theorem relating the two is a statement
about the translation (`docs/air-semantics.md`).

The fragment:

* values: integers of any width with their signedness, `bool`, `void`, and a single or many
  pointer (`Zig.Ptr`); the SSA environment records each value's AIR type, so an access takes
  its alignment and pointee from the pointer's type;
* integer arithmetic (`add`/`sub`/`mul` checked, wrapping and saturating; division and
  remainder; `min`/`max`; bitwise `and`/`or`/`xor`/`not`), comparisons, `bool_and`/`bool_or`,
  `intcast` and `trunc`;
* control flow: `block`/`br`, `cond_br`, `switch_br` on an integer, `loop`/`repeat`, `ret`,
  `unreach`, `trap`, and a call to a safety-panic handler;
* memory, ZigLean's byte-level `Zig.Mem` (`Zig.MemM`): `alloc` makes a stack block
  (`Zig.allocStack`) freed when the function returns; `load`/`store` of an integer, `bool` or
  pointer go through `Zig.load`/`Zig.store` at the pointer type's alignment (`store` of
  `undefined`: `Zig.storeUndef`); `struct_field_ptr` of a non-`packed` struct is
  `Zig.ptrProject` by the field's offset; a pointer `bitcast` keeps the pointer; `==`/`!=` and
  the order of two pointers compare their addresses (`Zig.ptrEqAddr`, `Zig.ptrLt`, `Zig.ptrLe`);
* direct calls through an oracle (`Ctx.call`); `run` ties the oracle to the program;
* debug instructions have no effect.

Every other instruction, value or shape is *stuck*: it denotes `⊥` (no behaviour, `Option`'s
`none`). The arithmetic primitives are ZigLean's (`Zig.add`, `Zig.intCast`, …): this file fixes
the meaning of the AIR *program structure* (SSA dataflow, operand typing, control flow, locals,
calls) over those primitives. The primitives' own fidelity to Zig is a separate premise
(`docs/air-semantics.md` §Trusted base).

There is one memory model: the one the generated code of a memory-using function runs in.
-/

namespace Air2Lean.Sem

open Zig

/-- A runtime value of the fragment. An integer carries its AIR signedness and width. -/
inductive Value where
  | int (signed : Bool) (w : Nat) (v : BitVec w)
  | bool (b : Bool)
  | void
  /-- A single or many pointer. Its alignment and pointee come from its AIR type (`Env`). -/
  | ptr (p : Zig.Ptr)
  deriving DecidableEq, Inhabited

/-- No behaviour: an ill-typed or out-of-fragment step. Distinct from every panic
(`Zig.Error`): it is `Option`'s `none`, the bottom of `Zig.Result`'s order. -/
def stuck {α : Type} : Result α := ExceptT.mk none

/-- SSA environment: the AIR type and the value of each instruction that has run. -/
abbrev Env := InstId → Option (TyId × Value)

/-- The stack blocks the running function has allocated, in allocation order. -/
abbrev Frame := List Zig.Ptr

def Env.set (env : Env) (id : InstId) (t : TyId) (v : Value) : Env :=
  fun j => if j = id then some (t, v) else env j

/-- How a body ends: `br` to a block (with its value), `repeat` of a loop, or `ret`. -/
inductive Exit where
  | br (target : InstId) (v : Value)
  | rep (target : InstId)
  | ret (v : Value)
  deriving DecidableEq, Inhabited

/-- A call oracle: the meaning of a direct call by fully qualified name. -/
abbrev Oracle := String → List Value → MemM Value

/-- Everything a body needs besides its environment: the function (its type table) and a
call oracle for direct calls by fully qualified name. -/
structure Ctx where
  func : Func
  /-- The runtime arguments, in parameter order. -/
  args : List Value
  call : Oracle

def tyOf (f : Func) (t : TyId) : Ty := f.types[t]?.getD .void

/-- A constant of an integer type as the bit vector the generated code writes:
`n` for `n ≥ 0`, `-(|n|)` otherwise (both equal `BitVec.ofInt w n`, `litBV_eq_ofInt`). -/
def litBV (w : Nat) (n : Int) : BitVec w :=
  if n < 0 then -(BitVec.ofNat w (-n).toNat) else BitVec.ofNat w n.toNat

theorem litBV_eq_ofInt (w : Nat) (n : Int) : litBV w n = BitVec.ofInt w n := by
  unfold litBV
  split
  · rename_i h
    have : n = -((-n).toNat : Int) := by omega
    conv => rhs; rw [this]
    rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · rename_i h
    have : n = (n.toNat : Int) := by omega
    conv => rhs; rw [this]
    rw [BitVec.ofInt_natCast]

/-- An operand's value. -/
def operand (f : Func) (env : Env) : Val → Result Value
  | .inst id => match env id with
    | some (_, v) => pure v
    | none => stuck
  | .int t n => match tyOf f t with
    | .int s w => pure (.int s w (litBV w n))
    | _ => stuck
  | .bool b => pure (.bool b)
  | .void => pure .void
  | _ => stuck

/-- An operand's AIR type: an instruction's from the environment, a constant's own. -/
def operandTy (env : Env) : Val → Option TyId
  | .inst id => (env id).map (·.1)
  | v => v.constTy?

/-- An integer operand of width `w`. -/
def Value.asInt (w : Nat) : Value → Result (BitVec w)
  | .int _ w' v => if h : w' = w then pure (v.cast h) else stuck
  | _ => stuck

def Value.asBool : Value → Result Bool
  | .bool b => pure b
  | _ => stuck

/-- The integer type of an instruction's result, or `none`. -/
def intTy? (f : Func) (t : TyId) : Option (Bool × Nat) :=
  match tyOf f t with
  | .int s w => some (s, w)
  | _ => none

def arithFn (op : ArithOp) (mode : Mode) (s : Bool) {w : Nat} (a b : BitVec w) : Result (BitVec w) :=
  match op, mode with
  | .add, .checked => Zig.add s a b
  | .add, .wrap => pure (Zig.addWrap a b)
  | .add, .sat => pure (Zig.addSat s a b)
  | .sub, .checked => Zig.sub s a b
  | .sub, .wrap => pure (Zig.subWrap a b)
  | .sub, .sat => pure (Zig.subSat s a b)
  | .mul, .checked => Zig.mul s a b
  | .mul, .wrap => pure (Zig.mulWrap a b)
  | .mul, .sat => pure (Zig.mulSat s a b)

def divFn (op : DivOp) (s : Bool) {w : Nat} (a b : BitVec w) : Result (BitVec w) :=
  match op with
  | .divTrunc => Zig.divTrunc s a b
  | .divFloor => Zig.divFloor s a b
  | .divExact => Zig.divExact s a b
  | .rem => Zig.rem s a b
  | .mod => Zig.mod s a b
  | .divCeil => Zig.divCeil s a b

def bitFn (op : BitOp) {w : Nat} (a b : BitVec w) : BitVec w :=
  match op with
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b

def cmpFn (op : CmpOp) (s : Bool) {w : Nat} (a b : BitVec w) : Bool :=
  match op with
  | .lt => Zig.lt s a b
  | .le => Zig.le s a b
  | .gt => Zig.gt s a b
  | .ge => Zig.ge s a b
  | .eq => a == b
  | .ne => a != b

/-- A binary integer operation whose operands and result have the instruction's type. -/
def intBin (f : Func) (env : Env) (ty : TyId) (a b : Val)
    (k : Bool → (w : Nat) → BitVec w → BitVec w → Result (BitVec w)) : Result Value :=
  match intTy? f ty with
  | some (s, w) => do
    let x ← (← operand f env a).asInt w
    let y ← (← operand f env b).asInt w
    let r ← k s w x y
    pure (.int s w r)
  | none => stuck

/-- The panic of a call to a safety-panic handler: Zig's default panic handler and the
non-generic members of `debug.FullPanic(defaultPanic)`, by exact name. The same classification
as the translator's `panicErrorFor?` (`docs/generated-code.md` §Panics) for these names; a
generic member (`inactiveUnionField__anon_<n>`) is outside the fragment. Stated as a literal
table so that a proof can evaluate it. -/
def panicOf? : String → Option Zig.Error
  | "debug.defaultPanic" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).integerOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).integerOutOfBounds" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).integerPartOutOfBounds" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).shlOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).shrOverflow" => some .overflow
  | "debug.FullPanic((function 'defaultPanic')).outOfBounds" => some .outOfBounds
  | "debug.FullPanic((function 'defaultPanic')).startGreaterThanEnd" => some .outOfBounds
  | "debug.FullPanic((function 'defaultPanic')).divideByZero" => some .divByZero
  | "debug.FullPanic((function 'defaultPanic')).reachedUnreachable" => some .unreachable
  | "debug.FullPanic((function 'defaultPanic')).exactDivisionRemainder" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).unwrapNull" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).unwrapError" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).forLenMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).invalidEnumValue" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).corruptSwitch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).call" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).sentinelMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).copyLenMismatch" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).memcpyAlias" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).castToNull" => some .panic
  | "debug.FullPanic((function 'defaultPanic')).incorrectAlignment" => some .panic
  | _ => none

/-- The value of one straight-line instruction (no control flow, memory or calls). -/
def evalPure (f : Func) (env : Env) (i : Inst) : Result Value :=
  match i.op with
  | .arith op mode a b => intBin f env i.ty a b fun s _ x y => arithFn op mode s x y
  | .div op a b => intBin f env i.ty a b fun s _ x y => divFn op s x y
  | .minMax isMax a b => intBin f env i.ty a b fun s _ x y =>
      pure (if isMax then Zig.max s x y else Zig.min s x y)
  | .bit op a b => match tyOf f i.ty with
    | .bool => do
      let x ← (← operand f env a).asBool
      let y ← (← operand f env b).asBool
      pure (.bool (match op with | .and => x && y | .or => x || y | .xor => x ^^ y))
    | _ => intBin f env i.ty a b fun _ _ x y => pure (bitFn op x y)
  | .not a => match tyOf f i.ty with
    | .bool => do pure (.bool (!(← (← operand f env a).asBool)))
    | .int s w => do pure (.int s w (~~~(← (← operand f env a).asInt w)))
    | _ => stuck
  | .cmp op a b => do
    match ← operand f env a with
    | .int s w x => do
      let y ← (← operand f env b).asInt w
      pure (.bool (cmpFn op s x y))
    | .bool x => match op with
      | .eq => do pure (.bool (x == (← (← operand f env b).asBool)))
      | .ne => do pure (.bool (x != (← (← operand f env b).asBool)))
      | _ => stuck
    | _ => stuck
  | .boolAnd a b => do
    let x ← (← operand f env a).asBool
    let y ← (← operand f env b).asBool
    pure (.bool (x && y))
  | .boolOr a b => do
    let x ← (← operand f env a).asBool
    let y ← (← operand f env b).asBool
    pure (.bool (x || y))
  | .intCast a => match intTy? f i.ty with
    | some (s₂, m) => do
      match ← operand f env a with
      | .int s₁ _ x => pure (.int s₂ m (← Zig.intCast s₁ s₂ m x))
      | _ => stuck
    | none => stuck
  | .trunc a => match intTy? f i.ty with
    | some (s₂, m) => do
      match ← operand f env a with
      | .int _ _ x => pure (.int s₂ m (Zig.trunc m x))
      | _ => stuck
    | none => stuck
  | _ => stuck

/-- Does the integer `x` select this `switch_br` case (an item equal, or inside a range)? -/
def caseHit (f : Func) (env : Env) (s : Bool) {w : Nat} (x : BitVec w) (sc : SwitchCase) :
    Result Bool := do
  let items ← sc.items.toList.mapM fun it => do pure (x == (← (← operand f env it).asInt w))
  let ranges ← sc.ranges.toList.mapM fun (lo, hi) => do
    let l ← (← operand f env lo).asInt w
    let h ← (← operand f env hi).asInt w
    pure (Zig.le s l x && Zig.le s x h)
  pure ((items ++ ranges).foldr (· || ·) false)

/-- Does `e` repeat the loop `id`? -/
def Exit.again (id : InstId) : Exit → Bool
  | .rep t => t == id
  | _ => false

/-- A body runs over the memory, with its stack frame. -/
abbrev SM := Zig.MM Frame

theorem sizeOf_toList {α : Type} [SizeOf α] (a : Array α) : sizeOf a.toList = sizeOf a - 1 := by
  cases a; simp

theorem sizeOf_case_body (sc : SwitchCase) : sizeOf sc.body < sizeOf sc := by
  cases sc; simp; omega

def liftR {α : Type} (x : Result α) : SM α := StateT.lift (StateT.lift x)

def liftMem {α : Type} (x : MemM α) : SM α := StateT.lift x

/-- The size and ABI alignment of a type, from the export's layout table. -/
def layoutOf (f : Func) (t : TyId) : Option (Nat × Nat) := do
  let l ← f.layouts[t]?
  pure (← l.size, ← l.align)

/-- The `align(N)` of a pointer type. -/
def ptrAlignOf (f : Func) (t : TyId) : Option Nat := (f.layouts[t]?).bind (·.ptrAlign)

/-- A single or many pointer type through which an access is an ordinary memory access: not a
slice, not `volatile` (a device access, L13) and not a bit-pointer into a packed field. -/
def plainPtr (f : Func) (t : TyId) : Bool :=
  match tyOf f t, f.layouts[t]? with
  | .ptr size _ _, some l => (size == "one" || size == "many") && !l.isVolatile && l.hostSize == 0
  | _, _ => false

/-- The pointee type of a pointer type. -/
def pointee? (f : Func) (t : TyId) : Option TyId :=
  match tyOf f t with
  | .ptr _ _ c => some c
  | _ => none

/-- The pointer operand `v`, with the alignment of its (plain) pointer type. -/
def ptrOperand (f : Func) (env : Env) (v : Val) : Result (Zig.Ptr × Nat) := do
  match operandTy env v with
  | some t =>
    match plainPtr f t, ptrAlignOf f t, ← operand f env v with
    | true, some a, .ptr p => pure (p, a)
    | _, _, _ => stuck
  | none => stuck

/-- Load a value of the AIR type `t`. -/
def loadAs (f : Func) (t : TyId) (p : Zig.Ptr) (align : Nat) : MemM Value :=
  match tyOf f t with
  | .int s w => do pure (.int s w (← Zig.load (BitVec w) align p))
  | .bool => do pure (.bool (← Zig.load Bool align p))
  | .ptr .. => if plainPtr f t then do pure (.ptr (← Zig.load Zig.Ptr align p)) else StateT.lift stuck
  | _ => StateT.lift stuck

/-- Store the operand `v` (an integer, `bool` or pointer); `undefined` makes the bytes of its
type undefined. -/
def storeAs (f : Func) (env : Env) (p : Zig.Ptr) (align : Nat) (v : Val) : MemM Unit :=
  match v with
  | .undef t => match tyOf f t with
    | .int _ w => Zig.storeUndef (BitVec w) align p
    | .bool => Zig.storeUndef Bool align p
    | .ptr .. => if plainPtr f t then Zig.storeUndef Zig.Ptr align p else StateT.lift stuck
    | _ => StateT.lift stuck
  | v => do
    match ← StateT.lift (operand f env v) with
    | .int _ _ x => Zig.store align p x
    | .bool b => Zig.store align p b
    | .ptr q => Zig.store align p q
    | _ => StateT.lift stuck

/-- The byte offset of field `idx` of the non-`packed` struct that a pointer of type `t` points
to. -/
def fieldOffset? (f : Func) (t : TyId) (idx : Nat) : Option Nat := do
  let s ← pointee? f t
  match tyOf f s with
  | .struct _ layout _ => if layout == "packed" then none else (← f.layouts[s]?).offsets[idx]?
  | _ => none

/-- The value of an instruction that may access memory but has no control flow and makes no
call: the straight-line operations (`evalPure`), `load`, `store`, `struct_field_ptr`, a pointer
`bitcast` and pointer comparisons. -/
def evalMem (f : Func) (env : Env) (i : Inst) : MemM Value :=
  match i.op with
  | .load p => do
    let (q, a) ← StateT.lift (ptrOperand f env p)
    loadAs f i.ty q a
  | .store p v => do
    let (q, a) ← StateT.lift (ptrOperand f env p)
    storeAs f env q a v
    pure .void
  | .fieldPtr base idx => do
    let (q, _) ← StateT.lift (ptrOperand f env base)
    match (operandTy env base).bind (fieldOffset? f · idx), plainPtr f i.ty with
    | some off, true => do pure (.ptr (← Zig.ptrProject q (·.add off)))
    | _, _ => StateT.lift stuck
  | .bitcast a =>
    if plainPtr f i.ty then do
      let (q, _) ← StateT.lift (ptrOperand f env a)
      pure (.ptr q)
    else StateT.lift stuck
  | .cmp op a b => do
    match ← StateT.lift (operand f env a) with
    | .ptr _ => do
      let (p, _) ← StateT.lift (ptrOperand f env a)
      let (q, _) ← StateT.lift (ptrOperand f env b)
      match op with
      | .eq => do pure (.bool (← Zig.ptrEqAddr p q))
      | .ne => do pure (.bool (!(← Zig.ptrEqAddr p q)))
      | .lt => do pure (.bool (← Zig.ptrLt p q))
      | .le => do pure (.bool (← Zig.ptrLe p q))
      | .gt => do pure (.bool (← Zig.ptrLt q p))
      | .ge => do pure (.bool (← Zig.ptrLe q p))
    | _ => StateT.lift (evalPure f env i)
  | _ => StateT.lift (evalPure f env i)

mutual

/-- Run an instruction sequence until it exits. Falling off the end is stuck (a well-formed
body ends in a terminator). -/
def execBody (c : Ctx) : List Inst → Env → SM Exit
  | [], _ => liftR stuck
  | i :: rest, env => execInst c i rest env
termination_by l => (sizeOf l, 0)

/-- Run `i`, then (unless it exits) `rest`. -/
def execInst (c : Ctx) (i : Inst) (rest : List Inst) (env : Env) : SM Exit :=
  match _h : i.op with
  | .arg index =>
    match c.args[index]? with
    | some v => execBody c rest (env.set i.id i.ty v)
    | none => liftR stuck
  | .block body => do
    let e ← execBody c body.toList env
    match e with
    | .br t v => if t = i.id then execBody c rest (env.set i.id i.ty v) else pure e
    | _ => pure e
  | .loop body =>
    -- A loop never falls through: it repeats on its own `repeat` and otherwise propagates.
    Zig.loop (execBody c body.toList env) (Exit.again i.id)
  | .br t v => do pure (.br t (← liftR (operand c.func env v)))
  | .«repeat» t => pure (.rep t)
  | .ret v => do pure (.ret (← liftR (operand c.func env v)))
  | .unreach => liftR (throw .unreachable)
  | .trap => liftR (throw .panic)
  | .condBr cv th el => do
    if ← liftR ((← liftR (operand c.func env cv)).asBool) then execBody c th.toList env
    else execBody c el.toList env
  | .switchBr v cases el => do
    match ← liftR (operand c.func env v) with
    | .int s _ x => execSwitch c s x cases.toList el env
    | _ => liftR stuck
  | .alloc => do
    -- The block's alignment is the pointer type's `align(N)` (MM-1).
    match (pointee? c.func i.ty).bind (layoutOf c.func), ptrAlignOf c.func i.ty with
    | some (size, _), some align => do
      let p ← liftMem (Zig.allocStack size align)
      modify (· ++ [p])
      execBody c rest (env.set i.id i.ty (.ptr p))
    | _, _ => liftR stuck
  | .call (.func name _ _) args => do
    match panicOf? name with
    | some e => liftR (throw e)
    | none => do
      let vs ← liftR (args.toList.mapM (operand c.func env))
      let v ← liftMem (c.call name vs)
      execBody c rest (env.set i.id i.ty v)
  | .line _ => execBody c rest env
  | .dbg _ _ => execBody c rest env
  | _ => do
    let v ← liftMem (evalMem c.func env i)
    execBody c rest (env.set i.id i.ty v)
termination_by (sizeOf i + sizeOf rest, 1)
decreasing_by
  all_goals
    obtain ⟨id, ty, op⟩ := i
    simp only at _h
    subst _h
    simp_wf
    try simp only [sizeOf_toList]
    omega

/-- `switch_br`'s case chain: the first case that `x` selects, else the `else` body. -/
def execSwitch (c : Ctx) (s : Bool) {w : Nat} (x : BitVec w) :
    List SwitchCase → Array Inst → Env → SM Exit
  | [], el, env => execBody c el.toList env
  | sc :: more, el, env => do
    if ← liftR (caseHit c.func env s x sc) then execBody c sc.body.toList env
    else execSwitch c s x more el env
termination_by l el => (sizeOf l + sizeOf el, 0)
decreasing_by
  all_goals simp_wf
  all_goals try simp only [sizeOf_toList]
  all_goals (try have := sizeOf_case_body sc); omega

end

/-- Does `v` have the AIR type `t`? Only the fragment's parameter types (integers, `bool`,
`void`, single and many pointers) have values here. -/
def valOk (t : Ty) (v : Value) : Bool :=
  match t, v with
  | .int s w, .int s' w' _ => s == s' && w == w'
  | .bool, .bool _ => true
  | .void, .void => true
  | .ptr size _ _, .ptr _ => size == "one" || size == "many"
  | _, _ => false

/-- Do the arguments match the parameter types, one for one? -/
def argsOk (f : Func) : List TyId → List Value → Bool
  | [], [] => true
  | t :: ts, v :: vs => valOk (tyOf f t) v && argsOk f ts vs
  | _, _ => false

/-- Run a function on its argument values: an empty SSA environment (each `arg` instruction
binds its parameter) and no local cells. A call whose arguments do not match the parameter
types, and a function that ends other than by `ret`, are stuck. -/
def execFunc (call : Oracle) (f : Func) (args : List Value) : MemM Value :=
  if argsOk f f.params.toList args then do
    let (e, frame) ← (execBody ⟨f, args, call⟩ f.body.toList (fun _ => none)).run []
    -- The stack frame ends at the return (a panic leaves the memory behind).
    frame.forM Zig.free
    match e with
    | .ret v => pure v
    | _ => StateT.lift stuck
  else StateT.lift stuck

/-- The integer an `int` value holds, at width `w` (`0` for any other value). -/
def Value.toBV (w : Nat) : Value → BitVec w
  | .int _ w' v => if h : w' = w then v.cast h else 0
  | _ => 0

def Value.toBool : Value → Bool
  | .bool b => b
  | _ => false

/-- The pointer a `ptr` value holds (`Zig.Ptr.null` for any other value). -/
def Value.toPtr : Value → Zig.Ptr
  | .ptr p => p
  | _ => Zig.Ptr.null

theorem argsOk_nil {f : Func} {args : List Value} (h : argsOk f [] args = true) : args = [] := by
  cases args <;> simp_all [argsOk]

theorem argsOk_cons {f : Func} {t : TyId} {ts : List TyId} {args : List Value}
    (h : argsOk f (t :: ts) args = true) :
    ∃ v vs, args = v :: vs ∧ valOk (tyOf f t) v = true ∧ argsOk f ts vs = true := by
  cases args with
  | nil => simp [argsOk] at h
  | cons v vs => simp only [argsOk, Bool.and_eq_true] at h; exact ⟨v, vs, rfl, h⟩

theorem valOk_int {s : Bool} {w : Nat} {v : Value} (h : valOk (.int s w) v = true) :
    v = .int s w (v.toBV w) := by
  cases v <;> simp_all [valOk, Value.toBV]
  obtain ⟨rfl, rfl⟩ := h; simp

theorem valOk_bool {v : Value} (h : valOk .bool v = true) : v = .bool v.toBool := by
  cases v <;> simp_all [valOk, Value.toBool]

theorem valOk_void {v : Value} (h : valOk .void v = true) : v = .void := by
  cases v <;> simp_all [valOk]

theorem valOk_ptr {size : String} {c : Bool} {t : TyId} {v : Value}
    (h : valOk (.ptr size c t) v = true) : v = .ptr v.toPtr := by
  cases v <;> simp_all [valOk, Value.toPtr]

/-! ## Programs -/

section Monotone
open Lean.Order

theorem monotone_liftMem {γ α : Type} [PartialOrder γ] (g : γ → MemM α) (hg : monotone g) :
    monotone (fun x => liftMem (g x)) := by
  apply monotone_of_monotone_apply; intro fr
  show monotone (fun x => (g x) >>= fun a => pure (a, fr))
  exact monotone_bind _ _ _ hg (monotone_const _)

/-- `Zig.monotone_loop` for a body over memory (`Zig.MM`). -/
theorem monotone_loopMM {σ ε γ : Type} [PartialOrder γ] (f : γ → Zig.MM σ ε) (again : ε → Bool)
    (hmono : monotone f) : monotone (fun (x : γ) => Zig.loop (f x) again) := by
  intro x1 x2 hx
  have hle : f x1 ⊑ f x2 := hmono x1 x2 hx
  apply Zig.loop.fixpoint_induct (f x1) again (motive := fun v => v ⊑ Zig.loop (f x2) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [Zig.loop.eq_1 (f x2) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

local macro "mono_step" : tactic => `(tactic| first
  | exact monotone_const _
  | (dsimp only; exact monotone_const _)
  | assumption
  | (apply_assumption <;> rfl)
  | (apply monotone_apply; first | assumption | apply_assumption)
  | (apply monotone_loopMM)
  | (apply monotone_bind)
  | (apply monotone_ite)
  | split
  | (apply monotone_of_monotone_apply; intro))

/-- A body is monotone in its call oracle: a more defined callee gives a more defined
caller. -/
theorem execBody_mono (f : Func) (args : List Value) :
    ∀ l env, monotone (fun o : Oracle => execBody ⟨f, args, o⟩ l env) := by
  apply execBody.induct ⟨f, args, fun _ _ => StateT.lift stuck⟩
    (motive2 := fun i rest env => monotone (fun o : Oracle => execInst ⟨f, args, o⟩ i rest env))
    (motive3 := fun s w x cs el env => monotone (fun o : Oracle => execSwitch ⟨f, args, o⟩ s x cs el env))
  case case1 => intros; simp only [execBody]; exact monotone_const _
  case case2 => intros; simp only [execBody]; assumption
  case case21 => intros; simp only [execSwitch]; assumption
  case case22 => intros; unfold execSwitch; repeat' mono_step
  case case20 =>
    intro i rest env n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 ih
    unfold execInst
    split <;> (try (exfalso; first
      | exact n1 _ ‹_› | exact n2 _ ‹_› | exact n3 _ ‹_› | exact n4 _ _ ‹_› | exact n5 _ ‹_›
      | exact n6 _ ‹_› | exact n7 ‹_› | exact n8 ‹_› | exact n9 _ _ _ ‹_› | exact n10 _ _ _ ‹_›
      | exact n11 ‹_› | exact n12 _ _ _ _ ‹_› | exact n13 _ ‹_› | exact n14 _ _ ‹_›))
    apply monotone_bind
    · first | exact monotone_const _ | (dsimp only; exact monotone_const _)
    · apply monotone_of_monotone_apply; intro v; exact ih v
  case case17 =>
    intro i; obtain ⟨id, ty, op⟩ := i; intro rest env; intros
    simp only at *
    subst_vars
    simp only [execInst]
    try simp only [*]
    apply monotone_bind
    · first | exact monotone_const _ | (dsimp only; exact monotone_const _)
    · apply monotone_of_monotone_apply; intro vs
      apply monotone_bind
      · apply monotone_liftMem
        exact monotone_apply _ _ (monotone_apply _ _ monotone_id)
      · apply monotone_of_monotone_apply; intro v; apply_assumption
  all_goals
    intro i; obtain ⟨id, ty, op⟩ := i; intro rest env; intros
    simp only at *
    subst_vars
    simp only [execInst]
    try simp only [*]
    repeat' mono_step

@[partial_fixpoint_monotone]
theorem execFunc_mono {γ : Type} [PartialOrder γ] (g : γ → Oracle) (hg : monotone g)
    (f : Func) (args : List Value) : monotone (fun x => execFunc (g x) f args) := by
  unfold execFunc
  apply monotone_ite _ _ _ _ (monotone_const _)
  apply monotone_bind
  · exact monotone_compose (g := fun o : Oracle =>
      (execBody ⟨f, args, o⟩ f.body.toList (fun _ => none)).run []) hg
      (monotone_stateTRun _ (execBody_mono f args _ _) _)
  · exact monotone_const _

end Monotone


/-- A program: its functions by fully qualified name. -/
abbrev Prog := String → Option Func

/-- The semantics of a program: the least oracle that each function's body satisfies (the
least fixpoint of `execFunc`, in `Zig.MemM`'s order where non-termination and stuck states
are the bottom). A call to a name outside the program is stuck. -/
def run (p : Prog) (name : String) (args : List Value) : MemM Value :=
  match p name with
  | some f => execFunc (run p) f args
  | none => StateT.lift stuck
partial_fixpoint

open Lean.Order in
/-- Soundness of any fixpoint: if an oracle `G` satisfies every function's equation on
well-typed arguments (`execFunc G f args = G name args`), the program semantics is below it.
So every terminating AIR behaviour (a value or a panic) is `G`'s behaviour too
(`Result.eq_of_le`). -/
theorem run_le_of_fixpoint (p : Prog) (G : Oracle)
    (hG : ∀ name f args, p name = some f → argsOk f f.params.toList args = true →
      execFunc G f args = G name args) :
    run p ⊑ G := by
  apply run.fixpoint_induct p (motive := fun r => r ⊑ G)
  · exact fun c hc h => csup_le hc h
  · intro r hr name args
    show (match p name with | some f => execFunc r f args | none => StateT.lift stuck) ⊑ G name args
    split
    · rename_i f hf
      by_cases ht : argsOk f f.params.toList args = true
      · rw [← hG name f args hf ht]
        exact execFunc_mono (fun o : Oracle => o) monotone_id f args _ _ hr
      · simp only [execFunc, ht]
        intro m; exact FlatOrder.rel.bot
    · intro m; exact FlatOrder.rel.bot

theorem run_of_lookup {p : Prog} {name : String} {f : Func} (h : p name = some f)
    (args : List Value) : run p name args = execFunc (run p) f args := by
  rw [run]; simp only [h]

open Lean.Order in
/-- In `Zig.Result`'s order a defined result is maximal: below means equal. -/
theorem Result.eq_of_le {α : Type} {x y : Result α} (h : x ⊑ y) (hx : x ≠ stuck) : x = y := by
  cases h with
  | bot => exact absurd rfl hx
  | refl => rfl

section Complete
open Lean.Order

/-! For the converse of `run_le_of_fixpoint` on a generated `partial_fixpoint` clique: its
`fixpoint_induct` needs these admissibility facts for a motive "the generated function, encoded,
is below `run`" at each arity. -/

theorem rel_of_eq {α : Type} [PartialOrder α] {x y : α} (h : x = y) : x ⊑ y := by
  subst h; exact PartialOrder.rel_refl

theorem adm_app0 {β γ : Type} (f : β → γ) (c : Result γ) :
    admissible (fun x : Result β => f <$> x ⊑ c) := by
  apply admissible_flatOrder (b := (none : Option (Except Zig.Error β)))
  exact FlatOrder.rel.bot

theorem adm_app1 {A β γ : Type} (f : β → γ) (a : A) (c : Result γ) :
    admissible (fun g : A → Result β => f <$> g a ⊑ c) :=
  admissible_apply (fun _ (r : Result β) => f <$> r ⊑ c) a (adm_app0 f c)

theorem adm_app2 {A B β γ : Type} (f : β → γ) (a : A) (b : B) (c : Result γ) :
    admissible (fun g : A → B → Result β => f <$> g a b ⊑ c) :=
  admissible_apply (fun _ (h : B → Result β) => f <$> h b ⊑ c) a (adm_app1 f b c)

theorem adm_app3 {A B C β γ : Type} (f : β → γ) (a : A) (b : B) (d : C) (c : Result γ) :
    admissible (fun g : A → B → C → Result β => f <$> g a b d ⊑ c) :=
  admissible_apply (fun _ (h : B → C → Result β) => f <$> h b d ⊑ c) a (adm_app2 f b d c)

theorem adm_app4 {A B C D β γ : Type} (f : β → γ) (a : A) (b : B) (d : C) (e : D) (c : Result γ) :
    admissible (fun g : A → B → C → D → Result β => f <$> g a b d e ⊑ c) :=
  admissible_apply (fun _ (h : B → C → D → Result β) => f <$> h b d e ⊑ c) a (adm_app3 f b d e c)

theorem execFunc_le {o₁ o₂ : Oracle} (h : o₁ ⊑ o₂) (f : Func) (args : List Value) :
    execFunc o₁ f args ⊑ execFunc o₂ f args :=
  execFunc_mono (fun o : Oracle => o) monotone_id f args _ _ h

end Complete

/-- A program as a table of fully qualified names and functions (`progOf`). -/
abbrev Table := List (String × Func)

def progOf (t : Table) : Prog := fun name => (t.find? (·.1 == name)).map (·.2)

/-- Every function of the table satisfies its equation under `G` on well-typed arguments. -/
def Fixpoint (G : Oracle) : Table → Prop
  | [] => True
  | (n, f) :: t =>
    (∀ args, argsOk f f.params.toList args = true → execFunc G f args = G n args) ∧ Fixpoint G t

theorem run_le_of_table {t : Table} {G : Oracle} (h : Fixpoint G t) :
    Lean.Order.PartialOrder.rel (run (progOf t)) G := by
  apply run_le_of_fixpoint
  intro name f args hp
  induction t with
  | nil => simp [progOf] at hp
  | cons e t ih =>
    obtain ⟨n, g⟩ := e
    obtain ⟨hn, ht⟩ := h
    simp only [progOf, List.find?_cons] at hp
    by_cases he : n = name
    · subst he
      simp only [beq_self_eq_true, Option.map_some, Option.some.injEq] at hp
      subst hp
      exact hn args
    · have : (n == name) = false := by simp [he]
      simp only [this] at hp
      exact ih ht hp

/-! ## Normalization lemmas for certificates -/

namespace Cert

theorem throw_bind {α β : Type} (e : Zig.Error) (f : α → Result β) :
    (throw e : Result α) >>= f = throw e := rfl

theorem run_throw {σ α : Type} (e : Zig.Error) (s : σ) :
    (throw e : Zig.M σ α).run s = throw e := rfl

theorem run_throwMM {σ α : Type} (e : Zig.Error) (s : σ) :
    (throw e : Zig.MM σ α).run s = throw e := rfl

theorem run_throwMem {α : Type} (e : Zig.Error) (s : Zig.Mem) :
    (throw e : Zig.MemM α).run s = throw e := rfl

theorem map_throw {α β : Type} (e : Zig.Error) (f : α → β) :
    f <$> (throw e : Result α) = throw e := rfl

theorem free_nil : List.forM ([] : Frame) Zig.free = pure () := rfl

theorem bind_ite {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → m β) : (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem map_ite {m : Type → Type} [Functor m] {α β : Type} (c : Prop) [Decidable c]
    (a b : m α) (f : α → β) : f <$> (if c then a else b) = if c then f <$> a else f <$> b := by
  split <;> rfl

theorem run_ite' {m : Type → Type} {σ α : Type} (c : Prop) [Decidable c] (a b : StateT σ m α) (s : σ) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  split <;> rfl

/-- A zero-offset projection is the pointer itself (no instruction natively). -/
theorem ptrProject_add_zero (p : Zig.Ptr) : Zig.ptrProject p (·.add 0) = pure p := by
  have h : p.add 0 = p := by cases p; simp [Zig.Ptr.add]
  funext m
  simp only [Zig.ptrProject, h, true_or, ite_true]
  rfl

/-- A field offset, a natural-number literal, as the integer literal the generated code writes. -/
theorem natCast_ofNat (n : Nat) : ((no_index (OfNat.ofNat n : Nat)) : Int) = (OfNat.ofNat n : Int) := rfl

attribute [air_sem] execFunc argsOk valOk execBody execInst execSwitch caseHit evalPure intBin intTy? tyOf
  evalMem ptrOperand operandTy plainPtr loadAs storeAs fieldOffset? pointee? ptrAlignOf layoutOf
  Val.constTy? Value.toPtr ptrProject_add_zero Zig.callM Zig.callR
  Bool.true_or Bool.or_true Bool.not_false Bool.not_true Bool.false_and Bool.and_false
  Option.map_some Option.map_none Option.bind_some Option.bind_none Option.pure_def
  Option.bind_eq_bind String.reduceBEq String.reduceBNe Nat.reduceBEq Nat.reduceBNe Option.getD_none
  Bool.false_eq_true Bool.true_eq_false natCast_ofNat Int.natCast_zero
  operand Env.set Value.asInt Value.asBool arithFn divFn cmpFn bitFn liftR litBV Exit.again
  bind_ite map_ite run_ite' throw_bind map_throw run_throw run_throwMM run_throwMem Zig.call liftMem free_nil
  Array.toList List.mapM_cons List.mapM_nil List.getElem?_toArray Option.getD_some
  List.getElem_cons_zero StateT.run'_eq StateT.run_bind StateT.run_pure StateT.run_map
  StateT.run_lift StateT.run_monadLift StateT.run_get StateT.run_modify liftM monadLift
  MonadLift.monadLift bind_assoc pure_bind map_pure map_bind bind_map_left Functor.map_map
  BitVec.cast_eq dite_true ite_true ite_false decide_eq_true_eq List.getElem?_cons_zero
  List.getElem?_cons_succ Nat.reduceEqDiff reduceIte reduceDIte Bool.or_false Bool.false_or
  Int.reduceLT Int.reduceNeg Int.reduceToNat BitVec.ofNat_eq_ofNat List.cons_append
  List.nil_append List.foldr_cons List.foldr_nil true_and and_true Bool.and_true
  Bool.true_and beq_self_eq_true List.toList_toArray
  Value.toBV Value.toBool List.getD_cons_zero List.getD_cons_succ bind_pure_comp

end Cert

end Air2Lean.Sem
