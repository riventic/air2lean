/-!
# Internal IR

The version-independent form of one function. `Normalize.lean` builds it from the raw JSON
of one Zig version; `Check.lean` and `Emit.lean` read only this. Do not add Zig-version
details here.
-/

namespace Air2Lean

/-- A type ID, the same as the index into the file's `types` table. -/
abbrev TyId := Nat

/-- An instruction ID, the same as the AIR instruction index. -/
abbrev InstId := Nat

inductive Ty where
  | int (signed : Bool) (bits : Nat)
  | bool
  | void
  | noreturn
  /-- `size`: `one`, `many`, `slice` or `c`. -/
  | ptr (size : String) (isConst : Bool) (child : TyId)
  | array (len : Nat) (child : TyId)
  | optional (child : TyId)
  | struct (name : String) (layout : String) (fields : Array (String × TyId))
  | tuple (fields : Array TyId)
  | other (name : String)
  deriving Repr, Inhabited, BEq

inductive Val where
  | inst (id : InstId)
  /-- An integer constant. `ty` is an `int` type. -/
  | int (ty : TyId) (v : Int)
  | bool (b : Bool)
  /-- `{}`, the only value of `void`. -/
  | void
  | undef (ty : TyId)
  | func (name : String) (noreturn : Bool)
  deriving Repr, Inhabited, BEq

/-- Integer overflow behaviour of `+`, `-`, `*`. -/
inductive Mode where
  | checked  -- overflow ⇒ `throw .overflow` (`add`, `add_safe`)
  | wrap     -- `+%`
  | sat      -- `+|`
  deriving Repr, Inhabited, BEq

inductive ArithOp where
  | add | sub | mul
  deriving Repr, Inhabited, BEq

inductive DivOp where
  | divTrunc | divFloor | divExact | rem | mod
  deriving Repr, Inhabited, BEq

inductive BitOp where
  | and | or | xor
  deriving Repr, Inhabited, BEq

inductive ShiftOp where
  | shl | shlExact | shlSat | shr | shrExact
  deriving Repr, Inhabited, BEq

inductive CmpOp where
  | lt | le | eq | ne | ge | gt
  deriving Repr, Inhabited, BEq

mutual

inductive Op where
  | arg (index : Nat)
  | arith (op : ArithOp) (mode : Mode) (a b : Val)
  | div (op : DivOp) (a b : Val)
  | minMax (isMax : Bool) (a b : Val)
  | withOverflow (op : ArithOp) (a b : Val)
  | bit (op : BitOp) (a b : Val)
  /-- `not` on an integer (bitwise) or a `bool` (logical); `Emit` looks at the type. -/
  | not (a : Val)
  | neg (a : Val)
  | shift (op : ShiftOp) (a b : Val)
  | cmp (op : CmpOp) (a b : Val)
  | boolAnd (a b : Val)
  | boolOr (a b : Val)
  /-- `@intCast`. The target type is the instruction's result type. -/
  | intCast (a : Val)
  /-- `@truncate`. -/
  | trunc (a : Val)
  /-- Same bits, other type with the same representation (for example `usize` → `u64`). -/
  | bitcast (a : Val)
  | alloc
  | load (ptr : Val)
  | store (ptr : Val) (v : Val)
  | sliceLen (s : Val)
  | sliceElemVal (s : Val) (i : Val)
  | structFieldVal (s : Val) (index : Nat)
  | aggregateInit (elems : Array Val)
  | call (callee : Val) (args : Array Val)
  | block (body : Array Inst)
  | loop (body : Array Inst)
  | br (target : InstId) (v : Val)
  | «repeat» (target : InstId)
  | condBr (c : Val) (thenBody elseBody : Array Inst)
  | switchBr (v : Val) (cases : Array SwitchCase) (elseBody : Array Inst)
  | ret (v : Val)
  | unreach
  | trap
  /-- `dbg_stmt`: source line. No effect. -/
  | line (n : Nat)
  /-- `dbg_var_*`, `dbg_empty_stmt`: no effect. `name` is kept for readable output. -/
  | dbg (name : Option String) (v : Option Val)

structure SwitchCase where
  items : Array Val
  ranges : Array (Val × Val)
  body : Array Inst

structure Inst where
  id : InstId
  ty : TyId
  op : Op

end

structure Func where
  zigVersion : String
  name : String
  params : Array TyId
  ret : TyId
  body : Array Inst
  types : Array Ty

end Air2Lean
