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
  /-- `E!T`: `set` is the error set type, `payload` is `T`. -/
  | errorUnion (set payload : TyId)
  /-- An error set. `none` = `anyerror` (every error name, `docs/air-json.md`). -/
  | errorSet (names : Option (Array String))
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
  /-- A `null` constant of an optional type. `ty` is the `optional` type. -/
  | optNull (ty : TyId)
  /-- An optional constant holding a payload (`docs/air-json.md`'s `Ref` reuses the plain `val`
  string, disambiguated by `ty`: the exporter's `fmtValue` prints a non-null optional as just its
  payload's own text). `ty` is the `optional` type; `v` is the payload, recursively. -/
  | optSome (ty : TyId) (v : Val)
  /-- An error value: `error.Name`. `ty`'s `k` is `error_set` (`docs/air-json.md`). -/
  | err (ty : TyId) (name : String)
  /-- An error-union constant in the error state (schema 2). `ty`'s `k` is `error_union`. -/
  | errUnionErr (ty : TyId) (name : String)
  /-- An error-union constant in the payload state (schema 2). `ty`'s `k` is `error_union`. -/
  | errUnionOk (ty : TyId) (payload : Val)
  deriving Repr, Inhabited, BEq

/-- The `Zig.Error` constructor for a noreturn panic-handler callee, e.g.
`debug.FullPanic((function 'defaultPanic')).outOfBounds`: the member name after the last `.`
(docs/generated-code.md §Panics). The same table as `scripts/diff.sh`'s
`expected_ctor_for_zig_kind` (`call` is the member that `@panic` calls; the harness reports it
as `panic`). `none`: a callee outside the table, which `Check.lean` rejects. -/
def panicErrorFor? (calleeName : String) : Option String :=
  match (calleeName.splitOn ".").getLast? with
  | some "integerOverflow" | some "integerOutOfBounds" | some "shlOverflow"
  | some "shrOverflow" => some ".overflow"
  | some "outOfBounds" => some ".outOfBounds"
  | some "divideByZero" => some ".divByZero"
  | some "reachedUnreachable" => some ".unreachable"
  | some "exactDivisionRemainder" | some "unwrapNull" | some "unwrapError"
  | some "call" => some ".panic"
  | _ => none

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
  /-- `is_null`: true iff the optional `a` is `null`. -/
  | isNull (a : Val)
  /-- `is_non_null`: true iff the optional `a` holds a value. -/
  | isNonNull (a : Val)
  /-- Unwrap an optional's payload. Sema emits this only after an `is_non_null` check, so the
  `null` case is statically unreachable — `Zig.optPayload` (`ZigLean/Basic.lean`) panics on it
  anyway. -/
  | optPayload (a : Val)
  /-- Wrap a value into `some`. -/
  | wrapOptional (a : Val)
  /-- `is_err`: does an error union hold an error? -/
  | isErr (a : Val)
  /-- `is_non_err`. -/
  | isNonErr (a : Val)
  /-- `unwrap_errunion_payload`. Sema always checks the union first (`is_err`/`is_non_err` or a
  `try`), so the error case is statically impossible here. -/
  | errPayload (a : Val)
  /-- `unwrap_errunion_err`. Sema always checks the union first, so the ok case is statically
  impossible here. -/
  | errCode (a : Val)
  /-- `wrap_errunion_payload`: build an error union in the ok state. -/
  | wrapErrPayload (a : Val)
  /-- `wrap_errunion_err`: build an error union in the error state. -/
  | wrapErr (a : Val)
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
  /-- `try`/`try_cold`: `v` is an error union; `errBody` runs when it holds an error (it ends in
  an exit, like a `cond_br` branch). Otherwise the `try` instruction's value is the payload. -/
  | «try» (v : Val) (errBody : Array Inst)
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
