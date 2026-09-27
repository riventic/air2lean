/-!
# Internal IR

The version-independent form of one function. `Normalize.lean` builds it from the raw JSON
of one Zig version; `Check.lean` and `Emit.lean` read only this. Do not add Zig-version
details here.
-/

namespace Air2Lean

/-- A type ID, the same as the index into the file's `types` table. -/
abbrev TyId := Nat

/-- An instruction ID: the instruction's position in the function, debug instructions last
(`Air2Lean/Air/Canon.lean`'s `renumber`), so the same code has the same IDs in every Zig version. -/
abbrev InstId := Nat

inductive Ty where
  | int (signed : Bool) (bits : Nat)
  /-- An IEEE-754 float type. `bits` is one of `16 32 64 80 128` (`Check.lean`). -/
  | float (bits : Nat)
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
  /-- `tag` is the integer tag type; `fields` are the names with their tag values. A
  non-exhaustive enum (`_`) also has every other value of `tag`. -/
  | enum (name : String) (tag : TyId) (exhaustive : Bool) (fields : Array (String × Int))
  /-- `tag` is the tag enum of a tagged union, `none` for a bare, `extern` or `packed` union.
  `fields` are in tag order. -/
  | union (name : String) (layout : String) (tag : Option TyId) (fields : Array (String × TyId))
  | tuple (fields : Array TyId)
  /-- `std.mem.Allocator`: the model's `Zig.Allocator` (`ZigLean/Mem/Alloc.lean`). Its fields
  (`*anyopaque`, a table of function pointers) are not translated. -/
  | allocator
  | other (name : String)
  deriving Repr, Inhabited, BEq

/-- The memory facts of one type (`docs/air-json.md` schema 6), in a table parallel to the
types. `none` where the exporter did not know the layout. -/
structure Layout where
  size : Option Nat := none
  align : Option Nat := none
  /-- The byte offset of each struct or tuple field, in field order. Empty if unknown, and for
  a packed struct. -/
  offsets : Array Nat := #[]
  /-- A pointer type's `align(N)` (explicit, or the child's ABI alignment). -/
  ptrAlign : Option Nat := none
  /-- An array `[N:s]T`, or a pointer `[*:s]T` or `[:s]T`, with a sentinel. -/
  sentinel : Bool := false
  isVolatile : Bool := false
  allowzero : Bool := false
  /-- A bit-pointer (`&packed_struct.field`): its host integer's size in bytes; else 0. -/
  hostSize : Nat := 0
  deriving Repr, Inhabited

inductive Val where
  | inst (id : InstId)
  /-- An integer constant. `ty` is an `int` type. -/
  | int (ty : TyId) (v : Int)
  /-- A float constant: the raw bit pattern (`docs/air-json.md`'s `fbits`). `ty` is a `float`
  type. -/
  | float (ty : TyId) (bits : Nat)
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
  /-- An enum constant: its tag value. `ty`'s `k` is `enum`. -/
  | enumTag (ty : TyId) (v : Int)
  /-- A union constant: the active field's index and its payload. `ty`'s `k` is `union`. -/
  | unionVal (ty : TyId) (field : Nat) (payload : Val)
  /-- An array, struct or tuple constant: its items or fields. An array with a sentinel has the
  sentinel as the last item. -/
  | agg (ty : TyId) (elems : Array Val)
  /-- A pointer constant: byte `off` of the global with index `global` in `Func.globals`. -/
  | ptrConst (ty : TyId) (global : Nat) (off : Nat)
  /-- A pointer constant without a global (`@ptrFromInt`, a comptime-only value): `kind` names
  its base. `Check.lean` rejects it. -/
  | ptrOther (ty : TyId) (kind : String)
  /-- A slice constant. -/
  | sliceConst (ty : TyId) (ptr : Val) (len : Val)
  deriving Repr, Inhabited, BEq

/-- The type of a constant; `none` for an instruction, `func` and the constants without a type
field. -/
def Val.constTy? (v : Val) : Option TyId :=
  match v with
  | .int t _ | .float t _ | .undef t | .optNull t | .optSome t _ | .err t _ | .errUnionErr t _
  | .errUnionOk t _ | .enumTag t _ | .unionVal t .. | .agg t _ | .ptrConst t .. | .ptrOther t _
  | .sliceConst t .. => some t
  | _ => none

/-- The `Zig.Error` constructor for a noreturn panic-handler callee, e.g.
`debug.FullPanic((function 'defaultPanic')).outOfBounds`: the member name after the last `.`,
without the `__anon_<n>` suffix of a generic member (docs/generated-code.md §Panics). The same table as `scripts/diff.sh`'s
`expected_ctor_for_zig_kind` (`call` is the member that `@panic` calls; the harness reports it
as `panic`). `none`: a callee outside the table, which `Check.lean` rejects. -/
def panicErrorFor? (calleeName : String) : Option String :=
  -- A generic handler (`inactiveUnionField`) is an instance: `<name>__anon_<n>`.
  match ((calleeName.splitOn ".").getLast?.map fun m => (m.splitOn "__anon_").headD m) with
  | some "integerOverflow" | some "integerOutOfBounds" | some "integerPartOutOfBounds"
  | some "shlOverflow" | some "shrOverflow" => some ".overflow"
  | some "outOfBounds" => some ".outOfBounds"
  | some "divideByZero" => some ".divByZero"
  | some "reachedUnreachable" => some ".unreachable"
  | some "exactDivisionRemainder" | some "unwrapNull" | some "unwrapError"
  | some "forLenMismatch" | some "invalidEnumValue" | some "inactiveUnionField"
  | some "corruptSwitch" | some "call" | some "sentinelMismatch" | some "copyLenMismatch"
  | some "memcpyAlias" => some ".panic"
  | some "startGreaterThanEnd" => some ".outOfBounds"
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

/-- `floor`, `ceil`, `trunc_float`, `round` (float-only; `trunc` is bit truncation, unrelated). -/
inductive FloatRoundOp where
  | floor | ceil | trunc | round
  deriving Repr, Inhabited, BEq

/-- The libm-backed transcendentals (`docs/floats.md`). -/
inductive LibmOp where
  | sin | cos | tan | exp | exp2 | log | log2 | log10
  deriving Repr, Inhabited, BEq

mutual

inductive Op where
  | arg (index : Nat)
  | arith (op : ArithOp) (mode : Mode) (a b : Val)
  | div (op : DivOp) (a b : Val)
  /-- `div_float`: float-only division, always exact rounding (no overflow check). -/
  | divFloat (a b : Val)
  | minMax (isMax : Bool) (a b : Val)
  | withOverflow (op : ArithOp) (a b : Val)
  | bit (op : BitOp) (a b : Val)
  /-- `not` on an integer (bitwise) or a `bool` (logical); `Emit` looks at the type. -/
  | not (a : Val)
  | neg (a : Val)
  /-- `@abs`. Float-only in the subset (`Check.lean` rejects an integer `abs`). -/
  | abs (a : Val)
  | shift (op : ShiftOp) (a b : Val)
  | cmp (op : CmpOp) (a b : Val)
  | boolAnd (a b : Val)
  | boolOr (a b : Val)
  /-- `@intCast`. The target type is the instruction's result type. -/
  | intCast (a : Val)
  /-- `@truncate`. -/
  | trunc (a : Val)
  /-- Same bits, other type with the same representation (for example `usize` → `u64`); also
  int ↔ float bit reinterpretation (`Emit` looks at the types on each side). -/
  | bitcast (a : Val)
  | floatRound (op : FloatRoundOp) (a : Val)
  | sqrt (a : Val)
  | libm (op : LibmOp) (a : Val)
  /-- `mul_add`: `a * b + c`. `raw.args` order is `[lhs, rhs, addend]`. -/
  | mulAdd (a b c : Val)
  /-- `fptrunc`/`fpext`: float ↔ float. The target format is the instruction's result type. -/
  | floatConv (a : Val)
  /-- `float_from_int`. The source int's signedness matters (`Emit`); the target format is the
  instruction's result type. -/
  | floatFromInt (a : Val)
  /-- `int_from_float` (`safe = false`) / `int_from_float_safe` (`safe = true`). The target int's
  signedness and width are the instruction's result type. -/
  | intFromFloat (safe : Bool) (a : Val)
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
  /-- `is_null_ptr` (`isNull = true`) / `is_non_null_ptr`: is the optional at the pointer `p`
  `null` / not `null`? -/
  | isNullPtr (isNull : Bool) (p : Val)
  /-- `optional_payload_ptr` / `optional_payload_ptr_set` (`set = true`: the optional at `p`
  becomes non-null): the pointer to the payload of the optional at `p`. -/
  | optPayloadPtr (set : Bool) (p : Val)
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
  /-- `is_named_enum_value`: does the enum value `a` have a name? -/
  | isNamedEnum (a : Val)
  /-- `get_union_tag`: the tag of the tagged union `a`. -/
  | unionTag (a : Val)
  /-- `union_init`: a union with field `index` active, holding `a`. -/
  | unionInit (index : Nat) (a : Val)
  /-- A local: `alloc`, or `ret_ptr` (the place the result is built in). -/
  | alloc
  /-- `struct_field_ptr*`: the pointer to field `index` of the struct or union at `base`. -/
  | fieldPtr (base : Val) (index : Nat)
  /-- `set_union_tag`: make `tag`'s field active in the union at `ptr` (its payload undefined). -/
  | setUnionTag (ptr : Val) (tag : Val)
  /-- `ret_load`: return the value at `ptr` (the `ret_ptr` local). -/
  | retLoad (ptr : Val)
  | load (ptr : Val)
  | store (ptr : Val) (v : Val)
  | sliceLen (s : Val)
  | sliceElemVal (s : Val) (i : Val)
  /-- `ptr_add` (`sub = false`) / `ptr_sub`: the pointer `n` items after / before `p`. -/
  | ptrAdd (sub : Bool) (p n : Val)
  /-- `ptr_elem_ptr`, `slice_elem_ptr`: the pointer to item `i` of the many-pointer, array pointer
  or slice `p`. -/
  | elemPtr (p i : Val)
  /-- `ptr_elem_val`: item `i` of the many-pointer or array pointer `p`. -/
  | ptrElemVal (p i : Val)
  /-- `array_elem_val`: item `i` of the array value `a`. -/
  | arrayElemVal (a i : Val)
  /-- `slice`: the slice with item pointer `p` and length `len`. -/
  | slice (p len : Val)
  /-- `slice_ptr`: the item pointer of the slice `s`. -/
  | slicePtr (s : Val)
  /-- `array_to_slice`: the slice of all items of the array that `p` points to. -/
  | arrayToSlice (p : Val)
  /-- `ptr_slice_len_ptr` (`len = true`) / `ptr_slice_ptr_ptr`: the pointer to the length / item
  pointer of the slice at `p`. -/
  | sliceFieldPtr (len : Bool) (p : Val)
  /-- `memset`, `memset_safe`: each item of the slice or array pointer `dst` becomes `v`. -/
  | memset (dst v : Val)
  /-- `memcpy`, `memmove`: copy the items of `src` to the slice or array pointer `dst`. -/
  | memcpy (dst src : Val)
  /-- `tag_name`: the name of the enum value `a`, a `[:0]const u8`. -/
  | tagName (a : Val)
  /-- `error_name`: the name of the error `a`, a `[:0]const u8`. -/
  | errorName (a : Val)
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

/-- A global that a pointer constant points into: a container-level `var` or `const` (`name`),
or an unnamed constant such as a string literal. -/
structure Global where
  name : Option String
  ty : TyId
  isConst : Bool
  threadlocal : Bool
  isExtern : Bool
  /-- `none`: the exporter did not have the initial value (`docs/air-json.md`). -/
  init : Option Val
  deriving Repr, Inhabited

structure Func where
  zigVersion : String
  name : String
  params : Array TyId
  ret : TyId
  body : Array Inst
  types : Array Ty
  /-- `layouts[i]` is the layout of `types[i]`. -/
  layouts : Array Layout
  globals : Array Global

end Air2Lean
