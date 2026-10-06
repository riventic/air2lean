import Std.Data.HashSet

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
  /-- `[len]child`, or `[len:s]child` (`sentinel`): the value then has `len + 1` items, the
  sentinel last, as in the AIR (`aggregate_init`, `docs/air-json.md`'s `elems`). -/
  | array (len : Nat) (child : TyId) (sentinel : Bool)
  /-- `@Vector(len, child)`. Distinct from `array`: its ABI layout rounds the size up to a power
  of 2 (`Check.lean`'s `modelLayout`, `ZigLean/Vec.lean`'s `Zig.Enc` instance). -/
  | vector (len : Nat) (child : TyId)
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
  /-- `std.Thread`: the model's `Zig.ThreadId` (`ZigLean/Mem/Thread.lean`). Its field (a
  platform-specific handle, e.g. `pthread_t`) is not translated. -/
  | thread
  /-- `std.Io` (0.16.0): the model's `Zig.Io` (`ZigLean/Conc/Call.lean`). Its fields
  (`userdata`, the `vtable`) are not translated. -/
  | io
  | other (name : String)
  deriving Repr, Inhabited, BEq

/-- Float widths supported by parsing and the checked model. -/
def supportedFloatWidth (bits : Nat) : Bool :=
  bits == 16 || bits == 32 || bits == 64 || bits == 80 || bits == 128

private def integerDomain (signed : Bool) (bits : Nat) : Int → Bool :=
  if bits == 0 then fun v => v == 0 else
  let bound : Int := 2 ^ (if signed then bits - 1 else bits)
  if signed then fun v => decide (-bound ≤ v ∧ v < bound)
  else fun v => decide (0 ≤ v ∧ v < bound)

/-- Constants must fit the declared Zig integer width; validation never inserts a wrap. -/
def integerFits (signed : Bool) (bits : Nat) (v : Int) : Bool :=
  integerDomain signed bits v

/-- The types that `ty` names directly. -/
def childTys (ty : Ty) : Array TyId :=
  match ty with
  | .ptr _ _ c | .array _ c _ | .vector _ c | .optional c => #[c]
  | .errorUnion s p => #[s, p]
  | .struct _ _ fs => fs.map (·.2)
  | .enum _ t _ _ => #[t]
  | .union _ _ t fs => t.toArray ++ fs.map (·.2)
  | .tuple fs => fs
  | _ => #[]

/-- Children traversed through values; a pointer ends a value-type path. -/
def valueChildTys (ty : Ty) : Array TyId :=
  match ty with
  | .ptr .. => #[]
  | _ => childTys ty

private inductive TypeVisit where
  | unseen | active | done (height : Nat)
  deriving Inhabited

/-- Reject cycles through values before width/layout traversal. Pointer edges break a
value cycle, so ordinary linked structures remain valid. All child IDs are range checked. -/
partial def validateTypeGraph (fnName : String) (types : Array Ty) : Except String Unit := do
  for t in types do
    if let .int _ bits := t then
      if bits > 65535 then throw s!"{fnName}: integer width {bits} exceeds Zig's 65535-bit limit"
    if let .float bits := t then
      unless supportedFloatWidth bits do
        throw s!"{fnName}: float type of {bits} bits is outside the subset (only 16, 32, 64, 80, 128)"
    for c in childTys t do
      unless c < types.size do throw s!"{fnName}: unknown type id {c}"
    let fields : Array String := match t with
      | .struct _ _ fs | .union _ _ _ fs => fs.map (fun (field : String × TyId) => field.1)
      | .enum _ _ _ fs => fs.map (fun (field : String × Int) => field.1)
      | _ => #[]
    let mut names : Std.HashSet String := {}
    for name in fields do
      if names.contains name then throw s!"{fnName}: duplicate type field name '{name}'"
      names := names.insert name
    match t with
    | .errorUnion set _ =>
      unless (match types[set]? with | some (.errorSet _) => true | _ => false) do
        throw s!"{fnName}: error union set type {set} is not an error set"
    | .enum name tag _ fs =>
      let some (.int signed bits) := types[tag]?
        | throw s!"{fnName}: enum '{name}' tag type {tag} is not an integer"
      if bits > 65535 then throw s!"{fnName}: enum '{name}' tag width exceeds 65535 bits"
      let fits := integerDomain signed bits
      let mut values : Std.HashSet Int := {}
      for (_, v) in fs do
        unless fits v do throw s!"{fnName}: enum '{name}' tag {v} does not fit its integer type"
        if values.contains v then throw s!"{fnName}: enum '{name}' has duplicate tag {v}"
        values := values.insert v
    | _ => pure ()
  let rec visit (id : TyId) (states : Array TypeVisit) (depth : Nat := 0) : Except String (Array TypeVisit) := do
    if depth ≥ 256 then throw s!"{fnName}: value type traversal exceeds 256 levels"
    match states[id]? with
    | some (.done _) => return states
    | some .active => throw s!"{fnName}: cyclic value type at type {id}"
    | none => throw s!"{fnName}: unknown type id {id}"
    | some .unseen =>
      let some t := types[id]? | throw s!"{fnName}: unknown type id {id}"
      let mut states := states.set! id .active
      let children := valueChildTys t
      for c in children do states ← visit c states (depth + 1)
      let height : Nat := 1 + children.foldl (fun n c => match states[c]? with
          | some (.done h) => max n h | _ => n) (0 : Nat)
      if height > 256 then throw s!"{fnName}: value type traversal exceeds 256 levels"
      pure (states.set! id (.done height))
  let mut states : Array TypeVisit := Array.replicate types.size .unseen
  for id in Array.range types.size do states ← visit id states

/-- A pointer cast preserves a value/place only when its child type is unchanged. Changing
the pointee reinterprets bytes, even when the cast is only read through. -/
def samePointee (types : Array Ty) (a b : TyId) : Bool :=
  match types[a]?, types[b]? with
  | some (.ptr _ _ ca), some (.ptr _ _ cb) => ca == cb
  | _, _ => false

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
  /-- Exact comptime sentinel for a byte pointer, explicitly exported as decimal text.
  Missing in older exports; allocSentinel must not guess zero. -/
  sentinelByte : Option Nat := none
  isVolatile : Bool := false
  allowzero : Bool := false
  /-- A bit-pointer (`&packed_struct.field`): its host integer's size in bytes; else 0. -/
  hostSize : Nat := 0
  /-- A bit-pointer: the first bit of its field in the host integer. -/
  bitOffset : Nat := 0
  deriving Repr, Inhabited, BEq

/-- Both legacy exports may omit the byte value, preserving the presence-only
comparison. Explicit values must agree; known and missing metadata cannot establish
the same sentinel contract. Callers separately compare presence and the child type. -/
def Layout.sameKnownSentinel (a b : Layout) : Bool :=
  a.sentinelByte == b.sentinelByte

/-- C and allowzero pointers can carry address zero as a value. -/
def nullablePtrTy (types : Array Ty) (layouts : Array Layout) (id : TyId) : Bool :=
  match types[id]? with
  | some (.ptr size _ _) => size == "c" || (layouts[id]?.map (·.allowzero)).getD false
  | _ => false

inductive Val where
  | inst (id : InstId)
  /-- An integer constant. `ty` is an `int` type, or a packed struct (its backing integer). -/
  | int (ty : TyId) (v : Int)
  /-- A float constant: the raw bit pattern (`docs/air-json.md`'s `fbits`). `ty` is a `float`
  type. -/
  | float (ty : TyId) (bits : Nat)
  | bool (b : Bool)
  /-- `{}`, the only value of `void`. -/
  | void
  | undef (ty : TyId)
  /-- `spawnFn`: for a generic instantiation of `std.Thread.spawn`, the fqn of the function
  passed as its comptime `function` argument (the exporter's `comptime_fn`,
  `docs/std-models.md` §Thread model). `none` for any other function value. -/
  | func (name : String) (noreturn : Bool) (spawnFn : Option String := none)
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
  /-- Address zero of a C/allowzero pointer. No global or allocation is attached. -/
  | ptrNull (ty : TyId)
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
  | .errUnionOk t _ | .enumTag t _ | .unionVal t .. | .agg t _ | .ptrConst t .. | .ptrNull t | .ptrOther t _
  | .sliceConst t .. => some t
  | _ => none

/-- The `Zig.Error` constructor for a noreturn panic-handler callee, e.g.
`debug.FullPanic((function 'defaultPanic')).outOfBounds`: the member name after the last `.`,
without the `__anon_<n>` suffix of a generic member (docs/generated-code.md §Panics). The same table as `scripts/diff.sh`'s
`expected_ctor_for_zig_kind` (`call` is the member that `@panic` calls; the harness reports it
as `panic`). `none`: a callee outside the table, which `Check.lean` rejects. -/
def panicErrorFor? (calleeName : String) : Option String :=
  if calleeName == "debug.defaultPanic" then some ".panic" else
  if !calleeName.startsWith "debug.FullPanic((function 'defaultPanic'))." then none else
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
  | some "memcpyAlias" | some "castToNull" | some "incorrectAlignment" => some ".panic"
  | some "startGreaterThanEnd" => some ".outOfBounds"
  | _ => none

/-- `std.builtin.ReduceOp`: `@reduce`'s operator. -/
inductive ReduceOp where
  | and | or | xor | min | max | add | mul
  deriving Repr, Inhabited, BEq

/-- One lane of a `@shuffle`'s mask: an index into the first (only, for a single-source shuffle)
source (`a`), an index into the second source (`b`; two-source shuffle only), an undefined lane,
or a comptime-known value (single-source shuffle only). Unifies 0.14.1's one `shuffle` tag (mask
always `a`/`b`/`undef`) with 0.15.2+'s `shuffle_one` (mask `a`/`value`) and `shuffle_two` (mask
`a`/`b`/`undef`) (`docs/air-json.md`). -/
inductive ShuffleLane where
  | a (idx : Nat)
  | b (idx : Nat)
  | undef
  | value (v : Val)
  deriving Repr, Inhabited, BEq

/-- One `outputs`/`inputs` entry of an `Op.asm` (`docs/air-json.md`). `ref` is `none` only for
an output that is the asm expression's own result (`=r` with no operand). -/
structure AsmOperand where
  constraint : String
  name : String
  ref : Option Val
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

/-- Counts bits in the operand representation, including for signed integers. -/
inductive BitCountOp where
  | clz | ctz | popcount
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

/-- `std.builtin.AtomicOrder`. Within one thread every atomic op is sequentially consistent
(`docs/generated-code.md` §Atomics and threads): the translator reads the ordering and
otherwise ignores it. -/
inductive AtomicOrder where
  | unordered | monotonic | acquire | release | acqRel | seqCst
  deriving Repr, Inhabited, BEq

/-- `std.builtin.AtomicRmwOp`. -/
inductive RmwOp where
  | xchg | add | sub | and | nand | or | xor | max | min
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
  | shlWithOverflow (a b : Val)
  | countBits (op : BitCountOp) (a : Val)
  /-- `splat`: a vector with every lane equal to the scalar `a`. -/
  | splat (a : Val)
  /-- `select`: a vector built lane-wise from `a` (where the bool-vector `pred`'s lane is true)
  or `b` (false). -/
  | select (pred a b : Val)
  /-- `@reduce`: fold the vector `a` with `op` (`reduce_optimized` is outside the subset, like
  every other `*_optimized` tag). -/
  | reduce (op : ReduceOp) (a : Val)
  /-- `@shuffle`: a vector built lane-wise from `mask` reading `a` and, for a two-source shuffle,
  `b` (`none` for a single-source shuffle). -/
  | shuffle (a : Val) (b : Option Val) (mask : Array ShuffleLane)
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
  /-- `is_err_ptr` (`isErr = true`) / `is_non_err_ptr`: does the error union at `p` hold an
  error? -/
  | isErrPtr (isErr : Bool) (p : Val)
  /-- `unwrap_errunion_payload_ptr` / `errunion_payload_ptr_set` (`set = true`: the error union
  at `p` gets no error): the pointer to the payload of the error union at `p`. -/
  | errPayloadPtr (set : Bool) (p : Val)
  /-- `unwrap_errunion_err_ptr`: the error of the error union at `p`. -/
  | errCodePtr (p : Val)
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
  /-- `field_parent_ptr` (`@fieldParentPtr`): the pointer to the struct that has `fieldPtr` at
  field `index` (`fieldPtr` minus that field's byte offset). -/
  | fieldParentPtr (fieldPtr : Val) (index : Nat)
  /-- `set_union_tag`: make `tag`'s field active in the union at `ptr` (its payload undefined). -/
  | setUnionTag (ptr : Val) (tag : Val)
  /-- `ret_load`: return the value at `ptr` (the `ret_ptr` local). -/
  | retLoad (ptr : Val)
  | load (ptr : Val)
  | store (ptr : Val) (v : Val)
  | atomicLoad (ptr : Val) (order : AtomicOrder)
  | atomicStore (ptr v : Val) (order : AtomicOrder)
  | atomicRmw (op : RmwOp) (order : AtomicOrder) (ptr v : Val)
  /-- `cmpxchg_weak` (`weak = true`) permits spurious read-only failure;
  `cmpxchg_strong` succeeds whenever the selected value matches. -/
  | cmpxchg (weak : Bool) (ptr expected new : Val) (succ fail : AtomicOrder)
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
  /-- A switch with a selector replaced by dispatches from its descendant bodies. -/
  | loopSwitchBr (initial : Val) (cases : Array SwitchCase) (elseBody : Array Inst)
  /-- Jump to an enclosing loop-switch, replacing its selector, preserving other state. -/
  | switchDispatch (target : InstId) (selector : Val)
  /-- `try`/`try_cold`: `v` is an error union; `errBody` runs when it holds an error (it ends in
  an exit, like a `cond_br` branch). Otherwise the `try` instruction's value is the payload. -/
  | «try» (v : Val) (errBody : Array Inst)
  /-- Pointer-form `try`: test the addressed error tag, run `errBody` on error, otherwise
  return the payload's address in the same allocation without reading or copying it. -/
  | tryPtr (p : Val) (errBody : Array Inst)
  | ret (v : Val)
  | unreach
  | trap
  /-- `dbg_stmt`: source line. No effect. -/
  | line (n : Nat)
  /-- `dbg_var_*`, `dbg_empty_stmt`: no effect. `name` is kept for readable output. -/
  | dbg (name : Option String) (v : Option Val)
  /-- `assembly`: register-operand-only inline asm (M21). Translated as a call to an `opaque`
  Lean function keyed by a hash of `source` and the operand constraints
  (`docs/generated-code.md` §asm); a proof knows nothing about it beyond what the caller
  states. `Check.lean` accepts only a register constraint (`=r`, `r`, `{reg}`, `={reg}`), no
  `"memory"` clobber, and at most one result output (an `=r`/`={reg}` output with no `ref`). -/
  | asm (source : String) (isVolatile : Bool) (clobbers : Array String)
      (outputs inputs : Array AsmOperand)

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
