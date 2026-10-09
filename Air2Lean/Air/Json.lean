import Air2Lean.Air.StrictJson
import Air2Lean.Air.Op
import Air2Lean.Air.Profile

/-!
# AIR JSON parser

Parses one exported function file (`docs/air-json.md`) into `RawFunc`: a literal,
tag-agnostic mirror of the JSON. `Normalize.lean` turns a `RawFunc` into a version-independent
`Func` (`Air2Lean/Air/Op.lean`).

The `types` table and `Ref` shapes do not depend on the Zig version (`docs/air-json.md`), so
this file builds `Air2Lean.Ty` and `Air2Lean.Val` directly. Only instruction *tags* are
version-specific, so `RawInst` keeps `tag` as a raw string for `Normalize.lean` to interpret.
-/

namespace Air2Lean.Raw

open Lean (Json)

/-- One operand of an `assembly` instruction: its constraint, its ZIR-source name, and (for an
input, always; for an output, unless it is the asm expression's own result) the operand `Val`
(`docs/air-json.md`). -/
structure RawAsmOperand where
  constraint : String
  name : String
  ref : Option Val

/-- The `assembly` instruction's asm-specific fields (`docs/air-json.md`). Not a variant of
`RawInst` itself: `id`/`ty` already cover the result, and every other AIR tag has no use for
these fields, so keeping them optional on `RawInst` (like `body`/`callee`/...) matches the
existing shape. -/
structure RawAsm where
  source : String
  isVolatile : Bool
  clobbers : Array String
  outputs : Array RawAsmOperand
  inputs : Array RawAsmOperand

/-- A function's declaration site (`src`, additive exporter metadata): its file relative to the
owning module's root, the module name and the 1-based declaration line. Provenance only:
translation never reads it. -/
structure RawSrc where
  file : String
  module : String
  declLine : Nat
  deriving BEq, Repr

mutual

structure RawInst where
  id : InstId
  tag : String
  /-- Missing only for `inferred_alloc*`, which is outside the subset. -/
  ty : Option TyId
  args : Array Val
  /-- `block`, `loop`, `dbg_inline_block`. -/
  body : Array RawInst
  /-- `cond_br`. -/
  thenBody : Array RawInst
  /-- `cond_br`'s `else`, or `switch_br`/`loop_switch_br`'s `else`. -/
  elseBody : Array RawInst
  /-- `switch_br`, `loop_switch_br`. -/
  cases : Array RawCase
  /-- `br`, `switch_dispatch`: a block id. `repeat`: a loop id. -/
  target : Option InstId
  /-- `arg`: ZIR parameter index. -/
  param : Option Nat
  /-- `call*`. -/
  callee : Option Val
  /-- `struct_field_val`, `struct_field_ptr`, `union_init`. -/
  index : Option Nat
  /-- `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`. -/
  name : Option String
  /-- `dbg_stmt`. -/
  line : Option Nat
  /-- `dbg_stmt`: 1-based column (additive provenance; absent in older exports). -/
  column : Option Nat := none
  /-- `dbg_inline_block`: the inlined function's declaration site (additive provenance). -/
  src : Option RawSrc := none
  /-- `atomic_load`, `atomic_rmw`'s ordering. -/
  order : Option String
  /-- `atomic_rmw`'s `AtomicRmwOp`. -/
  rmwOp : Option String
  /-- `cmpxchg_weak`/`cmpxchg_strong`. -/
  successOrder : Option String
  failureOrder : Option String
  /-- `reduce`'s (`std.builtin.ReduceOp`) or `cmp_vector`'s (`std.math.CompareOperator`) operator
  name. -/
  op : Option String
  /-- `shuffle_one`, `shuffle_two` (0.15.2+), `shuffle` (0.14.1): the mask, in lane order. -/
  mask : Array ShuffleLane
  /-- `assembly`. -/
  asm : Option RawAsm
  /-- `runtime_nav_ptr`: the global's entry in the `globals` table. -/
  global : Option Nat := none
  unsupported : Bool

/-- One case of a `switch_br`/`loop_switch_br`, before tag interpretation. -/
structure RawCase where
  items : Array Val
  ranges : Array (Val × Val)
  body : Array RawInst

end

structure RawFunc where
  schema : Nat
  zigVersion : String
  profile : BuildProfile
  name : String
  params : Array TyId
  ret : TyId
  body : Array RawInst
  types : Array Ty
  layouts : Array Layout
  globals : Array Global
  /-- The function's declaration site (additive provenance; absent in older exports). -/
  src : Option RawSrc := none
  /-- `unchecked_ib`: the illegal behaviours that the patched compiler's Sema lowers to `unreach`
  where it has no safety check (`zig-patch/<version>/hook.patch`); empty in older exports. -/
  uncheckedIb : Array String := #[]

/-- `some j` if `j`'s object has a non-null value at `k`, `none` if the key is absent (or
`null`). -/
def optField (j : Json) (k : String) : Option Json :=
  let v := j.getObjValD k
  if v.isNull then none else some v

/-- Optional flags default only when absent; malformed supplied flags are errors. -/
def boolField (j : Json) (k : String) : Except String Bool :=
  match j.getObjVal? k with
  | .ok v => v.getBool?
  | .error _ => pure false

/-- Presence markers must be the literal `true`. -/
def trueMarker (j : Json) (k : String) : Except String Bool := do
  match j.getObjVal? k with
  | .ok v =>
    unless (← v.getBool?) do throw s!"'{k}' must be true when supplied"
    pure true
  | .error _ => pure false

/-- Nested constants must match their fields. SSA refs are rejected later with the
canonicalizer's contextual diagnostic. Bool, void, and function refs have no stored type ID. -/
def checkConstType (fnName : String) (types : Array Ty) (expected : TyId) (v : Val) :
    Except String Unit := do
  let some t := types[expected]? | throw s!"{fnName}: unknown type id {expected}"
  let compatible : Bool := match v with
    | .inst _ => true
    | .bool _ => t == .bool
    | .void => t == .void
    | .func .. => match t with
      | .other n => n.startsWith "fn ("
      | .ptr "one" _ c => match types[c]? with
        | some (.other n) => n.startsWith "fn ("
        | _ => false
      | _ => false
    | _ => (v.constTy?.bind (types[·]?)) == some t
  unless compatible do throw s!"{fnName}: constant does not match type {expected}"

/-- An integer constant as `fmtValue` prints it: optional leading `-`, then decimal digits. -/
def parseIntLit (fnName : String) (s : String) : Except String Int := do
  if s.length > 32768 then throw s!"{fnName}: integer literal exceeds 32768 characters"
  if s.startsWith "-" then
    match (s.drop 1).toNat? with
    | some n => return (-(n : Int))
    | none => throw s!"{fnName}: not an integer literal: {s}"
  else
    match s.toNat? with
    | some n => return (n : Int)
    | none => throw s!"{fnName}: not an integer literal: {s}"

def parseTy (j : Json) : Except String Ty := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "int" =>
    let signed ← (← j.getObjVal? "signed").getBool?
    let bits ← (← j.getObjVal? "bits").getNat?
    return .int signed bits
  | "float" =>
    let bits ← (← j.getObjVal? "bits").getNat?
    return .float bits
  | "bool" => return .bool
  | "void" => return .void
  | "noreturn" => return .noreturn
  | "ptr" =>
    let size ← (← j.getObjVal? "size").getStr?
    let isConst ← (← j.getObjVal? "const").getBool?
    let child ← (← j.getObjVal? "child").getNat?
    return .ptr size isConst child
  | "array" =>
    let len ← (← j.getObjVal? "len").getNat?
    let child ← (← j.getObjVal? "child").getNat?
    return .array len child (← boolField j "sentinel")
  | "vector" =>
    let len ← (← j.getObjVal? "len").getNat?
    let child ← (← j.getObjVal? "child").getNat?
    return .vector len child
  | "optional" =>
    let child ← (← j.getObjVal? "child").getNat?
    return .optional child
  | "struct" =>
    let name ← (← j.getObjVal? "name").getStr?
    if name == "mem.Allocator" then return .allocator
    if name == "Thread" then return .thread
    if name == "Io" then return .io
    -- A struct that is only behind a pointer can have no known fields (`no_fields`).
    if (← trueMarker j "no_fields") then return .other name
    -- `Io.Future(T)`: exactly `any_future: ?*Io.AnyFuture` then `result: T` (Zig 0.16.0).
    if name.startsWith "Io.Future(" && name.endsWith ")" then
      let fieldsJ ← (← j.getObjVal? "fields").getArr?
      let names ← fieldsJ.mapM fun fj => do (← fj.getObjVal? "name").getStr?
      unless names == #["any_future", "result"] do
        throw s!"{name}: unexpected fields {names}"
      return .future (← (← fieldsJ[1]!.getObjVal? "ty").getNat?)
    let layout ← (← j.getObjVal? "layout").getStr?
    let fieldsJ ← (← j.getObjVal? "fields").getArr?
    let fields ← fieldsJ.mapM fun fj => do
      let fname ← (← fj.getObjVal? "name").getStr?
      let fty ← (← fj.getObjVal? "ty").getNat?
      return (fname, fty)
    return .struct name layout fields
  | "tuple" =>
    let fieldsJ ← (← j.getObjVal? "fields").getArr?
    let fields ← fieldsJ.mapM fun fj => do
      let fty ← fj.getObjVal? "ty"
      fty.getNat?
    return .tuple fields
  | "enum" =>
    let name ← (← j.getObjVal? "name").getStr?
    let tag ← (← j.getObjVal? "tag").getNat?
    let exhaustive ← (← j.getObjVal? "exhaustive").getBool?
    let fieldsJ ← (← j.getObjVal? "fields").getArr?
    let fields ← fieldsJ.mapM fun fj => do
      let fname ← (← fj.getObjVal? "name").getStr?
      let v ← (← fj.getObjVal? "value").getStr?
      return (fname, ← parseIntLit name v)
    return .enum name tag exhaustive fields
  | "union" =>
    let name ← (← j.getObjVal? "name").getStr?
    if (← trueMarker j "no_fields") then return .other name
    let layout ← (← j.getObjVal? "layout").getStr?
    -- A bare union's hidden tag (`safety_tag`) is a tag like the one of a `union(enum)`: the
    -- layout, the ops and the safety checks are the same.
    let tag ← match optField j "tag" <|> optField j "safety_tag" with
      | some tj => some <$> tj.getNat?
      | none => pure none
    let fieldsJ ← (← j.getObjVal? "fields").getArr?
    let fields ← fieldsJ.mapM fun fj => do
      let fname ← (← fj.getObjVal? "name").getStr?
      let fty ← (← fj.getObjVal? "ty").getNat?
      return (fname, fty)
    return .union name layout tag fields
  | "other" =>
    let name ← (← j.getObjVal? "name").getStr?
    return .other name
  | "error_union" =>
    let set ← (← j.getObjVal? "error").getNat?
    let payload ← (← j.getObjVal? "payload").getNat?
    return .errorUnion set payload
  | "error_set" =>
    -- `inferred`: an inferred set not yet resolved; like `anyerror`, its names are unknown.
    let any ← trueMarker j "any"
    let inferred ← trueMarker j "inferred"
    if any || inferred then return .errorSet none
    else
      let errsJ ← (← j.getObjVal? "errors").getArr?
      let errs ← errsJ.mapM Json.getStr?
      return .errorSet (some errs)
  | other => throw s!"unknown type kind: {other}"

/-- The memory facts of a type entry (schema 6): `abi_size`, `abi_align`, the fields' `offset`,
`sentinel`, and a pointer's `ptr_align`, `volatile`, `allowzero`, `host_size`, `bit_offset`,
`vector_index`. -/
def parseLayout (j : Json) : Except String Layout := do
  let nat? (k : String) : Except String (Option Nat) :=
    match optField j k with
    | some v => some <$> v.getNat?
    | none => pure none
  let bool := boolField j
  let offsets ← match optField j "fields" with
    | some (.arr fs) => fs.filterMapM fun fj => match optField fj "offset" with
      | some o => some <$> o.getNat?
      | none => pure none
    | _ => pure #[]
  let hostSize := (← nat? "host_size").getD 0
  let bitOffset ← nat? "bit_offset"
  let sentinelByte ← match optField j "sentinel_byte" with
    | none => pure none
    | some v => do
      let text ← v.getStr?
      let some n := text.toNat? | throw "sentinel_byte must be decimal byte text"
      unless n < 256 do throw "sentinel_byte must be in 0..255"
      unless (← bool "sentinel") do throw "sentinel_byte requires sentinel=true"
      pure (some n)
  if hostSize != 0 && bitOffset.isNone then
    throw "a bit-pointer needs 'bit_offset' (schema ≥ 11)"
  -- `null`: not a lane pointer. Absent: an older export, which did not tell the two apart.
  let vectorIndexExported := (j.getObjVal? "vector_index").toOption.isSome
  let (vectorIndex, runtimeLane) ← match optField j "vector_index" with
    | none => pure (none, false)
    | some (.str "runtime") => pure (none, true)
    | some v => match v.getNat? with
      | .ok i => pure (some i, false)
      | .error _ => throw "vector_index must be null, a lane index or \"runtime\""
  return { size := ← nat? "abi_size", align := ← nat? "abi_align", offsets,
           ptrAlign := ← nat? "ptr_align", sentinel := ← bool "sentinel", sentinelByte,
           isVolatile := ← bool "volatile",
           allowzero := ← bool "allowzero", hostSize,
           bitOffset := bitOffset.getD 0, vectorIndex, runtimeLane, vectorIndexExported }

/-- A hex digit's value, `0`-`9`/`a`-`f`/`A`-`F`. -/
def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A float's bits as `"0x"` + exactly `bits / 4` hex digits: an `fbits` constant
(`docs/air-json.md`) or a diff-protocol value (`tests/diff/Diff.lean`). -/
def parseHexNat (fnName : String) (bits : Nat) (s : String) : Except String Nat := do
  unless supportedFloatWidth bits do
    throw s!"{fnName}: unsupported float width {bits} (only 16, 32, 64, 80, 128)"
  if !s.startsWith "0x" then throw s!"{fnName}: not a hex literal: {s}"
  let digits := (s.drop 2).toString.toList
  if digits.length != bits / 4 then
    throw s!"{fnName}: {s} has {digits.length} hex digits, expected {bits / 4} for {bits} bits"
  digits.foldlM (fun acc c => do
    let some d := hexDigitVal c
      | throw s!"{fnName}: invalid hex digit '{c}' in {s}"
    return acc * 16 + d) 0

/-- A constant's `val` string, given its already-resolved type: decimal integer, `true`/`false`,
or `{}`. Shared between a top-level constant and an optional's payload (below): the exporter's
`fmtValue` reuses this same string format for the payload, disambiguated only by `ty`. -/
def parseLeafVal (fnName : String) (tyId : TyId) (ty : Ty) (s : String) : Except String Val := do
  match ty with
  | .int .. => return .int tyId (← parseIntLit fnName s)
  -- A packed struct constant is its backing integer (`Emit.lean` writes `Zig.Packed.ofBits`).
  | .struct _ "packed" _ => return .int tyId (← parseIntLit fnName s)
  | .bool =>
    match s with
    | "true" => return .bool true
    | "false" => return .bool false
    | _ => throw s!"{fnName}: not a boolean literal: {s}"
  | .void =>
    if s == "{}" then return .void
    else throw s!"{fnName}: not a void literal: {s}"
  | other => throw s!"{fnName}: constant of unsupported type {repr other}"

private inductive PackedVisit where
  | unseen | active | done (width : Nat)
  deriving Inhabited

/-- The bit width of an integer, bool, enum tag, or packed struct (the `packedBits` model
in `Memory.lean`, which this file cannot import). Memoized explicit DFS completes shared
field types once; cycles/unknown widths return `none` even for direct API calls that did not run `validateTypeGraph`. -/
def packedWidth (types : Array Ty) (id : TyId) : Option Nat := Id.run do
  match types[id]? with
  | some (.int _ bits) => return some bits
  | some .bool => return some 1
  | some (.enum ..) | some (.struct _ "packed" _) => pure ()
  | _ => return none
  let mut states : Array PackedVisit := Array.replicate types.size .unseen
  let mut tasks : List (TyId × Bool) := [(id, false)]
  while !tasks.isEmpty do
    let (current, finish) := tasks.head!
    tasks := tasks.tail!
    let some t := types[current]? | return none
    if finish then
      let children : Array TyId := match t with
        | .enum _ tag _ _ => #[tag]
        | .struct _ "packed" fs => fs.map (fun (field : String × TyId) => field.2)
        | _ => #[]
      let mut width : Nat := 0
      for child in children do
        let some (PackedVisit.done w) := states[child]? | return none
        width := width + w
      states := states.set! current (.done width)
    else
      match states[current]? with
      | some (.done _) => pure ()
      | some .active | none => return none
      | some .unseen =>
        match t with
        | .int _ bits => states := states.set! current (.done bits)
        | .bool => states := states.set! current (.done 1)
        | .enum _ tag _ _ =>
          states := states.set! current .active
          tasks := (tag, false) :: (current, true) :: tasks
        | .struct _ "packed" fs =>
          states := states.set! current .active
          tasks := fs.toList.map (fun (field : String × TyId) => (field.2, false)) ++ ((current, true) :: tasks)
        | _ => return none
  match states[id]? with
  | some (.done width) => return some width
  | _ => return none

/-- A packed struct constant written as `.{ .f = v, … }` (the exporter's `fmtValue` for some
constants): its backing integer, field 0 in the lowest bits. A field value is an integer or
`true`/`false`. -/
def parsePackedLit (fnName : String) (types : Array Ty) (fields : Array (String × TyId)) (s : String) :
    Except String Int := do
  unless s.startsWith ".{" && s.endsWith "}" do
    throw s!"{fnName}: malformed packed constant: {s}"
  let body := ((s.drop 2).dropEnd 1).toString
  let parts := (body.splitOn ",").map (·.trimAscii.toString) |>.filter (· != "")
  let mut acc : Nat := 0
  let mut off : Nat := 0
  for ((name, fty), part) in fields.toList.zip parts do
    let some w := packedWidth types fty
      | throw s!"{fnName}: packed field {name} has no bit width"
    if off + w > 65535 then throw s!"{fnName}: packed integer width exceeds 65535 bits"
    let v ← match (part.splitOn "=").map (·.trimAscii.toString) with
      | [lhs, rhs] =>
        if lhs != "." ++ name then throw s!"{fnName}: packed constant {s}: field {lhs}, expected .{name}"
        match types[fty]? with
        | some .bool =>
          if rhs == "true" then pure (1 : Int) else if rhs == "false" then pure 0
          else throw s!"{fnName}: packed field {name} requires true or false"
        | some (.int signed bits) =>
          let v ← parseIntLit fnName rhs
          unless integerFits signed bits v do
            throw s!"{fnName}: packed field {name} value {v} does not fit its integer type"
          pure v
        | some (.enum _ tag exhaustive tags) =>
          let some (.int signed bits) := types[tag]?
            | throw s!"{fnName}: packed field {name} has a non-integer enum tag"
          let v ← parseIntLit fnName rhs
          unless integerFits signed bits v do
            throw s!"{fnName}: packed field {name} value {v} does not fit its enum tag type"
          if exhaustive && !tags.any (fun (_, value) => value == v) then
            throw s!"{fnName}: packed field {name} value {v} is not a declared enum tag"
          pure v
        | some (.struct _ "packed" _) =>
          let v ← parseIntLit fnName rhs
          unless integerFits false w v do
            throw s!"{fnName}: packed field {name} value {v} does not fit its packed backing type"
          pure v
        | _ => throw s!"{fnName}: packed field {name} has an unsupported value type"
      | _ => throw s!"{fnName}: packed constant {s}: cannot read {part}"
    acc := acc + (v % (2 ^ w : Nat)).toNat * 2 ^ off
    off := off + w
  if parts.length != fields.size then
    throw s!"{fnName}: packed constant {s} has {parts.length} fields, expected {fields.size}"
  pure acc

/-- A `Ref`: `{"inst": id}`, `{"ty", "val"}`, `{"ty", "undef": true}`, `{"ty", "func",
"noreturn"}`, `{"ty", "err"}` (an error value, or an error-union constant in the error state —
`ty`'s `k` disambiguates) / `{"ty", "payload"}` (an error-union constant in the ok state; nested
`Ref`, recursively), `{"ty", "fbits"}` (a float constant, schema 3), or `{"ty", "some"}` (an
optional constant holding a payload; nested `Ref`, recursively) / `{"ty", "null": true}` (an
optional constant, `null`) (`docs/air-json.md`). -/
partial def parseVal (fnName : String) (types : Array Ty) (j : Json) : Except String Val := do
  let forms := ["inst", "func", "undef", "err", "payload", "some", "null", "enum",
    "uval", "elems", "ptr", "slice_ptr", "fbits", "val"]
  unless (forms.filter fun k => (j.getObjVal? k).toOption.isSome).length == 1 do
    throw s!"{fnName}: a reference must have exactly one value form"
  if let some instJ := optField j "inst" then
    return .inst (← instJ.getNat?)
  else if let some funcJ := optField j "func" then
    let name ← funcJ.getStr?
    let noreturn ← boolField j "noreturn"
    let spawnFn ← match optField j "comptime_fn" with
      | some sj => some <$> sj.getStr?
      | none => pure none
    return .func name noreturn spawnFn
  else
    let tyId ← (← j.getObjVal? "ty").getNat?
    let some ty := types[tyId]?
      | throw s!"{fnName}: unknown type id {tyId} in constant ref"
    if (← trueMarker j "undef") then
      return .undef tyId
    else if let some errJ := optField j "err" then
      let name ← errJ.getStr?
      match ty with
      | .errorSet _ => return .err tyId name
      | .errorUnion .. => return .errUnionErr tyId name
      | other => throw s!"{fnName}: 'err' constant of unexpected type {repr other}"
    else if let some payloadJ := optField j "payload" then
      match ty with
      | .errorUnion _ p =>
        let v ← parseVal fnName types payloadJ
        checkConstType fnName types p v
        return .errUnionOk tyId v
      | other => throw s!"{fnName}: 'payload' constant of unexpected type {repr other}"
    else if let some someJ := optField j "some" then
      match ty with
      | .optional p =>
        let v ← parseVal fnName types someJ
        checkConstType fnName types p v
        return .optSome tyId v
      | other => throw s!"{fnName}: 'some' constant of unexpected type {repr other}"
    else if (← trueMarker j "null") then
      match ty with
      | .optional .. => return .optNull tyId
      | other => throw s!"{fnName}: 'null' constant of unexpected type {repr other}"
    else if let some enumJ := optField j "enum" then
      match ty with
      | .enum .. => return .enumTag tyId (← parseIntLit fnName (← enumJ.getStr?))
      | other => throw s!"{fnName}: 'enum' constant of unexpected type {repr other}"
    else if let some uvalJ := optField j "uval" then
      match ty with
      | .union _ _ _ fields =>
        -- The active field is the tag enum constant's position among the union fields; the
        -- tag enum lists its names in the same order (`docs/air-json.md`). An `extern` or
        -- `packed` union constant has a `utag` too, unless the compiler made it from bytes.
        let some tagJ := optField j "utag"
          | throw s!"{fnName}: union constant without 'utag' (an `extern` or `packed` union \
              constant without an active field is outside the subset)"
        let .enumTag tagTy v ← parseVal fnName types tagJ
          | throw s!"{fnName}: union constant: 'utag' is not an enum constant"
        let some (.enum _ _ _ tagFields) := types[tagTy]?
          | throw s!"{fnName}: union constant: bad tag type {tagTy}"
        let some fname := (tagFields.find? (·.2 == v)).map (·.1)
          | throw s!"{fnName}: union constant: no tag field with value {v}"
        let some idx := fields.findIdx? (·.1 == fname)
          | throw s!"{fnName}: union constant: no field {fname}"
        if let .union _ _ (some tag) _ := ty then
          checkConstType fnName types tag (.enumTag tagTy v)
        if uninhabitedTy types fields[idx]!.2 then
          throw s!"{fnName}: union constant with the noreturn variant '{fname}' active (the \
            variant has no values)"
        let payload ← parseVal fnName types uvalJ
        checkConstType fnName types fields[idx]!.2 payload
        return .unionVal tyId idx payload
      | other => throw s!"{fnName}: 'uval' constant of unexpected type {repr other}"
    else if let some elemsJ := optField j "elems" then
      let elemsJ ← elemsJ.getArr?
      let (count, fields) ← match ty with
        | .array n _ sentinel => pure (n + (if sentinel then 1 else 0), #[])
        | .vector n _ => pure (n, #[])
        | .struct _ _ fs => pure (fs.size, fs.map (·.2))
        | .tuple fs => pure (fs.size, fs)
        | _ => throw s!"{fnName}: 'elems' constant of unexpected type {repr ty}"
      unless elemsJ.size == count do
        throw s!"{fnName}: aggregate has {elemsJ.size} elements, expected {count}"
      let elems ← elemsJ.mapM (parseVal fnName types)
      for (v, k) in elems.zipIdx do
        let t := match ty with | .array _ c _ | .vector _ c => c | _ => fields[k]!
        checkConstType fnName types t v
      return .agg tyId elems
    else if let some ptrJ := optField j "ptr" then
      unless (match ty with | .ptr "one" .. | .ptr "many" .. | .ptr "c" .. => true | _ => false) do
        throw s!"{fnName}: 'ptr' constant of unexpected type {repr ty}"
      if let some nullJ := optField ptrJ "null" then
        unless (← nullJ.getBool?) do throw s!"{fnName}: pointer null marker must be true"
        if (optField ptrJ "global").isSome || (optField ptrJ "unsupported").isSome then
          throw s!"{fnName}: ambiguous null pointer constant"
        unless (← (← ptrJ.getObjVal? "off").getNat?) == 0 do
          throw s!"{fnName}: null pointer constant has a nonzero offset"
        return .ptrNull tyId
      if let some k := optField ptrJ "unsupported" then
        return .ptrOther tyId (← k.getStr?)
      return .ptrConst tyId (← (← ptrJ.getObjVal? "global").getNat?) (← (← ptrJ.getObjVal? "off").getNat?)
    else if let some pJ := optField j "slice_ptr" then
      let .ptr "slice" _ child := ty
        | throw s!"{fnName}: 'slice_ptr' constant of unexpected type {repr ty}"
      let p ← parseVal fnName types pJ
      let n ← parseVal fnName types (← j.getObjVal? "slice_len")
      unless (match p.constTy?.bind (types[·]?) with
        | some (.ptr "many" _ c) => types[c]? == types[child]?
        | _ => false) do throw s!"{fnName}: slice constant has an incompatible pointer"
      -- The profile's exact `usize` width is checked with the normalized layouts (`Check.lean`).
      unless (match n.constTy?.bind (types[·]?) with
        | some (.int false 64) | some (.int false 32) => true | _ => false) do
        throw s!"{fnName}: slice constant length is not a 32- or 64-bit unsigned integer"
      return .sliceConst tyId p n
    else if let some fbitsJ := optField j "fbits" then
      let s ← fbitsJ.getStr?
      match ty with
      | .float n => return .float tyId (← parseHexNat fnName n s)
      | other => throw s!"{fnName}: 'fbits' constant of unexpected type {repr other}"
    else
      let s ← (← j.getObjVal? "val").getStr?
      match ty with
      | .struct _ "packed" fields =>
        if s.startsWith ".{" then return .int tyId (← parsePackedLit fnName types fields s)
        parseLeafVal fnName tyId ty s
      | _ => parseLeafVal fnName tyId ty s

/-- One lane of a shuffle mask: `{"a": i}`, `{"b": i}`, `{"u": true}`, or `{"v": Ref}`
(`docs/air-json.md`). -/
def parseMaskLane (fnName : String) (types : Array Ty) (j : Json) : Except String ShuffleLane := do
  unless (["a", "b", "u", "v"].filter fun k => (j.getObjVal? k).toOption.isSome).length == 1 do
    throw s!"{fnName}: a shuffle lane must have exactly one value form"
  if let some aJ := optField j "a" then return .a (← aJ.getNat?)
  else if let some bJ := optField j "b" then return .b (← bJ.getNat?)
  else if (← trueMarker j "u") then return .undef
  else if let some vJ := optField j "v" then return .value (← parseVal fnName types vJ)
  else throw s!"{fnName}: bad shuffle mask lane"

/-- One `outputs`/`inputs` entry of an `assembly` instruction. -/
def parseAsmOperand (fnName : String) (types : Array Ty) (j : Json) : Except String RawAsmOperand := do
  let constraint ← (← j.getObjVal? "constraint").getStr?
  let name ← (← j.getObjVal? "name").getStr?
  let ref ← match optField j "ref" with
    | some rj => some <$> parseVal fnName types rj
    | none => pure none
  return { constraint, name, ref }

/-- `assembly`'s asm-specific fields, given the instruction already carries `source`
(`docs/air-json.md`). -/
def parseAsm (fnName : String) (types : Array Ty) (j : Json) : Except String RawAsm := do
  let source ← (← j.getObjVal? "source").getStr?
  let isVolatile ← boolField j "volatile"
  let clobbersJ ← (← j.getObjVal? "clobbers").getArr?
  let clobbers ← clobbersJ.mapM Json.getStr?
  let outputsJ ← (← j.getObjVal? "outputs").getArr?
  let outputs ← outputsJ.mapM (parseAsmOperand fnName types)
  let inputsJ ← (← j.getObjVal? "inputs").getArr?
  let inputs ← inputsJ.mapM (parseAsmOperand fnName types)
  return { source, isVolatile, clobbers, outputs, inputs }

/-- Provenance fields are read leniently: a missing or malformed `src`/`column` yields no
source span, never a translation error or a guessed location. -/
def parseSrc? (j : Json) : Option RawSrc := do
  let s ← optField j "src"
  let file ← (s.getObjValAs? String "file").toOption
  let module ← (s.getObjValAs? String "module").toOption
  let declLine ← (s.getObjValAs? Nat "decl_line").toOption
  guard (declLine ≥ 1 && !file.isEmpty && file.length ≤ 4096 && !module.isEmpty && module.length ≤ 1024)
  pure { file, module, declLine }

mutual

partial def parseInst (fnName : String) (types : Array Ty) (j : Json) : Except String RawInst := do
  let id ← (← j.getObjVal? "id").getNat?
  let tag ← (← j.getObjVal? "tag").getStr?
  let ty ← match optField j "ty" with
    | some tyJ => some <$> tyJ.getNat?
    | none => pure none
  let args ← match optField j "args" with
    | some (.arr a) => a.mapM (parseVal fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'args' must be an array"
    | none => pure #[]
  let body ← match optField j "body" with
    | some (.arr a) => a.mapM (parseInst fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'body' must be an array"
    | none => pure #[]
  let thenBody ← match optField j "then" with
    | some (.arr a) => a.mapM (parseInst fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'then' must be an array"
    | none => pure #[]
  let elseBody ← match optField j "else" with
    | some (.arr a) => a.mapM (parseInst fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'else' must be an array"
    | none => pure #[]
  let cases ← match optField j "cases" with
    | some (.arr a) => a.mapM (parseCase fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'cases' must be an array"
    | none => pure #[]
  let target ← match optField j "target" with
    | some tj => some <$> tj.getNat?
    | none => pure none
  let param ← match optField j "param" with
    | some pj => some <$> pj.getNat?
    | none => pure none
  let callee ← match optField j "callee" with
    | some cj => some <$> parseVal fnName types cj
    | none => pure none
  let index ← match optField j "index" with
    | some ij => some <$> ij.getNat?
    | none => pure none
  let name ← match optField j "name" with
    | some nj => some <$> nj.getStr?
    | none => pure none
  let line ← match optField j "line" with
    | some lj => some <$> lj.getNat?
    | none => pure none
  let order ← match optField j "order" with
    | some oj => some <$> oj.getStr?
    | none => pure none
  let rmwOp ← match optField j "op" with
    | some oj => some <$> oj.getStr?
    | none => pure none
  let successOrder ← match optField j "success_order" with
    | some oj => some <$> oj.getStr?
    | none => pure none
  let failureOrder ← match optField j "failure_order" with
    | some oj => some <$> oj.getStr?
    | none => pure none
  let op ← match optField j "op" with
    | some oj => some <$> oj.getStr?
    | none => pure none
  let mask ← match optField j "mask" with
    | some (.arr a) => a.mapM (parseMaskLane fnName types)
    | some _ => throw s!"{fnName}: inst {id}: 'mask' must be an array"
    | none => pure #[]
  let asm ← match optField j "source" with
    | some _ => some <$> parseAsm fnName types j
    | none => pure none
  let global ← match optField j "global" with
    | some gj => some <$> gj.getNat?
    | none => pure none
  let unsupported ← boolField j "unsupported"
  let column := (optField j "column").bind (·.getNat?.toOption) |>.filter (· ≥ 1)
  return { id, tag, ty, args, body, thenBody, elseBody, cases, target, param, callee, index, name,
           line, column, src := parseSrc? j, order, rmwOp, successOrder, failureOrder, op, mask,
           asm, global, unsupported }

partial def parseCase (fnName : String) (types : Array Ty) (j : Json) : Except String RawCase := do
  let itemsJ ← (← j.getObjVal? "items").getArr?
  let items ← itemsJ.mapM (parseVal fnName types)
  let rangesJ ← (← j.getObjVal? "ranges").getArr?
  let ranges ← rangesJ.mapM fun rj => do
    let pair ← rj.getArr?
    let #[a, b] := pair | throw s!"{fnName}: switch range needs 2 elements"
    return (← parseVal fnName types a, ← parseVal fnName types b)
  let bodyJ ← (← j.getObjVal? "body").getArr?
  let body ← bodyJ.mapM (parseInst fnName types)
  return { items, ranges, body }

end

/-- One entry of the `globals` table (`docs/air-json.md`). -/
def parseGlobal (fnName : String) (types : Array Ty) (j : Json) : Except String Global := do
  let bool := boolField j
  let name ← match optField j "name" with
    | some n => some <$> n.getStr?
    | none => pure none
  let ty ← (← j.getObjVal? "ty").getNat?
  let init ← match optField j "init" with
    | some v =>
      let v ← parseVal fnName types v
      checkConstType fnName types ty v
      pure (some v)
    | none => pure none
  return { name, ty, isConst := ← bool "const",
           threadlocal := ← bool "threadlocal", isExtern := ← bool "extern", init }

/-- The identity fields every later decode step needs. -/
def parseHeader (j : Json) : Except String (String × Nat × String) := do
  let name ← (← j.getObjVal? "name").getStr?
  let schema ← (← j.getObjVal? "schema").getNat?
  let zigVersion ← (← j.getObjVal? "zig_version").getStr?
  return (name, schema, zigVersion)

/-- Decode everything but the profile, given an already validated (or, for diagnostics, a
placeholder) profile. -/
def parseFuncWith (j : Json) (profile : BuildProfile) : Except String RawFunc := do
  let (name, schema, zigVersion) ← parseHeader j
  let typesJ ← (← j.getObjVal? "types").getArr?
  let types ← typesJ.mapM parseTy
  -- Zig 0.17.0 removed the `i0` type; one in a 0.17.0 file is a malformed export.
  if zigVersion == "0.17.0" && types.any (· matches .int true 0) then
    throw s!"{name}: type i0 does not exist in Zig 0.17.0"
  validateTypeGraph name types
  let layouts ← typesJ.mapM parseLayout
  let paramsJ ← (← j.getObjVal? "params").getArr?
  let params ← paramsJ.mapM Json.getNat?
  let ret ← (← j.getObjVal? "ret").getNat?
  let bodyJ ← (← j.getObjVal? "body").getArr?
  let body ← bodyJ.mapM (parseInst name types)
  let globalsJ ← match optField j "globals" with
    | some g => g.getArr?
    | none => pure #[]
  let globals ← globalsJ.mapM (parseGlobal name types)
  let uncheckedIb ← match optField j "unchecked_ib" with
    | some u => do (← u.getArr?).mapM Json.getStr?
    | none => pure #[]
  return {
    schema
    zigVersion
    profile
    name
    params
    ret
    body
    types
    layouts
    globals
    src := parseSrc? j
    uncheckedIb
  }

def parseFunc (j : Json) : Except String RawFunc := do
  let (name, schema, zigVersion) ← parseHeader j
  let profile ← (BuildProfile.parse j schema zigVersion).mapError fun e => s!"{name}: {e}"
  parseFuncWith j profile

/-- Parse one `<fqn>.json` file's contents (`docs/air-json.md`). -/
def parseFile (contents : String) : Except String RawFunc := do
  let j ← StrictJson.parse contents
  parseFunc j

end Air2Lean.Raw
