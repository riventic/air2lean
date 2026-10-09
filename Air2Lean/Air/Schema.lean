import Lean.Data.Json

/-!
# AIR JSON schema table (deny by default)

One table lists, for every object kind of a schema-12 AIR file, its keys: required or
optional, and the JSON shape of each value (`docs/air-json.md` §Schema table). `validate`
walks a whole file against it before `Json.lean` decodes it. A key outside the table, a
missing required key, or a value of the wrong shape rejects the file. The decoder therefore
never defaults an absent flag or ignores an attribute that a newer exporter added: the next
omission or addition fails closed instead of changing the model silently.

The table also names the *semantic attributes* of a type entry that the translator does not
model, with the only value it accepts (`unmodeled`). The decoder records any other value in
`Layout.unmodeled`; `Check.checkTy` rejects every used type that has one. Unused entries of
the type table (std types the function never touches) do not reject the file.

Schemas 1–11 predate the table. They keep the historical permissive reader and are only
translated behind the explicit `--profile legacy-abi64-le` opt-in (`Air2Lean/Main.lean`).
-/

namespace Air2Lean.Schema

open Lean (Json)

/-- The JSON value shape of one key. -/
inductive Shape where
  | nat | str | bool | arr | obj
  /-- The literal `true` (a presence marker). -/
  | marker
  /-- One of these strings. -/
  | oneOf (values : List String)
  /-- A vector lane index: a natural number, `"runtime"` or `null`. -/
  | lane
  /-- A string or `null`. -/
  | strOrNull
  deriving BEq, Repr

def Shape.accepts : Shape → Json → Bool
  | .nat, v => v.getNat?.toOption.isSome
  | .str, v => v.getStr?.toOption.isSome
  | .bool, v => v.getBool?.toOption.isSome
  | .arr, v => v.getArr?.toOption.isSome
  | .obj, v => v.getObj?.toOption.isSome
  | .marker, v => v == .bool true
  | .oneOf values, v => match v.getStr? with
    | .ok s => values.contains s
    | .error _ => false
  | .lane, v => v.isNull || v == .str "runtime" || v.getNat?.toOption.isSome
  | .strOrNull, v => v.isNull || v.getStr?.toOption.isSome

def Shape.describe : Shape → String
  | .nat => "a natural number"
  | .str => "a string"
  | .bool => "a boolean"
  | .arr => "an array"
  | .obj => "an object"
  | .marker => "the literal true"
  | .oneOf values => s!"one of {values}"
  | .lane => "a lane index, \"runtime\" or null"
  | .strOrNull => "a string or null"

structure Key where
  name : String
  shape : Shape
  required : Bool := true

private def req (name : String) (shape : Shape) : Key := { name, shape }
private def opt (name : String) (shape : Shape) : Key := { name, shape, required := false }

/-- Module identity keys (B1, `docs/air-json.md` §Identity): the `module` of the file's
function, of a `func` ref (and `comptime_fn_module` with `comptime_fn`), of a named global and
of a struct, enum or union type. Required: a schema-12 file without its module identities is
rejected, and only legacy schemas (behind `--profile legacy-abi64-le`) lack them. -/
def moduleRequired : Bool := true

private def moduleKey : Key :=
  { name := "module", shape := .str, required := moduleRequired }

/-- A semantic attribute of a type entry, or of one of its fields, that the translator does not
model. Only `accepted` passes; another value is recorded in `Layout.unmodeled`. Absent counts as
`accepted` (only legacy schemas can omit a required attribute, see the module comment). -/
structure Unmodeled where
  /-- `true`: the key is on each element of the entry's `fields`. -/
  inField : Bool
  key : String
  accepted : Json
  what : String

/-- Keys of every type entry: the layout facts, absent when the compiler had no layout. -/
private def layoutKeys : List Key := [req "k" .str, opt "abi_size" .nat, opt "abi_align" .nat]

def containerLayouts : List String := ["auto", "extern", "packed"]
def pointerSizes : List String := ["one", "many", "slice", "c"]

/-- The keys of a type entry of kind `k` (`types[i]`). -/
def typeKeys : String → Option (List Key)
  | "int" => some [req "signed" .bool, req "bits" .nat]
  | "float" => some [req "bits" .nat]
  | "bool" | "void" | "noreturn" => some []
  | "ptr" => some [req "size" (.oneOf pointerSizes), req "const" .bool, req "child" .nat,
      opt "ptr_align" .nat, req "volatile" .bool, req "allowzero" .bool,
      req "address_space" .str, req "sentinel" .bool, opt "sentinel_byte" .str,
      req "host_size" .nat, opt "bit_offset" .nat, opt "vector_index" .lane]
  | "array" => some [req "len" .nat, req "child" .nat, req "sentinel" .bool]
  | "vector" => some [req "len" .nat, req "child" .nat]
  | "optional" => some [req "child" .nat]
  | "error_union" => some [req "error" .nat, req "payload" .nat]
  | "error_set" => some [opt "inferred" .marker, opt "any" .marker, opt "errors" .arr]
  | "struct" => some [req "name" .str, moduleKey, req "layout" (.oneOf containerLayouts),
      opt "no_fields" .marker, opt "fields" .arr]
  | "tuple" => some [req "fields" .arr]
  | "enum" => some [req "name" .str, moduleKey, req "tag" .nat, req "exhaustive" .bool,
      req "fields" .arr]
  | "union" => some [req "name" .str, moduleKey, req "layout" (.oneOf containerLayouts),
      opt "no_fields" .marker, opt "tag" .nat, opt "safety_tag" .nat, opt "fields" .arr]
  | "other" => some [req "name" .str]
  | _ => none

/-- The keys of one element of a type entry's `fields`. -/
def fieldKeys : String → List Key
  | "struct" | "tuple" => [opt "name" .str, req "ty" .nat, opt "offset" .nat, opt "comptime" .marker]
  | "union" => [req "name" .str, req "ty" .nat]
  | "enum" => [req "name" .str, req "value" .str]
  | _ => []

/-- Semantic attributes that the translator does not model, per type kind. -/
def unmodeledAttrs (kind : String) : List Unmodeled :=
  match kind with
  | "ptr" => [⟨false, "address_space", Json.str "generic",
      "a pointer outside the generic address space"⟩]
  | "struct" | "tuple" => [⟨true, "comptime", Json.bool false,
      "a comptime field (no runtime storage)"⟩]
  | _ => []

/-- The value forms of a `Ref` and the keys each form has besides the form key itself. -/
def refForms : List (String × List Key) :=
  [("inst", [req "inst" .nat]),
   ("func", [req "ty" .nat, req "func" .str, moduleKey, req "noreturn" .bool,
     opt "comptime_fn" .str, opt "comptime_fn_module" .str,
     -- Content-addressed instance identity (`docs/air-json.md` §Instances).
     opt "instance_key" .str, opt "comptime_fn_instance_key" .str]),
   -- An extern function (G1, `docs/air-json.md` §Extern calls): its linker symbol.
   ("extern", [req "ty" .nat, req "extern" .str, req "noreturn" .bool]),
   ("undef", [req "ty" .nat, req "undef" .marker]),
   ("err", [req "ty" .nat, req "err" .str]),
   ("payload", [req "ty" .nat, req "payload" .obj]),
   ("some", [req "ty" .nat, req "some" .obj]),
   ("null", [req "ty" .nat, req "null" .marker]),
   ("enum", [req "ty" .nat, req "enum" .str]),
   ("uval", [req "ty" .nat, opt "utag" .obj, req "uval" .obj]),
   ("elems", [req "ty" .nat, req "elems" .arr]),
   ("ptr", [req "ty" .nat, req "ptr" .obj]),
   ("slice_ptr", [req "ty" .nat, req "slice_ptr" .obj, req "slice_len" .obj]),
   ("fbits", [req "ty" .nat, req "fbits" .str]),
   ("val", [req "ty" .nat, req "val" .str])]

/-- A pointer constant's target: a global (`payload_base`: reached through an optional or
error-union payload, informational), null, or an unsupported base. -/
def ptrForms : List (String × List Key) :=
  [("global", [req "global" .nat, opt "payload_base" .marker, req "off" .nat]),
   ("null", [req "null" .marker, req "off" .nat]),
   ("unsupported", [req "unsupported" .str, req "off" .nat])]

def laneForms : List (String × List Key) :=
  [("a", [req "a" .nat]), ("b", [req "b" .nat]), ("u", [req "u" .marker]), ("v", [req "v" .obj])]

def topKeys : List Key :=
  [req "schema" .nat, req "zig_version" .str, req "target_endian" .str, req "profile" .obj,
   req "name" .str, moduleKey, opt "src" .obj, opt "instance_key" .str, opt "export" .obj,
   opt "externs" .arr, req "params" .arr, req "ret" .nat, req "body" .arr, opt "globals" .arr,
   req "types" .arr]

/-- An `export fn`'s linker symbol and calling convention (`export`, G1). -/
def exportKeys : List Key := [req "name" .str, req "cc" .str]

/-- One extern function the body calls (an `externs` entry, G1). -/
def externKeys : List Key :=
  [req "name" .str, req "library" .strOrNull, req "cc" .str, req "params" .arr, req "ret" .nat,
   req "varargs" .bool]

/-- A declaration site (`src`, I05): of the file's function and of a `dbg_inline_block`'s
inlined function. Diagnostics read it; translation does not. -/
def srcKeys : List Key := [req "file" .str, req "module" .str, req "decl_line" .nat]

/-- A named global (a `nav`: container-level `var` or `const`; `init` is absent for an extern
or unresolved one) or an unnamed constant (a `uav`, always initialized). -/
def globalKeys (named : Bool) : List Key :=
  if named then
    [req "name" .str, moduleKey, req "ty" .nat, req "const" .bool, req "threadlocal" .bool,
     req "extern" .bool, opt "init" .obj]
  else [req "ty" .nat, req "const" .bool, req "init" .obj]

def caseKeys : List Key := [req "items" .arr, req "ranges" .arr, req "body" .arr]

def asmOperandKeys : List Key := [req "constraint" .str, req "name" .str, opt "ref" .obj]

/-- The payload keys of each exported instruction tag, besides `id`, `tag` and `ty`. The tag
lists follow `zig-patch/air-json/json.zig` `writeInst` for every supported Zig version. A tag
without an entry is accepted only as `"unsupported": true`, which `Normalize` rejects. -/
def instPayload (tag : String) : Option (List Key) :=
  let args := req "args" .arr
  if binTags.contains tag || unTags.contains tag || tyOpTags.contains tag ||
      extraBinTags.contains tag || ["select", "mul_add", "aggregate_init"].contains tag then
    some [args]
  else match tag with
  | "atomic_load" => some [args, req "order" .str]
  | "atomic_rmw" => some [args, req "op" .str, req "order" .str]
  | "cmpxchg_weak" | "cmpxchg_strong" =>
    some [args, req "success_order" .str, req "failure_order" .str]
  | "reduce" | "reduce_optimized" | "cmp_vector" | "cmp_vector_optimized" =>
    some [args, req "op" .str]
  | "union_init" | "struct_field_ptr" | "struct_field_val" | "agg_field_val" | "field_parent_ptr" =>
    some [args, req "index" .nat]
  | "arg" => some [req "param" .nat]
  | "block" | "loop" => some [req "body" .arr]
  | "dbg_inline_block" => some [opt "src" .obj, req "body" .arr]
  | "call" | "call_always_tail" | "call_never_tail" | "call_never_inline" =>
    some [req "callee" .obj, args]
  | "dbg_var_ptr" | "dbg_var_val" | "dbg_arg_inline" => some [args, req "name" .str]
  | "br" | "switch_dispatch" => some [req "target" .nat, args]
  | "repeat" => some [req "target" .nat]
  | "cond_br" => some [args, req "then" .arr, req "else" .arr]
  | "try" | "try_cold" | "try_ptr" | "try_ptr_cold" => some [args, req "body" .arr]
  | "switch_br" | "loop_switch_br" => some [args, req "cases" .arr, req "else" .arr]
  | "dbg_stmt" => some [req "line" .nat, opt "column" .nat]
  -- 0.15.2+: the global's entry in `globals` (an older exporter marks the tag unsupported).
  | "runtime_nav_ptr" => some [req "global" .nat]
  | "assembly" => some [req "source" .str, req "volatile" .bool, req "clobbers" .arr,
      req "outputs" .arr, req "inputs" .arr]
  | "shuffle" | "shuffle_one" | "shuffle_two" => some [args, req "mask" .arr]
  | "alloc" | "ret_ptr" | "unreach" | "trap" | "dbg_empty_stmt" => some []
  | _ => none
where
  binTags : List String := ["add", "add_safe", "add_wrap", "add_sat", "sub", "sub_safe",
    "sub_wrap", "sub_sat", "mul", "mul_safe", "mul_wrap", "mul_sat", "div_float", "div_trunc",
    "div_floor", "div_exact", "rem", "mod", "bit_and", "bit_or", "xor", "cmp_lt", "cmp_lte",
    "cmp_eq", "cmp_gte", "cmp_gt", "cmp_neq", "bool_and", "bool_or", "store", "store_safe",
    "array_elem_val", "slice_elem_val", "ptr_elem_val", "shl", "shl_exact", "shl_sat", "shr",
    "shr_exact", "min", "max", "set_union_tag", "memset", "memset_safe", "memcpy", "memmove",
    "atomic_store_unordered", "atomic_store_monotonic", "atomic_store_release",
    "atomic_store_seq_cst",
    -- Zig 0.17.0 only (`Compat.isNewBinOp`).
    "div_ceil"]
  unTags : List String := ["is_null", "is_non_null", "is_err", "is_non_err", "ret", "ret_safe",
    "ret_load", "neg", "is_named_enum_value", "is_null_ptr", "is_non_null_ptr", "tag_name",
    "error_name", "is_err_ptr", "is_non_err_ptr", "sqrt", "sin", "cos", "tan", "exp", "exp2",
    "log", "log2", "log10", "floor", "ceil", "round", "trunc_float"]
  tyOpTags : List String := ["not", "bitcast", "load", "intcast", "intcast_safe", "trunc",
    "slice_ptr", "slice_len", "array_to_slice", "clz", "ctz", "popcount", "byte_swap",
    "bit_reverse", "abs", "optional_payload", "wrap_optional", "unwrap_errunion_payload",
    "unwrap_errunion_err", "wrap_errunion_payload", "wrap_errunion_err",
    "struct_field_ptr_index_0", "struct_field_ptr_index_1", "struct_field_ptr_index_2",
    "struct_field_ptr_index_3", "ptr_slice_len_ptr", "ptr_slice_ptr_ptr", "fptrunc", "fpext",
    "int_from_float", "int_from_float_safe", "float_from_int", "get_union_tag",
    "optional_payload_ptr", "optional_payload_ptr_set", "splat", "unwrap_errunion_payload_ptr",
    "unwrap_errunion_err_ptr", "errunion_payload_ptr_set",
    -- Zig 0.17.0's renamed and split casts (`Compat.isNewTyOp`; `Canon.tagAliases017`).
    "bit_cast", "bit_cast_safe", "int_cast", "int_cast_safe", "ptr_cast", "ptr_from_int",
    "int_from_ptr", "error_cast", "error_from_int", "int_from_error", "union_from_enum",
    "array_to_vector"]
  extraBinTags : List String := ["add_with_overflow", "sub_with_overflow", "mul_with_overflow",
    "shl_with_overflow", "slice_elem_ptr", "ptr_elem_ptr", "ptr_add", "ptr_sub", "slice"]

/-- Check one object against its keys: no other key, every required key, each value's shape. -/
def checkKeys (path : String) (keys : List Key) (j : Json) : Except String Unit := do
  let fields ← j.getObj? |>.mapError fun _ => s!"{path}: expected a JSON object"
  for (k, v) in fields.toArray do
    match keys.find? (·.name == k) with
    | none => throw s!"{path}: unknown key '{k}' (schema 12 rejects keys outside its table, \
        docs/air-json.md §Schema table)"
    | some key =>
      unless key.shape.accepts v do throw s!"{path}: '{k}' must be {key.shape.describe}"
  for key in keys do
    if key.required && (j.getObjVal? key.name).toOption.isNone then
      throw s!"{path}: missing required key '{key.name}'"

/-- The single form of a value with several forms (`Ref`, pointer target, shuffle lane). -/
def checkForm (path : String) (forms : List (String × List Key)) (j : Json) :
    Except String String := do
  let present := forms.filter fun (k, _) => (j.getObjVal? k).toOption.isSome
  let [(form, keys)] := present
    | throw s!"{path}: expected exactly one of {forms.map (·.1)}"
  checkKeys path keys j
  pure form

private def items (path : String) (j : Json) (k : String) : Except String (Array Json) :=
  match j.getObjVal? k with
  | .ok v => v.getArr? |>.mapError fun _ => s!"{path}: '{k}' must be an array"
  | .error _ => pure #[]

private def child? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

partial def checkRef (path : String) (j : Json) : Except String Unit := do
  let form ← checkForm path refForms j
  match form with
  | "payload" | "some" => checkRef s!"{path}.{form}" (j.getObjValD form)
  | "uval" =>
    if let some t := child? j "utag" then checkRef s!"{path}.utag" t
    checkRef s!"{path}.uval" (j.getObjValD "uval")
  | "elems" => for (e, i) in (← items path j "elems").zipIdx do checkRef s!"{path}.elems[{i}]" e
  | "ptr" => discard <| checkForm s!"{path}.ptr" ptrForms (j.getObjValD "ptr")
  | "slice_ptr" =>
    checkRef s!"{path}.slice_ptr" (j.getObjValD "slice_ptr")
    checkRef s!"{path}.slice_len" (j.getObjValD "slice_len")
  | _ => pure ()

partial def checkInst (path : String) (j : Json) : Except String Unit := do
  let tag := (j.getObjValD "tag").getStr?.toOption.getD ""
  let id := (j.getObjValD "id").getNat?.toOption.map toString |>.getD "?"
  let path := s!"{path} inst {id} ({tag})"
  let base := [req "id" .nat, req "tag" .str]
  let ty := req "ty" .nat
  if child? j "unsupported" |>.isSome then
    -- `inferred_alloc*` has no result type; every other tag has one.
    checkKeys path (base ++ [opt "ty" .nat, req "unsupported" .marker]) j
    return
  let some payload := instPayload tag
    | throw s!"{path}: tag '{tag}' has no schema entry and is not marked unsupported"
  checkKeys path (base ++ ty :: payload) j
  for (a, i) in (← items path j "args").zipIdx do checkRef s!"{path} args[{i}]" a
  if let some src := child? j "src" then checkKeys s!"{path} src" srcKeys src
  if let some c := child? j "callee" then checkRef s!"{path} callee" c
  for k in ["body", "then", "else"] do
    for i in (← items path j k) do checkInst s!"{path} {k}:" i
  for c in (← items path j "cases") do
    checkKeys s!"{path} case" caseKeys c
    for v in (← items path c "items") do checkRef s!"{path} case item" v
    for r in (← items path c "ranges") do
      let some #[lo, hi] := r.getArr?.toOption
        | throw s!"{path}: a switch range must be a two-element array"
      checkRef s!"{path} range" lo
      checkRef s!"{path} range" hi
    for i in (← items path c "body") do checkInst s!"{path} case:" i
  for lane in (← items path j "mask") do
    if (← checkForm s!"{path} mask" laneForms lane) == "v" then
      checkRef s!"{path} mask" (lane.getObjValD "v")
  for k in ["outputs", "inputs"] do
    for o in (← items path j k) do
      checkKeys s!"{path} {k}" asmOperandKeys o
      if let some r := child? o "ref" then checkRef s!"{path} {k}" r
  for c in (← items path j "clobbers") do
    unless Shape.str.accepts c do throw s!"{path}: clobbers must be strings"

def checkType (path : String) (j : Json) : Except String Unit := do
  let k := (j.getObjValD "k").getStr?.toOption.getD ""
  let path := s!"{path} ({k})"
  let some keys := typeKeys k | throw s!"{path}: unknown type kind '{k}'"
  checkKeys path (layoutKeys ++ keys) j
  for f in (← items path j "fields") do checkKeys s!"{path} field" (fieldKeys k) f
  for e in (← items path j "errors") do
    unless Shape.str.accepts e do throw s!"{path}: errors must be strings"

/-- Validate a whole schema-12 AIR document against the table. -/
def validate (j : Json) : Except String Unit := do
  checkKeys "AIR file" topKeys j
  if let some src := child? j "src" then checkKeys "AIR file src" srcKeys src
  if let some e := child? j "export" then checkKeys "AIR file export" exportKeys e
  for (e, i) in (← items "AIR file" j "externs").zipIdx do
    checkKeys s!"externs[{i}]" externKeys e
    for p in (← items s!"externs[{i}]" e "params") do
      unless Shape.nat.accepts p do throw s!"externs[{i}]: params must be type ids"
  let types ← items "AIR file" j "types"
  for (t, i) in types.zipIdx do checkType s!"types[{i}]" t
  for p in (← items "AIR file" j "params") do
    unless Shape.nat.accepts p do throw "AIR file: params must be type ids"
  for i in (← items "AIR file" j "body") do checkInst "body:" i
  for (g, i) in (← items "AIR file" j "globals").zipIdx do
    let path := s!"globals[{i}]"
    checkKeys path (globalKeys (child? g "name").isSome) g
    if let some init := child? g "init" then checkRef s!"{path}.init" init

/-- The unmodeled semantic attributes of one type entry with a non-accepted value, as
diagnostics. Applies to every schema: absent attributes are accepted. -/
def unmodeled (j : Json) : Array String := Id.run do
  let k := (j.getObjValD "k").getStr?.toOption.getD ""
  let fields := (j.getObjValD "fields").getArr?.toOption.getD #[]
  let mut out := #[]
  for attr in unmodeledAttrs k do
    let holders := if attr.inField then fields else #[j]
    for h in holders do
      if let some v := child? h attr.key then
        unless v == attr.accepted do
          let field := match child? h "name" with
            | some (.str n) => s!" (field '{n}')"
            | _ => ""
          out := out.push s!"{attr.what}{field}: '{attr.key}' is {v.compress}, the translator \
            models only {attr.accepted.compress}"
  return out

end Air2Lean.Schema
