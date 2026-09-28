import Lean.Data.Json
import Air2Lean.Air.Op

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
  /-- `reduce`'s (`std.builtin.ReduceOp`) or `cmp_vector`'s (`std.math.CompareOperator`) operator
  name. -/
  op : Option String
  /-- `shuffle_one`, `shuffle_two` (0.15.2+), `shuffle` (0.14.1): the mask, in lane order. -/
  mask : Array ShuffleLane
  /-- `assembly`. -/
  asm : Option RawAsm
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
  name : String
  params : Array TyId
  ret : TyId
  body : Array RawInst
  types : Array Ty
  layouts : Array Layout
  globals : Array Global

/-- `some j` if `j`'s object has a non-null value at `k`, `none` if the key is absent (or
`null`). -/
def optField (j : Json) (k : String) : Option Json :=
  let v := j.getObjValD k
  if v.isNull then none else some v

/-- An integer constant as `fmtValue` prints it: optional leading `-`, then decimal digits. -/
def parseIntLit (fnName : String) (s : String) : Except String Int :=
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
    return .array len child
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
    -- A struct that is only behind a pointer can have no known fields (`no_fields`).
    if (optField j "no_fields").isSome then return .other name
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
    if (optField j "no_fields").isSome then return .other name
    let layout ← (← j.getObjVal? "layout").getStr?
    let tag ← match optField j "tag" with
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
    if (optField j "any").isSome || (optField j "inferred").isSome then return .errorSet none
    else
      let errsJ ← (← j.getObjVal? "errors").getArr?
      let errs ← errsJ.mapM Json.getStr?
      return .errorSet (some errs)
  | other => throw s!"unknown type kind: {other}"

/-- The memory facts of a type entry (schema 6): `abi_size`, `abi_align`, the fields' `offset`,
`sentinel`, and a pointer's `ptr_align`, `volatile`, `allowzero`, `host_size`. -/
def parseLayout (j : Json) : Except String Layout := do
  let nat? (k : String) : Except String (Option Nat) :=
    match optField j k with
    | some v => some <$> v.getNat?
    | none => pure none
  let bool (k : String) : Except String Bool :=
    match optField j k with
    | some v => v.getBool?
    | none => pure false
  let offsets ← match optField j "fields" with
    | some (.arr fs) => fs.filterMapM fun fj => match optField fj "offset" with
      | some o => some <$> o.getNat?
      | none => pure none
    | _ => pure #[]
  return { size := ← nat? "abi_size", align := ← nat? "abi_align", offsets,
           ptrAlign := ← nat? "ptr_align", sentinel := ← bool "sentinel",
           isVolatile := ← bool "volatile",
           allowzero := ← bool "allowzero", hostSize := (← nat? "host_size").getD 0 }

/-- A hex digit's value, `0`-`9`/`a`-`f`/`A`-`F`. -/
def hexDigitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A float's bits as `"0x"` + exactly `bits / 4` hex digits: an `fbits` constant
(`docs/air-json.md`) or a diff-protocol value (`tests/diff/Diff.lean`). -/
def parseHexNat (fnName : String) (bits : Nat) (s : String) : Except String Nat := do
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
  | .bool => return .bool (s == "true")
  | .void => return .void
  | other => throw s!"{fnName}: constant of unsupported type {repr other}"

/-- A `Ref`: `{"inst": id}`, `{"ty", "val"}`, `{"ty", "undef": true}`, `{"ty", "func",
"noreturn"}`, `{"ty", "err"}` (an error value, or an error-union constant in the error state —
`ty`'s `k` disambiguates) / `{"ty", "payload"}` (an error-union constant in the ok state; nested
`Ref`, recursively), `{"ty", "fbits"}` (a float constant, schema 3), or `{"ty", "some"}` (an
optional constant holding a payload; nested `Ref`, recursively) / `{"ty", "null": true}` (an
optional constant, `null`) (`docs/air-json.md`). -/
partial def parseVal (fnName : String) (types : Array Ty) (j : Json) : Except String Val := do
  if let some instJ := optField j "inst" then
    return .inst (← instJ.getNat?)
  else if let some funcJ := optField j "func" then
    let name ← funcJ.getStr?
    let noreturn := match optField j "noreturn" with
      | some b => b.getBool?.toOption.getD false
      | none => false
    return .func name noreturn
  else
    let tyId ← (← j.getObjVal? "ty").getNat?
    let some ty := types[tyId]?
      | throw s!"{fnName}: unknown type id {tyId} in constant ref"
    if optField j "undef" |>.isSome then
      return .undef tyId
    else if let some errJ := optField j "err" then
      let name ← errJ.getStr?
      match ty with
      | .errorSet _ => return .err tyId name
      | .errorUnion .. => return .errUnionErr tyId name
      | other => throw s!"{fnName}: 'err' constant of unexpected type {repr other}"
    else if let some payloadJ := optField j "payload" then
      match ty with
      | .errorUnion .. => return .errUnionOk tyId (← parseVal fnName types payloadJ)
      | other => throw s!"{fnName}: 'payload' constant of unexpected type {repr other}"
    else if let some someJ := optField j "some" then
      match ty with
      | .optional .. => return .optSome tyId (← parseVal fnName types someJ)
      | other => throw s!"{fnName}: 'some' constant of unexpected type {repr other}"
    else if (optField j "null").isSome then
      match ty with
      | .optional .. => return .optNull tyId
      | other => throw s!"{fnName}: 'null' constant of unexpected type {repr other}"
    else if let some enumJ := optField j "enum" then
      match ty with
      | .enum .. => return .enumTag tyId (← parseIntLit fnName (← enumJ.getStr?))
      | other => throw s!"{fnName}: 'enum' constant of unexpected type {repr other}"
    else if let some uvalJ := optField j "uval" then
      match ty with
      | .union _ _ (some _) fields =>
        -- The active field is the tag enum constant's position among the union fields; the
        -- tag enum lists its names in the same order (`docs/air-json.md`).
        let some tagJ := optField j "utag"
          | throw s!"{fnName}: tagged union constant without 'utag'"
        let .enumTag tagTy v ← parseVal fnName types tagJ
          | throw s!"{fnName}: union constant: 'utag' is not an enum constant"
        let some (.enum _ _ _ tagFields) := types[tagTy]?
          | throw s!"{fnName}: union constant: bad tag type {tagTy}"
        let some fname := (tagFields.find? (·.2 == v)).map (·.1)
          | throw s!"{fnName}: union constant: no tag field with value {v}"
        let some idx := fields.findIdx? (·.1 == fname)
          | throw s!"{fnName}: union constant: no field {fname}"
        return .unionVal tyId idx (← parseVal fnName types uvalJ)
      | other => throw s!"{fnName}: 'uval' constant of unexpected type {repr other}"
    else if let some elemsJ := optField j "elems" then
      return .agg tyId (← (← elemsJ.getArr?).mapM (parseVal fnName types))
    else if let some ptrJ := optField j "ptr" then
      if let some k := optField ptrJ "unsupported" then
        return .ptrOther tyId (← k.getStr?)
      return .ptrConst tyId (← (← ptrJ.getObjVal? "global").getNat?) (← (← ptrJ.getObjVal? "off").getNat?)
    else if let some pJ := optField j "slice_ptr" then
      return .sliceConst tyId (← parseVal fnName types pJ)
        (← parseVal fnName types (← j.getObjVal? "slice_len"))
    else if let some fbitsJ := optField j "fbits" then
      let s ← fbitsJ.getStr?
      match ty with
      | .float n => return .float tyId (← parseHexNat fnName n s)
      | other => throw s!"{fnName}: 'fbits' constant of unexpected type {repr other}"
    else
      let s ← (← j.getObjVal? "val").getStr?
      parseLeafVal fnName tyId ty s

/-- One lane of a shuffle mask: `{"a": i}`, `{"b": i}`, `{"u": true}`, or `{"v": Ref}`
(`docs/air-json.md`). -/
def parseMaskLane (fnName : String) (types : Array Ty) (j : Json) : Except String ShuffleLane := do
  if let some aJ := optField j "a" then return .a (← aJ.getNat?)
  else if let some bJ := optField j "b" then return .b (← bJ.getNat?)
  else if (optField j "u").isSome then return .undef
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
  let isVolatile := match optField j "volatile" with
    | some (.bool b) => b
    | _ => false
  let clobbersJ ← (← j.getObjVal? "clobbers").getArr?
  let clobbers ← clobbersJ.mapM Json.getStr?
  let outputsJ ← (← j.getObjVal? "outputs").getArr?
  let outputs ← outputsJ.mapM (parseAsmOperand fnName types)
  let inputsJ ← (← j.getObjVal? "inputs").getArr?
  let inputs ← inputsJ.mapM (parseAsmOperand fnName types)
  return { source, isVolatile, clobbers, outputs, inputs }

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
  let unsupported := match optField j "unsupported" with
    | some (.bool b) => b
    | _ => false
  return { id, tag, ty, args, body, thenBody, elseBody, cases, target, param, callee, index, name,
           line, op, mask, asm, unsupported }

partial def parseCase (fnName : String) (types : Array Ty) (j : Json) : Except String RawCase := do
  let itemsJ ← (← j.getObjVal? "items").getArr?
  let items ← itemsJ.mapM (parseVal fnName types)
  let rangesJ ← (← j.getObjVal? "ranges").getArr?
  let ranges ← rangesJ.mapM fun rj => do
    let pair ← rj.getArr?
    let some a := pair[0]? | throw s!"{fnName}: switch range needs 2 elements"
    let some b := pair[1]? | throw s!"{fnName}: switch range needs 2 elements"
    return (← parseVal fnName types a, ← parseVal fnName types b)
  let bodyJ ← (← j.getObjVal? "body").getArr?
  let body ← bodyJ.mapM (parseInst fnName types)
  return { items, ranges, body }

end

/-- One entry of the `globals` table (`docs/air-json.md`). -/
def parseGlobal (fnName : String) (types : Array Ty) (j : Json) : Except String Global := do
  let bool (k : String) : Except String Bool :=
    match optField j k with
    | some v => v.getBool?
    | none => pure false
  let name ← match optField j "name" with
    | some n => some <$> n.getStr?
    | none => pure none
  let init ← match optField j "init" with
    | some v => some <$> parseVal fnName types v
    | none => pure none
  return { name, ty := ← (← j.getObjVal? "ty").getNat?, isConst := ← bool "const",
           threadlocal := ← bool "threadlocal", isExtern := ← bool "extern", init }

def parseFunc (j : Json) : Except String RawFunc := do
  let name ← (← j.getObjVal? "name").getStr?
  let schema ← (← j.getObjVal? "schema").getNat?
  let zigVersion ← (← j.getObjVal? "zig_version").getStr?
  let typesJ ← (← j.getObjVal? "types").getArr?
  let types ← typesJ.mapM parseTy
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
  return { schema, zigVersion, name, params, ret, body, types, layouts, globals }

/-- Parse one `<fqn>.json` file's contents (`docs/air-json.md`). -/
def parseFile (contents : String) : Except String RawFunc := do
  let j ← Json.parse contents
  parseFunc j

end Air2Lean.Raw
