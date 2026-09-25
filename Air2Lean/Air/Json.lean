import Lean.Data.Json
import Air2Lean.Air.Op

/-!
# AIR JSON parser

Parses one exported function file (`docs/air-json.md`, schema 1 or 2) into `RawFunc`: a literal,
tag-agnostic mirror of the JSON. `Normalize.lean` turns a `RawFunc` into a version-independent
`Func` (`Air2Lean/Air/Op.lean`).

The `types` table and `Ref` shapes do not depend on the Zig version (`docs/air-json.md`), so
this file builds `Air2Lean.Ty` and `Air2Lean.Val` directly. Only instruction *tags* are
version-specific, so `RawInst` keeps `tag` as a raw string for `Normalize.lean` to interpret.
-/

namespace Air2Lean.Raw

open Lean (Json)

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
  /-- `struct_field_val`, `struct_field_ptr`. -/
  index : Option Nat
  /-- `dbg_var_ptr`, `dbg_var_val`, `dbg_arg_inline`. -/
  name : Option String
  /-- `dbg_stmt`. -/
  line : Option Nat
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

/-- `some j` if `j`'s object has a non-null value at `k`, `none` if the key is absent (or
`null`). -/
def optField (j : Json) (k : String) : Option Json :=
  let v := j.getObjValD k
  if v.isNull then none else some v

def parseTy (j : Json) : Except String Ty := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "int" =>
    let signed ← (← j.getObjVal? "signed").getBool?
    let bits ← (← j.getObjVal? "bits").getNat?
    return .int signed bits
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
  | "optional" =>
    let child ← (← j.getObjVal? "child").getNat?
    return .optional child
  | "struct" =>
    let name ← (← j.getObjVal? "name").getStr?
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
"noreturn"}`, or (schema 2) `{"ty", "err"}` (an error value, or an error-union constant in the
error state — `ty`'s `k` disambiguates) / `{"ty", "payload"}` (an error-union constant in the ok
state; `payload` is itself a `Ref`, recursively) (`docs/air-json.md`). An optional constant is a
`{"ty", "val"}`: the exporter's `fmtValue` prints `null` for `null`, or (recursively) the
payload's own text for a non-null value — `parseVal` tells the two apart by comparing `s` to
`"null"` once `ty`'s kind is `optional`. -/
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
    else
      let s ← (← j.getObjVal? "val").getStr?
      match ty with
      | .optional child =>
        if s == "null" then return .optNull tyId
        else
          let some childTy := types[child]?
            | throw s!"{fnName}: unknown type id {child} in optional constant"
          return .optSome tyId (← parseLeafVal fnName child childTy s)
      | _ => parseLeafVal fnName tyId ty s

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
  let unsupported := match optField j "unsupported" with
    | some (.bool b) => b
    | _ => false
  return { id, tag, ty, args, body, thenBody, elseBody, cases, target, param, callee, index, name,
           line, unsupported }

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

def parseFunc (j : Json) : Except String RawFunc := do
  let name ← (← j.getObjVal? "name").getStr?
  let schema ← (← j.getObjVal? "schema").getNat?
  let zigVersion ← (← j.getObjVal? "zig_version").getStr?
  let typesJ ← (← j.getObjVal? "types").getArr?
  let types ← typesJ.mapM parseTy
  let paramsJ ← (← j.getObjVal? "params").getArr?
  let params ← paramsJ.mapM Json.getNat?
  let ret ← (← j.getObjVal? "ret").getNat?
  let bodyJ ← (← j.getObjVal? "body").getArr?
  let body ← bodyJ.mapM (parseInst name types)
  return { schema, zigVersion, name, params, ret, body, types }

/-- Parse one `<fqn>.json` file's contents (`docs/air-json.md`). -/
def parseFile (contents : String) : Except String RawFunc := do
  let j ← Json.parse contents
  parseFunc j

end Air2Lean.Raw
