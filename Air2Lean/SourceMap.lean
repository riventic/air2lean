import Std.Data.HashMap
import Lean.Data.Json

/-!
# Source maps and canonical bodies for semantic fingerprints

`--source-map-json` writes a sidecar next to the generated Lean file
(`docs/stable-generation.md`). It never changes the generated Lean text. For each
emitted function the sidecar keeps:

* `source`: the function identity after generic-instance renumbering (`Anon.lean`),
  the key under which proof interfaces are compared;
* `air_name`, `air_file`: the exporter's original identity and storage file;
* `definition`: the emitted Lean declaration (and the `--proof-api` names, if any);
* `callees`: every function the body references (calls, function values, spawn targets);
* `canonical`: the AIR body with every debug instruction and every inlined callee's
  declaration site (`src`) removed, and instruction IDs
  renumbered `0, 1, …` in pre-order, so that exporter renumbering and source-line
  shifts do not change it;
* `lines`: `[instruction, line]` pairs mapping canonical IDs to the latest preceding
  `dbg_stmt` line. Lines are provenance only and are not part of `canonical`.

`scripts/semantic-fingerprints.py` hashes `canonical` together with the profile metadata and
the callees' fingerprints. This module has only core-Lean dependencies.
-/

namespace Air2Lean.SourceMap
open Lean

/-- AIR tags without semantics (the same set as `Raw.isDbgTag`). -/
def debugTags : List String :=
  ["dbg_stmt", "dbg_empty_stmt", "dbg_var_ptr", "dbg_var_val", "dbg_arg_inline"]

def isDebug (inst : Json) : Bool :=
  match inst.getObjValAs? String "tag" with
  | .ok tag => debugTags.contains tag
  | .error _ => false

private def arrayField (j : Json) (key : String) : Array Json :=
  match j.getObjVal? key with
  | .ok (.arr items) => items
  | _ => #[]

/-- The nested bodies of one instruction, in pre-order. -/
def nestedBodies (inst : Json) : Array (Array Json) :=
  #[arrayField inst "body", arrayField inst "then", arrayField inst "else"] ++
    (arrayField inst "cases").map (arrayField · "body")

/-- Non-debug instruction IDs in pre-order. -/
partial def canonicalIds (body : Array Json) (acc : Array Nat := #[]) : Array Nat :=
  body.foldl (init := acc) fun acc inst =>
    if isDebug inst then acc else
      let acc := match inst.getObjValAs? Nat "id" with
        | .ok id => acc.push id
        | .error _ => acc
      (nestedBodies inst).foldl (fun acc nested => canonicalIds nested acc) acc

private def remap (ids : Std.HashMap Nat Nat) (j : Json) : Json :=
  match j.getNat? with
  | .ok n => match ids[n]? with
    | some k => toJson k
    | none => j
  | .error _ => j

private def mapObject (j : Json) (f : String → Json → Json) : Json :=
  match j with
  | .obj kvs => Json.mkObj (kvs.foldl (fun acc k v => acc.push (k, f k v)) #[]).toList
  | other => other

/-- Values (operands, callees, constants): renumber every `{"inst": id}` reference. -/
partial def canonicalValue (ids : Std.HashMap Nat Nat) : Json → Json
  | .arr items => .arr (items.map (canonicalValue ids))
  | j@(.obj _) => mapObject j fun k v => if k == "inst" then remap ids v else canonicalValue ids v
  | j => j

mutual
partial def canonicalBody (ids : Std.HashMap Nat Nat) (body : Array Json) : Json :=
  .arr ((body.filter (!isDebug ·)).map (canonicalInst ids))

partial def canonicalInst (ids : Std.HashMap Nat Nat) (inst : Json) : Json :=
  -- An inlined callee's declaration site (`src`) is source provenance, like `dbg_stmt`.
  let inst := match inst with
    | .obj kvs => Json.mkObj (kvs.foldl (fun acc k v => if k == "src" then acc else acc.push (k, v)) #[]).toList
    | other => other
  mapObject inst fun k v =>
    if k == "id" || k == "target" then remap ids v
    else if k == "body" || k == "then" || k == "else" then
      match v with
      | .arr items => canonicalBody ids items
      | other => other
    else if k == "cases" then
      match v with
      | .arr cases => .arr (cases.map fun c => mapObject c fun ck cv =>
          match ck, cv with
          | "body", .arr items => canonicalBody ids items
          | _, _ => canonicalValue ids cv)
      | other => other
    else canonicalValue ids v
end

/-- Every function name referenced by a value inside `j`. -/
partial def callees (j : Json) (acc : Array String := #[]) : Array String :=
  match j with
  | .arr items => items.foldl (fun acc item => callees item acc) acc
  | .obj kvs => kvs.foldl (init := acc) fun acc k v =>
      match k, v with
      | "func", .str name | "comptime_fn", .str name => if acc.contains name then acc else acc.push name
      | _, _ => callees v acc
  | _ => acc

/-- `[canonical id, line]` for each non-debug instruction after a `dbg_stmt`. -/
partial def lineMap (ids : Std.HashMap Nat Nat) (body : Array Json)
    (state : Option Nat × Array Json := (none, #[])) : Option Nat × Array Json :=
  body.foldl (init := state) fun (line, acc) inst =>
    if isDebug inst then
      match inst.getObjValAs? String "tag", inst.getObjValAs? Nat "line" with
      | .ok "dbg_stmt", .ok n => (some n, acc)
      | _, _ => (line, acc)
    else
      let acc := match line, (inst.getObjValAs? Nat "id").toOption.bind (ids[·]?) with
        | some n, some id => acc.push (.arr #[toJson id, toJson n])
        | _, _ => acc
      (nestedBodies inst).foldl (fun st nested => lineMap ids nested st) (line, acc)

/-- One function's sidecar entry. `doc` is the AIR file after generic renumbering.
`proofApi` is the `--proof-api` lemma-name index (`proofLemmaIndex`), if any. -/
def record (doc : Json) (airName airFile definition : String) (proofApi : Option Json) :
    Json :=
  let body := arrayField doc "body"
  let order := canonicalIds body
  let ids : Std.HashMap Nat Nat := order.foldl (init := {}) fun m id =>
    if m.contains id then m else m.insert id m.size
  let source := (doc.getObjValAs? String "name").toOption.getD airName
  let field (k : String) := (doc.getObjVal? k).toOption.getD .null
  let canonical := Json.mkObj [("params", field "params"), ("ret", field "ret"),
    ("types", field "types"), ("globals", canonicalValue ids (field "globals")),
    ("body", canonicalBody ids body)]
  let referenced := callees (Json.arr #[canonical]) |>.qsort (· < ·)
  let api := proofApi.getD .null
  Json.mkObj [("source", .str source), ("air_name", .str airName), ("air_file", .str airFile),
    ("definition", .str definition), ("proof_api", api),
    ("callees", .arr (referenced.map Json.str)), ("canonical", canonical),
    ("lines", .arr (lineMap ids body).2)]

end Air2Lean.SourceMap
