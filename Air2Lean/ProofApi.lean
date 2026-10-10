import Air2Lean.Memory
import Lean.Data.Json

/-! Opt-in proof interfaces (`--proof-api`, `docs/generated-code.md`).
Every emitted function receives a stable model abbreviation and unfolding lemma, and each
of its loops a body/again abbreviation, a body unfolding lemma and a step lemma. Their names
derive from the function's source identity (after generic-instance renumbering) and the
loop's pre-order position, never from AIR instruction IDs. Checked, straight-line scalar
functions additionally carry a normalized-IR index. These are unfolding boundaries, not
compiler correspondence.
-/
namespace Air2Lean
open Lean

/-- Injective source-name encoding, independent of declaration allocation order. -/
def proofApiName (source : String) : String :=
  "air2lean_api" ++ String.join (source.toUTF8.toList.map fun b => s!"_{b.toNat}")

/-- The loops of `f` in pre-order (an outer loop before the loops nested in it). The
position of a loop in this list is its stable `loop<k>` index. -/
def proofLoops (f : Func) : Array Inst :=
  f.allInsts.filter fun i => match i.op with | .loop _ | .loopSwitchBr .. => true | _ => false

/-- The stable names of loop `k` of the function with lemma base `base`:
`(body, again, body_unfold, step)`. -/
def proofLoopNames (base : String) (k : Nat) : String × String × String × String :=
  let loop := s!"{base}_loop{k}"
  (loop ++ "_body", loop ++ "_again", loop ++ "_body_unfold", loop ++ "_step")

/-- Every declaration name `--proof-api` emits for `f`, reserved before ordinary
declaration allocation. -/
def proofLemmaNames (f : Func) : Array String :=
  let base := proofApiName f.name
  #[base ++ "_model", base ++ "_unfold"] ++ ((Array.range (proofLoops f).size).flatMap fun k =>
    let (body, again, bodyUnfold, step) := proofLoopNames base k
    #[body, again, bodyUnfold, step])

/-- The lemma names of `f` as JSON fields: `model`, `unfold` and, if `f` has loops, `loops`. -/
def proofLemmaFields (f : Func) : List (String × Json) :=
  let base := proofApiName f.name
  let loops := (Array.range (proofLoops f).size).map fun k =>
    let (body, again, bodyUnfold, step) := proofLoopNames base k
    Json.mkObj [("body", .str body), ("again", .str again), ("body_unfold", .str bodyUnfold),
      ("step", .str step)]
  [("model", .str (base ++ "_model")), ("unfold", .str (base ++ "_unfold"))] ++
    if loops.isEmpty then [] else [("loops", .arr loops)]

/-- `proofLemmaFields` as one JSON object (the source-map sidecar's `proof_api`). -/
def proofLemmaIndex (f : Func) : Json := Json.mkObj (proofLemmaFields f)

private def proofType (f : Func) (id : TyId) : Option Json := do
  let ty ← f.types[id]?
  let shape ← match ty with
    | .int signed bits => some (Json.mkObj [("kind", .str "int"), ("signed", toJson signed), ("bits", toJson bits)])
    | .bool => some (.str "bool")
    | .void => some (.str "void")
    | .noreturn => some (.str "noreturn")
    | _ => none
  let layout ← f.layouts[id]?
  return Json.mkObj [("type", shape), ("size", toJson layout.size), ("align", toJson layout.align)]

private def proofVal (f : Func) : Val → Option Json
  | .inst id => some (Json.mkObj [("inst", toJson id)])
  | .int ty value => do
    let ty ← proofType f ty
    return Json.mkObj [("integer", .str (toString value)), ("type", ty)]
  | .bool value => some (Json.mkObj [("bool", toJson value)])
  | .void => some (.str "void")
  | _ => none

private def proofArith : ArithOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
private def proofMode : Mode → String
  | .checked => "checked" | .unchecked => "unchecked" | .wrap => "wrapping" | .sat => "saturating"

private def proofOp (f : Func) (op : Op) : Option Json := do
  let unary (name : String) (a : Val) : Option Json := do
    return Json.mkObj [("op", .str name), ("arg", ← proofVal f a)]
  let binary (name : String) (a b : Val) : Option Json := do
    return Json.mkObj [("op", .str name), ("args", .arr #[← proofVal f a, ← proofVal f b])]
  match op with
  | .arg index => return Json.mkObj [("op", .str "arg"), ("parameter", toJson index)]
  | .arith arith mode a b =>
    return Json.mkObj [("op", .str (proofArith arith)), ("mode", .str (proofMode mode)),
      ("args", .arr #[← proofVal f a, ← proofVal f b])]
  | .bit bit a b => binary (match bit with | .and => "bit-and" | .or => "bit-or" | .xor => "bit-xor") a b
  | .not a => unary "not" a
  | .neg a => unary "neg" a
  | .intCast _ a => unary "int-cast" a
  | .trunc a => unary "truncate" a
  | .bitcast a => unary "bitcast" a
  | .ret a => unary "return" a
  | _ => none

/-- Versioned facts use structural scalar types and canonical instruction IDs. Debug
locations are a separate map. Calls, loops, memory, anonymous functions and models are
outside this first slice; they are never assigned a misleading partial fingerprint. -/
def proofApiFacts (f : Func) : Option Json := do
  if (f.name.splitOn "__anon_").length > 1 || !f.globals.isEmpty then none else do
    let params ← f.params.mapM (proofType f)
    let ret ← proofType f f.ret
    let code := f.body.filter fun i => match i.op with | .line _ | .dbg .. => false | _ => true
    let instructions ← code.mapM fun i => do
      let ty ← proofType f i.ty
      let op ← proofOp f i.op
      return Json.mkObj [("id", toJson i.id), ("type", ty), ("operation", op)]
    return Json.mkObj [("format", .str "air2lean-scalar-ir-v1"), ("source", .str f.name),
      ("parameters", .arr params), ("return", ret), ("instructions", .arr instructions)]

/-- Debug information remains provenance, rather than entering semantic fingerprints. -/
def proofApiSourceMap (f : Func) : Json := Id.run do
  let mut line : Option Nat := none
  let mut entries := #[]
  for i in f.body do
    match i.op with
    | .line n => line := some n
    | .dbg .. => pure ()
    | _ => entries := entries.push (Json.mkObj [("instruction", toJson i.id), ("source_line", toJson line)])
  return .arr entries
end Air2Lean
