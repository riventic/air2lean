import Lean.Data.Json
import Air2Lean.Air.Normalize
import Air2Lean.Air.Effects

/-!
# Op table

`air2lean --print-op-table` prints, for every AIR tag the translator names, what `normalizeOp`
decodes it to (by decoding a synthetic instruction, not by reading source), that op's effect
class (`Op.effects`) and its emitter route (`Op.emitRoute`), and the reviewed rejection reasons.
`scripts/coverage.py` reads the committed copy, `coverage/op-table.json`, instead of scanning
Lean source; `tests/roadmap/op-effects` checks that the copy is current and that every tag in
`normalizeOp` is in the table. Any other tag is rejected (`unknown AIR tag`).
-/

namespace Air2Lean

open Lean (Json ToJson toJson)

/-- A synthetic `tag` instruction with `n` operands and `op` as its operator name: enough
fields for `normalizeOp` to decode every tag of `decodedTags`. -/
private def probeInst (tag : String) (n : Nat) (op : String) : Raw.RawInst :=
  { id := 0, tag, ty := some 0, args := Array.replicate n .void, body := #[], thenBody := #[],
    elseBody := #[], cases := #[], target := some 0, param := some 0,
    callee := some (.func "f" false), index := some 0, name := none, line := some 0,
    order := some "seq_cst", rmwOp := some "Add", successOrder := some "seq_cst",
    failureOrder := some "seq_cst", op := some op, mask := #[],
    asm := some { source := "", isVolatile := false, clobbers := #[], outputs := #[], inputs := #[] },
    global := some 0, unsupported := false }

/-- The op that `normalizeOp` decodes `tag` to, if it decodes it. -/
def probeTag (tag : String) : Option Op :=
  [0, 1, 2, 3].findSome? fun n => ["eq", "Add"].findSome? fun op =>
    (normalizeOp "probe" (probeInst tag n op)).toOption

/-- The reasons table's tags, in table order. -/
private def reasonTags (table : Array (Array String × String)) : Array String :=
  table.flatMap (·.1)

/-- The op table (module doc), format 1. -/
def opTableJson : Json :=
  let tags := (decodedTags ++ reasonTags runtimeTagReasons ++ reasonTags exporterTagReasons).foldl
    (fun acc t => if acc.contains t then acc else acc.push t) #[]
  let rows := tags.map fun tag =>
    let op := if decodedTags.contains tag then probeTag tag else none
    Json.mkObj [
      ("tag", toJson tag),
      ("constructor", toJson (op.map (·.ctorName))),
      ("effect", toJson (op.map (·.effects.cls.name))),
      ("emit", toJson (op.map (·.emitRoute.name))),
      ("runtime_reason", toJson (runtimeTagReason? tag)),
      ("exporter_reason", toJson (exporterTagReason? tag))]
  Json.mkObj [
    ("format", toJson (1 : Nat)),
    ("unknown_tags", toJson "rejected"),
    ("fast_math_suffix", toJson fastMathSuffix),
    ("fast_math_reason", toJson optimizedFloatGuidance),
    ("tags", Json.arr rows)]

end Air2Lean
