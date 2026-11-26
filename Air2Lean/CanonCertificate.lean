import Air2Lean.CanonSem
import Air2Lean.RenumberProgram
import Air2Lean.SemDrop
import Air2Lean.Memory

/-!
Native evidence for the final debug-definition-ID mapping and for `renumber`. The generic kernel
theorems live in `CanonSem` and `Renumber`; these checks bind actual normalized snapshots to
them under TRU-02. A successful native comparison is not a kernel proof of Raw or normalization.
-/

namespace Air2Lean.CanonCertificate

-- Derive a complete structural comparison, including every operation and Func field.
-- These instances are local implementation details, not imported typeclass defaults
-- (`Global`'s derived `BEq` is the default one, from `Air/Op.lean`).
deriving instance BEq for Op, SwitchCase, Inst, Func
attribute [-instance] instBEqOp instBEqSwitchCase instBEqInst instBEqFunc
attribute [local instance] instBEqOp instBEqSwitchCase instBEqInst instBEqFunc

/-- Complete structural native comparison, without exporting a default Func instance. -/
def sameFunction (before after : Func) : Bool := before == after

/-- Every actual after-function must equal the complete before-function with only debug
definition IDs mapped by the actual offset. This is native binding evidence under TRU-02.
It does not establish that either function has a non-stuck execution in Sem's fragment. -/
def checkBindings (snapshots : Array (Nat × Func × Func)) : Except String Bool := do
  let mut changed := false
  for (offset, before, after) in snapshots do
    let mapped := { before with body := DebugIds.mapDebugArray (fun id => id - offset) before.body }
    unless sameFunction mapped after do
      throw s!"{after.name}: normalized debug-ID snapshots do not match the actual Raw renumber offset"
    changed := changed || !(sameFunction before after)
  return changed

/-- `renumber`'s renaming: each instruction ID of `pre` with the ID at the same place of
`canonical` (`Func.allInsts` visits both bodies in the same order). -/
def renumberPairs (pre canonical : Func) : List (InstId × InstId) :=
  (pre.allInsts.toList.map (·.id)).zip (canonical.allInsts.toList.map (·.id))

/-- Native binding evidence for `Renumber.execFunc_rename` under TRU-02: `canonical` is the
complete `pre` with its instruction IDs renamed by `Renumber.zipRen` of the pairs, and no two
pairs share a target, so that renaming is injective (`Renumber.zipRen_inj`). -/
def renumberBound (pre canonical : Func) : Bool :=
  let pairs := renumberPairs pre canonical
  decide (pairs.map (·.2)).Nodup &&
    sameFunction (Renumber.renFunc (Renumber.zipRen pairs) pre) canonical

/-- The IDs of the instructions of `pre` that `post` does not have. -/
def droppedIds (pre post : Func) : List InstId :=
  let kept := post.allInsts.toList.map (·.id)
  (pre.allInsts.toList.map (·.id)).filter (!kept.contains ·)

/-- Native binding evidence for the drop theorems of `SemDrop` under TRU-02: `post` is the
complete `pre` without the instructions it no longer has (`sameFunction`, every field), and the
drop meets its obligation (`Drop.dropOk`): with `strict`, only debug information goes
(`Drop.execFunc_dropDebug`, an equality); without, also instructions that have no behaviour in
`Sem` (`Drop.execFunc_drop_le`, a refinement). The dropped set is only a guess: a wrong one fails
the final comparison. -/
def dropBound (strict : Bool) (pre post : Func) : Bool :=
  let dead := droppedIds pre post
  let D : InstId → Bool := fun id => dead.contains id
  Drop.dropOk strict D pre && sameFunction (Drop.dropFunc D pre) post

/-- Compact native evidence only: no generated data modules or per-function re-proofs.
Main owns the exact original arguments and returns before any output-file writes. -/
def emit (snapshots : Array (Nat × Func × Func)) : Except String String := do
  let changed ← checkBindings snapshots
  return (Lean.Json.mkObj [
    ("kind", Lean.toJson "canon-debug-native-binding"), ("version", Lean.toJson (1 : Nat)),
    ("functions", Lean.toJson snapshots.size), ("changed", Lean.toJson changed)]).compress ++ "\n"

end Air2Lean.CanonCertificate
