import Air2Lean.CanonSem

/-!
Native evidence for the final debug-definition-ID mapping. The generic kernel theorem
lives in `CanonSem`; this check binds actual normalized snapshots to that map under
TRU-02. A successful native comparison is not a kernel proof of Raw or normalization.
-/

namespace Air2Lean.CanonCertificate

-- Derive a complete structural comparison, including every operation and Func field.
-- These instances are local implementation details, not imported typeclass defaults.
deriving instance BEq for Op, SwitchCase, Inst, Global, Func
attribute [-instance] instBEqOp instBEqSwitchCase instBEqInst instBEqGlobal instBEqFunc
attribute [local instance] instBEqOp instBEqSwitchCase instBEqInst instBEqGlobal instBEqFunc

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

/-- Compact native evidence only: no generated data modules or per-function re-proofs.
Main owns the exact original arguments and returns before any output-file writes. -/
def emit (snapshots : Array (Nat × Func × Func)) : Except String String := do
  let changed ← checkBindings snapshots
  return (Lean.Json.mkObj [
    ("kind", Lean.toJson "canon-debug-native-binding"), ("version", Lean.toJson (1 : Nat)),
    ("functions", Lean.toJson snapshots.size), ("changed", Lean.toJson changed)]).compress ++ "\n"

end Air2Lean.CanonCertificate
