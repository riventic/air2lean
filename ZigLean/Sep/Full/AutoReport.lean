import Lean

/-!
# Data reported by `fsym`

The executor supplies origins; this module collects and renders them without running proof
search. Temporary goal tags belong to Lean's metavariable state, so restoring a failed rule
also restores its attribution. The tags are removed before goals are returned to the caller.
-/

register_option fsym.report : Bool := {
  defValue := false
  descr := "emit a versioned JSON report of fsym's residual goals"
}

register_option fsym.quiet : Bool := {
  defValue := false
  descr := "suppress fsym's human-readable stop messages (reports are independent)"
}

namespace Zig.Full.Auto.Report

open Lean Meta Elab Tactic

/-- A term for display, with a separately accessible constant head. The text is Lean pretty
printing, not a serialization of the expression. -/
structure Term where
  head : Option String
  text : String
  deriving Inhabited, ToJson

def term (e : Expr) : MetaM Term := do
  let e ← instantiateMVars e
  return { head := e.getAppFn.constName?.map toString, text := (← ppExpr e).pretty }

/-- Where a residual was generated. `program` is the command at that point, not the entry's
whole program; `rule` includes the arguments of a caller-supplied rule. -/
structure Origin where
  judgment : Option String
  source : Term
  program : Option Term
  rule : Option Term
  condition : String
  reason : String
  deriving Inhabited, ToJson

structure Residual where
  index : Nat
  goal : Term
  origin : Origin
  deriving Inhabited, ToJson

/-- Schema version 1. Array indices are local to this report; metavariable names are not IDs. -/
structure Result where
  schemaVersion : Nat := 1
  status : String
  residuals : Array Residual
  deriving Inhabited, ToJson

def line (r : Result) : String := "fsym-report " ++ (toJson r).compress

private structure Entry where
  originalTag : Name
  origin : Origin

private structure Collector where
  entries : IO.Ref (Std.HashMap Name Entry)
  tagPrefix : Name

private initialize collectors : IO.Ref (Std.HashMap Nat Collector) ← IO.mkRef {}
private initialize nextCollector : IO.Ref Nat ← IO.mkRef 0

private def current : CoreM (Option Collector) := do
  let id := (← getOptions).get `fsym.report.collector (0 : Nat)
  if id == 0 then return none
  return (← collectors.get).get? id

/-- These labels are metadata, not names callers can use to find goals. Leave Lean's
user-name lookup table alone while they are installed. -/
private def setLabel (g : MVarId) (tag : Name) : MetaM Unit :=
  modify fun s => { s with mctx := s.mctx.setMVarUserNameTemporarily g tag }

private def cleanup (c : Collector) : MetaM Unit := do
  let entries ← c.entries.get
  if entries.isEmpty then return
  for (g, decl) in (← getMCtx).decls do
    if let some e := entries.get? decl.userName then setLabel g e.originalTag
  c.entries.set {}

/-- Attach an origin only to residuals actually returned by a step. Formatting is performed
only inside a report collection. Goal tags make this survive successful state replacement and
disappear with an abandoned speculative branch. -/
def record (source : MVarId) (goals : List MVarId) (reason condition : String)
    (program : Option Expr := none) (rule : Option Expr := none) : TacticM Unit := do
  if goals.isEmpty then return
  let some c ← current | return
  let mut origin? : Option Origin := none
  for g in goals do
    let old ← g.getTag
    -- A nested walk's more precise attribution takes precedence.
    if (← c.entries.get).contains old then continue
    let origin ← match origin? with
      | some o => pure o
      | none => source.withContext do
        let t ← instantiateMVars (← source.getType)
        return {
          judgment := t.getAppFn.constName?.map toString
          source := ← term t
          program := ← program.mapM (fun e => do term e)
          rule := ← rule.mapM (fun e => do term e)
          condition
          reason }
    origin? := some origin
    let tag := Name.num c.tagPrefix (← c.entries.get).size
    c.entries.modify (·.insert tag { originalTag := old, origin })
    setLabel g tag

def leave (source : MVarId) (goals : List MVarId) (reason condition : String)
    (program : Option Expr := none) (rule : Option Expr := none) : TacticM (List MVarId) := do
  record source goals reason condition program rule
  return goals

private def finish (c : Collector) (goals : List MVarId) : TacticM Result := do
  -- Read every origin before removing labels: a goal may occur more than once in the list.
  let origins ← goals.mapM fun g => do
    let some e := (← c.entries.get).get? (← g.getTag)
      | throwError "fsym report: residual goal has no origin"
    return e.origin
  cleanup c
  let mut out := #[]
  for (g, origin) in goals.zip origins do
    out := out.push { index := out.size, goal := ← g.withContext (term (← g.getType)), origin }
  return { status := if out.isEmpty then "complete" else "stopped", residuals := out }

/-- Collect one run. This neither emits a message nor changes which goals the walk returns. -/
def collect (run : TacticM (List MVarId)) : TacticM (List MVarId × Result) := do
  let id ← nextCollector.modifyGet fun n => (n + 1, n + 1)
  let c : Collector := { entries := ← IO.mkRef {}, tagPrefix := Name.num `fsym.report.goal id }
  collectors.modify (·.insert id c)
  try
    withOptions (·.set `fsym.report.collector id) do
      let goals ← run
      return (goals, ← finish c goals)
  finally
    cleanup c
    collectors.modify (·.erase id)

/-- The old human-readable messages are useful by default. Machine consumers can ask for a
quiet walk, and a JSON-reporting walk emits just its report. -/
def stopMessage (msg : MessageData) : TacticM Unit := do
  unless fsym.quiet.get (← getOptions) || (← current).isSome do logInfo msg

end Zig.Full.Auto.Report
