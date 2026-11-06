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

namespace Zig.Full.Auto.Report

open Lean Meta Elab Tactic

/-- A term for display, with a separately accessible constant head. The text is Lean pretty
printing, not a serialization of the expression. -/
structure Term where
  head : Option String
  text : String
  deriving Inhabited, BEq, ToJson

def term (e : Expr) : MetaM Term := do
  let e ← instantiateMVars e
  return { head := e.getAppFn.constName?.map toString, text := (← ppExpr e).pretty }

/-- An unknown of an atom that a plan missed (P09-E3): its display name (`?u0`, …, as in the
atom's text) and its type. -/
structure Unknown where
  name : String
  type : Term
  deriving Inhabited, BEq, ToJson

/-- An atom that a plan missed, with the unknowns that the plan left in it (`noteWanted`). -/
structure Missing where
  atom : Term
  unknowns : Array Unknown
  deriving Inhabited, BEq, ToJson

/-- A rule whose precondition had no plan in the state (P09-E3): the rule, and the atoms of
its precondition that no atom of the state provided. -/
structure Plan where
  rule : Term
  missing : Array Missing
  deriving Inhabited, BEq, ToJson

/-- Where a residual was generated. `program` is the command at that point, not the entry's
whole program; `rule` includes the arguments of a caller-supplied rule. `plans` are the rules
of the stopped step whose precondition had no plan (only at a stop with no rule). -/
structure Origin where
  judgment : Option String
  source : Term
  program : Option Term
  rule : Option Term
  condition : String
  reason : String
  plans : Array Plan := #[]
  deriving Inhabited

/-- `plans` is left out when it is empty: the key is optional in schema version 1. -/
instance : ToJson Origin where
  toJson o := Json.mkObj <|
    [("judgment", toJson o.judgment), ("source", toJson o.source), ("program", toJson o.program),
     ("rule", toJson o.rule), ("condition", toJson o.condition), ("reason", toJson o.reason)] ++
    (if o.plans.isEmpty then [] else [("plans", toJson o.plans)])

structure Residual where
  index : Nat
  goal : Term
  origin : Origin
  deriving Inhabited, ToJson

/-- A postcondition that the walk inferred (P09-E2): of the goal (`kind` `return`: the
strongest post of the program's returns) or of a loop with a registered invariant and no
registered exit post (`kind` `loop_exit`, `program` the loop: the strongest post of its step's
exits). -/
structure Post where
  kind : String
  program : Option Term
  post : Term
  deriving Inhabited, ToJson

/-- Schema version 1. Array indices are local to this report; metavariable names are not IDs. -/
structure Result where
  schemaVersion : Nat := 1
  status : String
  residuals : Array Residual
  posts : Array Post := #[]
  deriving Inhabited

/-- `posts` is left out when it is empty: the key is optional in schema version 1. -/
instance : ToJson Result where
  toJson r := Json.mkObj <|
    [("schemaVersion", toJson r.schemaVersion), ("status", toJson r.status),
     ("residuals", toJson r.residuals)] ++
    (if r.posts.isEmpty then [] else [("posts", toJson r.posts)])

def line (r : Result) : String := "fsym-report " ++ (toJson r).compress

private structure Entry where
  originalTag : Name
  origin : Origin

/-- An unknown postcondition to report once the run ends: its kind and the loop it belongs to. -/
private structure PostEntry where
  post : MVarId
  kind : String
  program : Option Expr

private structure Collector where
  entries : IO.Ref (Std.HashMap Name Entry)
  posts : IO.Ref (Array PostEntry)
  tagPrefix : Name

private initialize collectors : IO.Ref (Std.HashMap Nat Collector) ← IO.mkRef {}
private initialize nextCollector : IO.Ref Nat ← IO.mkRef 0

private def current : CoreM (Option Collector) := do
  let id := (← getOptions).get `fsym.report.collector (0 : Nat)
  if id == 0 then return none
  return (← collectors.get).get? id

/-- A report is being collected: the executor renders report data only then. -/
def active : CoreM Bool := return (← current).isSome

/-- A missed atom `r` (`abstractMVars` of the atom: a `fun` over its unknowns) for display,
its unknowns named `?u0`, `?u1`, … in their order. -/
def missing (r : AbstractMVarsResult) : MetaM Missing := do
  let rec go (i : Nat) (e : Expr) (us : Array Unknown) : MetaM Missing := do
    match i, e with
    | i + 1, .lam _ ty b _ =>
      let n := Name.mkSimple s!"?u{r.numMVars - (i + 1)}"
      let u := { name := n.toString, type := ← term ty }
      withLocalDeclD n ty fun x => go i (b.instantiate1 x) (us.push u)
    | _, e => return { atom := ← term e, unknowns := us }
  go r.numMVars r.expr #[]

/-- A rule whose precondition had no plan, for display (`rule` as the caller passed it). -/
def plan (rule : Expr) (missed : Array AbstractMVarsResult) : MetaM Plan := do
  return { rule := ← term rule, missing := ← missed.mapM missing }

/-- Report the unknown postcondition `post` once the run ends, if the walk determines it
(P09-E2). `program` is the loop of a `loop_exit` post. -/
def notePost (post : MVarId) (kind : String) (program : Option Expr := none) : MetaM Unit := do
  let some c ← current | return
  c.posts.modify (·.push { post, kind, program })

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

/-- Keep the caller's original label even when a nested collection replaces an origin. -/
private def remember (c : Collector) (g : MVarId) (origin : Origin) : MetaM Unit := do
  let old ← g.getTag
  let originalTag := ((← c.entries.get).get? old).map (·.originalTag) |>.getD old
  let tag := Name.num c.tagPrefix (← c.entries.get).size
  c.entries.modify (·.insert tag { originalTag, origin })
  setLabel g tag

/-- Attach an origin only to residuals actually returned by a step. Formatting is performed
only inside a report collection. Goal tags make this survive successful state replacement and
disappear with an abandoned speculative branch. -/
def record (source : MVarId) (goals : List MVarId) (reason condition : String)
    (program : Option Expr := none) (rule : Option Expr := none) (plans : Array Plan := #[]) :
    TacticM Unit := do
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
          reason
          plans }
    origin? := some origin
    remember c g origin

def leave (source : MVarId) (goals : List MVarId) (reason condition : String)
    (program : Option Expr := none) (rule : Option Expr := none) (plans : Array Plan := #[]) :
    TacticM (List MVarId) := do
  record source goals reason condition program rule plans
  return goals

/-- The posts noted in the run that it determined: an unknown restored away by backtracking
(no longer declared) or left undetermined is not reported. -/
private def finishPosts (c : Collector) : MetaM (Array Post) := do
  let mut out := #[]
  for e in ← c.posts.get do
    let some decl := (← getMCtx).findDecl? e.post | continue
    unless ← e.post.isAssigned do continue
    let v ← instantiateMVars (mkMVar e.post)
    if v.hasExprMVar then continue
    out := out.push (← withLCtx decl.lctx decl.localInstances do
      return { kind := e.kind, program := ← e.program.mapM term, post := ← term v })
  return out

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
  return { status := if out.isEmpty then "complete" else "stopped", residuals := out,
           posts := ← finishPosts c }

/-- Collect one run. This neither emits a message nor changes which goals the walk returns. -/
def collect (run : TacticM (List MVarId)) : TacticM (List MVarId × Result) := do
  let parent ← current
  let id ← nextCollector.modifyGet fun n => (n + 1, n + 1)
  let c : Collector := { entries := ← IO.mkRef {}, posts := ← IO.mkRef #[],
                         tagPrefix := Name.num `fsym.report.goal id }
  collectors.modify (·.insert id c)
  try
    let (goals, report) ← withOptions (·.set `fsym.report.collector id) do
      let goals ← run
      return (goals, ← finish c goals)
    if let some parent := parent then
      for (g, residual) in goals.zip report.residuals.toList do
        remember parent g residual.origin
      parent.posts.modify (· ++ (← c.posts.get))
    return (goals, report)
  finally
    cleanup c
    collectors.modify (·.erase id)

/-- A human-readable stop message; a JSON-reporting walk emits just its report. -/
def stopMessage (msg : MessageData) : TacticM Unit := do
  unless (← current).isSome do logInfo msg

end Zig.Full.Auto.Report
