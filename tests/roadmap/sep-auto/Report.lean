import ZigLean.Sep.Full.AutoAll

/-!
# Residual attribution from `fsym` (P09-E1)

Incomplete proofs are inspected as metavariable goals, never admitted as declarations. The
ordinary entry and the reporting entry must return the same obligations and proof term.
-/

namespace SepAuto.Report

open Lean Meta Elab Tactic Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Zig.Full.Auto.Report

private def targetTypes (gs : List MVarId) : MetaM (List Expr) :=
  gs.mapM fun g => do instantiateMVars (← g.getType)

/-- The reporting entry neither discharges a residual nor changes the proof assembled by the
ordinary entry. It restores the caller's goal labels too. -/
private def inspect (ty : Expr) (reason condition : String) (rule : Option Name := none)
    (user : Array Expr := #[]) : TacticM Unit := do
  let g ← mkFreshExprSyntheticOpaqueMVar ty `original
  let s ← saveState
  -- Lean's backtracking deliberately keeps name generators and caches. Restart those too:
  -- this comparison requires the two walks to begin in identical executor state.
  let core ← getThe Core.State
  let metaState ← getThe Meta.State
  let restart : TacticM Unit := do
    s.restore
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState
  let plain ← withOptions (·.setBool `fsym.quiet true) (Auto.run g.mvarId! user)
  let plainTypes ← targetTypes plain
  let plainTags ← plain.mapM (·.getTag)
  let plainProof ← instantiateMVars g
  restart
  let repeated ← withOptions (·.setBool `fsym.quiet true) (Auto.run g.mvarId! user)
  unless (← targetTypes repeated) == plainTypes && (← instantiateMVars g) == plainProof do
    throwError "ordinary walk comparison did not restart identical executor state"
  restart
  let (gs, report) ← runReport g.mvarId! user
  let reportedTypes ← targetTypes gs
  let reportedProof ← instantiateMVars g
  unless reportedTypes == plainTypes && reportedProof == plainProof do
    throwError "reporting changed the walk: goals {reportedTypes} vs {plainTypes}; proof {reportedProof} vs {plainProof}"
  unless gs.length == 1 && report.status == "stopped" && report.residuals.size == 1 do
    throwError "expected exactly one residual: {line report}"
  let r := report.residuals[0]!
  unless r.index == 0 && r.origin.reason == reason && r.origin.condition == condition do
    throwError "wrong residual attribution: {line report}"
  unless r.origin.rule.bind (·.head) == rule.map toString do
    throwError "wrong rule: {line report}"
  unless (← gs.mapM (·.getTag)) == plainTags do
    throwError "reporting changed the goal label"
  -- Exercise the actual machine-readable line, not just the typed API.
  let .ok json := Json.parse ((line report).drop "fsym-report ".length).toString
    | throwError "invalid JSON report line: {line report}"
  unless (json.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
      (json.getObjValAs? String "status").toOption == some "stopped" do
    throwError "wrong JSON envelope: {line report}"
  let .ok residuals := json.getObjValAs? (Array Json) "residuals"
    | throwError "missing JSON residuals: {line report}"
  let .ok origin := residuals[0]!.getObjVal? "origin"
    | throwError "missing JSON origin: {line report}"
  unless residuals.size == gs.length &&
      (origin.getObjValAs? String "reason").toOption == some reason &&
      (origin.getObjValAs? String "condition").toOption == some condition do
    throwError "wrong JSON residual: {line report}"

/-- No rule describes this command. Its body is opaque to the walker. -/
opaque unavailable : MemM Unit := pure ()

/-- A deliberately impossible premise tests attribution of a selected rule's obligation. -/
theorem needs_false (h : False) : FTotalTriple emp unavailable (fun _ => emp) := h.elim

theorem update_needs_false (_h : False) : EUpd emp emp := EUpd.of_imp (fun _ h => h)

/-- info: fsym-report {"residuals":[],"schemaVersion":1,"status":"complete"} -/
#guard_msgs in
set_option fsym.report true in
theorem report_complete : FTotalTriple emp (pure ()) (fun _ => emp) := by
  fsym

/- A quiet ordinary entry does not emit a stop message or a report. -/
#guard_msgs in
set_option fsym.quiet true in
example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp unavailable (fun _ => emp))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let gs ← Auto.run g.mvarId!
    unless gs.length == 1 do throwError "quiet mode changed the residuals"
  trivial

/-- A failed earlier rule contributes no residual when the next rule completes the walk. -/
example (h : FTotalTriple emp unavailable (fun _ => emp)) : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp unavailable (fun _ => emp))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (_, report) ← runReport g.mvarId!
      #[← mkConstWithFreshMVarLevels ``needs_false, (← getLocalDeclFromUserName `h).toExpr]
    unless report.status == "complete" && report.residuals.isEmpty do
      throwError "a discarded rule leaked its residual attribution: {line report}"
  trivial

example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp unavailable (fun _ => emp))) none
    inspect ty "no_rule" "program"
  trivial

/-- Reachability stops are distinct from failed postconditions, in every sequential/thread
logic. The reporting call must leave the same panic goal open. -/
example : True := by
  run_tac do
    for kind in [``FTotalTriple, ``FTriple, ``FTTotalTriple, ``FTTriple] do
      let ty ← elabTerm (← `($(mkIdent kind) emp (throw .illegal : MemM Unit) (fun _ => emp))) none
      inspect ty "panic_not_refuted" "reachability"
  trivial

/-- The concurrent backend uses the same return attribution with its own structural rule. -/
example : True := by
  run_tac do
    let ty ← elabTerm (← `(CTriple (Tgt := Unit) emp (pure ()) (fun _ => ⟪False⟫))) none
    inspect ty "postcondition_not_proved" "postcondition" (some ``Auto.C.ret)
  trivial

example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp unavailable (fun _ => emp))) none
    inspect ty "side_condition_not_proved" "rule_premise" (some ``needs_false)
      #[← mkConstWithFreshMVarLevels ``needs_false]
  trivial

example : True := by
  run_tac do
    for kind in [``FTotalTriple, ``FTriple, ``FTTotalTriple, ``FTTriple] do
      let ty ← elabTerm (← `($(mkIdent kind) emp (pure ()) (fun _ => ⟪False⟫))) none
      inspect ty "postcondition_not_proved" "postcondition"
        (some (if kind == ``FTTotalTriple || kind == ``FTTriple then ``Auto.Th.ret else ``Auto.ret))
  trivial

/-- Distinct return obligations keep their own targets and the postcondition origin. -/
example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp (pure ()) (fun _ => ⟪False⟫ ⋆ ⟪(0 : Nat) = 1⟫))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId!
    unless gs.length == 2 && report.residuals.size == 2 &&
        report.residuals.all (fun r => r.origin.reason == "postcondition_not_proved") &&
        report.residuals[0]!.goal.text != report.residuals[1]!.goal.text do
      throwError "postcondition conjuncts lost: {line report}"
  trivial

/-- A caller update's own premise and the postcondition it leaves retain distinct origins. -/
example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp (pure ()) (fun _ => ⟪(0 : Nat) = 1⟫))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← runReport g.mvarId! #[← mkConstWithFreshMVarLevels ``update_needs_false]
    unless gs.length == 2 && report.residuals.map (·.origin.condition) ==
        #["update_premise", "postcondition"] do
      throwError "update premises and final postcondition were mixed: {line report}"
  trivial

/-- Attribution is rolled back with a failed speculative branch. -/
example : True := by
  run_tac do
    let g ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) `original
    let (gs, report) ← Auto.Report.collect do
      let s ← saveState
      Auto.Report.record g.mvarId! [g.mvarId!] "discarded" "program"
      s.restore
      Auto.Report.leave g.mvarId! [g.mvarId!] "selected" "program"
    unless report.residuals[0]!.origin.reason == "selected" && (← gs[0]!.getTag) == `original do
      throwError "attribution survived a restored speculative branch"
  trivial

/-- A budget stop keeps its distinct reason and its residual. -/
example : True := by
  run_tac do
    let ty ← elabTerm (← `(FTotalTriple emp (pure ()) (fun _ => emp))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, report) ← Auto.Report.collect (walk g.mvarId! #[] #[] 0)
    unless gs.length == 1 && report.residuals[0]!.origin.reason == "fuel_exhausted" do
      throwError "fuel stop lost: {line report}"
  trivial

/-- Duplicate residuals still get one report entry per list position. -/
example : True := by
  run_tac do
    let g ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) `original
    let (gs, report) ← Auto.Report.collect do
      Auto.Report.leave g.mvarId! [g.mvarId!, g.mvarId!] "selected" "program"
    unless gs.length == 2 && report.residuals.size == 2 &&
        (← g.mvarId!.getTag) == `original do
      throwError "duplicate residual lost its origin or original label"
  trivial

/-- Reporting metadata is removed even when a caller catches a walk error. -/
example : True := by
  run_tac do
    let g ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) `original
    try
      discard <| Auto.Report.collect do
        Auto.Report.record g.mvarId! [g.mvarId!] "selected" "program"
        throwError "deliberate failure"
    catch _ => pure ()
    unless (← g.mvarId!.getTag) == `original do
      throwError "report label survived an exception"
  trivial

/-- The protocol backend attributes its return obligation to the structural return rule. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) (pure ())
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "postcondition_not_proved" "postcondition" (some ``Zig.Conc.Proto.WP.pure')
  trivial

end SepAuto.Report
