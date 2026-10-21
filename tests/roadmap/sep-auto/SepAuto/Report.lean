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

/-- Both entries start from identical executor state, including Lean's non-backtracked
name generators. The repeated ordinary call first checks that the control is stable. -/
private def compareRuns (ty : Expr)
    (ordinary : MVarId → TacticM (List MVarId))
    (reporting : MVarId → TacticM (List MVarId × Result))
    (proofUses : List Name := []) : TacticM (List MVarId × Result) := do
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
  let plain ← withOptions (·.setBool `fsym.quiet true) (ordinary g.mvarId!)
  let plainTypes ← targetTypes plain
  let plainTags ← plain.mapM (·.getTag)
  let plainProof ← instantiateMVars g
  restart
  let repeated ← withOptions (·.setBool `fsym.quiet true) (ordinary g.mvarId!)
  unless (← targetTypes repeated) == plainTypes && (← instantiateMVars g) == plainProof &&
      (← repeated.mapM (·.getTag)) == plainTags do
    throwError "ordinary walk comparison did not restart identical executor state"
  restart
  let (gs, report) ← reporting g.mvarId!
  let reportedTypes ← targetTypes gs
  let reportedProof ← instantiateMVars g
  unless reportedTypes == plainTypes && reportedProof == plainProof do
    throwError "reporting changed the walk: goals {reportedTypes} vs {plainTypes}; proof {reportedProof} vs {plainProof}"
  unless (← gs.mapM (·.getTag)) == plainTags do
    throwError "reporting changed the goal label"
  for n in proofUses do
    unless (reportedProof.find? (·.isConstOf n)).isSome do
      throwError "diagnostic did not exercise the expected structural rule {n}"
  return (gs, report)

/-- The reporting entry neither discharges a residual nor changes the proof assembled by the
ordinary entry. It restores the caller's goal labels too. An explicit executor exercises a
bounded internal entry without adding another tactic or proof engine. -/
private def inspect (ty : Expr) (reason condition : String) (rule : Option Name := none)
    (user : Array Expr := #[]) (rulePresent : Bool := rule.isSome)
    (executor : Option (MVarId → TacticM (List MVarId)) := none)
    (programPresent : Bool := true) (proofUses : List Name := []) : TacticM Unit := do
  let ordinary := executor.getD (fun g => Auto.run g user)
  let reporting (g : MVarId) : TacticM (List MVarId × Result) :=
    match executor with
    | none => runReport g user
    | some execute => Auto.Report.collect (execute g)
  let (gs, report) ← compareRuns ty ordinary reporting proofUses
  unless gs.length == 1 && report.status == "stopped" && report.residuals.size == 1 do
    throwError "expected exactly one residual: {line report}"
  let r := report.residuals[0]!
  unless r.index == 0 && r.origin.reason == reason && r.origin.condition == condition do
    throwError "wrong residual attribution: {line report}"
  unless r.origin.rule.isSome == rulePresent && r.origin.rule.bind (·.head) == rule.map toString do
    throwError "wrong rule: {line report}"
  unless r.origin.program.isSome == programPresent do
    throwError "wrong residual program presence: {line report}"
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
    let u ← mkConstWithFreshMVarLevels ``update_needs_false
    let (gs, report) ← compareRuns ty
      (fun g => Auto.run g #[u]) (fun g => runReport g #[u])
    unless gs.length == 2 && report.residuals.map (·.origin.condition) ==
        #["update_premise", "postcondition"] do
      throwError "update premises and final postcondition were mixed: {line report}"
    let .ok json := Json.parse ((line report).drop "fsym-report ".length).toString
      | throwError "invalid update report: {line report}"
    let .ok residuals := json.getObjValAs? (Array Json) "residuals"
      | throwError "missing update residuals: {line report}"
    unless residuals.size == 2 do throwError "wrong update residual count"
    for (i, condition, reason) in [(0, "update_premise", "side_condition_not_proved"),
        (1, "postcondition", "postcondition_not_proved")] do
      let .ok origin := residuals[i]!.getObjVal? "origin"
        | throwError "missing update origin"
      unless (residuals[i]!.getObjValAs? Nat "index").toOption == some i &&
          (origin.getObjValAs? String "condition").toOption == some condition &&
          (origin.getObjValAs? String "reason").toOption == some reason do
        throwError "wrong update JSON attribution: {line report}"
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
    Tactic.tryCatch (do
      discard <| Auto.Report.collect do
        Auto.Report.record g.mvarId! [g.mvarId!] "selected" "program"
        throwError "deliberate failure") (fun _ => pure ())
    unless (← g.mvarId!.getTag) == `original do
      throwError "report label survived an exception"
  trivial

/-- An internal protocol-backend exercise attributes the return obligation to its structural
rule; the unfinished program proof exists only as a diagnostic metavariable. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) (pure ())
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "postcondition_not_proved" "postcondition" (some ``Zig.Conc.Proto.WP.pure')
  trivial

/-- The internal rule backend solves a segment before its post-dependent side conditions.
An impossible condition after that inference must retain the selected caller rule. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : Zig.ConcM Tgt Unit)
    (h : ∀ Qa : Unit → FAssn, FTTotalTriple emp (pure () : MemM Unit) Qa →
      (∀ a r, Qa a r → False) → P.WP t c (fun _ _ _ _ => True) G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "side_condition_not_proved" "rule_premise" none
      #[(← getLocalDeclFromUserName `h).toExpr] (rulePresent := true)
  trivial

/-! Additional diagnostic cases for the final Auto integration. -/

/-- A real bind rule first produces a false side condition while collection is active.
The ordinary walk must reject that candidate, take the complete library candidate and
return no leaked attribution. No unfinished program proof becomes a declaration. -/
example (w q : Ptr) : True := by
  run_tac do
    let ty ← elabTerm (← `(CTriple (Tgt := Unit)
      (aptsE $(mkIdent `w) (none : Option Ptr))
      ((ConcM.sync (.pick (weakCasPtrCount 8 $(mkIdent `w) (none : Option Ptr))) :
          ConcM Unit Nat) >>= fun k =>
        (ConcM.liftMem (cmpxchgWeakPtrAt k .relaxed .relaxed 8 $(mkIdent `w)
          (none : Option Ptr) (some $(mkIdent `q))) :
            ConcM Unit (Option (Option Ptr))) >>= fun r => pure r)
      (fun r => match r with
        | none => aptsE $(mkIdent `w) (some $(mkIdent `q))
        | some x => ⟪x = none⟫ ⋆ aptsE $(mkIdent `w) (none : Option Ptr)))) none
    let base ← mkConstWithFreshMVarLevels ``CTriple.weakCasPtr_bind
    let bad ← withLocalDeclD `impossible (mkConst ``False) fun h =>
      mkLambdaFVars #[h] base
    let s ← saveState
    let core ← getThe Core.State
    let metaState ← getThe Meta.State
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (_, probe) ← Auto.Report.collect do
      withRunCaches do
        discard <| arithSimpCtx
        let some (next, left) ← tryBindRule g.mvarId! bad
          | throwError "false-premise bind candidate did not apply"
        unless next.length == 2 && left.length == 1 &&
            (← instantiateMVars (← left[0]!.getType)).isConstOf ``False do
          throwError "bind candidate did not leave its actual false side condition"
        return left
    unless probe.residuals.size == 1 &&
        probe.residuals[0]!.origin.reason == "side_condition_not_proved" &&
        probe.residuals[0]!.origin.condition == "rule_premise" &&
        probe.residuals[0]!.origin.rule.isSome do
      throwError "active bind candidate had no side-condition origin: {line probe}"
    s.restore
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState
    let (gs, report) ← compareRuns ty
      (fun g => Auto.run g #[bad]) (fun g => runReport g #[bad])
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "discarded bind candidate leaked an origin: {line report}"
  trivial

/-- Unknown indirect-call arms are a real program term, not fabricated matcher metadata. -/
example {Tgt : Type} (fp : Ptr) (arms : List (Ptr × ConcM Tgt Unit)) : True := by
  run_tac do
    let ty ← elabTerm (← `(CTriple (Tgt := $(mkIdent `Tgt)) emp
      (Full.callIndirect $(mkIdent `fp) $(mkIdent `arms) (throw .illegal))
      (fun _ => emp))) none
    inspect ty "indirect_targets_not_literal" "program"
  trivial

/-- The concurrent panic case preserves its judgment, as do the sequential/thread cases. -/
example : True := by
  run_tac do
    let ty ← elabTerm (← `(CTriple (Tgt := Unit) emp
      (throw .illegal : ConcM Unit Unit) (fun _ => emp))) none
    inspect ty "panic_not_refuted" "reachability"
  trivial

/-- A side condition before the internal WP segments keeps the caller rule's origin. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit)
    (h : False → P.WP t c (fun _ _ _ _ => True) G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "side_condition_not_proved" "rule_premise" none
      #[(← getLocalDeclFromUserName `h).toExpr] (rulePresent := true)
  trivial

/-- A segment's more specific return origin must outrank the enclosing internal WP rule. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit)
    (h : FTTotalTriple emp (pure () : MemM Unit) (fun _ => ⟪False⟫) →
      P.WP t c (fun _ _ _ _ => True) G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "postcondition_not_proved" "postcondition" (some ``Auto.Th.ret)
      #[(← getLocalDeclFromUserName `h).toExpr]
  trivial

/-- A caller rule with an inferred post leaves its continuation, not a rule premise. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit)
    (h : ∀ Q : Unit → (ThreadId → γ) → Mem → Nat → Prop,
      (∀ a G' m' d, Q a G' m' d) → P.WP t c Q G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "postcondition_not_proved" "rule_continuation" none
      #[(← getLocalDeclFromUserName `h).toExpr] (rulePresent := true)
  trivial

/-- A fixed caller post still has to imply the requested post. The impossible implication
is inspected as a goal; the existing mono rule is the actual assembled proof path. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit)
    (h : P.WP t c (fun _ _ _ _ => True) G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "postcondition_not_proved" "postcondition" none
      #[(← getLocalDeclFromUserName `h).toExpr] (rulePresent := true)
      (proofUses := [``Zig.Conc.Proto.WP.mono])
  trivial

/-- Zero fuel is tested at both existing internal entries with exact proof equality. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) : True := by
  run_tac do
    let seqTy ← elabTerm (← `(FTotalTriple emp (pure ()) (fun _ => emp))) none
    inspect seqTy "fuel_exhausted" "program"
      (executor := some (fun g => walk g #[] #[] 0)) (programPresent := false)
    let wpTy ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) (pure ())
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect wpTy "fuel_exhausted" "program"
      (executor := some (fun g => wpWalk g #[] #[] 0)) (programPresent := false)
  trivial

/-- The internal WP panic goal remains the original run, rather than exfalso's False. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t)
      (throw .illegal : ConcM $(mkIdent `Tgt) Unit)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "panic_not_refuted" "reachability"
  trivial

/-- A symbolic internal command with no rule is left untouched and reported as such. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect ty "no_rule" "program"
  trivial

/-- Structural map/bind rules keep an inner command's more specific no-rule origin.
The assembled proof must contain the intended structural rule, so this is not merely
another invocation of the standalone no-rule example. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit) : True := by
  run_tac do
    let mapTy ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t)
      ((fun (_ : Unit) => (0 : Nat)) <$> $(mkIdent `c))
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect mapTy "no_rule" "program" (proofUses := [``Zig.Conc.Proto.WP.map])
    let bindTy ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t)
      ($(mkIdent `c) >>= fun (_ : Unit) => (throw .illegal : ConcM $(mkIdent `Tgt) Nat))
      (fun _ _ _ _ => False) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    inspect bindTy "no_rule" "program" (proofUses := [``Zig.Conc.Proto.WP.bind])
  trivial

/-! Diagnostic coverage for the current shared entry. -/

/-- Capture only this invocation's messages and preserve the surrounding command's log. -/
private def messagesOf (execute : TacticM (List MVarId)) :
    TacticM (List MVarId × List String) := do
  let old ← Core.getMessageLog
  Core.resetMessageLog
  try
    let gs ← execute
    let messages ← (← Core.getMessageLog).toList.mapM fun m => m.data.toString
    return (gs, messages)
  finally
    Core.setMessageLog old

/-- Exercise the public reporting branch, including its nested collector and message. -/
private def reportedTactic (tac : Syntax) (g : MVarId) :
    TacticM (List MVarId × Result) :=
  Auto.Report.collect do
    let (gs, messages) ← messagesOf do
      withOptions (·.setBool `fsym.report true) do evalTacticAt tac g
    unless messages.length == 1 && messages[0]!.startsWith "fsym-report " do
      throwError "public reporting tactic must emit exactly one report"
    return gs

/-- The actual public tactic emits one parseable report, one ordinary stop message, or
nothing, according to its two options. A stopped proof stays a diagnostic metavariable. -/
example : True := by
  run_tac do
    for (report, quiet) in [(false, false), (false, true), (true, false), (true, true)] do
      let ty ← elabTerm (← `(FTotalTriple emp unavailable (fun _ => emp))) none
      let g ← mkFreshExprSyntheticOpaqueMVar ty
      let (gs, messages) ← messagesOf do
        withOptions (fun o => (o.setBool `fsym.report report).setBool `fsym.quiet quiet) do
          if report then
            let (gs, collected) ← Auto.Report.collect do
              evalTacticAt (← `(tactic| fsym)) g.mvarId!
            unless collected.status == "stopped" && collected.residuals.size == 1 &&
                collected.residuals[0]!.origin.reason == "no_rule" do
              throwError "nested public report lost its residual origin"
            return gs
          else
            evalTacticAt (← `(tactic| fsym)) g.mvarId!
      unless gs.length == 1 do throwError "public options changed the stopped proof"
      if report then
        let [message] := messages | throwError "public report must emit exactly one message"
        unless message.startsWith "fsym-report " do throwError "missing public report prefix"
        let .ok json := Json.parse ((message.drop "fsym-report ".length).toString)
          | throwError "public report is not JSON"
        unless (json.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
            (json.getObjValAs? String "status").toOption == some "stopped" do
          throwError "wrong public stopped report"
        let .ok residuals := json.getObjValAs? (Array Json) "residuals"
          | throwError "missing public residuals"
        unless residuals.size == 1 do throwError "wrong public residual count"
        let .ok origin := residuals[0]!.getObjVal? "origin"
          | throwError "missing public origin"
        unless (origin.getObjValAs? String "reason").toOption == some "no_rule" do
          throwError "wrong public stop reason"
      else if quiet then
        unless messages.isEmpty do throwError "quiet public walk emitted a message"
      else
        let [message] := messages | throwError "ordinary walk lost its stop message"
        unless message.startsWith "fsym: no rule for the command" do
          throwError "ordinary walk changed its default stop message"
  trivial

/-- A caller's existential forward fact must reach both shared entries through the actual
public classifier. Without that argument the symbolic command has no applicable rule. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (c : ConcM Tgt Unit)
    (R : Prop) (S : Nat → Prop) (_hr : R) (fwd : R → ∃ k, S k)
    (stop : ∀ k, S k → P.WP t c (fun _ _ _ _ => True) G m n) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t) $(mkIdent `c)
      (fun _ _ _ _ => True) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    let tac ← `(tactic| fsym [$(mkIdent `fwd), $(mkIdent `stop)])
    let (gs, report) ← compareRuns ty (evalTacticAt tac) (reportedTactic tac)
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "caller existential facts were dropped by a shared entry"
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let stopped ← withOptions (·.setBool `fsym.quiet true) do
      evalTacticAt (← `(tactic| fsym [$(mkIdent `stop)])) g.mvarId!
    unless !stopped.isEmpty do
      throwError "existential-forward control did not require its caller argument"
  trivial

/-- A caller's fact about a memory step's actual run follows the same path with reporting
enabled, explicitly or from the local context. Without that fact, the generic store rule
cannot supply the unknown result proposition. -/
example {Tgt γ : Type} (P : Zig.Conc.Proto Tgt γ) (_hpart : P.Partial) (t : ThreadId)
    (G : ThreadId → γ) (m : Mem) (n : Nat) (own : ThreadId → Res) (rO : Res) (q : Ptr)
    (v w : BitVec 32) (_ho : FOwned own rO m) (_hc : m.current = t)
    (_htl : t < m.threads.size) (_hp : up (pts q 4 v) (own t)) (R : Prop)
    (fact : ∀ m₀ m₁ (x : Unit), ((store 4 q w).run m₀).run =
      some (.ok (x, m₁)) → R) : True := by
  run_tac do
    let ty ← elabTerm (← `($(mkIdent `P).WP $(mkIdent `t)
      (ConcM.liftMem (store 4 $(mkIdent `q) $(mkIdent `w)))
      (fun _ _ _ _ => $(mkIdent `R)) $(mkIdent `G) $(mkIdent `m) $(mkIdent `n))) none
    let tac ← `(tactic| fsym [$(mkIdent `fact)])
    let ordinary ← mkFreshExprSyntheticOpaqueMVar ty
    unless (← withOptions (·.setBool `fsym.quiet true)
        (evalTacticAt tac ordinary.mvarId!)).isEmpty do
      throwError "ordinary run-fact control did not close"
    let (gs, report) ← compareRuns ty (evalTacticAt tac) (reportedTactic tac)
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "caller run facts were dropped by a shared entry: {line report}"
    let localTac ← `(tactic| fsym)
    let (gs, report) ← compareRuns ty (evalTacticAt localTac) (reportedTactic localTac)
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "local run facts were dropped by a shared entry: {line report}"
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let missingFact ← g.mvarId!.clear (← getLocalDeclFromUserName `fact).fvarId
    let stopped ← withOptions (·.setBool `fsym.quiet true) do
      evalTacticAt localTac missingFact
    unless !stopped.isEmpty do
      throwError "run-fact control did not require its caller fact"
  trivial

/-! Task15 causal recursive-contract controls. -/

namespace RecursiveGroup

def descend (n : Nat) : MemM Unit := do
  Zig.enterFrame
  if n == 0 then pure () else descend (n - 1)
  Zig.leaveFrame
partial_fixpoint

def pre (t S : Nat) (a : Nat × Nat) : FAssn :=
  ⟪a.2 + frameBase * (a.1 + 1) ≤ S⟫ ⋆ (cur t ⋆ sp t S a.2)

def post (t S : Nat) (a : Nat × Nat) (_ : Unit) : FAssn := cur t ⋆ sp t S a.2

theorem self_total (t S : Nat) (a : Nat × Nat) :
    FTotalTriple (pre t S a) (descend a.1) (post t S a) := by
  refine FTotalTriple.rec_group (fun a : Nat × Nat => descend a.1)
    (pre t S) (post t S) Prod.fst ?_ a
  intro a smaller
  fsym

theorem self_thread_total (t S : Nat) (a : Nat × Nat) :
    FTTotalTriple (pre t S a) (descend a.1) (post t S a) := by
  refine FTTotalTriple.rec_group (fun a : Nat × Nat => descend a.1)
    (pre t S) (post t S) Prod.fst ?_ a
  intro a smaller
  fsym

/-- The general well-founded relation is not restricted to a Nat-valued measure. -/
theorem pair_measure (t S : Nat) (a : Nat × Nat) :
    FTotalTriple (pre t S a) (descend a.1) (post t S a) := by
  refine FTotalTriple.rec_group_wf (fun a : Nat × Nat => descend a.1)
    (pre t S) (post t S) id (InvImage.wf Prod.fst Nat.lt_wfRel.wf) ?_ a
  intro a smaller
  fsym

/-- An impossible same-input IH still permits the one initial base-case entry. -/
theorem initial_zero (t S D : Nat)
    (smaller : ∀ a : Nat × Nat, a.1 < 0 →
      FTotalTriple (pre t S a) (descend a.1) (post t S a)) :
    FTotalTriple (pre t S (0, D)) (descend 0) (post t S (0, D)) := by
  fsym

/-- These deliberately retain the existing caller-supplied bounded unfolding behavior. -/
theorem no_ih_total (t S D : Nat) :
    FTotalTriple (pre t S (1, D)) (descend 1) (post t S (1, D)) := by
  fsym [descend.eq_def]

theorem no_ih_partial (t S D : Nat) :
    FTriple (pre t S (1, D)) (descend 1) (post t S (1, D)) := by
  fsym [descend.eq_def]

/-- The relation cannot supply invocation data absent from the entire contract. -/
theorem unrelated_conditional (t S D : Nat)
    (unrelated : ∀ b : Nat, b < 0 →
      FTotalTriple (pre t S (1, D)) (descend 1) (post t S (1, D))) :
    FTotalTriple (pre t S (1, D)) (descend 1) (post t S (1, D)) := by
  fsym [descend.eq_def]


mutual
def left (n : Nat) : MemM Nat := do
  Zig.enterFrame
  let out ← if n == 0 then pure 0 else do
    right n
    pure n
  Zig.leaveFrame
  pure out
partial_fixpoint

def right (n : Nat) : MemM Unit := do
  Zig.enterFrame
  if n == 0 then pure () else do
    let _ ← left (n - 1)
    pure ()
  Zig.leaveFrame
partial_fixpoint
end

inductive Invocation where
  | left (n D : Nat)
  | right (n D : Nat)

def Return : Invocation → Type
  | .left _ _ => Nat
  | .right _ _ => Unit

def code : (a : Invocation) → MemM (Return a)
  | .left n _ => left n
  | .right n _ => right n

def rank : Invocation → Nat
  | .left n _ => 2 * n + 1
  | .right n _ => 2 * n

def inv (t S : Nat) : Invocation → FAssn
  | .left n D => ⟪D + frameBase * (2 * n + 2) ≤ S⟫ ⋆ (cur t ⋆ sp t S D)
  | .right n D => ⟪D + frameBase * (2 * n + 1) ≤ S⟫ ⋆ (cur t ⋆ sp t S D)

def out (t S : Nat) : (a : Invocation) → Return a → FAssn
  | .left n D => fun v => ⟪v = n⟫ ⋆ (cur t ⋆ sp t S D)
  | .right _ D => fun _ => cur t ⋆ sp t S D

/-- One fsym for the whole tagged step: sibling entry state and dependent returns both matter.
The left-to-right edge preserves n and decreases only the member rank. -/
theorem mutual_total (t S : Nat) (a : Invocation) :
    FTotalTriple (inv t S a) (code a) (out t S a) := by
  refine FTotalTriple.rec_group code (inv t S) (out t S) rank ?_ a
  intro a smaller
  fsym

/-- An inline dispatcher has the same positional boundary as a named definition. -/
theorem mutual_inline_total (t S : Nat) (a : Invocation) :
    FTotalTriple (inv t S a) (code a) (out t S a) := by
  refine FTotalTriple.rec_group (B := Return)
    (fun a : Invocation => match a with | .left n _ => left n | .right n _ => right n)
    (inv t S) (out t S) rank ?_ a
  intro a smaller
  fsym

def nestedCode (a : Invocation × Unit) : MemM (Return a.1) := code a.1

/-- Splitting an outer tuple must preserve the inner dependent invocation anchor. -/
theorem nested_total (t S : Nat) (a : Invocation × Unit) :
    FTotalTriple (inv t S a.1) (nestedCode a) (out t S a.1) := by
  refine FTotalTriple.rec_group nestedCode (fun a => inv t S a.1)
    (fun a => out t S a.1) (fun a => rank a.1) ?_ a
  intro a smaller
  fsym

def argOnly : Invocation → Nat
  | .left n _ | .right n _ => n

/-- Dropping the member rank exposes the exact nondecrease despite sufficient stack room. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ a : Invocation, argOnly a < 1 →
        FTotalTriple (inv 0 (frameBase * 4) a) (code a) (out 0 (frameBase * 4) a)) →
      FTotalTriple (inv 0 (frameBase * 4) (.left 1 0))
        (left 1) (out 0 (frameBase * 4) (.left 1 0)))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "expected exactly the dropped-rank decrease"
    gs[0]!.withContext do
      let expected ← mkAppM ``Nat.lt #[mkNatLit 1, mkNatLit 1]
      unless ← withDefault (isDefEq (← instantiateMVars (← gs[0]!.getType)) expected) do
        throwError "the framed same-argument edge did not leave its actual 1 < 1 target: {← gs[0]!.getType}"
    unless report.residuals.all (fun r => r.origin.reason != "fuel_exhausted") do
      throwError "dropped rank permitted recursive body unfolding"
  trivial

/-- Compiler membership includes a sibling for which no contract was supplied. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ a : Nat × Nat, 2 * a.1 + 1 < 3 →
        FTotalTriple (inv 0 (frameBase * 4) (.left a.1 a.2)) (left a.1)
          (out 0 (frameBase * 4) (.left a.1 a.2))) →
      FTotalTriple (inv 0 (frameBase * 4) (.left 1 0))
        (left 1) (out 0 (frameBase * 4) (.left 1 0)))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "expected exactly the missing-member call"
    gs[0]!.withContext do
      let (_, _, _, _, c, _) ← view gs[0]!
      let x := if c.isAppOfArity ``Bind.bind 6 then c.getArg! 4 else c
      let expected ← mkAppM ``right #[mkNatLit 1]
      unless ← withReducibleAndInstances (isDefEq (← recCommandHead x) expected) do
        throwError "a missing member contract did not retain right 1"
    unless report.residuals.all (fun r => r.origin.reason == "no_rule") do
      throwError "a missing member was unfolded or replaced by an invented obligation"
  trivial

def repeats (a : Nat) : MemM Unit := repeats a
partial_fixpoint

/-- Negative targets are actual typed residuals, with and without an explicit caller equation.
Existing compareRuns checks parity, assembled proof terms and original labels. -/
example : True := by
  run_tac do
    for extra in #[#[], #[← `(repeats.eq_def)]] do
      let ty ← Term.elabTerm (← `(∀ (a : Nat)
        (smaller : ∀ b : Nat, b < a → FTotalTriple emp (repeats b) (fun _ => emp)),
        FTotalTriple emp (repeats a) (fun _ => emp))) none
      let (gs, report) ← compareRuns ty (fun g => Auto.run g (extra := extra))
        (fun g => Auto.runReport g (extra := extra))
      unless gs.length == 1 && report.status == "stopped" do
        throwError "expected exactly the identical-argument decrease, not completion or fuel stop"
      gs[0]!.withContext do
        let some a := (← getLCtx).findDecl? (fun d =>
          if d.userName.eraseMacroScopes == `a then some d else none)
          | throwError "missing original input"
        let expected ← mkAppM ``Nat.lt #[a.toExpr, a.toExpr]
        unless ← withReducibleAndInstances (isDefEq (← instantiateMVars (← gs[0]!.getType)) expected) do
          throwError "identical recursion: expected {expected}, got {← gs[0]!.getType}"
      unless report.residuals.all (fun r => r.origin.reason != "fuel_exhausted") do
        throwError "repeated body unfolding exhausted fuel"
  trivial

/-- Initial stack room is independent of the impossible smaller-call family. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(∀ (t S D : Nat)
      (smaller : ∀ a : Nat × Nat, a.1 < 0 →
        FTotalTriple (⟪a.2 + frameBase * a.1 ≤ S⟫ ⋆ (cur t ⋆ sp t S a.2))
          (descend a.1) (post t S a)),
      FTotalTriple (⟪D ≤ S⟫ ⋆ (cur t ⋆ sp t S D)) (descend 0) (post t S (0, D)))) none
    let (gs, _) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "expected the actual one-frame-short obligation"
    gs[0]!.withContext do
      let lctx ← getLCtx
      let some d := lctx.findDecl? (fun d =>
        if d.userName.eraseMacroScopes == `D then some d else none)
        | throwError "missing caller depth"
      let some s := lctx.findDecl? (fun d =>
        if d.userName.eraseMacroScopes == `S then some d else none)
        | throwError "missing actual budget"
      let depth ← mkAppM ``Nat.add #[d.toExpr, mkConst ``Zig.frameBase]
      let expected ← mkAppM ``Nat.le #[depth, s.toExpr]
      unless ← withReducibleAndInstances (isDefEq (← instantiateMVars (← gs[0]!.getType)) expected) do
        throwError "stack shortage: expected {expected}, got {← gs[0]!.getType}"
  trivial
def caller (n : Nat) : MemM Unit := do
  Zig.enterFrame
  Zig.leaveFrame
  descend n

/-- An ordinary prefix cannot grant an initial entry to its nested group call. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(∀ (t S D : Nat)
      (smaller : ∀ n : Nat, n < 0 →
        FTotalTriple (pre t S (n, D)) (caller n) (post t S (n, D))),
      FTotalTriple (pre t S (0, D)) (caller 0) (post t S (0, D)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (_, g) ← g.mvarId!.intros
    withRunCaches do
      (← caches).userCtx.set (← g.withContext getLCtx)
      unless (← recRoot? g).isNone do
        throwError "ordinary caller prefix activated a nested entry"
  trivial

namespace CompleteContracts

def settles (n : Nat) : MemM Unit := if n == 0 then pure () else settles 0
partial_fixpoint

def rank (n : Nat) : Nat := if n == 0 then 1 else 0

theorem zero : FTotalTriple emp (settles 0) (fun _ => emp) := by
  fsym [settles.eq_def]

/-- A complete explicit contract is usable even though the active IH cannot decrease. -/
theorem explicit_complete (n : Nat) : FTotalTriple emp (settles n) (fun _ => emp) := by
  refine FTotalTriple.rec_group settles (fun _ => emp) (fun _ _ => emp) rank ?_ n
  intro a smaller
  fsym [zero]

/-- The specialized contract belongs to the current context; no client rule argument is needed. -/
theorem local_complete (n : Nat) : FTotalTriple emp (settles n) (fun _ => emp) := by
  refine FTotalTriple.rec_group settles (fun _ => emp) (fun _ _ => emp) rank ?_ n
  intro a smaller
  have finished := zero
  fsym

/-- A quantified complete local contract uses the same forall instantiation as an explicit rule. -/
theorem local_function_complete (n : Nat) : FTotalTriple emp (settles n) (fun _ => emp) := by
  refine FTotalTriple.rec_group settles (fun _ => emp) (fun _ _ => emp) rank ?_ n
  intro a smaller
  have finished := explicit_complete
  fsym

theorem local_after_subst (a : Nat × Nat) :
    FTotalTriple (⟪a.2 = 0⟫ ⋆ emp) (settles a.1) (fun _ => emp) := by
  refine FTotalTriple.rec_group (fun a : Nat × Nat => settles a.1)
    (fun a => ⟪a.2 = 0⟫ ⋆ emp) (fun _ _ => emp) (fun a => rank a.1) ?_ a
  intro a smaller
  have finished := zero
  fsym

theorem rejected (h : False) : FTotalTriple emp (settles 0) (fun _ => emp) := False.elim h

/-- A failed ordinary candidate rolls back before a complete contract wins. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ b : Nat, rank b < rank 1 →
        FTotalTriple emp (settles b) (fun _ => emp)) →
      FTotalTriple emp (settles 1) (fun _ => emp))) none
    let user := #[mkConst ``rejected, mkConst ``zero]
    let (gs, report) ← compareRuns ty (fun g => Auto.run g user)
      (fun g => Auto.runReport g user) [``zero]
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "a rejected ordinary candidate hid the complete contract or leaked attribution"
  trivial
/-- Without a complete contract, the actual failed decrease remains visible. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ b : Nat, rank b < rank 1 →
        FTotalTriple emp (settles b) (fun _ => emp)) →
      FTotalTriple emp (settles 1) (fun _ => emp))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "expected exactly the failed independent-contract decrease"
    gs[0]!.withContext do
      let expected ← mkAppM ``Nat.lt #[mkNatLit 1, mkNatLit 0]
      unless ← withDefault (isDefEq (← instantiateMVars (← gs[0]!.getType)) expected) do
        throwError "missing complete contract did not expose rank 0 < rank 1"
    unless report.residuals.all (fun r => r.origin.reason != "fuel_exhausted") do
      throwError "missing complete contract permitted body inlining"
  trivial

def needsStack (a : Nat × Nat) : FAssn :=
  if a.1 == 1 then emp else sp 0 4096 a.2

def remembers (a : Nat × Nat) (_ : Unit) : FAssn := ⟪a.2 = a.2⟫

/-- A known root does not determine an absent recursive-call resource or frame. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ a : Nat × Nat, a.1 < 1 →
        FTotalTriple (needsStack a) (settles a.1) (remembers a)) →
      FTotalTriple (needsStack (1, 0)) (settles 1) (remembers (1, 0)))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "expected the actual undetermined-resource call"
    gs[0]!.withContext do
      let (_, _, _, _, c, _) ← view gs[0]!
      let x := if c.isAppOfArity ``Bind.bind 6 then c.getArg! 4 else c
      let expected ← mkAppM ``settles #[mkNatLit 0]
      unless ← withReducibleAndInstances (isDefEq x expected) do
        throwError "missing stack frame was replaced by a guessed ghost or decrease"
      if (← instantiateMVars (← gs[0]!.getType)).hasExprMVar then
        throwError "undetermined-resource residual contains an invented unknown"
    unless report.residuals.all (fun r => r.origin.reason == "no_rule") do
      throwError "undetermined resource did not retain the actual call"
  trivial

section Registered

attribute [local fsym] zero

/-- The ordinary registered selector also beats the independently impossible IH edge. -/
theorem registered_complete (n : Nat) : FTotalTriple emp (settles n) (fun _ => emp) := by
  refine FTotalTriple.rec_group settles (fun _ => emp) (fun _ _ => emp) rank ?_ n
  intro a smaller
  fsym

example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ b : Nat, rank b < rank 1 →
        FTotalTriple emp (settles b) (fun _ => emp)) →
      FTotalTriple emp (settles 1) (fun _ => emp))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g) [``zero]
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "registered direct contract did not displace the false IH decrease"
  trivial

end Registered

section AliasRegistered

def zeroAlias := settles

@[local fsym] theorem registered_alias : FTotalTriple emp (zeroAlias 0) (fun _ => emp) := zero

example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ b : Nat, rank b < rank 1 →
        FTotalTriple emp (settles b) (fun _ => emp)) →
      FTotalTriple emp (settles 1) (fun _ => emp))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
      [``registered_alias]
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "registered alias contract was hidden by its raw key"
  trivial

end AliasRegistered

section DecidedRegistered

@[local fsym] theorem registered_decided :
    FTotalTriple emp (dite (true = true) (fun _ => settles 0) (fun _ => repeats 0))
      (fun _ => emp) := by
  simpa using zero

example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(
      (smaller : ∀ b : Nat, rank b < rank 1 →
        FTotalTriple emp (settles b) (fun _ => emp)) →
      FTotalTriple emp (settles 1) (fun _ => emp))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
      [``registered_decided]
    unless gs.isEmpty && report.status == "complete" && report.residuals.isEmpty do
      throwError "registered constructor-selected contract lost its equality transport"
  trivial

end DecidedRegistered

end CompleteContracts

def alias01 := descend
def alias02 := alias01
def alias03 := alias02
def alias04 := alias03
def alias05 := alias04
def alias06 := alias05
def alias07 := alias06
def alias08 := alias07
def alias09 := alias08
def alias10 := alias09
def alias11 := alias10
def alias12 := alias11
def alias13 := alias12
def alias14 := alias13
def alias15 := alias14
def alias16 := alias15
def alias17 := alias16

/-- Safe aliases are not limited by an arbitrary unfolding-count heuristic. -/
theorem aliases_total (t S : Nat) (a : Nat × Nat) :
    FTotalTriple (pre t S a) (alias17 a.1) (post t S a) := by
  refine FTotalTriple.rec_group (fun a : Nat × Nat => alias17 a.1)
    (pre t S) (post t S) Prod.fst ?_ a
  intro a smaller
  fsym

def routed (n : Nat) : MemM Unit :=
  if n == 0 then pure () else (fun f : Nat → MemM Unit => f (n - 1)) (fun m => routed m)
partial_fixpoint

theorem routed_total (n : Nat) : FTotalTriple emp (routed n) (fun _ => emp) := by
  refine FTotalTriple.rec_group routed (fun _ => emp) (fun _ _ => emp) id ?_ n
  intro a smaller
  fsym

/-- The invocation can be entirely logical data, inferred from owned memory. -/
def drain (p : Ptr) : MemM Unit := do
  let n ← Zig.load (BitVec 64) 8 p
  if n == 0 then pure () else do
    let next ← StateT.lift (Zig.sub false n 1)
    Zig.store 8 p next
    drain p
partial_fixpoint

theorem ghost_memory_total (p : Ptr) (w : BitVec 64) :
    FTotalTriple (up (pts p 8 w)) (drain p) (fun _ => up (pts p 8 (0 : BitVec 64))) := by
  refine FTotalTriple.rec_group (fun _ : BitVec 64 => drain p)
    (fun w => up (pts p 8 w)) (fun _ _ => up (pts p 8 (0 : BitVec 64))) BitVec.toNat ?_ w
  intro a smaller
  fsym

/-- A condition view touches neither branch bodies nor the traversal/cache state. -/
example : True := by
  run_tac do
    let expected ← Term.elabTerm (← `(descend 0)) none
    let other ← Term.elabTerm (← `(repeats 0)) none
    let some (_, members) ← recMember? expected | throwError "missing compiler member metadata"
    withRunCaches do
      (← caches).recBoundary.set (some { members, invocation := mkNatLit 0 })
      for term in #[← `(if true then descend 0 else repeats 0),
          ← `(if false then repeats 0 else descend 0),
          ← `(dite (true = true) (fun _ => descend 0) (fun _ => repeats 0))] do
        let c ← Term.elabTerm term none
        Term.synthesizeSyntheticMVarsNoPostponing
        let c ← instantiateMVars c
        let some r ← recConditionalView? c
          | throwError "constructor condition was not decided: {c}"
        unless ← withReducibleAndInstances (isDefEq r.expr expected) do
          throwError "conditional reducer executed or changed the selected member"
        let pf ← r.getProof' c
        unless ← withReducibleAndInstances (isDefEq (← inferType pf) (← mkEq c r.expr)) do
          throwError "conditional view discarded its equality proof"
        if (pf.find? (fun e => e.isConstOf ``descend.eq_def || e.isConstOf ``repeats.eq_def)).isSome then
          throwError "conditional proof exposed a member equation"
      unless (← (← caches).prog.get).isNone &&
          ((← (← caches).recBoundary.get).map (·.entered)) == some false do
        throwError "condition reduction contaminated program context or consumed entry"
    withLocalDeclD `flag (mkConst ``Bool) fun flag => do
      let c ← mkAppM ``ite #[← mkEq flag (mkConst ``Bool.true), expected, other]
      unless (← recConditionalView? c).isNone do
        throwError "an unknown condition triggered a search or case split"
  trivial

def flagged (a : Bool × Nat) : MemM Unit :=
  if a.1 then descend a.2 else repeats a.2

/-- Constructor-specialized discovery does not license an unknown initial conditional walk. -/
example : True := by
  run_tac do
    let ty ← Term.elabTerm (← `(∀ (t S D : Nat) (a : Bool × Nat)
      (smaller : ∀ b : Bool × Nat, b.2 < a.2 →
        FTotalTriple (pre t S (b.2, D)) (flagged b) (post t S (b.2, D))),
      FTotalTriple (pre t S (a.2, D)) (flagged a) (post t S (a.2, D)))) none
    let (gs, report) ← compareRuns ty (fun g => Auto.run g) (fun g => Auto.runReport g)
    unless gs.length == 1 do throwError "unknown initial ite was walked instead of left open"
    gs[0]!.withContext do
      let (_, _, _, _, c, _) ← view gs[0]!
      unless c.isAppOf ``flagged && recUnknownConditional (← recCommandHead c) do
        throwError "unknown entry changed its actual program or consumed a member body"
    unless report.residuals.all (fun r => r.origin.reason == "no_rule") do
      throwError "unknown initial conditional lost its explicit no-rule boundary"
  trivial

end RecursiveGroup

end SepAuto.Report
