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

end SepAuto.Report
