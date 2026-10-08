import ZigLean.Sep.LoopTemplate

/-!
# Invariant/measure templates for generated loop-switch dispatch

A labelled `switch` whose prongs `continue :sw v` is emitted as `Zig.loop (f.loopN ..) f.againN`:
the body reads the selector field `dispatchValueN` of the locals, runs one prong, and stores the
next selector on `.dispatchN v`; `f.againN` repeats exactly on `.dispatchN`. Any other exit
(`ret`, `brK`, an outer dispatch) leaves the loop.

`DispatchTemplate body again sel inv μ post` is the state-machine form of `LoopTemplate`:

* `sel : σ → κ` is the selector (for generated code, the `dispatchValueN` field);
* `inv : κ → σ → Assn` is a *state-indexed* invariant: `inv k s` holds when the machine is about
  to run prong `k` (`sel s = k`);
* `μ : σ → Nat × Nat` is a lexicographic measure, usually `(data, rank (sel s))`: a transition
  either consumes data (the first component drops) or keeps it and moves to a state of lower rank.
  A plain measure is `(n, 0)`, a pure state ranking `(0, rank k)`.

The one premise is per state: from `inv k s` with `sel s = k`, one body run either dispatches to a
state `sel s'` whose invariant holds at a lexicographically smaller measure, or exits with `post`.
`DispatchTemplate.total` proves the loop by well-founded induction on `μ`.

`DispatchSpec` is the same template for a body without memory (`Zig.M`), with propositions.

`dispatch_template inv μ post` applies the template to a `TotalTriple`/`Triple` goal about
`(Zig.loop body again).run s`, or a pure goal `∃ r, (Zig.loop body again).run s = pure r ∧ Q r`.
It derives the selector from the generated iterator `f.againN` (the field `dispatchValueN`; a
goal whose locals have no such field, such as an ordinary loop, is rejected) and leaves:

* `step.<state>`: one goal per selector state. An enum selector is split by its constructors;
  any other selector type needs `states [v₁, …]`, which leaves `step.<vᵢ>` for each listed value
  and `step.other` for every unlisted value (usually closed by an invariant that excludes them);
* `entry`: the precondition gives the invariant of the initial state;
* `exit`: `post` gives the goal's postcondition (closed automatically when they coincide).

`dispatch_template? …` also reports the remaining premises. With `using tac`, `tac` is run on
every per-state premise; the states where it fails are reported by name, with the failing goal.
-/

namespace Zig

open Assn

/-- The lexicographic order of `(data, rank)` measures. -/
def DispatchLt (a b : Nat × Nat) : Prop := Prod.Lex (· < ·) (· < ·) a b

theorem dispatchLt_wf : WellFounded DispatchLt :=
  (Prod.lex ⟨(· < ·), Nat.lt_wfRel.wf⟩ ⟨(· < ·), Nat.lt_wfRel.wf⟩).wf

theorem dispatchLt_iff {a b : Nat × Nat} : DispatchLt a b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 :=
  Prod.lex_def

/-- A transition that consumes data. -/
theorem DispatchLt.data {a b : Nat × Nat} (h : a.1 < b.1) : DispatchLt a b :=
  dispatchLt_iff.mpr (.inl h)

/-- A transition that keeps the data and lowers the state rank. -/
theorem DispatchLt.rank {a b : Nat × Nat} (h₁ : a.1 = b.1) (h₂ : a.2 < b.2) : DispatchLt a b :=
  dispatchLt_iff.mpr (.inr ⟨h₁, h₂⟩)

/-! ## Memory form -/

/-- The assertion after one prong: dispatch to the next state's invariant at a smaller
measure, or exit. -/
def dispatchNext {σ ε κ : Type} (again : ε → Bool) (sel : σ → κ) (inv : κ → σ → Assn)
    (μ : σ → Nat × Nat) (post : ε → σ → Assn) (s : σ) (r : ε × σ) : Assn :=
  if again r.1 then ⌜DispatchLt (μ r.2) (μ s)⌝ ∗ inv (sel r.2) r.2 else post r.1 r.2

theorem dispatchNext_repeat {σ ε κ : Type} {again : ε → Bool} {sel : σ → κ}
    {inv : κ → σ → Assn} {μ : σ → Nat × Nat} {post : ε → σ → Assn} {s s' : σ} {e : ε}
    {h : Heap} (ha : again e = true) (hlt : DispatchLt (μ s') (μ s)) (hi : inv (sel s') s' h) :
    dispatchNext again sel inv μ post s (e, s') h := by
  simp only [dispatchNext, ha, ↓reduceIte]
  exact sep_lift.mpr ⟨hlt, hi⟩

theorem dispatchNext_exit {σ ε κ : Type} {again : ε → Bool} {sel : σ → κ}
    {inv : κ → σ → Assn} {μ : σ → Nat × Nat} {post : ε → σ → Assn} {s s' : σ} {e : ε}
    {h : Heap} (ha : again e = false) (hp : post e s' h) :
    dispatchNext again sel inv μ post s (e, s') h := by
  simpa only [dispatchNext, ha, Bool.false_eq_true, ↓reduceIte] using hp

/-- The state-machine template of a dispatch loop: one prong per state, as a total triple. -/
structure DispatchTemplate {σ ε κ : Type} (body : MM σ ε) (again : ε → Bool) (sel : σ → κ)
    (inv : κ → σ → Assn) (μ : σ → Nat × Nat) (post : ε → σ → Assn) : Prop where
  step : ∀ k s, sel s = k → TotalTriple (inv k s) (body.run s) (dispatchNext again sel inv μ post s)

namespace DispatchTemplate

variable {σ ε κ : Type} {body : MM σ ε} {again : ε → Bool} {sel : σ → κ} {inv : κ → σ → Assn}
  {μ : σ → Nat × Nat} {post : ε → σ → Assn}

/-- The loop terminates from every state whose selector's invariant holds. -/
theorem total (t : DispatchTemplate body again sel inv μ post) (s : σ) :
    TotalTriple (inv (sel s) s) ((Zig.loop body again).run s) (fun r => post r.1 r.2) := by
  induction s using (InvImage.wf μ dispatchLt_wf).induction with
  | _ s ih =>
  intro m h hF hd hm hi hst
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hnext, hst'⟩ := t.step (sel s) s rfl m h hF hd hm hi hst
  cases ha : again e
  · simp only [dispatchNext, ha, Bool.false_eq_true, ↓reduceIte] at hnext
    refine ⟨(e, s'), m', h', ?_, hd', hm', hnext, hst'⟩
    rw [loopMM_run]
    simp [hr, ha, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]
  · simp only [dispatchNext, ha, ↓reduceIte] at hnext
    obtain ⟨hlt, hi'⟩ := sep_lift.mp hnext
    obtain ⟨r, m'', h'', hr', hd'', hm'', hp, hst''⟩ := ih s' hlt m' h' hF hd' hm' hi' hst'
    refine ⟨r, m'', h'', ?_, hd'', hm'', hp, hst''⟩
    rw [loopMM_run]
    simp [hr, ha, hr', bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]

theorem «partial» (t : DispatchTemplate body again sel inv μ post) (s : σ) :
    Triple (inv (sel s) s) ((Zig.loop body again).run s) (fun r => post r.1 r.2) :=
  (t.total s).toPartial

/-- The per-state premises for the listed selector values, and one premise for the rest. -/
theorem of_states (states : List κ)
    (listed : ∀ k ∈ states, ∀ s, sel s = k →
      TotalTriple (inv k s) (body.run s) (dispatchNext again sel inv μ post s))
    (other : ∀ k, k ∉ states → ∀ s, sel s = k →
      TotalTriple (inv k s) (body.run s) (dispatchNext again sel inv μ post s)) :
    DispatchTemplate body again sel inv μ post := by
  refine ⟨fun k => ?_⟩
  by_cases hk : k ∈ states
  · exact listed k hk
  · exact other k hk

end DispatchTemplate

/-- The target of `dispatch_template` on a total goal. -/
theorem TotalTriple.dispatch_template {σ ε κ : Type} {body : MM σ ε} {again : ε → Bool} {s : σ}
    {P : Assn} {Q : ε × σ → Assn} (sel : σ → κ) (inv : κ → σ → Assn) (μ : σ → Nat × Nat)
    (post : ε → σ → Assn) (step : DispatchTemplate body again sel inv μ post)
    (entry : ∀ h, P h → inv (sel s) s h) (exit : ∀ e s' h, post e s' h → Q (e, s') h) :
    TotalTriple P ((Zig.loop body again).run s) Q :=
  (step.total s).conseq entry (fun r h hp => exit r.1 r.2 h hp)

/-- The target of `dispatch_template` on a partial goal. The measure still has to decrease. -/
theorem Triple.dispatch_template {σ ε κ : Type} {body : MM σ ε} {again : ε → Bool} {s : σ}
    {P : Assn} {Q : ε × σ → Assn} (sel : σ → κ) (inv : κ → σ → Assn) (μ : σ → Nat × Nat)
    (post : ε → σ → Assn) (step : DispatchTemplate body again sel inv μ post)
    (entry : ∀ h, P h → inv (sel s) s h) (exit : ∀ e s' h, post e s' h → Q (e, s') h) :
    Triple P ((Zig.loop body again).run s) Q :=
  (TotalTriple.dispatch_template sel inv μ post step entry exit).toPartial

/-! ## Pure form -/

/-- The state-machine template of a dispatch loop without memory. -/
structure DispatchSpec {σ ε κ : Type} (body : M σ ε) (again : ε → Bool) (sel : σ → κ)
    (inv : κ → σ → Prop) (μ : σ → Nat × Nat) (post : ε → σ → Prop) : Prop where
  step : ∀ k s, sel s = k → inv k s → ∃ e s', body.run s = pure (e, s') ∧
    (if again e then DispatchLt (μ s') (μ s) ∧ inv (sel s') s' else post e s')

namespace DispatchSpec

variable {σ ε κ : Type} {body : M σ ε} {again : ε → Bool} {sel : σ → κ} {inv : κ → σ → Prop}
  {μ : σ → Nat × Nat} {post : ε → σ → Prop}

theorem run (t : DispatchSpec body again sel inv μ post) (s : σ) (hs : inv (sel s) s) :
    ∃ r, (Zig.loop body again).run s = pure r ∧ post r.1 r.2 := by
  induction s using (InvImage.wf μ dispatchLt_wf).induction with
  | _ s ih =>
  obtain ⟨e, s', hr, hnext⟩ := t.step (sel s) s rfl hs
  rw [loop_run, hr]
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hnext
    exact ⟨(e, s'), by simp [ha], hnext⟩
  · simp only [ha, ↓reduceIte] at hnext
    obtain ⟨r, hr', hp⟩ := ih s' hnext.1 hnext.2
    exact ⟨r, by simp [ha, hr'], hp⟩

theorem of_states (states : List κ)
    (listed : ∀ k ∈ states, ∀ s, sel s = k → inv k s → ∃ e s', body.run s = pure (e, s') ∧
      (if again e then DispatchLt (μ s') (μ s) ∧ inv (sel s') s' else post e s'))
    (other : ∀ k, k ∉ states → ∀ s, sel s = k → inv k s → ∃ e s', body.run s = pure (e, s') ∧
      (if again e then DispatchLt (μ s') (μ s) ∧ inv (sel s') s' else post e s')) :
    DispatchSpec body again sel inv μ post := by
  refine ⟨fun k => ?_⟩
  by_cases hk : k ∈ states
  · exact listed k hk
  · exact other k hk

end DispatchSpec

/-- The target of `dispatch_template` on a pure goal. -/
theorem DispatchSpec.dispatch_template {σ ε κ : Type} {body : M σ ε} {again : ε → Bool} {s : σ}
    {Q : ε × σ → Prop} (sel : σ → κ) (inv : κ → σ → Prop) (μ : σ → Nat × Nat)
    (post : ε → σ → Prop) (step : DispatchSpec body again sel inv μ post) (entry : inv (sel s) s)
    (exit : ∀ e s', post e s' → Q (e, s')) :
    ∃ r, (Zig.loop body again).run s = pure r ∧ Q r := by
  obtain ⟨r, hr, hp⟩ := step.run s entry
  exact ⟨r, hr, exit r.1 r.2 hp⟩

/-- Splitting `∀ k ∈ a :: l, P k` into the head premise and the rest. -/
theorem dispatch_forall_mem_cons {κ : Type} {P : κ → Prop} {a : κ} {l : List κ} (ha : P a)
    (hl : ∀ k ∈ l, P k) : ∀ k ∈ a :: l, P k :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

theorem dispatch_forall_mem_nil {κ : Type} {P : κ → Prop} : ∀ k ∈ ([] : List κ), P k :=
  fun _ h => nomatch h

end Zig

namespace Zig.DispatchTemplateTactic

open Lean Elab Tactic Meta

/-- The selector `fun s => s.dispatchValueN` of the generated iterator `f.againN`. -/
def selectorOf (again σ : Expr) : MetaM Expr := do
  let again ← instantiateMVars again
  let some fn := again.getAppFn.constName?
    | throwError "dispatch_template: the loop iterator {again} is not a generated `f.againN`"
  let last := fn.componentsRev.headD .anonymous |>.toString
  let id := (last.toList.drop 5).asString
  unless last.startsWith "again" && id.isNat do
    throwError "dispatch_template: the loop iterator {fn} is not a generated `f.againN`"
  let field := Name.mkSimple s!"dispatchValue{id}"
  let some struct := (← whnfR σ).getAppFn.constName?
    | throwError "dispatch_template: the loop state {σ} is not generated locals"
  unless (getStructureFields (← getEnv) struct).contains field do
    throwError "dispatch_template: {fn} is not a loop-switch dispatch target: \
      {struct} has no selector field {field}"
  withLocalDeclD `s σ fun s => do mkLambdaFVars #[s] (← mkProjection s field)

/-- The goal's loop: its iterator `again`, its initial locals `s`, and whether it uses memory. -/
def loopOf (goal : Expr) : MetaM (Expr × Expr × Bool) := do
  let goal ← whnfR goal
  let (c, mem) ← match goal.getAppFn.constName? with
    | some ``Zig.TotalTriple | some ``Zig.Triple => pure (goal.getArg! 2, true)
    | some ``Exists =>
      let .lam _ _ b _ := goal.getArg! 1
        | throwError "dispatch_template: unexpected goal {goal}"
      let b := b.instantiate1 (mkConst ``Unit)
      unless b.isAppOfArity ``And 2 && (b.getArg! 0).isAppOfArity ``Eq 3 do
        throwError "dispatch_template: unexpected goal {goal}"
      pure ((b.getArg! 0).getArg! 1, false)
    | _ => throwError "dispatch_template: the goal is not a TotalTriple, Triple or \
        `∃ r, _ = pure r ∧ _` about (Zig.loop body again).run s"
  -- `@StateT.run σ m α (@Zig.loop m _ _ _ ε body again) s`
  let c ← instantiateMVars c
  unless c.isAppOfArity ``StateT.run 5 && (c.getArg! 3).isAppOfArity ``Zig.loop 7 do
    throwError "dispatch_template: the goal is not about (Zig.loop body again).run s"
  pure ((c.getArg! 3).getArg! 6, c.getArg! 4, mem)

/-- Is `κ` an enumeration (an inductive whose constructors have no fields)? -/
def isEnum (κ : Expr) : MetaM Bool := do
  let some n := (← whnfR κ).getAppFn.constName? | return false
  let some (.inductInfo i) := (← getEnv).find? n | return false
  if i.isRec || i.numIndices != 0 || i.ctors.isEmpty then return false
  i.ctors.allM fun c => do
    let .ctorInfo ci ← getConstInfo c | return false
    return ci.numFields == 0

/-- Tag a goal and `beta`-reduce the selector applications in it. -/
def tidy (g : MVarId) (tag : Name) : TacticM MVarId := do
  g.setTag tag
  match ← observing? (evalTacticAt (← `(tactic| dsimp only)) g) with
  | some [g'] => pure g'
  | _ => pure g

/-- Split the `step` premise into one goal per state. -/
def splitStates (step : MVarId) (κ : Expr) (mem : Bool) (states : Option (Array Term)) :
    TacticM (List MVarId) := do
  match states with
  | some ks =>
    let list ← `([$ks,*])
    let rule := mkIdent (if mem then ``Zig.DispatchTemplate.of_states else ``Zig.DispatchSpec.of_states)
    let [listed, other] ← evalTacticAt (← `(tactic| refine $rule $list ?listed ?other)) step
      | throwError "dispatch_template: could not split the step premise by states"
    let mut goals := #[]
    let mut g := listed
    for k in ks do
      let [hd, tl] ← evalTacticAt
          (← `(tactic| refine Zig.dispatch_forall_mem_cons ?head ?tail)) g
        | throwError "dispatch_template: could not split the state {k}"
      goals := goals.push (← tidy hd (`step ++ Name.mkSimple (toString k.raw.prettyPrint).trim))
      g := tl
    discard <| evalTacticAt (← `(tactic| exact Zig.dispatch_forall_mem_nil)) g
    return goals.toList ++ [← tidy other `step.other]
  | none =>
    unless ← isEnum κ do
      throwError "dispatch_template: the selector type {κ} is not an enumeration; \
        name its states with `states [v₁, …]`"
    let [g] ← evalTacticAt (← `(tactic| refine ⟨fun k => ?_⟩)) step
      | throwError "dispatch_template: unexpected step premise"
    let (fs, g) ← g.introN 1
    let subgoals ← g.cases fs[0]!
    subgoals.toList.mapM fun sg => do
      let tag := `step ++ Name.mkSimple (sg.ctorName.componentsRev.headD .anonymous).toString
      tidy sg.mvarId tag

/-- Apply the template; return the remaining premises (other goals untouched). -/
def applyTemplate (inv μ post : Term) (states : Option (Array Term)) :
    TacticM (List MVarId) := do
  let g :: others ← getGoals | throwError "dispatch_template: no goals"
  let goal ← g.getType
  let (again, s, mem) ← g.withContext <| loopOf goal
  let σ ← g.withContext <| inferType s
  let sel ← g.withContext <| selectorOf again σ
  let κ ← g.withContext <| do inferType (mkApp sel s)
  let selStx ← g.withContext <| Term.exprToSyntax sel
  let rule ← if mem then
      match (← whnfR goal).getAppFn.constName? with
      | some ``Zig.TotalTriple => pure (mkIdent ``Zig.TotalTriple.dispatch_template)
      | _ => pure (mkIdent ``Zig.Triple.dispatch_template)
    else pure (mkIdent ``Zig.DispatchSpec.dispatch_template)
  let goals ← evalTacticAt
    (← `(tactic| refine $rule $selStx $inv $μ $post ?step ?entry ?exit)) g
  let mut rest := #[]
  for g in goals do
    let tag := (← g.getTag).eraseMacroScopes
    g.setTag tag
    if tag == `step then
      rest := rest ++ (← g.withContext <| splitStates g κ mem states).toArray
    else if tag == `entry then
      rest := rest.push (← tidy g `entry)
    else if tag == `exit then
      let tac ← if mem then `(tactic| (intro _ _ _ hp; exact hp)) else `(tactic| (intro _ _ hp; exact hp))
      match ← observing? (evalTacticAt tac g) with
      | some [] => pure ()
      | _ => rest := rest.push (← tidy g `exit)
    else
      rest := rest.push g
  setGoals (rest.toList ++ others)
  return rest.toList

/-- Run `tac` on each per-state premise; report every state where it fails. -/
def discharge (goals : List MVarId) (tac : Syntax) : TacticM (List MVarId) := do
  let mut rest := #[]
  let mut failed : Array MessageData := #[]
  for g in goals do
    let tag ← g.getTag
    unless tag.getPrefix == `step do
      rest := rest.push g
      continue
    let ty ← instantiateMVars (← g.getType)
    match ← observing? (evalTacticAt tac g) with
    | some [] => pure ()
    | some left =>
      failed := failed.push m!"state {tag.componentsRev.head!}: {left.length} goal(s) remain\n    {ty}"
    | none =>
      failed := failed.push m!"state {tag.componentsRev.head!}: the step tactic failed\n    {ty}"
  unless failed.isEmpty do
    throwError (m!"dispatch_template: the invariant/measure is not established at \
      {failed.size} state(s):" ++ MessageData.joinSep (failed.toList.map (m!"\n  " ++ ·)) m!"")
  let others := (← getGoals).filter (!goals.contains ·)
  setGoals (rest.toList ++ others)
  return rest.toList

/-- The remaining goals, one line each: `tag : type`. -/
def reportPremises (goals : List MVarId) : TacticM Unit := do
  let lines ← goals.mapM fun g => do
    let d ← g.getDecl
    return m!"{d.userName} : {← instantiateMVars d.type}"
  logInfo (m!"dispatch_template remaining premises ({goals.length}):" ++
    MessageData.joinSep (lines.map (m!"\n  " ++ ·)) m!"")

end Zig.DispatchTemplateTactic

syntax dispatchStates := &" states " "[" term,* "]"
syntax dispatchUsing := " using " tacticSeq

open Lean Elab Tactic in
def Zig.DispatchTemplateTactic.run (inv μ post : Term) (st : Option (TSyntax ``dispatchStates))
    (u : Option (TSyntax ``dispatchUsing)) : TacticM (List MVarId) := do
  let states ← st.mapM fun
    | `(dispatchStates| states [$ks,*]) => pure ks.getElems
    | _ => throwUnsupportedSyntax
  let goals ← applyTemplate inv μ post states
  match u with
  | some (`(dispatchUsing| using $tac)) => discharge goals tac
  | some _ => throwUnsupportedSyntax
  | none => pure goals

/-- Apply the dispatch-loop template; leaves `step.<state>` per state, `entry` and `exit`. -/
elab "dispatch_template " inv:term:max μ:term:max post:term:max st:(dispatchStates)?
    u:(dispatchUsing)? : tactic =>
  discard <| Zig.DispatchTemplateTactic.run inv μ post st u

/-- `dispatch_template`, reporting the remaining premises with their types. -/
elab "dispatch_template? " inv:term:max μ:term:max post:term:max st:(dispatchStates)?
    u:(dispatchUsing)? : tactic => do
  Zig.DispatchTemplateTactic.reportPremises (← Zig.DispatchTemplateTactic.run inv μ post st u)
