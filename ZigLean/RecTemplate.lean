import Lean

/-!
# Measure induction scaffolding for generated recursive functions

A recursive Zig function (or a group of mutually recursive ones) becomes a `mutual` block of
`partial_fixpoint` defs; each has the unfold equation `<fn>.eq_1` (docs/generated-code.md).
A `partial_fixpoint` def has no induction principle of its own, so a total specification needs
an induction on something that each recursive call makes smaller.

`rec_template μ` proves a goal `∀ x₁ … xₖ, B x₁ … xₖ` by strong induction on the natural-number
measure `μ : α₁ → … → αₖ → Nat` of its first `k` binders (`k` is the arity of `μ`). It leaves one
named goal, `step`, in which `x₁ … xₖ` are introduced and

  `ih : ∀ y₁ … yₖ, μ y₁ … yₖ < μ x₁ … xₖ → B y₁ … yₖ`

is the induction hypothesis: every call with a smaller measure already meets the specification.
Further binders of the goal (premises, ghost values) stay in `B` and so are quantified in `ih`.

`rec_template μ unfolding f, g` also rewrites, once, each application of `f` and `g` that the
target contains (`f.eq_1`), so the goal shows the generated body and its recursive call sites.
For a mutually recursive group, state the specifications of the members as one conjunction over
the same arguments (or over an index type such as `Sum`) and unfold every member; the shared
measure must decrease across the group's calls.

`rec_template? μ …` does the same and reports the remaining premise with its type.

The scaffold only supplies the induction. At each recursive call site the user discharges the
decrease `μ ȳ < μ x̄` and any premise of the specification when applying `ih`; the report
states that obligation in the type of `ih`. It does not infer the measure.
-/

namespace Zig.RecTemplate

open Lean Elab Tactic Meta

/-- Build the proof of `∀ x̄, B x̄` from a fresh `step` goal; returns that goal. -/
def scaffold (g : MVarId) (μ : Expr) : MetaM (MVarId × Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let k ← forallTelescopeReducing (← inferType μ) fun xs _ => pure xs.size
  if k == 0 then throwError "rec_template: the measure takes no arguments"
  let nat := mkConst ``Nat
  -- `μ ȳ`, checked against the goal's binders.
  let measureAt (ys : Array Expr) : MetaM Expr := do
    let e := mkAppN μ ys
    let fits ← try check e; isDefEq (← inferType e) nat catch _ => pure false
    unless fits do throwError "rec_template: the measure does not fit the goal's binders"
    pure e.headBeta
  let telescope {β} (k' : Array Expr → Expr → MetaM β) : MetaM β :=
    forallBoundedTelescope tgt k fun ys b => do
      unless ys.size == k do
        throwError "rec_template: the goal has fewer than {k} leading binders: {tgt}"
      k' ys b
  -- step : ∀ x̄, (∀ ȳ, μ ȳ < μ x̄ → B ȳ) → B x̄
  let ihType (xs : Array Expr) : MetaM Expr := telescope fun ys b => do
    mkForallFVars ys (← mkArrow (← mkAppM ``LT.lt #[← measureAt ys, ← measureAt xs]) b)
  let stepType ← telescope fun xs b => do
    mkForallFVars xs (mkForall `ih .default (← ihType xs) b)
  let step ← mkFreshExprSyntheticOpaqueMVar stepType `step
  -- motive n := ∀ ȳ, μ ȳ = n → B ȳ
  let motive ← withLocalDeclD `n nat fun n => do
    let body ← telescope fun ys b => do
      mkForallFVars ys (← mkArrow (← mkEq (← measureAt ys) n) b)
    mkLambdaFVars #[n] body
  -- ind n ih ȳ hy := step ȳ (fun z̄ hz => ih (μ z̄) (lt_of_lt_of_eq hz hy) z̄ rfl)
  let ind ← withLocalDeclD `n nat fun n => do
    let ihT ← withLocalDeclD `m nat fun m => do
      mkForallFVars #[m] (← mkArrow (← mkAppM ``LT.lt #[m, n]) (motive.beta #[m]))
    withLocalDeclD `ih ihT fun ih => telescope fun ys _ => do
      let hyT ← mkEq (← measureAt ys) n
      withLocalDeclD `hy hyT fun hy => do
        let smaller ← telescope fun zs _ => do
          let hzT ← mkAppM ``LT.lt #[← measureAt zs, ← measureAt ys]
          withLocalDeclD `hz hzT fun hz => do
            let lt ← mkAppM ``Nat.lt_of_lt_of_eq #[hz, hy]
            let call := mkAppN (mkApp2 ih (← measureAt zs) lt) zs
            mkLambdaFVars (zs.push hz) (mkApp call (← mkEqRefl (← measureAt zs)))
        mkLambdaFVars (#[n, ih] ++ ys ++ #[hy]) (mkApp (mkAppN step ys) smaller)
  let proof ← telescope fun xs _ => do
    let μx ← measureAt xs
    let rec_ := mkAppN (mkConst ``Nat.strongRecOn [Level.zero]) #[motive, μx, ind]
    mkLambdaFVars xs (mkApp (mkAppN rec_ xs) (← mkEqRefl μx))
  check proof
  g.assign proof
  let (_, step) ← step.mvarId!.introNP k
  let (_, step) ← step.intro `ih
  return (step, stepType)

/-- Rewrite each listed function's unfold equation `f.eq_1` once in the goal. -/
def unfoldOnce (g : MVarId) (fns : Array Ident) : TacticM MVarId := do
  let mut g := g
  for f in fns do
    let eqn := mkIdent (f.getId ++ `eq_1)
    match ← evalTacticAt (← `(tactic| rewrite [$eqn:ident])) g with
    | [g'] => g := g'
    | gs => throwError "rec_template: unfolding {f} left {gs.length} goals"
  return g

def run (μ : Term) (fns : Array Ident) (report : Bool) : TacticM Unit := do
  let g :: others ← getGoals | throwError "rec_template: no goals"
  let μ ← instantiateMVars (← g.withContext <| elabTerm μ none)
  if μ.hasExprMVar then throwError "rec_template: could not elaborate the measure {μ}"
  let (step, stepType) ← scaffold g μ
  let step ← unfoldOnce step fns
  step.setTag `step
  setGoals (step :: others)
  if report then
    let unfolded := if fns.isEmpty then m!"" else
      m!"\n  unfolded: {MessageData.joinSep (fns.toList.map (m!"{·.getId}")) m!", "}"
    logInfo m!"rec_template remaining premise (1):\n  step : {stepType}{unfolded}"

end Zig.RecTemplate

syntax recUnfolding := " unfolding " ident,+

/-- Strong induction on the measure `μ` of the goal's leading binders; leaves the goal `step`
with the induction hypothesis `ih`. `unfolding f, …` rewrites each `f.eq_1` once. -/
elab "rec_template " μ:term:max u:(recUnfolding)? : tactic => do
  let fns := match u with
    | some u => match u with
      | `(recUnfolding| unfolding $fs,*) => fs.getElems
      | _ => #[]
    | none => #[]
  Zig.RecTemplate.run μ fns false

/-- `rec_template`, reporting the remaining premise and the induction hypothesis. -/
elab "rec_template? " μ:term:max u:(recUnfolding)? : tactic => do
  let fns := match u with
    | some u => match u with
      | `(recUnfolding| unfolding $fs,*) => fs.getElems
      | _ => #[]
    | none => #[]
  Zig.RecTemplate.run μ fns true
