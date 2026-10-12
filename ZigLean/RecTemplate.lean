import Lean
import ZigLean.Mem.Basic

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

`rec_template μ unfolding f, g` also rewrites the goal with `f.eq_1` and `g.eq_1`: the first
application of each (and identical copies) becomes the generated body, whose recursive call
sites stay folded.
For a mutually recursive group, state the specifications of the members as one conjunction over
the same arguments (or over an index type such as `Sum`) and unfold every member; the shared
measure must decrease across the group's calls.

`rec_template? μ …` does the same and reports the remaining premise with its type.

The scaffold only supplies the induction. At each recursive call site the user discharges the
decrease `μ ȳ < μ x̄` and any premise of the specification when applying `ih`; the report
states that obligation in the type of `ih`.

## Measure inference

`rec_template _ unfolding f, …` (and `rec_template? _ unfolding f, …`, which also prints what it
read) infers the measure from the recursive call sites of the group. It reads each member's
unfold equation `f.eq_1` once (no evaluation) and classifies, at every call to a member, the
argument at each parameter position by the value that the body bound to it:

* `p - k` by a checked `Zig.sub` of a positive literal, with `p` the caller's parameter at that
  position: the argument is smaller than `p` (unsigned: `p.toNat`; signed: `p.toInt.toNat`,
  smaller while `p > 0`);
* `x % p` (`Zig.rem`/`Zig.mod`), `p / k` (`Zig.divTrunc`/`divFloor`/`divExact`, `k ≥ 2`) and
  `p >> k` (`Zig.shr`/`shrChk`/`shrExact`, `k ≥ 1`), unsigned: smaller than `p` when `p ≠ 0`;
* a value read from memory (`Zig.load`): a link of a data structure; no value measure decreases,
  so the report asks for a ghost measure (the length of the structure in the specification's
  representation predicate, quantified in the goal);
* anything else: no decrease.

A position that decreases at every call site of the group is a measure; the measure is that
argument's goal binder (`x.toNat` or `x.toInt.toNat`) over the goal's leading binders up to it.
The side premises of each decrease (the guard under which the call is reached: `p ≥ k`, `p > 0`,
`p ≠ 0`) are reported, not proved: they are discharged where `ih` is applied, as every decrease
is. A measure that the scaffold accepts is checked by that application, so a wrong suggestion
cannot prove anything. When no position decreases, inference fails with the classification.
-/

namespace Zig.RecTemplate

open Lean Elab Tactic Meta

/-- Build the proof of `∀ x̄, B x̄` from a fresh `step` goal; returns that goal. -/
def scaffold (g : MVarId) (μ : Expr) : MetaM (MVarId × Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  unless ← isProp tgt do throwError "rec_template: the goal is not a proposition: {tgt}"
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

/-- Rewrite with each listed function's unfold equation `f.eq_1`: the first application of `f`
in the goal (and identical copies) becomes its body. Calls inside the body are left alone. -/
def unfoldOnce (g : MVarId) (fns : Array Ident) : TacticM MVarId := do
  let mut g := g
  for f in fns do
    let eqn := mkIdent ((← realizeGlobalConstNoOverloadWithInfo f) ++ `eq_1)
    match ← evalTacticAt (← `(tactic| rewrite [$eqn:ident])) g with
    | [g'] => g := g'
    | gs => throwError "rec_template: unfolding {f} left {gs.length} goals"
  return g

/-! ### Measure inference -/

/-- How a recursive call's argument relates to the caller's parameter at the same position. -/
inductive Dec where
  /-- `p - k`, a checked subtraction of a positive literal. -/
  | sub (signed : Bool)
  /-- `x % p`, `p / k` (`k ≥ 2`), `p >> k` (`k ≥ 1`): unsigned, below `p` when `p ≠ 0`. -/
  | shrink (what : String)
  /-- A value read from memory. -/
  | loaded
  /-- The parameter itself. -/
  | same
  | other
  deriving Inhabited

def Dec.decreases : Dec → Bool
  | .sub _ | .shrink _ => true
  | _ => false

def Dec.describe (p : MessageData) : Dec → MessageData
  | .sub true => m!"{p} - k (signed checked sub): smaller while {p} > 0; side premise: the \
      subtraction does not overflow"
  | .sub false => m!"{p} - k (checked sub): smaller; side premise: {p} ≥ k (else the sub \
      overflows)"
  | .shrink w => m!"{w}: smaller than {p}; side premise: {p} ≠ 0"
  | .loaded => m!"read from memory: no value measure; supply a ghost measure (the length of the \
      structure in the specification's representation predicate)"
  | .same => m!"{p} unchanged"
  | .other => m!"no decrease recognized"

/-- A positive natural-number literal. -/
def litNat? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getArg! 1 |>.consumeMData with
    | .lit (.natVal k) => some k
    | _ => none
  else none

/-- Strip the lifts and `pure` around a computed value. -/
partial def stripLift (e : Expr) : Expr :=
  let e := e.consumeMData.headBeta
  match e.getAppFn with
  | .const c _ =>
    if [``liftM, ``MonadLiftT.monadLift, ``MonadLift.monadLift, ``StateT.lift, ``Pure.pure,
        ``Zig.call, ``Zig.callM].contains c && e.getAppNumArgs > 0 then
      stripLift e.appArg!
    else e
  | _ => e

/-- The recursive calls of a body: the callee and, per argument, the value bound to it. -/
partial def callsIn (fns : Array Name) (e : Expr) : StateRefT (Array (Name × Array Expr))
    (ReaderT (Std.HashMap FVarId Expr) MetaM) Unit := do
  let e := e.consumeMData
  match e with
  | .lam n ty b _ =>
    withLocalDeclD n ty fun x => callsIn fns (b.instantiate1 x)
  | .letE n ty v b _ =>
    callsIn fns v
    withLocalDeclD n ty fun x =>
      withReader (·.insert x.fvarId! v) (callsIn fns (b.instantiate1 x))
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Bind.bind && args.size == 6 then
      callsIn fns args[4]!
      if let .lam n ty b _ := args[5]!.consumeMData then
        return ← withLocalDeclD n ty fun x =>
          withReader (·.insert x.fvarId! args[4]!) (callsIn fns (b.instantiate1 x))
    if let .const c _ := fn then
      if fns.contains c then
        let env ← read
        let resolve (a : Expr) : Expr :=
          match (stripLift a) with
          | .fvar x => (env[x]?.map stripLift).getD (.fvar x)
          | a => a
        modify (·.push (c, args.map resolve))
    callsIn fns fn
    for a in args do callsIn fns a
  | .proj _ _ x => callsIn fns x
  | _ => pure ()

/-- The relation of the argument `a` to the parameter `p`. -/
def classifyArg (p a : Expr) : MetaM Dec := do
  let a := stripLift a
  if a == p then return .same
  let fn := a.getAppFn
  let args := a.getAppArgs
  let some c := fn.constName? | return .other
  if c == ``Zig.load then return .loaded
  if args.size < 3 then return .other
  let (x, y) := (args[args.size - 2]!, args[args.size - 1]!)
  let signed := args[args.size - 3]!.isConstOf ``Bool.true
  if c == ``Zig.sub && x == p && (litNat? y).any (· > 0) then return .sub signed
  if signed then return .other
  if (c == ``Zig.rem || c == ``Zig.mod) && y == p then return .shrink "x % p"
  if [``Zig.divTrunc, ``Zig.divFloor, ``Zig.divExact].contains c && x == p &&
      (litNat? y).any (· ≥ 2) then return .shrink "p / k"
  if [``Zig.shr, ``Zig.shrChk, ``Zig.shrExact].contains c && x == p &&
      (litNat? y).any (· ≥ 1) then return .shrink "p >> k"
  return .other

/-- Infer a measure for the goal from the recursive calls of the group `fns`: the measure (or
`none`) and the report. -/
def inferMeasure (g : MVarId) (fns : Array Name) : MetaM (Option Expr × MessageData) :=
  g.withContext do
  if fns.isEmpty then
    throwError "rec_template: inferring the measure needs the group: `rec_template _ unfolding f, …`"
  -- Per member: its parameters and the classification of every call's arguments.
  let mut lines : Array MessageData := #[]
  let mut decs : Array (Array Dec) := #[]
  let mut arity? : Option Nat := none
  for f in fns do
    let some eqns ← getEqnsFor? f | throwError "rec_template: {f} has no unfold equation"
    let some eqn := eqns[0]? | throwError "rec_template: {f} has no unfold equation"
    let eqn ← inferType (← mkConstWithFreshMVarLevels eqn)
    let (calls, ok) ← forallTelescopeReducing eqn fun ps body => do
      let some (_, _, rhs) := body.eq? | return (#[], false)
      let ((), calls) ← ((callsIn fns rhs).run #[]).run {}
      let mut out := #[]
      for (callee, args) in calls do
        if args.size != ps.size then
          return (#[], false)
        let ds ← (args.zip ps).mapM fun (a, p) => classifyArg p a
        out := out.push (callee, ds, ← ps.mapM fun p => p.fvarId!.getUserName)
      return (out, true)
    unless ok do
      lines := lines.push m!"{f}: a call whose arguments do not match the parameters; not followed"
      continue
    for (callee, ds, ps) in calls do
      arity? := arity?.getD ds.size |> some
      let descs := (ds.zip ps).toList.zipIdx.map fun ((d, p), j) =>
        m!"\n    argument {j + 1}: " ++ d.describe m!"{p}"
      lines := lines.push (m!"call {f} → {callee}:" ++ MessageData.joinSep descs m!"")
      decs := decs.push ds
  if decs.isEmpty then
    return (none, m!"rec_template? measure inference:" ++
      MessageData.joinSep ((lines.push m!"no recursive call found").toList.map (m!"\n  " ++ ·)) m!"")
  let arity := arity?.getD 0
  -- A position that decreases at every call.
  let pos? := (List.range arity).find? fun j => decs.all fun ds => (ds[j]?.map Dec.decreases).getD false
  let measure? ← match pos? with
    | none => pure none
    | some j => do
      let signed := decs.any fun ds => match ds[j]? with | some (.sub true) => true | _ => false
      -- The goal's first application of a member: argument `j` must be a goal binder.
      forallTelescope (← instantiateMVars (← g.getType)) fun xs body => do
        let some app := body.find? fun e => fns.any fun f => e.isAppOfArity f arity
          | return none
        let some i := xs.idxOf? (app.getArg! j) | return none
        if i ≥ xs.size then return none
        let x := xs[i]!
        let val ← if signed then mkAppM ``Int.toNat #[← mkAppM ``BitVec.toInt #[x]]
          else mkAppM ``BitVec.toNat #[x]
        some <$> mkLambdaFVars (xs.extract 0 (i + 1)) val
  let tail : MessageData := match pos?, measure? with
    | some j, some μ => m!"measure candidate (argument {j + 1}): {μ}"
    | some j, none => m!"argument {j + 1} decreases at every call, but it is not a binder of the \
        goal's call: state the goal over it"
    | none, _ => m!"measure: not inferred (no argument decreases at every call); supply one, or a \
        ghost measure for a structure read from memory"
  return (measure?, m!"rec_template? measure inference (unchecked until `ih` is applied):" ++
    MessageData.joinSep ((lines.push tail).toList.map (m!"\n  " ++ ·)) m!"")

def run (μ : Term) (fns : Array Ident) (report : Bool) : TacticM Unit := do
  let g :: others ← getGoals | throwError "rec_template: no goals"
  let μ ← if μ.raw.isOfKind ``Lean.Parser.Term.hole then do
      let names ← fns.mapM fun f => realizeGlobalConstNoOverloadWithInfo f
      let (μ?, msg) ← inferMeasure g names
      let some μ := μ? | throwError msg
      if report then logInfo msg
      pure μ
    else instantiateMVars (← g.withContext <| elabTerm μ none)
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
with the induction hypothesis `ih`. `unfolding f, …` rewrites each `f.eq_1` once. `_` for `μ`
infers the measure from the recursive calls of the `unfolding` group. -/
syntax "rec_template " term:max (recUnfolding)? : tactic

/-- `rec_template`, reporting the remaining premise and the induction hypothesis. -/
syntax "rec_template? " term:max (recUnfolding)? : tactic

elab_rules : tactic
  | `(tactic| rec_template $μ $[unfolding $fs,*]?) =>
    Zig.RecTemplate.run μ (fs.map (·.getElems) |>.getD #[]) false
  | `(tactic| rec_template? $μ $[unfolding $fs,*]?) =>
    Zig.RecTemplate.run μ (fs.map (·.getElems) |>.getD #[]) true
