import Lean

/-!
# Claim witnesses

A claim theorem `T : ∀ xs, H xs → C xs` is vacuous when its premises cannot be met, and a
partial-correctness conclusion says nothing when the program never returns. The claim layer
(`scripts/claims.py`, `docs/claim-strength.md`) therefore asks for two companion theorems whose
statements are *computed from the kernel type of `T`*, never written by hand:

* `T.nonvacuous : ∃ xs, ∃ (_ : H xs), …` — the premise telescope is inhabited. The telescope is
  `T`'s own binders followed by the binders of its conclusion head unfolded once, so a triple's
  framed precondition (`m`, `hP`, `hF`, disjointness, `P hP`, `m.Seq`) is part of it.
* `T.returns : ∃ xs, ∃ (_ : H xs), …, ∃ r, d = some (.ok r)` — for a conclusion head whose
  unfolding ends in `match d with …` (the partial triples), some admissible run returns.

* `T.reachable : ∃ σ, ∃ xs, ∃ (_ : H xs), …` — for a claim about an entry-point root whose
  generated module defines `mem0` (the memory at program start), the same telescope with the
  memory pinned to `mem0 σ`: the premises hold where the program starts, not only in some memory
  (audit soundness-2026-10-14 F3). A library function keeps the non-vacuity witness: it may be
  called in any state that satisfies its premises.

`nonvacuity_witness T := proof`, `liveness_witness T := proof` and `reachability_witness T :=
proof` add them; the assurance extractor (`tools/Assurance.lean`) recomputes the statements from
`T`'s type and only accepts a companion whose kernel type is exactly that statement. A telescope
without hypotheses whose binder types all have `Nonempty` instances is inhabited without a
companion.
-/

open Lean Meta Elab Command Term

namespace Zig.Witness

/-- The conclusion head unfolded once and beta-reduced, if it is a definition. -/
def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  unless e.getAppFn.consumeMData.isConst do return none
  let some e ← unfoldDefinition? e | return none
  return some (← Core.betaReduce e)

/-- The judgment inside an unfolded head whose own binders are more premises: the left half of a
conjunction (`FTotalTriple P c Q = FTriple P c Q ∧ FReturns P c`) or the body itself, when it is
a definition (not a `match`, not `Not`) that unfolds to a `∀`.
The flag is whether it is the left half of a conjunction. -/
def innerJudgment? (inner : Expr) : MetaM (Option (Expr × Bool)) := do
  let conj := inner.isAppOfArity ``And 2
  let e := if conj then inner.appFn!.appArg!.consumeMData else inner
  if e.isAppOf ``Not || (← isMatcherApp e) then return none
  let some unfolded ← unfoldHead? e | return none
  return if unfolded.consumeMData.isForall then some (e, conj) else none

/-- Run `k` on the premise telescope (theorem binders, then the unfolded head's binders, then
those of an inner judgment, `innerJudgment?`) and the remaining body. Past a conjunction the body
is `True`: a total head's other half states the return, so it has no liveness obligation. -/
partial def withPremises {β : Type} (type : Expr) (k : Array Expr → Expr → MetaM β) : MetaM β :=
  forallTelescope type fun xs body => go xs body true
where
  go (xs : Array Expr) (body : Expr) (keep : Bool) : MetaM β := do
    let body := body.consumeMData
    match ← unfoldHead? body with
    | some unfolded => forallTelescope unfolded fun ys inner => do
      let inner := inner.consumeMData
      match ← innerJudgment? inner with
      | some (e, conj) => go (xs ++ ys) e (keep && !conj)
      | none => k (xs ++ ys) (if keep then inner else mkConst ``True)
    | none => k xs (if keep then body else mkConst ``True)

/-- `∃ x₁, … ∃ xₙ, body` over the given free variables (Prop binders included). -/
def existsOver (xs : Array Expr) (body : Expr) : MetaM Expr := do
  let mut acc := body
  for x in xs.reverse do
    acc ← mkAppM ``Exists #[← mkLambdaFVars #[x] acc]
  return acc

/-- The non-vacuity statement of a claim with kernel type `type`. -/
def nonvacuityType (type : Expr) : MetaM Expr :=
  withPremises type fun xs _ => existsOver xs (mkConst ``True)

/-- `∃ r, d = some (.ok r)` for the discriminant `d : Option (Except ε β)` of the match that
ends the unfolded conclusion head, or for a call's run tree stop by stop
(`CTriple.Run Q m rF t`) of its reading in the thread (`Sched.soloTree t`); `none` if there is
no such match. -/
def returnsBody? (body : Expr) : MetaM (Option Expr) := do
  let d ← if body.isAppOfArity `Zig.Full.CTriple.Run 7 then
      mkAppM `Zig.Sched.soloTree #[body.appArg!]
    else
      let some app ← matchMatcherApp? body | return none
      let #[d] := app.discrs | return none
      pure d
  let ty ← whnfR (← instantiateMVars (← inferType d))
  let .app (.const ``Option [u]) exTy := ty.consumeMData | return none
  let some (ε, β) := exTy.consumeMData.app2? ``Except | return none
  let .const _ exceptLevels := exTy.consumeMData.getAppFn | return none
  withLocalDeclD `r β fun r => do
    let ok := mkApp3 (mkConst ``Except.ok exceptLevels) ε β r
    let value := mkApp2 (mkConst ``Option.some [u]) exTy ok
    some <$> mkAppM ``Exists #[← mkLambdaFVars #[r] (← mkEq d value)]

/-- The liveness statement of a partial claim, or `none` when its head needs none. -/
def livenessType? (type : Expr) : MetaM (Option Expr) :=
  withPremises type fun xs body => do
    let some returns ← returnsBody? body | return none
    some <$> existsOver xs returns

/-- Whether the telescope has no Prop binder and every binder type has a `Nonempty` instance
(given arbitrary earlier binders), so it is inhabited without a companion theorem. -/
def triviallyInhabited (type : Expr) : MetaM Bool :=
  withPremises type fun xs _ => xs.allM fun x => do
    let ty ← inferType x
    if ← isProp ty then return false
    let u ← getLevel ty
    return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) ty)).isSome

/-- The start memory of the program a claim is about: `N.mem0` for the first constant `N.f` of
the claim's conclusion whose namespace `N` defines `mem0` (a generated module's memory at
program start, `Mem.ofGlobals`). `none` if there is none. -/
def startMem? (type : Expr) : MetaM (Option Name) :=
  forallTelescope type fun _ body => do
    let env ← getEnv
    return body.getUsedConstants.findSome? fun c =>
      let n := c.getPrefix ++ `mem0
      if c.getPrefix.isAnonymous || !env.contains n then none else some n

/-- The memory binder of a premise telescope: the first binder of type `Zig.Mem`. -/
private def memBinder? (xs : Array Expr) : MetaM (Option Expr) :=
  xs.findM? fun x => return (← whnfR (← inferType x)).isConstOf `Zig.Mem

/-- The reachability statement of a claim about an entry-point root with kernel type `type`:
its non-vacuity telescope with the memory pinned to the root's start memory,
`∃ σ, ∃ xs, True` with the memory binder replaced by `N.mem0 σ` (`startMem?`). `none` when the
claim names no start memory or its telescope has no memory binder. -/
def reachabilityType? (type : Expr) : MetaM (Option Expr) := do
  let some mem0 ← startMem? type | return none
  withPremises type fun xs _ => do
    let some x ← memBinder? xs | return none
    let body ← existsOver (xs.filter (· != x)) (mkConst ``True)
    withLocalDeclD `σ (mkConst `Zig.Placement) fun σ => do
      let body := body.replaceFVar x (mkApp (mkConst mem0) σ)
      some <$> mkAppM ``Exists #[← mkLambdaFVars #[σ] body]

/-- Whether the pinned telescope has no Prop binder and every other binder type has a
`Nonempty` instance, so it is inhabited at every start memory without a companion. -/
def triviallyReachable (type : Expr) : MetaM Bool :=
  withPremises type fun xs _ => do
    let some x ← memBinder? xs | return false
    (xs.filter (· != x)).allM fun y => do
      let ty ← inferType y
      if ← isProp ty then return false
      let u ← getLevel ty
      return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) ty)).isSome

def nonvacuousSuffix : Name := `nonvacuous
def livenessSuffix : Name := `returns
def reachableSuffix : Name := `reachable

private def addWitness (thm : Ident) (suffix : Name) (build : Expr → MetaM (Option Expr))
    (proof : Term) (missing : String) : CommandElabM Unit := liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo thm
  let info ← getConstInfo name
  let some type ← build info.type
    | throwError "{name}: {missing}"
  let value ← elabTermEnsuringType proof type
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasMVar then throwError "{name}: the witness proof has unassigned metavariables"
  addDecl <| .thmDecl { name := name ++ suffix, levelParams := info.levelParams, type, value }

/-- `nonvacuity_witness T := proof` adds `T.nonvacuous`, whose statement is computed from `T`. -/
syntax (name := nonvacuityWitness) "nonvacuity_witness " ident " := " term : command
/-- `liveness_witness T := proof` adds `T.returns`, whose statement is computed from `T`. -/
syntax (name := livenessWitness) "liveness_witness " ident " := " term : command
/-- `reachability_witness T := proof` adds `T.reachable`, whose statement is computed from `T`:
the premises hold in the root's memory at program start (`reachabilityType?`). -/
syntax (name := reachabilityWitness) "reachability_witness " ident " := " term : command

elab_rules : command
  | `(nonvacuity_witness $thm := $proof) =>
    addWitness thm nonvacuousSuffix (fun t => some <$> nonvacuityType t) proof ""
  | `(liveness_witness $thm := $proof) => addWitness thm livenessSuffix livenessType? proof
    "its conclusion head has no liveness obligation (only partial triples do)"
  | `(reachability_witness $thm := $proof) =>
    addWitness thm reachableSuffix reachabilityType? proof
      "it names no start memory (`N.mem0`) or has no memory premise"

end Zig.Witness
