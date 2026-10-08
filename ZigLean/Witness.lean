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

`nonvacuity_witness T := proof` and `liveness_witness T := proof` add them; the assurance
extractor (`tools/Assurance.lean`) recomputes both statements from `T`'s type and only accepts a
companion whose kernel type is exactly that statement. A telescope without hypotheses whose
binder types all have `Nonempty` instances is inhabited without a companion.
-/

open Lean Meta Elab Command Term

namespace Zig.Witness

/-- The conclusion head unfolded once and beta-reduced, if it is a definition. -/
def unfoldHead? (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  unless e.getAppFn.consumeMData.isConst do return none
  let some e ← unfoldDefinition? e | return none
  return some (← Core.betaReduce e)

/-- Run `k` on the premise telescope (theorem binders, then the unfolded head's binders) and the
remaining body. `k` also receives how many binders belong to the theorem itself. -/
def withPremises {β : Type} (type : Expr) (k : Array Expr → Nat → Expr → MetaM β) : MetaM β :=
  forallTelescope type fun xs body => do
    match ← unfoldHead? body with
    | some unfolded => forallTelescope unfolded fun ys inner => k (xs ++ ys) xs.size inner.consumeMData
    | none => k xs xs.size body.consumeMData

/-- `∃ x₁, … ∃ xₙ, body` over the given free variables (Prop binders included). -/
def existsOver (xs : Array Expr) (body : Expr) : MetaM Expr := do
  let mut acc := body
  for x in xs.reverse do
    acc ← mkAppM ``Exists #[← mkLambdaFVars #[x] acc]
  return acc

/-- The non-vacuity statement of a claim with kernel type `type`. -/
def nonvacuityType (type : Expr) : MetaM Expr :=
  withPremises type fun xs _ _ => existsOver xs (mkConst ``True)

/-- `∃ r, d = some (.ok r)` for the discriminant `d : Option (Except ε β)` of the match that
ends the unfolded conclusion head; `none` if there is no such match. -/
def returnsBody? (body : Expr) : MetaM (Option Expr) := do
  let some app ← matchMatcherApp? body | return none
  let #[d] := app.discrs | return none
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
  withPremises type fun xs _ body => do
    let some returns ← returnsBody? body | return none
    some <$> existsOver xs returns

/-- Whether the telescope has no Prop binder and every binder type has a `Nonempty` instance
(given arbitrary earlier binders), so it is inhabited without a companion theorem. -/
def triviallyInhabited (type : Expr) : MetaM Bool :=
  withPremises type fun xs _ _ => xs.allM fun x => do
    let ty ← inferType x
    if ← isProp ty then return false
    let u ← getLevel ty
    return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) ty)).isSome

def nonvacuousSuffix : Name := `nonvacuous
def livenessSuffix : Name := `returns

private def addWitness (thm : Ident) (suffix : Name) (build : Expr → MetaM (Option Expr))
    (proof : Term) : CommandElabM Unit := liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo thm
  let info ← getConstInfo name
  let some type ← build info.type
    | throwError "{name}: its conclusion head has no liveness obligation (only partial triples do)"
  let value ← elabTermEnsuringType proof type
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasMVar then throwError "{name}: the witness proof has unassigned metavariables"
  addDecl <| .thmDecl { name := name ++ suffix, levelParams := info.levelParams, type, value }

/-- `nonvacuity_witness T := proof` adds `T.nonvacuous`, whose statement is computed from `T`. -/
syntax (name := nonvacuityWitness) "nonvacuity_witness " ident " := " term : command
/-- `liveness_witness T := proof` adds `T.returns`, whose statement is computed from `T`. -/
syntax (name := livenessWitness) "liveness_witness " ident " := " term : command

elab_rules : command
  | `(nonvacuity_witness $thm := $proof) =>
    addWitness thm nonvacuousSuffix (fun t => some <$> nonvacuityType t) proof
  | `(liveness_witness $thm := $proof) => addWitness thm livenessSuffix livenessType? proof

end Zig.Witness
