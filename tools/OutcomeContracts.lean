import Lean
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Thread

/-!
Conservative outcome extraction from a kernel conclusion. This is claim tooling, not a
judgment: it reads the postcondition, never the proof or samples. Returned error unions and
optional wrappers use the same constructor partition as tests/diff/Outcome.lean.
-/

open Lean Meta

namespace Air2Lean.Assurance

/-- Computation runners shared with the subject binder: name, arity, computation argument,
and domain arguments. Only StateT.run preserves its final state as a returned product. -/
def computationRunners : List (Name × Nat × Nat × List Nat) :=
  [(``StateT.run, 5, 3, [4]), (``StateT.run', 6, 4, [5]), (``ExceptT.run, 4, 3, []),
   (``OptionT.run, 3, 2, []), (``ReaderT.run, 5, 3, [4]), (``Zig.call, 3, 2, [])]

private def returnedKinds := #["valid", "error_return"]

/-- A stuck type projection or opaque type could be an error union. Only a concrete type
constructor (or function/sort) establishes the fallback, non-error return class. -/
private def concreteType (ty : Expr) : MetaM Bool := do
  match ty.getAppFn with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.inductInfo _) | some (.quotInfo _) => return true
    | _ => return false
  | .forallE .. | .sort .. => return true
  | _ => return false

/-- A constructor-disjoint equality is impossible. Other equalities may restrict payloads,
but cannot justify removing a constructor class. No reduction of an opaque is performed. -/
private partial def ctorClash (fuel : Nat) (a b : Expr) : MetaM Bool := do
  if fuel == 0 then return false
  -- Proof irrelevance makes e.g. Or.inl and Or.inr equal as proof fields.
  if ← isProof a then return false
  let a ← whnf a
  let b ← whnf b
  let .const an _ := a.getAppFn | return false
  let .const bn _ := b.getAppFn | return false
  let env ← getEnv
  let some (.ctorInfo ac) := env.find? an | return false
  let some (.ctorInfo bc) := env.find? bn | return false
  unless ac.induct == bc.induct do return false
  if an != bn then return true
  let aa := a.getAppArgs
  let ba := b.getAppArgs
  unless aa.size == ba.size do return false
  for i in [ac.numParams:aa.size] do
    if ← ctorClash (fuel - 1) aa[i]! ba[i]! then return true
  return false

private def relevant (value e : Expr) : Bool :=
  (e.find? (· == value)).isSome ||
    (value.find? fun x => x.isFVar && e.containsFVar x.fvarId!).isSome

/-- `none` means unsupported, `some false` constructor-impossible, and `some true` an upper
bound: this predicate has not excluded the constructor class. Existentials and resource
constraints are over-approximated; no satisfiability claim is made. -/
private partial def probe (fuel : Nat) (value e : Expr) : MetaM (Option Bool) := do
  if fuel == 0 then return none
  let e ← whnf e
  if e.isConstOf ``False then return some false
  if e.isConstOf ``True then return some true
  -- A resource predicate that does not read this return value cannot exclude its class.
  unless relevant value e do return some true
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
    let a ← probe (fuel - 1) value (e.getArg! 0)
    if e.isAppOfArity ``And 2 && a == some false then return some false
    let b ← probe (fuel - 1) value (e.getArg! 1)
    if e.isAppOfArity ``And 2 then
      if b == some false then return some false
    else if a == some false && b == some false then return some false
    return if a.isSome && b.isSome then some true else none
  if e.isAppOfArity ``Exists 2 then
    return ← withLocalDeclD `w (e.getArg! 0) fun x =>
      probe (fuel - 1) value (mkApp e.appArg! x)
  if e.isAppOfArity ``Eq 3 then
    return some (!(← ctorClash (fuel - 1) (e.getArg! 1) (e.getArg! 2)))
  if e.isAppOfArity ``ite 5 then
    let a ← probe (fuel - 1) value (e.getArg! 3)
    let b ← probe (fuel - 1) value (e.getArg! 4)
    return if a == some false && b == some false then some false
      else if a.isSome && b.isSome then some true else none
  -- In particular: an opaque or caller-supplied predicate over the result is unsupported.
  return none

/-- Visit every return-constructor class while its symbolic payloads are in scope. Abstract
types fail closed: they could be instantiated with a source error union. Depth is bounded to
keep extraction finite for recursively nested wrappers. -/
private partial def visitReturns (fuel : Nat) (ty : Expr) (k : String → Expr → MetaM (Option Bool)) :
    MetaM (Array (String × Option Bool)) := do
  if fuel == 0 then return returnedKinds.map (·, none)
  let ty ← whnf ty
  if ty.isAppOfArity ``Option 1 then
    let inner := ty.appArg!
    let nil ← mkAppOptM ``Option.none #[some inner]
    let no ← k "valid" nil
    let yes ← visitReturns (fuel - 1) inner fun kind v => do
      k kind (← mkAppOptM ``Option.some #[some inner, some v])
    return #[("valid", no)] ++ yes
  if ty.isAppOfArity ``Except 2 then
    let err := ty.getArg! 0
    let inner := ty.getArg! 1
    if ← isDefEq err (mkConst ``String) then
      let no ← withLocalDeclD `errorName err fun name => do
        k "error_return" (← mkAppOptM ``Except.error #[some err, some inner, some name])
      let yes ← visitReturns (fuel - 1) inner fun kind v => do
        k kind (← mkAppOptM ``Except.ok #[some err, some inner, some v])
      return #[("error_return", no)] ++ yes
    unless ← concreteType (← whnf err) do return returnedKinds.map (·, none)
  unless ← concreteType ty do return returnedKinds.map (·, none)
  return ← withLocalDeclD `returned ty fun v => do
    return #[("valid", ← k "valid" v)]

private def outcomeResult (checks : Array (String × Option Bool)) (unexcluded : Array String)
    (scope : String) : Json :=
  let supported := checks.all (·.2.isSome)
  let admitted := returnedKinds.filter fun kind => checks.any fun (k, possible) =>
    k == kind && possible != some false
  Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("status", toJson (if supported then "computed" else "unsupported")),
    ("returns", toJson admitted), ("unexcluded", toJson unexcluded),
    ("scope", toJson scope), ("precision", toJson "constructor upper bound"),
    ("reason", if supported then Json.null else toJson
      "unsupported or opaque return predicate/type; no precise outcome contract established")]

private def unsupportedOutcome (reason : String) : Json :=
  Json.mkObj [("schema_version", toJson (1 : Nat)), ("status", toJson "unsupported"),
    ("returns", Json.null), ("unexcluded", Json.null), ("scope", Json.null),
    ("precision", Json.null), ("reason", toJson reason)]

private def tripleOutcomes (body : Expr) (typeIndex postIndex : Nat) (total : Bool)
    (concurrent : Bool := false) : MetaM Json := do
  let args := body.getAppArgs
  if args.size <= postIndex then return unsupportedOutcome "unrecognised triple arguments"
  let ty := args[typeIndex]!
  let post := args[postIndex]!
  let checks ← visitReturns 12 ty fun _ v => do
    withLocalDeclD `resource (mkConst ``Zig.Full.Res) fun r =>
      probe 64 v (mkApp2 post v r)
  let unexcluded := if total then #[] else #["divergence", "stack_overflow"]
  let result := outcomeResult checks unexcluded (if total then "all_outcomes" else "conditional_on_return")
  return result.setObjVal! "concurrent" (toJson concurrent)

/-- StateT.run keeps its final state in the returned product; run' does not. Peel only the
registered computation runners, as the statement binder does, never arbitrary functions. -/
private partial def statePairs (e : Expr) : Nat :=
  let args := e.getAppArgs
  match e.getAppFn.consumeMData with
  | .const n _ =>
    match computationRunners.find? fun r => r.1 == n && args.size == r.2.1 with
    | some (_, _, program, _) => statePairs args[program]! + if n == ``StateT.run then 1 else 0
    | none => 0
  | _ => 0

private def exactFailure (e : Expr) : Option String :=
  match e.getAppFn with
  | .const ``Zig.Error.illegal _ => some "illegal_behavior"
  | .const ``Zig.Error.unspecified _ => some "unspecified_behavior"
  | .const ``Zig.Error.unsupportedTimer _ => some "unspecified_timer"
  | .const ``Zig.Error.deadlock _ => some "deadlock"
  | .const ``Zig.Error.trap _ => some "hardware_trap"
  | .const ``Zig.Error.stackOverflow _ => some "stack_overflow"
  | .const ``Zig.Error.overflow _ | .const ``Zig.Error.outOfBounds _ |
    .const ``Zig.Error.divByZero _ | .const ``Zig.Error.unreachable _ |
    .const ``Zig.Error.panic _ => some "panic"
  | _ => none

private def exactOutcome (outcome : String) : Json :=
  Json.mkObj [("schema_version", toJson (1 : Nat)), ("status", toJson "computed"),
    ("returns", toJson (#[] : Array String)), ("unexcluded", toJson #[outcome]),
    ("scope", toJson "all_outcomes"), ("precision", toJson "exact constructor"),
    ("concurrent", toJson false), ("reason", Json.null)]

/-- A state function contributes a final-state product; a reader function does not. Follow
type aliases one step at a time so that arbitrary function types are never guessed to be
StateT (a ReaderT can return a source product containing an error union). -/
private partial def stateFunction? (fuel : Nat) (ty : Expr) : MetaM (Option Bool) := do
  if fuel == 0 then return none
  if ty.isAppOfArity ``StateT 3 then return some true
  if ty.isAppOfArity ``ReaderT 3 then return some false
  let some unfolded ← unfoldDefinition? ty | return none
  if unfolded == ty then return none
  stateFunction? (fuel - 1) unfolded

private partial def equationOutcomes (fuel pairs : Nat) (lhs rhs : Expr) : MetaM Json := do
  if fuel == 0 then return unsupportedOutcome "unsupported equation result"
  -- The source computation fixes the effect: StateT and ReaderT can be definitionally equal
  -- function types, so the spelling of the RHS cannot decide whether a product is final state.
  let rawType ← inferType lhs
  let ty ← whnf rawType
  if let .forallE n dom _ _ := ty then
    -- An equation of state functions asserts the run for every state.
    let some state ← stateFunction? 12 rawType |
      return unsupportedOutcome "equation uses an unrecognised function runner"
    return ← withLocalDeclD n dom fun x =>
      equationOutcomes (fuel - 1) (pairs + if state then 1 else 0) (mkApp lhs x) (mkApp rhs x)
  unless ty.isAppOfArity ``Option 1 do
    return unsupportedOutcome "equation is not a Result-valued run"
  let layer ← whnf ty.appArg!
  unless layer.isAppOfArity ``Except 2 do
    return unsupportedOutcome "equation is not a Result-valued run"
  unless ← isDefEq (layer.getArg! 0) (mkConst ``Zig.Error) do
    return unsupportedOutcome "equation is not a Result-valued run"
  let rhs ← whnf rhs
  if rhs.isAppOfArity ``Option.none 1 then return exactOutcome "divergence"
  unless rhs.isAppOfArity ``Option.some 2 do
    return unsupportedOutcome "equation does not expose a Result constructor"
  let result ← whnf rhs.appArg!
  if result.isAppOfArity ``Except.error 3 then
    let some outcome := exactFailure (← whnf result.appArg!) |
      return unsupportedOutcome "equation has an unknown model-error constructor"
    return exactOutcome outcome
  unless result.isAppOfArity ``Except.ok 3 do
    return unsupportedOutcome "equation does not expose a successful Result constructor"
  let mut value := result.appArg!
  for _ in [:pairs] do
    let v ← whnf value
    unless v.isAppOfArity ``Prod.mk 4 do
      return unsupportedOutcome "equation does not expose the state runner's returned product"
    value := v.getArg! 2
  let ty ← inferType value
  let checks ← visitReturns 12 ty fun _ v => do
    probe 64 v (← mkEq v value)
  return (outcomeResult checks #[] "all_outcomes").setObjVal! "concurrent" (toJson false)

/-- Outcome structure of a conclusion already stripped of theorem binders. Registered-head
identity is checked separately by claims.py; wrappers and unregistered heads remain unknown. -/
def outcomeJson (body : Expr) : MetaM Json := withTransparency .default <| withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 50_000_000, maxRecDepth := 512 }) do
  try
    if body.isAppOfArity ``Zig.Full.FTotalTriple 4 || body.isAppOfArity ``Zig.Full.FTTotalTriple 4 then
      return ← tripleOutcomes body 0 3 true
    if body.isAppOfArity ``Zig.Full.FTriple 4 || body.isAppOfArity ``Zig.Full.FTTriple 4 then
      return ← tripleOutcomes body 0 3 false
    if body.isAppOfArity ``Zig.Full.CTriple 5 then
      return ← tripleOutcomes body 1 4 false true
    if body.isAppOfArity ``Eq 3 then
      return ← equationOutcomes 8 (statePairs (body.getArg! 1)) (body.getArg! 1) (body.getArg! 2)
    return unsupportedOutcome "conclusion has no supported outcome postcondition"
  catch error =>
    if error.isInterrupt then throw error
    return unsupportedOutcome "outcome extraction exceeded its reduction limits or could not inspect the predicate"

end Air2Lean.Assurance
