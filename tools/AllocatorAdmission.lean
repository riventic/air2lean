import Lean
import ZigLean.Witness

/-!
Actual allocator-contract applications in checked proof terms. The dependency graph selects
which declarations can contain a contract; it never supplies the arguments. Applications are
read after substituting the caller's actual arguments, with the complete dependent local
telescope retained. Unsupported or partial applications fail closed.

This is statement extraction for the existing witness audit, not a proof generator. Its caller
computes admission with `Zig.Witness.nonvacuityType` on the applied creation theorem.
-/

namespace Air2Lean.AllocatorAdmission

open Lean Meta

structure AppliedUse where
  contract : Name
  /-- The actual proof application, closed over its complete local telescope. -/
  application : Expr
  /-- Pointwise admission over the same telescope, computed from the applied creator. -/
  obligation : Expr
  /-- An existing exact admission hypothesis or checked let proof in the original context. -/
  evidence : Option Expr

/-- Read actual applications rather than reconstructing them from a set of dependency names.
`contracts` contains named implementation theorems. `relevant` also includes the declarations
whose checked dependency closures reach one of those theorems. All expressions returned here
are closed; their universe parameters remain those of the checked root declaration. -/
def collectUses (env : Environment) (root : Name) (contracts relevant : NameSet)
    (admission : Expr → MetaM (Option Expr)) : MetaM (Except String (Array AppliedUse)) := do
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let keys ← IO.mkRef ({} : Std.HashSet Expr)
  let uses ← IO.mkRef (#[] : Array AppliedUse)
  let remaining ← IO.mkRef (50000 : Nat)
  let close := fun scope expr => mkLambdaFVars scope expr
    (usedLetOnly := false) (generalizeNondepLet := false)
  let record (name : Name) (expr : Expr) (scope : Array Expr) : MetaM Unit := do
    let application ← close scope expr
    if (← keys.get).contains application then return
    if application.hasFVar || application.hasMVar then
      throwError "allocator admission has an unbound application context"
    let some expected ← admission expr |
      throwError "allocator admission has an unsupported or partial application of {name}"
    let expected ← instantiateMVars expected
    if expected.hasMVar then
      throwError "allocator admission predicate contains unresolved metavariables"
    let obligation ← mkForallFVars scope expected
      (usedLetOnly := false) (generalizeNondepLet := false)
    if obligation.hasFVar || obligation.hasMVar then
      throwError "allocator admission has an unbound dependent predicate"
    let mut evidence := none
    for x in scope do
      let ty ← instantiateMVars (← inferType x)
      if ty.hasMVar then throwError "allocator admission context contains unresolved metavariables"
      if ← isDefEq ty expected then
        let proof ← close scope x
        if proof.hasFVar || proof.hasMVar || !(← isDefEq (← inferType proof) obligation) then
          throwError "allocator admission evidence does not have the exact scoped predicate"
        evidence := some proof
        break
    keys.modify (·.insert application)
    uses.modify (·.push ⟨name, application, obligation, evidence⟩)
  let rec walk (expr : Expr) (scope : Array Expr) : Nat → MetaM Unit
    | 0 => throwError "allocator admission application expansion is too deep"
    | depth + 1 => do
      let expr := expr.consumeMData.headBeta
      -- The same term under a stronger local premise is a different use. In particular, an
      -- earlier use under False must not hide an unrestricted use of the same closed contract.
      let scoped ← close scope expr
      if (← seen.get).contains scoped then return
      let budget ← remaining.get
      if budget == 0 then throwError "allocator admission application expansion budget exhausted"
      remaining.set (budget - 1)
      seen.modify (·.insert scoped)
      match expr with
      | .lam name ty body bi =>
        withLocalDecl name bi ty fun x => walk (body.instantiate1 x) (scope.push x) depth
      | .letE name ty value body _ =>
        walk value scope depth
        withLetDecl name ty value fun x =>
          walk (body.instantiate1 x) (scope.push x) depth
      | _ =>
        let args := expr.getAppArgs
        if let .const name levels := expr.getAppFn then
          if name == `Zig.Full.FAllocSpec.mk || name == `Zig.Full.CAllocSpec.mk then
            let ty ← inferType expr
            if ty.isAppOfArity `Zig.Full.FAllocSpec 4 || ty.isAppOfArity `Zig.Full.CAllocSpec 4 then
              let inv := ty.appArg!.getAppFn
              unless inv.isFVar || inv.isBVar do
                throwError "allocator admission found an unnamed concrete constructor application"
          if contracts.contains name then
            record name expr scope
          else if relevant.contains name then
            let some info := env.checked.get.find? name |
              throwError "allocator admission names an unchecked declaration {name}"
            let some value := info.value? (allowOpaque := true) |
              throwError "allocator admission cannot inspect the application of {name}"
            let expanded := (value.instantiateLevelParams info.levelParams levels).beta args
            if expanded == expr then throwError "allocator admission application does not expand"
            walk expanded scope depth
        for arg in args do
          walk arg scope depth
        if let .proj _ _ value := expr then walk value scope depth
  try
    let some info := env.checked.get.find? root |
      return .error "allocator admission root is not a checked declaration"
    let levels := info.levelParams.map Level.param
    forallTelescope info.type fun xs _ => do
      if contracts.contains root then
        record root (mkAppN (mkConst root levels) xs) xs
        -- A named implementation's own constructor belongs to its checked contract proof.
        -- Its creation post is checked separately; this traversal binds uses by clients.
        return .ok (← uses.get)
      let some value := info.value? (allowOpaque := true) |
        throwError "allocator admission root has no checked proof body"
      walk ((value.instantiateLevelParams info.levelParams levels).beta xs) xs 512
      return .ok (← uses.get)
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Air2Lean.AllocatorAdmission
