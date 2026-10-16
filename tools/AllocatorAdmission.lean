import Lean
import ZigLean.Witness

/-!
Actual allocator-contract applications in checked proof terms. Dependency and argument types
select which checked bodies need expansion; they never supply the arguments. Applications are
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
  /-- Evidence is an original exact root hypothesis or a closed checked let proof. Extra
  semantic continuation premises do not establish root/program-start admission. -/
  rootBound : Bool

/-- Read actual applications rather than reconstructing them from a set of dependency names.
`contracts` contains named implementation theorems. `relevant` also includes the declarations
whose checked dependency closures reach an allocator contract type. All expressions returned here
are closed; their universe parameters remain those of the checked root declaration. -/
def collectUses (env : Environment) (root : Name) (contracts relevant : NameSet)
    (admission : Expr → MetaM (Option Expr)) (concretePremise : Expr → MetaM Bool) :
    MetaM (Except String (Array AppliedUse)) := do
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let keys ← IO.mkRef ({} : Std.HashSet Expr)
  let uses ← IO.mkRef (#[] : Array AppliedUse)
  let rootScope ← IO.mkRef (#[] : Array Expr)
  let ownResult ← IO.mkRef (none : Option Expr)
  let remaining ← IO.mkRef (50000 : Nat)
  let close := fun scope expr => mkLambdaFVars scope expr
    (usedLetOnly := false) (generalizeNondepLet := false)
  let touches := fun expr : Expr => expr.getUsedConstants.any relevant.contains
  let concreteResult (expr : Expr) : MetaM Bool := do
    let ty ← whnf (← inferType expr)
    if ty.isAppOfArity `Zig.Full.FAllocSpec 4 || ty.isAppOfArity `Zig.Full.CAllocSpec 4 then
      -- A local let naming a concrete invariant is not a fresh interface parameter.
      let inv := (← whnf ty.appArg!).getAppFn
      return !inv.isFVar && !inv.isBVar
    return false
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
    let roots ← rootScope.get
    -- Only closed checked lets may supply evidence without an exact root admission
    -- hypothesis. In particular, root data containing a hypothetical memory/proof package
    -- and newly introduced Holds/False premises do not manufacture an admitted domain.
    let mut closedLets : Std.HashSet FVarId := {}
    let mut rootedArgs := roots.foldl (init := ({} : Std.HashSet FVarId)) fun ids x =>
      ids.insert x.fvarId!
    for x in scope do
      if let some value := (← x.fvarId!.getDecl).value? (allowNondep := true) then
        if !value.hasAnyFVar (fun id => !closedLets.contains id) then
          closedLets := closedLets.insert x.fvarId!
        if !value.hasAnyFVar (fun id => !rootedArgs.contains id) then
          rootedArgs := rootedArgs.insert x.fvarId!
    if expr.hasAnyFVar (fun id => !rootedArgs.contains id) then
      throwError "allocator admission application arguments are not bound to the root"
    let mut evidence := none
    let mut rootBound := false
    for x in scope do
      let ty ← instantiateMVars (← inferType x)
      if ty.hasMVar then throwError "allocator admission context contains unresolved metavariables"
      if ← isDefEq ty expected then
        let proof ← close scope x
        if proof.hasFVar || proof.hasMVar || !(← isDefEq (← inferType proof) obligation) then
          throwError "allocator admission evidence does not have the exact scoped predicate"
        evidence := some proof
        rootBound := roots.contains x || closedLets.contains x.fvarId!
        if rootBound then break
    keys.modify (·.insert application)
    uses.modify (·.push ⟨name, application, obligation, evidence, rootBound⟩)
  let rec walk (expr : Expr) (scope : Array Expr) : Nat → MetaM Unit
    | 0 => throwError "allocator admission application expansion is too deep"
    | depth + 1 => do
      -- Inspect the original application before beta can erase an ignored argument or
      -- dependent binder annotation containing a contract producer.
      let expr := expr.consumeMData
      -- The same term under a stronger local premise is a different use. In particular, an
      -- earlier use under False must not hide an unrestricted use of the same closed contract.
      let closedExpr ← close scope expr
      if (← seen.get).contains closedExpr then return
      let budget ← remaining.get
      if budget == 0 then throwError "allocator admission application expansion budget exhausted"
      remaining.set (budget - 1)
      seen.modify (·.insert closedExpr)
      match expr with
      | .lam name ty body bi | .forallE name ty body bi =>
        walk ty scope depth
        withLocalDecl name bi ty fun x => walk (body.instantiate1 x) (scope.push x) depth
      | .letE name ty value body _ =>
        walk ty scope depth
        walk value scope depth
        withLetDecl name ty value fun x =>
          walk (body.instantiate1 x) (scope.push x) depth
      | _ =>
        let args := expr.getAppArgs
        let fn := expr.getAppFn.consumeMData
        -- Polymorphic forwarding helpers need not mention allocators in their own type
        -- or body. Their actual producer argument (or its checked type) selects expansion.
        let carriesContract ← args.anyM fun arg => do
          return touches arg || touches (← inferType arg)
        let functionType ← inferType fn
        if touches fn || touches functionType || carriesContract then
          let mut appliedType := functionType
          for arg in args do
            -- Reducing an opaque/aliased domain here could erase proof indices before
            -- they are inspected at the actual arguments. Unsupported exposure stays closed.
            let .forallE _ domain body _ := appliedType.consumeMData |
              throwError "allocator admission cannot inspect the checked argument telescope"
            walk domain scope depth
            appliedType := body.instantiate1 arg
          walk appliedType scope depth
        match fn with
        | .fvar id =>
          if let some value := (← id.getDecl).value? (allowNondep := true) then
            walk (mkAppN value args) scope depth
          else if carriesContract || (← concreteResult expr) then
            throwError "allocator admission found an unbound concrete contract application"
        | .letE name ty value body _ =>
          walk ty scope depth
          walk value scope depth
          withLetDecl name ty value fun x =>
            walk (mkAppN (body.instantiate1 x) args) (scope.push x) depth
        | .proj _ _ value =>
          -- A function stored in a structure field is still applied to these exact args.
          -- Inspect the holder as well; the projection must not hide other proof dependencies.
          walk value scope depth
          if let some field ← reduceProj? fn then
            walk (mkAppN field args) scope depth
          else if carriesContract || (← concreteResult expr) then
            throwError "allocator admission cannot inspect a concrete projected contract"
        | .const name levels =>
          let isCtor := name == `Zig.Full.FAllocSpec.mk || name == `Zig.Full.CAllocSpec.mk
          if isCtor then
            match ← ownResult.get with
            | some result =>
              -- Definitional equality remains valid under every later actual substitution.
              -- A foreign generic constructor could become concrete only in a caller, so
              -- it also needs its own named creation contract rather than this permission.
              unless ← isDefEq (← inferType expr) result do
                throwError "allocator admission found an unnamed concrete constructor application"
            | none =>
              if ← concreteResult expr then
                throwError "allocator admission found an unnamed concrete constructor application"
          if contracts.contains name then
            record name expr scope
          else if relevant.contains name || carriesContract then
            let some info := env.checked.get.find? name |
              throwError "allocator admission names an unchecked declaration {name}"
            match info with
            | .inductInfo _ | .ctorInfo _ => pure ()
            | _ =>
              let expanded ← match info.value? (allowOpaque := true) with
                | some value => pure (mkAppN (value.instantiateLevelParams info.levelParams levels) args)
                | none => whnfCore expr
              if expanded == expr then
                throwError "allocator admission cannot inspect the application of {name}"
              walk expanded scope depth
        | .lam .. => walk (fn.beta args) scope depth
        | _ =>
          -- Metadata around an applied head must not turn it into an unvisited subterm.
          if fn != expr.getAppFn then walk (mkAppN fn args) scope depth
        for arg in args do
          walk arg scope depth
  try
    let some info := env.checked.get.find? root |
      return .error "allocator admission root is not a checked declaration"
    let levels := info.levelParams.map Level.param
    forallTelescope info.type fun xs conclusion => do
      rootScope.set xs
      if contracts.contains root then ownResult.set (some conclusion)
      -- A checked producer can occur only in a binder's type/index while the proof body
      -- ignores that binder. Inspect those actual applications as part of the root as well.
      for x in xs do
        let ty ← inferType x
        if ← concretePremise ty then
          throwError "allocator admission found an unbound concrete contract premise"
        walk ty xs 512
      walk conclusion xs 512
      if contracts.contains root then
        record root (mkAppN (mkConst root levels) xs) xs
        -- Its exact own constructor is authenticated by the separately checked creation
        -- post; other constructors in the same body are not authenticated by that post.
      let some value := info.value? (allowOpaque := true) |
        throwError "allocator admission root has no checked proof body"
      walk (mkAppN (value.instantiateLevelParams info.levelParams levels) xs) xs 512
      return .ok (← uses.get)
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Air2Lean.AllocatorAdmission
