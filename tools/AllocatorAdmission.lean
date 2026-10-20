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

/-- The exact checked head selection followed before consuming a type telescope. Projection
arguments are term applications; `arguments` supplies the eventual function-type arguments. -/
private structure Inspection where
  arguments : Array Expr := #[]
  projections : List (Name × Nat × Array Expr) := []
  deriving BEq, Hashable

private def Inspection.isEmpty (ctx : Inspection) : Bool :=
  ctx.arguments.isEmpty && ctx.projections.isEmpty

/-- Read actual applications rather than reconstructing them from a set of dependency names.
`contracts` contains named implementation theorems. `relevant` also includes the declarations
whose checked dependency closures reach an allocator contract type. All expressions returned here
are closed; their universe parameters remain those of the checked root declaration. -/
def collectUses (env : Environment) (root : Name) (contracts relevant : NameSet)
    (admission : Expr → MetaM (Option Expr)) (concretePremise : Expr → MetaM Bool) :
    MetaM (Except String (Array AppliedUse)) := do
  let seen ← IO.mkRef ({} : Std.HashSet (Array Expr × Expr × Inspection))
  let keys ← IO.mkRef ({} : Std.HashSet Expr)
  let uses ← IO.mkRef (#[] : Array AppliedUse)
  let rootScope ← IO.mkRef (#[] : Array Expr)
  let selectedLets ← IO.mkRef ({} : Std.HashSet FVarId)
  let ownResult ← IO.mkRef (none : Option Expr)
  let remaining ← IO.mkRef (50000 : Nat)
  let close := fun scope expr => mkLambdaFVars scope expr
    (usedLetOnly := false) (generalizeNondepLet := false)
  -- Relevance selects work only. Follow checked local types and let values without reducing
  -- them, so a local type alias cannot hide a producer from a later actual application.
  let touches (expr : Expr) : MetaM Bool := do
    if expr.getUsedConstants.any relevant.contains then return true
    let deps ← (collectFVars {} expr).addDependencies
    deps.fvarIds.anyM fun id => do
      let decl ← id.getDecl
      return decl.type.getUsedConstants.any relevant.contains ||
        (decl.value? (allowNondep := true)).any fun value =>
          value.getUsedConstants.any relevant.contains
  let unboundResult (expr : Expr) : MetaM Bool := do
    let ty ← whnf (← inferType expr)
    if ty.isAppOfArity `Zig.Full.FAllocSpec 4 || ty.isAppOfArity `Zig.Full.CAllocSpec 4 then
      if let some result ← ownResult.get then
        -- A foreign generic field can become concrete at a later named call. The named
        -- body's creation post authenticates only its exact own contract result.
        return !(← isDefEq ty result)
      else
        -- A local let naming a concrete invariant is not a fresh interface parameter.
        let inv := (← whnf ty.appArg!).getAppFn
        return !inv.isFVar && !inv.isBVar
    return false
  let checkConstructor (name : Name) (expr : Expr) : MetaM Unit := do
    if name == `Zig.Full.FAllocSpec.mk || name == `Zig.Full.CAllocSpec.mk then
      match ← ownResult.get with
      | some result =>
        -- Definitional equality remains valid under every later actual substitution.
        unless ← isDefEq (← inferType expr) result do
          throwError "allocator admission found an unnamed concrete constructor application"
      | none =>
        if ← unboundResult expr then
          throwError "allocator admission found an unnamed concrete constructor application"
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
  let unsupportedTelescope (expr : Expr) (scope : Array Expr) (ctx : Inspection) : MetaM Unit :=
    throwError "allocator admission cannot inspect the checked argument telescope of {expr}; pending arguments: {ctx.arguments}; projection count: {ctx.projections.length}; scope depth: {scope.size}"
  -- A nonempty pending array inspects a checked function type at its actual arguments. The
  -- same walker exposes checked aliases and lets, stopping at each forall to substitute the
  -- next actual argument before inspecting later dependent domains. It never invents one.
  let rec walk (expr : Expr) (scope : Array Expr) : Nat → Inspection → MetaM Unit
    | 0, _ => throwError "allocator admission application expansion is too deep"
    | depth + 1, ctx => do
      -- Inspect the original application before beta can erase an ignored argument or
      -- dependent binder annotation containing a contract producer.
      let expr := expr.consumeMData
      -- The same term under a stronger local premise is a different use. In particular, an
      -- earlier use under False must not hide an unrestricted use of the same closed contract.
      -- The key is the open term with its actual scope. Every walked term is free of loose
      -- bound variables, so for a fixed scope it determines its closure over that scope and
      -- conversely: this is the same identity as the closed term, without building one. A
      -- closure copies the scope's let values (the proof's whole prefix) and was built for
      -- every visited term (AllocFba's audit: above 11 GB).
      let scopedExpr := (scope, expr, ctx)
      if (← seen.get).contains scopedExpr then return
      let budget ← remaining.get
      if budget == 0 then throwError "allocator admission application expansion budget exhausted"
      remaining.set (budget - 1)
      seen.modify (·.insert scopedExpr)
      match expr with
      | .forallE name ty body bi =>
        unless ctx.projections.isEmpty do unsupportedTelescope expr scope ctx
        walk ty scope depth {}
        if let some arg := ctx.arguments[0]? then
          walk (body.instantiate1 arg) scope depth
            { arguments := ctx.arguments.extract 1 ctx.arguments.size }
        else
          withLocalDecl name bi ty fun x => walk (body.instantiate1 x) (scope.push x) depth {}
      | .lam name ty body bi =>
        unless ctx.isEmpty do unsupportedTelescope expr scope ctx
        walk ty scope depth {}
        withLocalDecl name bi ty fun x => walk (body.instantiate1 x) (scope.push x) depth {}
      | .letE name ty value body _ =>
        withLetDecl name ty value fun x => do
          walk (body.instantiate1 x) (scope.push x) depth ctx
          -- A selected let has already had its type and value inspected at every actual use.
          -- Unused prefixes still need both raw walks, including ignored proof dependencies.
          unless (← selectedLets.get).contains x.fvarId! do
            walk ty scope depth {}
            walk value scope depth {}
      | _ =>
        let args := expr.getAppArgs
        let fn := expr.getAppFn.consumeMData
        let functionType ← inferType fn
        if let .const name _ := fn then checkConstructor name expr
        if let (name, index, applied) :: rest := ctx.projections then
          if let .const ctor _ := fn then
            if let some (.ctorInfo info) := env.checked.get.find? ctor then
              unless info.induct == name && index < info.numFields &&
                  args.size == info.numParams + info.numFields do
                unsupportedTelescope expr scope ctx
              let selected := info.numParams + index
              -- Constructor telescopes are checked structural foralls. Inspect each raw
              -- dependent domain at the constructor's actual arguments, selecting only the
              -- projected field's domain at its own actual applications.
              forallTelescope functionType fun xs result => do
                unless xs.size == args.size do unsupportedTelescope expr scope ctx
                for i in [:xs.size] do
                  let domain := (← inferType xs[i]!).replaceFVars xs args
                  walk domain scope depth (if i == selected then { arguments := applied } else {})
                walk (result.replaceFVars xs args) scope depth {}
              for i in [:args.size] do
                if i == selected then
                  walk (mkAppN args[i]! applied) scope depth { ctx with projections := rest }
                else
                  walk args[i]! scope depth {}
              return
        -- Polymorphic forwarding helpers need not mention allocators in their own type
        -- or body. Their actual producer argument (or its checked type) selects expansion.
        let carriesContract ← args.anyM fun arg => do
          if ← touches arg then return true
          touches (← inferType arg)
        -- Every selected local value must have its stored type inspected at this use's
        -- actual arguments, even when that type is itself only a local alias.
        if fn.isFVar || (← touches fn) || (← touches functionType) || carriesContract then
          walk functionType scope depth { arguments := args }
        match fn with
        | .fvar id =>
          if let some value := (← id.getDecl).value? (allowNondep := true) then
            walk (mkAppN value args) scope depth ctx
            selectedLets.modify (·.insert id)
          else if !ctx.isEmpty then unsupportedTelescope expr scope ctx
          else if carriesContract || (← unboundResult expr) then
            throwError "allocator admission found an unbound concrete contract application"
        | .letE name ty value body _ =>
          -- Reuse the let case without losing these checked applications.
          walk (.letE name ty value (mkAppN body (args.map (·.liftLooseBVars 0 1))) false)
            scope depth ctx
        | .proj name index value =>
          -- A function stored in a structure field is still applied to these exact args.
          -- Inspect the holder as well; the projection must not hide other proof dependencies.
          if (← reduceProj? fn).isSome then
            walk value scope depth { ctx with projections := (name, index, args) :: ctx.projections }
          else
            walk value scope depth {}
            if !ctx.isEmpty then unsupportedTelescope expr scope ctx
            else if carriesContract || (← unboundResult expr) then
              throwError "allocator admission cannot inspect a concrete projected contract"
        | .const name levels =>
          if contracts.contains name then
            unless ctx.isEmpty do unsupportedTelescope expr scope ctx
            record name expr scope
          else if relevant.contains name || carriesContract || !ctx.isEmpty then
            let some info := env.checked.get.find? name |
              throwError "allocator admission names an unchecked declaration {name}"
            if let some projection := env.getProjectionFnInfo? name then
              if args.size > projection.numParams then
                let some (.ctorInfo ctor) := env.checked.get.find? projection.ctorName |
                  unsupportedTelescope expr scope ctx
                unless ctor.numParams == projection.numParams && projection.i < ctor.numFields do
                  unsupportedTelescope expr scope ctx
                let some value := info.value? (allowOpaque := true) |
                  unsupportedTelescope expr scope ctx
                let holderArgs := args.extract 0 (projection.numParams + 1)
                -- Authenticate the cached projection against its checked lambda. Inspect its
                -- raw domains, then reuse the existing projection path exactly once; scanning
                -- the holder again without that path would invent fresh family arguments.
                lambdaTelescope (value.instantiateLevelParams info.levelParams levels) fun xs body => do
                  unless xs.size == holderArgs.size &&
                      body.consumeMData == .proj ctor.induct projection.i xs.back! do
                    unsupportedTelescope expr scope ctx
                  for x in xs do
                    walk ((← inferType x).replaceFVars xs holderArgs) scope depth {}
                walk (mkAppN (.proj ctor.induct projection.i args[projection.numParams]!)
                  (args.extract (projection.numParams + 1) args.size)) scope depth ctx
                for arg in args.extract 0 projection.numParams do
                  walk arg scope depth {}
                return
            match info with
            | .inductInfo _ | .ctorInfo _ | .recInfo _ =>
              unless ctx.isEmpty do unsupportedTelescope expr scope ctx
            | _ =>
              let expanded ← match info.value? (allowOpaque := true) with
                | some value => pure (mkAppN (value.instantiateLevelParams info.levelParams levels) args)
                | none => whnfCore expr
              if expanded == expr then
                throwError "allocator admission cannot inspect the application of {name}"
              walk expanded scope depth ctx
        | .lam .. => walk (fn.beta args) scope depth ctx
        | _ =>
          -- Metadata around an applied head must not turn it into an unvisited subterm.
          if fn != expr.getAppFn then walk (mkAppN fn args) scope depth ctx
          else unless ctx.isEmpty do unsupportedTelescope expr scope ctx
        for arg in args do
          walk arg scope depth {}
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
        walk ty xs 512 {}
      walk conclusion xs 512 {}
      if contracts.contains root then
        record root (mkAppN (mkConst root levels) xs) xs
        -- Its exact own constructor is authenticated by the separately checked creation
        -- post; other constructors in the same body are not authenticated by that post.
      let some value := info.value? (allowOpaque := true) |
        throwError "allocator admission root has no checked proof body"
      walk (mkAppN (value.instantiateLevelParams info.levelParams levels) xs) xs 512 {}
      return .ok (← uses.get)
  catch ex =>
    return .error (← ex.toMessageData.toString)

end Air2Lean.AllocatorAdmission
