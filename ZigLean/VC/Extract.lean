import ZigLean.VC.Rules
import Lean

/-!
# Automatic VC extraction for loop-free generated functions

`#vc_extract f` reflects the body of a generated, loop-free `Zig.Result`/`Zig.MemM` function
into the typed VC AST of `ZigLean.VC.Result`/`ZigLean.VC.Mem` and adds three declarations next
to `f` (for `Ns.f`):

* `Ns.vc_f : ∀ xs, ResultProgram α` (or `MemProgram α`), the extracted program;
* `Ns.vc_f_source : ∀ xs, (vc_f xs).eval = f xs`, a kernel-checked equality with the
  generated function (the normalization proof produced by `simp`, then definitional
  unfolding of `eval`);
* `Ns.vc_f_sound`, the existing `sound` theorem transported along that equality.

Extraction fails closed. A generated loop (`Ns.f.loop<i>`, from AIR instruction `%i`) produces
an explicit request for an invariant and a variant; no invariant is guessed. Self-recursion,
an unknown operation, or a call without a `@[vc_contract]` is refused with its reason.

`vc_gen` turns a contract goal `∃ v, f xs = pure v ∧ post v` or `Triple pre (f xs) post` into
the extracted program's VC and splits it into separate goals tagged `safety_i`, `memory_i`,
`result_i` or `error_i`. `vc_gen?` also logs that obligation report.
`#vc_extract_all Ns` extracts every `Result`/`MemM` function in `Ns` and reports the outcome of
each (extracted, loop request, or refusal); it never fails on a single function.
Each report message also carries one machine-readable `vc-report {json}` line.
-/

open Lean Meta Elab Term Command Tactic

namespace Zig.VC.Extract

/-! ## Obligation kinds -/

inductive Kind where
  | safety
  | result
  | memory
  | error
  deriving BEq, Inhabited

def Kind.name : Kind → String
  | .safety => "safety"
  | .result => "result"
  | .memory => "memory"
  | .error => "error"

/-! ## Loops and refusals -/

/-- A loop the extractor does not summarize. -/
structure LoopRequest where
  loopDef : Name
  instruction : Option Nat

def loopInstruction? : Name → Option Nat
  | .str _ s =>
    let cs := s.toList
    if cs.take 4 == "loop".toList then (String.ofList (cs.drop 4)).toNat? else none
  | _ => none

/-- Recursion bound of reflection and splitting (one unit per AST constructor). -/
def fuelLimit : Nat := 100000

/-- Every generated loop body reachable from `f`'s definition (nested loops included). -/
def loopRequests (f : Name) : MetaM (Array LoopRequest) := do
  let env ← getEnv
  let mut todo := [f]
  let mut seen : NameSet := {}
  let mut found := #[]
  -- A generated function has finitely many loop defs; each is visited once.
  for _ in [0:fuelLimit] do
    let n :: rest := todo | break
    todo := rest
    let some v := env.find? n |>.bind (·.value?) | continue
    let loops := v.getUsedConstants.filter fun c =>
      c.getPrefix == f && (loopInstruction? c).isSome && !seen.contains c
    seen := loops.foldl (·.insert ·) seen
    found := found ++ loops.map fun c => { loopDef := c, instruction := loopInstruction? c }
    todo := loops.toList ++ todo
  if found.isEmpty then
    if let some v := env.find? f |>.bind (·.value?) then
      if v.getUsedConstants.contains ``Zig.loop then
        return #[{ loopDef := f, instruction := none }]
  return found

def LoopRequest.describe (r : LoopRequest) : String :=
  let at_ := match r.instruction with
    | some i => s!"AIR instruction %{i}"
    | none => "an unnamed AIR loop"
  s!"invariant + variant required for loop `{r.loopDef}` at {at_}"

def loopGuidance : String :=
  "VC extraction does not guess invariants. For a memory loop, prove \
  `(Zig.loop body again).run s` with `loop_template inv post` (goals `step`, `entry`, `exit`; \
  `inv s n` carries the variant `n`) or `MemProgram.annotatedLoop`; for a `Result` loop use \
  `Zig.loop_spec` (invariant `inv`, variant `m`). Register the proved function contract with \
  `@[vc_contract]` so callers can use it."

/-- A machine-readable report line. -/
def reportLine (j : Json) : String := "vc-report " ++ j.compress

/-- The outcome of one extraction. -/
inductive Outcome where
  | ok (program source : Expr) (mem : Bool)
  | loops (requests : Array LoopRequest)
  | refused (reason : MessageData)

/-! ## Normalization -/

def normLemmas : Array Name := #[
  ``StateT.run'_eq, ``StateT.run_bind, ``StateT.run_pure, ``StateT.run_monadLift,
  ``StateT.run_lift, ``StateT.run_get, ``StateT.run_set, ``StateT.run_modify,
  ``StateT.run_modifyGet, ``run_ite, ``ite_bind, ``map_ite, ``bind_assoc, ``pure_bind,
  ``map_bind, ``map_pure, ``bind_map_left, ``bind_pure, ``run_throw_result, ``run_throw_mem,
  ``monadLift_self]

/-- Unfold `f` once and remove the locals/exit plumbing of the generated body. -/
def normalize (f : Name) (e : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for n in normLemmas do
    thms ← thms.addConst n
  for n in [``Zig.call, ``Zig.callM, ``Zig.callR] do
    thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let mut procs : Simprocs := {}
  procs ← procs.add ``reduceIte false
  procs ← procs.add ``reduceDIte false
  -- Unfold `f` exactly once through its `eq_def`, so a recursive body stays finite.
  let some eqDef ← getUnfoldEqnFor? f (nonRec := true)
    | throwError "`{f}` has no unfolding equation"
  let unfold := mkAppN (mkConst eqDef e.getAppFn.constLevels!) e.getAppArgs
  let body := (← whnfR (← inferType unfold)).appArg!
  let (r, _) ← simp body ctx #[procs]
  return { expr := r.expr, proof? := some (← match r.proof? with
    | some p => mkEqTrans unfold p
    | none => pure unfold) }

/-! ## Contracts -/

/-- The obligation category of a modular call's precondition. -/
def callKind (thm : Name) (mem : Bool) : String :=
  if (`Zig.VC.Prim).isPrefixOf thm then "safety" else if mem then "call-memory" else "call"

/-- A contract applies only to its own operation: compare head constants before a reducible
unification, so unrelated generated functions are never unfolded. -/
def sameHeadDefEq (pattern e : Expr) : MetaM Bool := do
  let pattern ← instantiateMVars pattern
  match pattern.getAppFn.constName?, e.getAppFn.constName? with
  | some a, some b => if a == b then withReducible (isDefEq pattern e) else pure false
  | _, _ => pure false

/-- Instantiate a `@[vc_contract]` theorem whose action is `e`. -/
def contractCall? (e α : Expr) (mem : Bool) : MetaM (Option Expr) := do
  for thm in ← labelled `vc_contract do
    let r ← commitWhenSome? do
      let c ← mkConstWithFreshMVarLevels thm
      -- A memory contract's conclusion is `Triple …`, a definition over a `∀`: do not unfold it.
      let (ms, _, body) ← if mem then forallMetaTelescope (← inferType c)
        else forallMetaTelescopeReducing (← inferType c)
      let body ← instantiateMVars body
      let head := e.getAppFn.constName?.getD .anonymous
      let label := s!"{callKind thm mem}: {head} [{thm}]"
      if mem then
        unless body.isAppOfArity ``Zig.Triple 4 do return none
        unless ← sameHeadDefEq (body.getArg! 2) e do return none
        synthesizeRemaining ms
        -- A memory contract must be an unconditional `Triple`; put conditions into `pre`.
        unless ← ms.allM (·.mvarId!.isAssigned) do
          throwError "`@[vc_contract]` theorem `{thm}` for `{head}` has hypotheses outside \
            its `Triple`; state them in the precondition (`⌜φ⌝ ∗ P`) instead"

        let pre ← instantiateMVars (body.getArg! 1)
        let post ← instantiateMVars (body.getArg! 3)
        let proof ← instantiateMVars (mkAppN c ms)
        return some (mkAppN (mkConst ``MemProgram.call) #[α, mkStrLit label, e, pre, post, proof])
      else
        unless body.isAppOfArity ``Exists 2 do return none
        let lam := body.getArg! 1
        unless lam.isLambda do return none
        let conj := lam.bindingBody!
        unless conj.isAppOfArity ``And 2 do return none
        let eq := conj.getArg! 0
        unless eq.isAppOfArity ``Eq 3 do return none
        let action := eq.getArg! 1
        if action.hasLooseBVars then return none
        unless ← sameHeadDefEq action e do return none
        -- The trailing non-dependent hypotheses form the precondition (their conjunction).
        let body ← instantiateMVars body
        let mut count := 0
        while count < ms.size do
          let m := ms[ms.size - 1 - count]!
          unless (← isProp (← inferType m)) && (body.find? (· == m)).isNone do break
          count := count + 1
        let args := ms.extract 0 (ms.size - count)
        let hyps := ms.extract (ms.size - count) ms.size
        synthesizeRemaining args
        unless ← args.allM (·.mvarId!.isAssigned) do return none
        let hypTypes ← hyps.mapM fun h => do instantiateMVars (← inferType h)
        if hypTypes.any (fun t => (t.find? fun x => hyps.contains x).isSome) then return none
        let summary ← instantiateMVars (mkLambda lam.bindingName! .default lam.bindingDomain!
          (conj.getArg! 1))
        let thmArgs ← instantiateMVars (mkAppN c args)
        let pre := if hypTypes.isEmpty then Lean.mkConst ``True
          else hypTypes.pop.foldr (fun t acc => mkApp2 (Lean.mkConst ``And) t acc) hypTypes.back!
        let proof ← withLocalDeclD `pre pre fun hp => do
          -- `pre` is `h₁ ∧ (h₂ ∧ …)`: project each hypothesis in order.
          let mut projs := #[]
          let mut rest := hp
          for i in [0:count] do
            if i + 1 == count then
              projs := projs.push rest
            else
              projs := projs.push (mkProj ``And 0 rest)
              rest := mkProj ``And 1 rest
          mkLambdaFVars #[hp] (mkAppN thmArgs projs)
        return some (mkAppN (mkConst ``ResultProgram.call)
          #[α, mkStrLit label, e, pre, summary, proof])
    if r.isSome then return r
  return none
where
  synthesizeRemaining (ms : Array Expr) : MetaM Unit := do
    for m in ms do
      unless ← m.mvarId!.isAssigned do
        if (← m.mvarId!.getKind) matches .synthetic || (← isClass? (← inferType m)).isSome then
          if let some inst ← synthInstance? (← instantiateMVars (← inferType m)) then
            discard <| isDefEq m inst

/-! ## Reflection -/

/-- Bound `Bool` conditions: generated branches are `if b then …` on a `Bool`. -/
def boolCondition? (c : Expr) : Option Expr :=
  if c.isAppOfArity ``Eq 3 && (c.getArg! 0).isConstOf ``Bool && (c.getArg! 2).isConstOf ``Bool.true
  then some (c.getArg! 1) else none

def isThrow (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``MonadExcept.throw 5 then some (e.getArg! 3, e.getArg! 4)
  else if e.isAppOfArity ``MonadExceptOf.throw 5 then some (e.getArg! 3, e.getArg! 4)
  else if e.isAppOfArity ``throwThe 5 then some (e.getArg! 3, e.getArg! 4)
  else none

def unsupported (e : Expr) : MetaM α := do
  let env ← getEnv
  if e.isAppOf ``StateT.run || (e.find? fun s => s.isApp && s.getAppFn.isConst &&
      isMatcherCore env s.getAppFn.constName!).isSome then
    throwError "the generated control flow did not normalize (a `match` on a value that is \
      not a constructor, e.g. tagged-union or exit dispatch):{indentExpr e}"
  let head := match e.getAppFn.constName? with
    | some n => m!"`{n}`"
    | none => m!"{e}"
  throwError "no VC rule or `@[vc_contract]` theorem for {head}:{indentExpr e}"

/-- Reflect a continuation `k : α → m β`, eta-expanding if needed. -/
def reflectCont (r : Expr → MetaM Expr) (α k : Expr) : MetaM Expr := do
  let name := if k.isLambda then k.bindingName! else `x
  withLocalDeclD name α fun v => do
    mkLambdaFVars #[v] (← r (mkApp k v).headBeta)

def reflectResult (fuel : Nat) (e : Expr) : MetaM Expr := do
  let fuel + 1 := fuel | throwError "program too large for VC extraction"
  let e := e.headBeta
  let α ← resultValueType e
  if e.isAppOfArity ``Bind.bind 6 then
    let x := e.getArg! 4
    let β := e.getArg! 2
    let px ← reflectResult fuel x
    let pk ← reflectCont (reflectResult fuel) β (e.getArg! 5)
    return mkAppN (mkConst ``ResultProgram.bind) #[β, α, px, pk]
  if e.isAppOfArity ``Pure.pure 4 then
    return mkAppN (mkConst ``ResultProgram.ret) #[α, e.getArg! 3]
  if e.isAppOfArity ``ite 5 then
    let some b := boolCondition? (e.getArg! 1)
      | throwError "branch condition is not a `Bool` test:{indentExpr (e.getArg! 1)}"
    -- A literal condition left by exit dispatch selects its branch definitionally.
    if b.isConstOf ``Bool.true then return ← reflectResult fuel (e.getArg! 3)
    if b.isConstOf ``Bool.false then return ← reflectResult fuel (e.getArg! 4)
    return mkAppN (mkConst ``ResultProgram.branch)
      #[α, b, ← reflectResult fuel (e.getArg! 3), ← reflectResult fuel (e.getArg! 4)]
  if let some (_, err) := isThrow e then
    return mkAppN (mkConst ``ResultProgram.panic) #[α, err]
  if e.isAppOfArity ``Zig.add 4 && (e.getArg! 1).isConstOf ``Bool.false then
    return mkAppN (mkConst ``ResultProgram.add) #[e.getArg! 0, e.getArg! 2, e.getArg! 3]
  if e.isAppOfArity ``Zig.intCast 5 && (e.getArg! 1).isConstOf ``Bool.false &&
      (e.getArg! 2).isConstOf ``Bool.false then
    if let (some n, some m) := (← evalNat (e.getArg! 0), ← evalNat (e.getArg! 3)) then
      if n ≤ m then
        return mkAppN (mkConst ``ResultProgram.widen) #[e.getArg! 0, e.getArg! 4, e.getArg! 3]
  if let some p ← contractCall? e α false then return p
  unsupported e
where
  resultValueType (e : Expr) : MetaM Expr := do
    let ty ← whnfR (← inferType e)
    -- `Zig.Result α` is `ExceptT Error Option α`.
    if ty.isAppOfArity ``ExceptT 3 then return ty.getArg! 2
    if ty.isAppOfArity ``Zig.Result 1 then return ty.getArg! 0
    throwError "expected a `Zig.Result` computation, got{indentExpr ty}"

def reflectMem (fuel : Nat) (e : Expr) : MetaM Expr := do
  let fuel + 1 := fuel | throwError "program too large for VC extraction"
  let e := e.headBeta
  let α ← memValueType e
  if e.isAppOfArity ``Bind.bind 6 then
    let β := e.getArg! 2
    let px ← reflectMem fuel (e.getArg! 4)
    let pk ← reflectCont (reflectMem fuel) β (e.getArg! 5)
    return mkAppN (mkConst ``MemProgram.bind) #[β, α, px, pk]
  if e.isAppOfArity ``Pure.pure 4 then
    return mkAppN (mkConst ``MemProgram.ret) #[α, e.getArg! 3]
  if e.isAppOfArity ``ite 5 then
    let some b := boolCondition? (e.getArg! 1)
      | throwError "branch condition is not a `Bool` test:{indentExpr (e.getArg! 1)}"
    -- A literal condition left by exit dispatch selects its branch definitionally.
    if b.isConstOf ``Bool.true then return ← reflectMem fuel (e.getArg! 3)
    if b.isConstOf ``Bool.false then return ← reflectMem fuel (e.getArg! 4)
    return mkAppN (mkConst ``MemProgram.branch)
      #[α, b, ← reflectMem fuel (e.getArg! 3), ← reflectMem fuel (e.getArg! 4)]
  if let some (_, err) := isThrow e then
    let panic := mkAppN (mkConst ``ResultProgram.panic) #[α, err]
    return mkAppN (mkConst ``MemProgram.lift) #[α, panic]
  if e.isAppOfArity ``Zig.load 4 then
    return mkAppN (mkConst ``MemProgram.load) #[e.getArg! 0, e.getArg! 1, e.getArg! 3, e.getArg! 2]
  if e.isAppOfArity ``Zig.store 5 then
    let T := e.getArg! 0
    let some lawful ← synthInstance? (mkApp2 (mkConst ``Zig.LawfulEnc) T (e.getArg! 1))
      | throwError "no `LawfulEnc` instance for the stored type{indentExpr T}"
    return mkAppN (mkConst ``MemProgram.store)
      #[T, e.getArg! 1, lawful, e.getArg! 3, e.getArg! 2, e.getArg! 4]
  if e.isAppOfArity ``MonadLiftT.monadLift 5 || e.isAppOfArity ``MonadLift.monadLift 5 ||
      e.isAppOfArity ``StateT.lift 5 || e.isAppOfArity ``liftM 5 then
    let x := e.appArg!
    let xty ← whnfR (← inferType x)
    if xty.isAppOfArity ``ExceptT 3 then
      return mkAppN (mkConst ``MemProgram.lift) #[α, ← reflectResult fuel x]
  if let some p ← contractCall? e α true then return p
  unsupported e
where
  memValueType (e : Expr) : MetaM Expr := do
    let ty ← whnfR (← inferType e)
    -- `Zig.MemM α` is `StateT Mem Result α`.
    if ty.isAppOfArity ``StateT 3 then return ty.getArg! 2
    if ty.isAppOfArity ``Zig.MemM 1 then return ty.getArg! 0
    throwError "expected a `Zig.MemM` computation, got{indentExpr ty}"

/-- `some true` for `Zig.MemM α`, `some false` for `Zig.Result α`. -/
def monadOf (ty : Expr) : Option Bool :=
  if ty.isAppOfArity ``Zig.MemM 1 then some true
  else if ty.isAppOfArity ``Zig.Result 1 then some false
  else none

/-- Extract the VC program of the application `app` of the generated function `f`. -/
def extractApp (f : Name) (app : Expr) : MetaM Outcome := do
  let some mem := monadOf (← inferType app)
    | return .refused m!"`{f}` does not return `Zig.Result` or `Zig.MemM`"
  let requests ← loopRequests f
  unless requests.isEmpty do return .loops requests
  try
    let r ← normalize f app
    if (r.expr.find? fun s => s.isConstOf f).isSome then
      return .refused m!"`{f}` is recursive; a recursive call needs an explicit measure and a \
        separately proved contract, so no VC is extracted"
    let program ← if mem then reflectMem fuelLimit r.expr else reflectResult fuelLimit r.expr
    let evalName := if mem then ``MemProgram.eval else ``ResultProgram.eval
    let α ← if mem then reflectMem.memValueType r.expr else reflectResult.resultValueType r.expr
    let eval := mkApp2 (mkConst evalName) α program
    unless ← isDefEq eval r.expr do
      return .refused m!"the reflected program of `{f}` does not evaluate to its \
        normalized body{indentExpr r.expr}"
    let source ← match r.proof? with
      | some p => mkEqSymm p
      | none => mkEqRefl app
    let source ← mkExpectedTypeHint source (← mkEq eval app)
    return .ok program source mem
  catch ex => return .refused ex.toMessageData

/-- Names of the three extracted declarations of `Ns.f`. -/
def vcNames (f : Name) : Name × Name × Name :=
  let last := match f with
    | .str _ s => s
    | _ => toString f
  let base := f.getPrefix ++ Name.mkSimple ("vc_" ++ last)
  (base, base.appendAfter "_source", base.appendAfter "_sound")

/-- Add `vc_f`, `vc_f_source` and `vc_f_sound` for `f`. -/
def extractDecl (f : Name) : MetaM Outcome := do
  -- All three declarations are added, or none: a rejected one restores the environment.
  let saved ← saveState
  try extractDeclCore f
  catch ex =>
    saved.restore
    return .refused m!"the extracted declarations were rejected: {ex.toMessageData}"
where
  extractDeclCore (f : Name) : MetaM Outcome := do
    let info ← getConstInfo f
    let lvls := info.levelParams.map mkLevelParam
    forallTelescope info.type fun xs _ => do
      let app := mkAppN (mkConst f lvls) xs
      let out ← extractApp f app
      let .ok program source mem := out | return out
      let (vcName, srcName, soundName) := vcNames f
      let progType ← mkForallFVars xs (← inferType program)
      let progValue ← mkLambdaFVars xs program
      addDecl <| .defnDecl {
        name := vcName, levelParams := info.levelParams, type := progType, value := progValue,
        hints := .abbrev, safety := .safe }
      modifyEnv (addNoncomputable · vcName)
      let vcApp := mkAppN (mkConst vcName lvls) xs
      let evalName := if mem then ``MemProgram.eval else ``ResultProgram.eval
      let α := (← whnf (← inferType vcApp)).appArg!
      let srcType ← mkEq (mkApp2 (mkConst evalName) α vcApp) app
      let srcValue ← mkExpectedTypeHint source srcType
      addDecl <| .thmDecl {
        name := srcName, levelParams := info.levelParams, type := ← mkForallFVars xs srcType,
        value := ← mkLambdaFVars xs srcValue }
      let srcApp := mkAppN (mkConst srcName lvls) xs
      let soundValue ← mkLambdaFVars xs (← mkAppM
        (if mem then ``MemProgram.sound_of else ``ResultProgram.sound_of) #[srcApp])
      addDecl <| .thmDecl {
        name := soundName, levelParams := info.levelParams,
        type := ← inferType soundValue, value := soundValue }
      return out

def loopsMessage (f : Name) (requests : Array LoopRequest) : MessageData :=
  let lines := requests.toList.map fun r => m!"\n  {r.describe}"
  m!"vc extraction for `{f}`:{MessageData.joinSep lines m!""}\n{loopGuidance}"

def loopsJson (f : Name) (requests : Array LoopRequest) : Json :=
  Json.mkObj [("function", toJson f.toString), ("status", "loop-request"),
    ("requests", Json.arr (requests.map fun r => Json.mkObj [
      ("loop", toJson r.loopDef.toString),
      ("instruction", match r.instruction with | some i => toJson i | none => Json.null),
      ("request", "invariant + variant")]))]

/-- `#vc_extract f`: add `vc_f`, `vc_f_source` and `vc_f_sound`, or fail closed. -/
elab "#vc_extract " id:ident : command => liftTermElabM do
  let f ← realizeGlobalConstNoOverloadWithInfo id
  match ← extractDecl f with
  | .ok _ _ _ =>
    let (vcName, srcName, soundName) := vcNames f
    logInfo m!"vc extraction for `{f}`: added `{vcName}`, `{srcName}`, `{soundName}`"
  | .loops requests =>
    throwError m!"{loopsMessage f requests}\n{reportLine (loopsJson f requests)}"
  | .refused reason => throwError m!"vc extraction for `{f}` refused: {reason}"

/-- Generated functions of `ns` that return `Zig.Result`/`Zig.MemM`. -/
def generatedFunctions (ns : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, info) in env.constants.toList do
    unless n.getPrefix == ns && !n.isInternalDetail do continue
    unless info matches .defnInfo _ do continue
    if (loopInstruction? n).isSome then continue
    let res ← forallTelescope info.type fun _ r => pure r
    if (monadOf res).isSome then out := out.push n
  return out.qsort (·.toString < ·.toString)

/-- `#vc_extract_all Ns`: extract every generated function of `Ns`, reporting each outcome. -/
elab "#vc_extract_all " id:ident : command => liftTermElabM do
  let ns := id.getId
  for f in ← generatedFunctions ns do
    let (vcName, _, _) := vcNames f
    let out ← if (← getEnv).contains vcName then pure (.ok (mkConst vcName) (mkConst vcName) false)
      else extractDecl f
    match out with
    | .ok _ _ _ =>
      logInfo m!"`{f}`: extracted `{vcName}`\n{reportLine (Json.mkObj
        [("function", toJson f.toString), ("status", "extracted"),
         ("program", toJson vcName.toString)])}"
    | .loops requests =>
      logWarning m!"{loopsMessage f requests}\n{reportLine (loopsJson f requests)}"
    | .refused reason =>
      logWarning m!"`{f}`: refused: {reason}\n{reportLine (Json.mkObj
        [("function", toJson f.toString), ("status", "refused"),
         ("reason", toJson (← reason.toString))])}"

/-! ## Splitting a generated VC into tagged obligations -/

structure Obligation where
  goal : MVarId
  kind : Kind
  label : String
  /-- How the extractor closed it, if it did (a matching hypothesis). -/
  closedBy : Option String := none

def stringLit : Expr → String
  | .lit (.strVal s) => s
  | _ => "call"

/-- Kind of a call precondition, from the label written by `contractCall?`. -/
def labelKind (label : String) : Kind :=
  if label.startsWith "safety" then .safety
  else if label.startsWith "memory" || label.startsWith "call-memory" then .memory
  else .safety

/-- `"safety: Zig.sub [thm]"` becomes `"Zig.sub precondition [thm]"`. -/
def callLabel (label : String) : String :=
  match label.splitOn ": " with
  | [_, rest] => s!"precondition of {rest}"
  | _ => s!"precondition of {label}"

def valueKind (value : Expr) : MetaM Kind := do
  let v ← whnfR value
  return if v.isAppOf ``Except.error then .error else .result

/-- A hypothesis (possibly inside conjunctions or one definition unfolding) that proves `pattern`. -/
def findHyp (pattern : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some p ← search 64 2 d.type d.toExpr then return some p
  return none
where
  /-- `steps` bounds the conjunction traversal, `unfolds` the definition unfoldings. -/
  search (steps unfolds : Nat) (ty proof : Expr) : MetaM (Option Expr) := do
    let steps + 1 := steps | return none
    let ty := (← instantiateMVars ty).headBeta
    if ty.getAppFn.constName? == pattern.getAppFn.constName? then
      if ← isDefEq ty pattern then return some proof
    let ty' ← whnfR ty
    if ty'.isAppOfArity ``And 2 then
      if let some p ← search steps unfolds (ty'.getArg! 0) (mkProj ``And 0 proof) then
        return some p
      return ← search steps unfolds (ty'.getArg! 1) (mkProj ``And 1 proof)
    let unfolds + 1 := unfolds | return none
    if let some ty'' ← unfoldDefinition? ty' then
      return ← search steps unfolds ty'' proof
    return none

def setGoal (g : MVarId) (ty : Expr) : MetaM MVarId := g.replaceTargetDefEq ty

def applyNamed (g : MVarId) (rule : Name) : MetaM (List MVarId) := do
  g.apply (← mkConstWithFreshMVarLevels rule)

/-- Apply `rule`, closing its first premise of `arg`'s type with `arg`. -/
def applyWith (g : MVarId) (rule : Name) (arg : Expr) : MetaM (List MVarId) := do
  let goals ← applyNamed g rule
  let argTy ← inferType arg
  let mut used := false
  for goal in goals do
    if !used && !(← goal.isAssigned) && (← isDefEq (← goal.getType) argTy) then
      goal.assign arg
      used := true
  unless used do throwError "vc_gen: `{rule}` has no premise of type{indentExpr argTy}"
  goals.filterM fun goal => not <$> goal.isAssigned

/-- Split `g` until no generated `vc` remains; `fallback` classifies a final user goal. -/
def split (fuel : Nat) (names : IO.Ref Nat) (g : MVarId) (fallback : Kind × String) :
    MetaM (Array Obligation) :=
  g.withContext do
  let fuel + 1 := fuel | throwError "vc_gen: VC too large"
  let ty := (← instantiateMVars (← g.getType)).headBeta
  if ty.isAppOfArity ``ResultProgram.vc 3 then
    let prog ← whnf (ty.getArg! 1)
    let g ← setGoal g (mkApp3 ty.getAppFn (ty.getArg! 0) prog (ty.getArg! 2))
    splitResult fuel names g prog
  else if ty.isAppOfArity ``MemProgram.vc 4 then
    let prog ← whnf (ty.getArg! 1)
    let g ← setGoal g (mkApp4 ty.getAppFn (ty.getArg! 0) prog (ty.getArg! 2) (ty.getArg! 3))
    splitMem fuel names g prog (ty.getArg! 3)
  else if ty.isAppOfArity ``ensures 5 then
    let g ← setGoal g ty
    let value := ty.getArg! 3
    let [r, m] ← applyNamed g ``ensures_intro | throwError "vc_gen: ensures_intro"
    let rs ← split fuel names r (← valueKind value, "functional result")
    return rs ++ (← split fuel names m (.memory, "memory effect"))
  else
    let g ← setGoal g ty
    return #[{ goal := g, kind := fallback.1, label := fallback.2 }]
where
  fresh (names : IO.Ref Nat) : MetaM Nat := do
    let i := (← names.get) + 1
    names.set i
    return i
  name (base : String) (i : Nat) : Name := Name.mkSimple s!"{base}{i}"
  retFallback (value : Expr) : MetaM (Kind × String) := do
    let k ← valueKind value
    return (k, if k == .error then "error return" else "functional result")
  splitResult (fuel : Nat) (names : IO.Ref Nat) (g : MVarId) (prog : Expr) :
      MetaM (Array Obligation) := do
    let fuel + 1 := fuel | throwError "vc_gen: VC too large"
    let some c := prog.getAppFn.constName? | leaf g
    match c with
    | ``ResultProgram.ret =>
      let [n] ← applyNamed g ``ResultProgram.ret_intro | leaf g
      split fuel names n (← retFallback prog.appArg!)
    | ``ResultProgram.add =>
      let [o, n] ← applyNamed g ``ResultProgram.add_intro | leaf g
      return #[{ goal := o, kind := .safety, label := "unsigned addition does not overflow" }] ++
        (← split fuel names n (.result, "functional result"))
    | ``ResultProgram.widen =>
      let [o, n] ← applyNamed g ``ResultProgram.widen_intro | leaf g
      return #[{ goal := o, kind := .safety, label := "unsigned cast widens" }] ++
        (← split fuel names n (.result, "functional result"))
    | ``ResultProgram.guard =>
      let [o, n] ← applyNamed g ``ResultProgram.guard_intro | leaf g
      return #[{ goal := o, kind := .safety, label := "safety guard holds" }] ++
        (← split fuel names n (.result, "functional result"))
    | ``ResultProgram.panic =>
      let [o] ← applyNamed g ``ResultProgram.panic_intro | leaf g
      return #[{ goal := o, kind := .safety, label := "panic/throw is unreachable" }]
    | ``ResultProgram.call =>
      let label := stringLit (prog.getArg! 1)
      let [p, n] ← applyNamed g ``ResultProgram.call_intro | leaf g
      let i ← fresh names
      let (_, n) ← n.introN 2 [name "value" i, name "summary" i]
      return #[{ goal := p, kind := labelKind label, label := callLabel label }] ++
        (← split fuel names n (.result, "functional result"))
    | ``ResultProgram.bind =>
      let [n] ← applyNamed g ``ResultProgram.bind_intro | leaf g
      split fuel names n (.result, "functional result")
    | ``ResultProgram.branch =>
      let [y, n] ← applyNamed g ``ResultProgram.branch_intro | leaf g
      let i ← fresh names
      let (_, y) ← y.intro (name "branch" i)
      let (_, n) ← n.intro (name "branch" i)
      return (← split fuel names y (.result, "functional result")) ++ (← split fuel names n (.result, "functional result"))
    | _ => leaf g
  splitMem (fuel : Nat) (names : IO.Ref Nat) (g : MVarId) (prog heap : Expr) :
      MetaM (Array Obligation) := do
    let fuel + 1 := fuel | throwError "vc_gen: VC too large"
    let some c := prog.getAppFn.constName? | leaf g
    match c with
    | ``MemProgram.ret =>
      let [n] ← applyNamed g ``MemProgram.ret_intro | leaf g
      let k ← valueKind prog.appArg!
      split fuel names n (if k == .error then (.error, "error return") else (.memory, "postcondition"))
    | ``MemProgram.load =>
      let T := prog.getArg! 0
      let pattern ← mkAppM ``Zig.pts #[prog.getArg! 2, prog.getArg! 3, ← mkFreshExprMVar T, heap]
      if let some owned ← findHyp pattern then
        let [s, n] ← applyWith g ``MemProgram.load_intro owned | return ← leaf g
        return #[{ goal := s, kind := .memory, label := "loaded type has positive size" }] ++
          (← split fuel names n (.memory, "postcondition"))
      let [s, o] ← applyNamed g ``MemProgram.load_intro_any | leaf g
      return #[{ goal := s, kind := .memory, label := "loaded type has positive size" },
        { goal := o, kind := .memory,
          label := "owned cell for the load (no hypothesis names it), with its continuation" }]
    | ``MemProgram.store =>
      let [s, o, n] ← applyNamed g ``MemProgram.store_intro | leaf g
      let T := prog.getArg! 0
      let old ← mkFreshExprMVar T
      let pattern ← mkAppM ``Zig.pts #[prog.getArg! 3, prog.getArg! 4, old, heap]
      let mut owned : Obligation :=
        { goal := o, kind := .memory, label := "owned cell for the store" }
      if let some p ← findHyp pattern then
        let pred := (← whnfR (← instantiateMVars (← o.getType))).appArg!
        o.assign (← mkAppOptM ``Exists.intro #[none, some pred, some (← instantiateMVars old), some p])
        owned := { owned with closedBy := some "hypothesis" }
      let i ← fresh names
      let (_, n) ← n.introN 2 [name "heap" i, name "stored" i]
      return #[{ goal := s, kind := .memory, label := "stored type has positive size" }, owned] ++
        (← split fuel names n (.memory, "postcondition"))
    | ``MemProgram.read | ``MemProgram.write =>
      let rule := if c == ``MemProgram.read then ``MemProgram.read_intro
        else ``MemProgram.write_intro
      let [s, o, n] ← applyNamed g rule | leaf g
      let i ← fresh names
      let n ← if c == ``MemProgram.write then
          pure (← n.introN 2 [name "heap" i, name "stored" i]).2
        else pure n
      return #[{ goal := s, kind := .memory, label := "accessed type has positive size" },
        { goal := o, kind := .memory, label := "owned annotated cell" }] ++
        (← split fuel names n (.memory, "postcondition"))
    | ``MemProgram.lift =>
      let [n] ← applyNamed g ``MemProgram.lift_intro | leaf g
      split fuel names n (.memory, "postcondition")
    | ``MemProgram.call =>
      let label := stringLit (prog.getArg! 1)
      let [p, n] ← applyNamed g ``MemProgram.call_intro | leaf g
      let i ← fresh names
      let (_, n) ← n.introN 3 [name "value" i, name "heap" i, name "summary" i]
      return #[{ goal := p, kind := labelKind label, label := callLabel label }] ++
        (← split fuel names n (.memory, "postcondition"))
    | ``MemProgram.bind =>
      let [n] ← applyNamed g ``MemProgram.bind_intro | leaf g
      split fuel names n (.memory, "postcondition")
    | ``MemProgram.branch =>
      let [y, n] ← applyNamed g ``MemProgram.branch_intro | leaf g
      let i ← fresh names
      let (_, y) ← y.intro (name "branch" i)
      let (_, n) ← n.intro (name "branch" i)
      return (← split fuel names y (.memory, "postcondition")) ++ (← split fuel names n (.memory, "postcondition"))
    | _ => leaf g
  leaf (g : MVarId) : MetaM (Array Obligation) :=
    return #[{ goal := g, kind := .safety, label := "unsplit generated condition" }]

/-- The extracted program and source equality for the action `app`, preferring `vc_f`. -/
def programFor (app : Expr) : MetaM (Expr × Expr × Name) := do
  let some f := app.getAppFn.constName?
    | throwError "vc_gen: the action is not an application of a generated function{indentExpr app}"
  let (vcName, srcName, _) := vcNames f
  let lvls := app.getAppFn.constLevels!
  if (← getEnv).contains srcName then
    return (mkAppN (mkConst vcName lvls) app.getAppArgs,
      mkAppN (mkConst srcName lvls) app.getAppArgs, f)
  match ← extractApp f app with
  | .ok program source _ => return (program, source, f)
  | .loops requests => throwError m!"{loopsMessage f requests}\n{reportLine (loopsJson f requests)}"
  | .refused reason => throwError m!"vc extraction for `{f}` refused: {reason}"

def runVcGen (report : Bool) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let before := (← getLCtx).getFVarIds
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let (f, gens) ← if ty.isAppOfArity ``Exists 2 then do
      let lam := ty.getArg! 1
      unless lam.isLambda && lam.bindingBody!.isAppOfArity ``And 2 do
        throwError "vc_gen: expected `∃ v, f xs = pure v ∧ post v`"
      let eq := lam.bindingBody!.getArg! 0
      unless eq.isAppOfArity ``Eq 3 do throwError "vc_gen: expected `∃ v, f xs = pure v ∧ post v`"
      let (_, src, f) ← programFor (eq.getArg! 1)
      pure (f, ← applyWith g ``result_intro src)
    else if ty.isAppOfArity ``Zig.Triple 4 then do
      let (_, src, f) ← programFor (ty.getArg! 2)
      let [o] ← applyWith g ``triple_intro src
        | throwError "vc_gen: triple_intro"
      let (_, o) ← o.introN 2 [`heap, `pre]
      pure (f, [o])
    else throwError "vc_gen: expected `∃ v, f xs = pure v ∧ post v` or `Triple pre (f xs) post`"
  let mut obls := #[]
  let names ← IO.mkRef 0
  for gen in gens do
    obls := obls ++ (← split fuelLimit names gen (.result, "functional result"))
  -- Number the open obligations by kind, so `case safety_1 => …` addresses one.
  let mut counts : Std.HashMap String Nat := {}
  let mut open_ := #[]
  let mut lines := #[]
  let mut items := #[]
  for o in obls do
    let k := o.kind.name
    let i := counts.getD k 0 + 1
    counts := counts.insert k i
    let tag := Name.mkSimple s!"{k}_{i}"
    if o.closedBy.isNone then
      o.goal.setTag tag
      open_ := open_.push o.goal
    let (goalFmt, given) ← o.goal.withContext do
      let t ← instantiateMVars (← o.goal.getType)
      let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
        if before.contains d.fvarId || d.isImplementationDetail then return acc
        return acc.push s!"{d.userName} : {← ppExpr (← instantiateMVars d.type)}"
      return (toString (← ppExpr t), hyps)
    let status := match o.closedBy with | some by_ => s!" (closed by {by_})" | none => ""
    let givenText := String.join (given.toList.map fun h => s!"\n    {h}")
    lines := lines.push m!"\n  [{tag}] {k}: {o.label}{status}{givenText}\n    ⊢ {goalFmt}"
    items := items.push (Json.mkObj [("case", toJson tag.toString), ("kind", toJson k),
      ("label", toJson o.label), ("goal", toJson goalFmt), ("given", toJson given),
      ("closed_by", match o.closedBy with | some by_ => toJson by_ | none => Json.null)])
  replaceMainGoal open_.toList
  if report then
    let json := Json.mkObj [("function", toJson f.toString), ("status", "obligations"),
      ("obligations", Json.arr items)]
    logInfo (m!"vc_gen obligations for `{f}` ({open_.size} open of {obls.size}):" ++
      MessageData.joinSep lines.toList m!"" ++ m!"\n{reportLine json}")

end Zig.VC.Extract

/-- Replace a contract goal about a loop-free generated function by its tagged VC obligations. -/
elab "vc_gen" : tactic => Zig.VC.Extract.runVcGen false

/-- `vc_gen`, also logging the obligation report. -/
elab "vc_gen?" : tactic => Zig.VC.Extract.runVcGen true
