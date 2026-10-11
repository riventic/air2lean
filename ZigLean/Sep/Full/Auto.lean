import ZigLean.Sep.Full.AutoRules

/-!
# `fsym`: symbolic execution of generated code in the full-state logic

`fsym` proves a goal `FTotalTriple P c Q`, `FTriple P c Q` or `L.T P c Q` (any `FLogic`) by walking
the generated program `c` (`docs/proof-automation.md`):

* **Preconditions** are kept as a flat list of atoms. Definitions that build assertions from
  `⋆`, `⟪φ⟫` and `FAssn.ex` (an invariant, a token, `pshare`, a projection of an `FAllocInv`) are
  unfolded; existentials and facts move into the context (conjunctions are split, equations of a
  variable are substituted, user definitions of facts are unfolded). Atoms are what is left: the
  library's assertions (`up`, `known`, `bshare`, …), `@[fsym_atom]`s and opaque terms.
* **Programs** are normalized with `fsym_norm` (the `MM`/`StateT` layer of generated code, binds,
  trivial results). A call of a generated function (or of a pure generated helper under
  `StateT.lift`) is inlined; a projection of a vtable is reduced.
* **Commands** are executed by the first `@[fsym]` rule (or rule given to `fsym [...]`) whose
  command unifies. A rule about a part of the precondition is framed (the part is found by
  unification, the rest is the frame, the reordering is proved by `ac_rfl`); a rule about any
  precondition takes the whole. Its hypotheses are side goals: blocks (`p.block = some b`, from
  the context), providers (`AddrOf`, `Reaches`, from the atoms, with backtracking over the
  candidates) and arithmetic (`fsym_arith` + `omega`); an arithmetic goal that is not proved is
  left to the caller.
* **Branches**: an `if` whose condition (or its negation) is proved takes one side; otherwise
  both are walked with the condition as a fact. A `match`/`Option.elim` on a variable is split by
  cases. A `throw` must be unreachable: the context is refuted, else the goal is left.
* **Returns** `pure v`: the goal becomes the frame-preserving update `EUpd P (Q v)`, which
  `fsym` closes when `Q v` is the precondition up to its existentials (found by unification),
  its facts (by the arithmetic solver), `junk` (which absorbs `up` atoms) and AC of `⋆`;
  otherwise the update goal is left to the caller.

Every step elaborates to applications of `ZigLean/Sep/Full/AutoRules.lean` and the library's
rules: the kernel checks the result.
-/

namespace Zig.Full.Auto

open Lean Meta Elab Tactic

initialize registerTraceClass `fsym

/-! ## Expressions -/

def sepN : Name := ``Zig.Full.FAssn.sep
def empN : Name := ``Zig.Full.FAssn.emp
def liftN : Name := ``Zig.Full.FAssn.lift
def exN : Name := ``Zig.Full.FAssn.ex

/-- The atoms of a `⋆`-tree (`emp` dropped). -/
partial def atoms (e : Expr) : Array Expr :=
  go [e] #[]
where
  go : List Expr → Array Expr → Array Expr
    | [], acc => acc
    | e :: rest, acc =>
      let e := e.consumeMData.headBeta
      if e.isAppOfArity sepN 2 then go (e.appFn!.appArg! :: e.appArg! :: rest) acc
      else if e.isConstOf empN then go rest acc
      else go rest (acc.push e)

def mkSep (a b : Expr) : Expr := mkApp2 (mkConst sepN) a b

def sepOf (xs : Array Expr) : Expr :=
  if xs.isEmpty then mkConst empN
  else xs.pop.foldr mkSep xs.back!

/-- A constant of the library or of Lean (not generated code, not the user's). -/
def isLibrary (c : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? c with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    return [`ZigLean, `Init, `Std, `Lean].contains m.getRoot
  | none => return false

/-- One unfolding step of a term: a projection of a structure value, or a definition. -/
def unfold1 (e : Expr) : MetaM (Option Expr) := do
  let e := e.headBeta
  let .const c _ := e.getAppFn | return none
  if let some info ← getProjectionFnInfo? c then
    let args := e.getAppArgs
    let some s := args[info.numParams]? | return none
    let s ← whnfD s
    let some ctor := s.getAppFn.constName? | return none
    unless ctor == info.ctorName do return none
    let some fld := s.getAppArgs[info.numParams + info.i]? | return none
    return some (mkAppN fld args[info.numParams + 1:]).headBeta
  if c == sepN || c == empN || c == liftN || c == exN then return none
  if fsymAtomAttr.hasTag (← getEnv) c then return none
  let some e' ← unfoldDefinition? e | return none
  return some e'.headBeta

/-- Unfold an assertion atom while it unfolds to a combination of assertions (not to a raw
predicate `fun r => …`). -/
partial def unfoldAtom (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity sepN 2 then
    return mkSep (← unfoldAtom e.appFn!.appArg!) (← unfoldAtom e.appArg!)
  if e.isAppOf liftN || e.isAppOf exN || e.isConstOf empN then return e
  match ← unfold1 e with
  | some e' => if e'.consumeMData.isLambda then return e else unfoldAtom e'
  | none => return e

/-- A goal `L.T P c Q`: `(L, α, P, c, Q)`; `FTotalTriple`/`FTriple` goals are restated. -/
def view (g : MVarId) : MetaM (MVarId × Expr × Expr × Expr × Expr × Expr) := do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  if t.isAppOfArity ``FLogic.T 5 then
    let a := t.getAppArgs
    return (g, a[0]!, a[1]!, a[2]!, a[3]!.consumeMData, a[4]!)
  for (k, L) in [(``FTotalTriple, ``FLogic.total), (``FTriple, ``FLogic.partial)] do
    if t.isAppOfArity k 4 then
      let a := t.getAppArgs
      let L := mkConst L
      let g' ← g.replaceTargetDefEq (mkAppN (mkConst ``FLogic.T) #[L, a[0]!, a[1]!, a[2]!, a[3]!])
      return (g', L, a[0]!, a[1]!, a[2]!.consumeMData, a[3]!)
  throwError "fsym: expected an FTotalTriple, FTriple or FLogic.T goal{indentExpr t}"

def mkT (L α P c Q : Expr) : Expr := mkAppN (mkConst ``FLogic.T) #[L, α, P, c, Q]

/-- The head of a command or an atom, through `StateT.lift` and `up`: a cheap filter before
unification (which may unfold definitions). -/
partial def headKey (e : Expr) : Name :=
  let e := e.consumeMData
  if e.isAppOfArity ``StateT.lift 5 || e.isAppOfArity ``Zig.Full.FAssn.up 1 then
    `lift ++ headKey e.appArg!
  else match e.getAppFn with
    | .const c _ => c
    | .fvar _ => `fvar
    | _ => .anonymous

/-- Unify when the heads agree. -/
def unifyKeyed (a b : Expr) : MetaM Bool := do
  let ka := headKey a
  let kb := headKey b
  if ka != kb && ka != .anonymous && kb != .anonymous then return false
  isDefEq a b

/-! ## Solvers -/

/-- The arithmetic solver for side goals. -/
syntax "fsym_arith" : tactic
macro_rules
  | `(tactic| fsym_arith) => `(tactic| first
      | assumption
      | omega
      | (simp only [fsym_arith] at *; omega)
      | bv_omega
      | (simp only [fsym_arith, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *; omega))

/-- Run a tactic on a goal; `true` if it closed the goal (else the state is restored). -/
def closeWith (g : MVarId) (tac : Syntax) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← evalTacticAt tac g
    if gs.isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

def arith (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  if !t.hasFVar && !t.hasMVar then
    if ← closeWith g (← `(tactic| decide)) then return true
  closeWith g (← `(tactic| fsym_arith))

/-- Prove `x = y` of assertions by AC of `⋆`. -/
def acEq (x y : Expr) : TacticM Expr := do
  let ty ← mkEq x y
  let m ← mkFreshExprMVar ty
  if x == y then return ← mkEqRefl x
  unless ← closeWith m.mvarId! (← `(tactic| ac_rfl)) do
    throwError "fsym: cannot reorder{indentExpr x}\nto{indentExpr y}"
  instantiateMVars m

/-- Prove `t` (a `_.block = _` goal) from the context, possibly assigning a block variable. -/
def solveBlock (t : Expr) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  let hyps := lctx.foldl (fun acc d => if d.isImplementationDetail then acc else acc.push d) #[]
  for h in hyps do
    let s ← saveState
    if ← isDefEq t h.type then return some h.toExpr
    s.restore
  for h1 in hyps do
    let ty1 ← instantiateMVars h1.type
    let some (_, _, r1) := ty1.eq? | continue
    unless r1.isAppOf ``Zig.Ptr.block do continue
    for h2 in hyps do
      let ty2 ← instantiateMVars h2.type
      let some (_, l2, _) := ty2.eq? | continue
      unless ← withReducible (isDefEq r1 l2) do continue
      let pf ← mkEqTrans h1.toExpr h2.toExpr
      let s ← saveState
      if ← isDefEq t (← inferType pf) then return some pf
      s.restore
  return none

/-- The block of a pointer, from the context (`p.block = some ?b`). -/
def blockOf (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let b ← mkFreshExprMVar (mkConst ``Zig.BlockId)
  let t ← mkEq (← mkAppM ``Zig.Ptr.block #[p]) (← mkAppM ``Option.some #[b])
  let some pf ← solveBlock t | return none
  return some (← instantiateMVars b, pf)

/-- Candidates for a provider goal `AddrOf b A P` or `Reaches b K P`: proofs that assign `A`/`K`. -/
def providerCands (t : Expr) : TacticM (Array (TacticM Expr)) := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  let (isAddr, b, P) := if t.isAppOfArity ``AddrOf 3 then (true, args[0]!, args[2]!)
    else (false, args[0]!, args[2]!)
  let ats := atoms P
  let mut out := #[]
  for i in [0:ats.size] do
    let a := ats[i]!
    let rest := sepOf (ats.eraseIdx! i)
    let close (h : Expr) : TacticM Expr := do
      let e ← acEq P (mkSep a rest)
      let lem := if isAddr then ``AddrOf.of_atom else ``Reaches.of_atom
      let pf ← mkAppM lem #[h, e]
      unless ← isDefEq t (← inferType pf) do throwError "fsym: provider mismatch"
      return pf
    if isAddr then
      if a.isAppOfArity ``Zig.Full.known 2 then
        out := out.push do
          unless ← isDefEq a.appFn!.appArg! b do throwError "block"
          close (← mkAppOptM ``AddrOf.known #[a.appFn!.appArg!, a.appArg!])
      else if a.isAppOfArity ``Zig.Full.FAssn.up 1 && a.appArg!.isAppOfArity ``Zig.regionIn 6 then
        let ra := a.appArg!.getAppArgs
        out := out.push do
          let some (b', hb) ← blockOf ra[0]! | throwError "block"
          unless ← isDefEq b' b do throwError "block"
          let hpos ← mkFreshExprMVar (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Array.size #[ra[5]!]])
          unless ← arith hpos.mvarId! do throwError "size"
          close (← mkAppM ``AddrOf.region #[hb, hpos])
    else
      if a.isAppOfArity ``Zig.Full.bshare 4 then
        let ba := a.getAppArgs
        out := out.push do
          unless ← isDefEq ba[0]! b do throwError "block"
          unless ← isDefEq ba[3]! (← mkAppOptM ``Option.none #[none]) do throwError "tag"
          close (← mkAppOptM ``Reaches.share #[ba[0]!, ba[2]!, ba[1]!])
      else if a.isAppOfArity ``Zig.Full.FAssn.up 1 && a.appArg!.isAppOfArity ``Zig.pts 5 then
        let pa := a.appArg!.getAppArgs
        out := out.push do
          let some (b', hb) ← blockOf pa[2]! | throwError "block"
          unless ← isDefEq b' b do throwError "block"
          let hn ← mkFreshExprMVar (← mkAppM ``LT.lt #[mkNatLit 0,
            ← mkAppOptM ``Zig.Enc.size #[pa[0]!, pa[1]!]])
          unless ← arith hn.mvarId! do throwError "size"
          close (← mkAppOptM ``Reaches.pts #[none, pa[0]!, pa[1]!, pa[2]!, pa[3]!, pa[4]!, hb, hn])
      else if a.isAppOfArity ``Zig.Full.FAssn.up 1 && a.appArg!.isAppOfArity ``Zig.regionIn 6 then
        let ra := a.appArg!.getAppArgs
        out := out.push do
          let some (b', hb) ← blockOf ra[0]! | throwError "block"
          unless ← isDefEq b' b do throwError "block"
          let hpos ← mkFreshExprMVar (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Array.size #[ra[5]!]])
          unless ← arith hpos.mvarId! do throwError "size"
          close (← mkAppM ``Reaches.region #[hb, hpos])
  return out

/-- Solve the side goals of a rule, in order; providers backtrack over their candidates.
Returns the arithmetic goals left unproved, or `none` if a block or provider goal fails. -/
partial def solveSides (gs : List MVarId) : TacticM (Option (List MVarId)) := do
  match gs with
  | [] => return some []
  | g :: rest =>
    if ← g.isAssigned then return ← solveSides rest
    let t ← instantiateMVars (← g.getType)
    if t.isAppOfArity ``AddrOf 3 || t.isAppOfArity ``Reaches 3 then
      let mut first? : Option (Tactic.SavedState × List MVarId) := none
      for cand in ← providerCands t do
        let s ← saveState
        try
          let pf ← cand
          g.assign pf
          match ← solveSides rest with
          | some [] => return some []
          | some left => if first?.isNone then first? := some (← saveState, left)
          | none => pure ()
        catch _ => pure ()
        s.restore
      match first? with
      | some (s, left) => s.restore; return some left
      | none => return none
    else if (t.eq?.map fun (_, l, _) => l.isAppOf ``Zig.Ptr.block).getD false then
      let some pf ← g.withContext (solveBlock t) | return none
      g.assign pf
      solveSides rest
    else
      let ok ← arith g
      let some left ← solveSides rest | return none
      return some (if ok then left else g :: left)

/-! ## Preconditions -/

/-- Split, unfold and substitute a fact in the context. -/
partial def destruct (g : MVarId) (h : FVarId) : TacticM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← h.getType))
  if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
    let isAnd := ty.isAppOfArity ``And 2
    let gs ← g.cases h
    let some sg := gs[0]? | return g
    let fs := sg.fields
    let mut g := sg.mvarId
    if isAnd then
      let f1 := fs[1]!.fvarId!
      g ← destruct g fs[0]!.fvarId!
      if (← g.withContext f1.findDecl?).isSome then g ← destruct g f1
      return g
    return ← destruct g fs[1]!.fvarId!
  if ty.isConstOf ``True then return ← g.clear h
  if let some (_, l, r) := ty.eq? then
    if l.isFVar || r.isFVar then
      if let some g' ← observing? (subst g h) then return g'
    return g
  -- a user definition of a fact
  if let .const c _ := ty.getAppFn then
    unless ← isLibrary c do
      if let some ty' ← unfold1 ty then
        let g' ← g.replaceLocalDeclDefEq h ty'
        let ty'' ← whnfR ty'
        if ty''.isAppOfArity ``And 2 || ty''.isAppOfArity ``Exists 2 then return ← destruct g' h
        return g'
  return g

/-- Normalize the precondition: unfold, flatten, move facts and existentials into the context. -/
partial def normPre (g : MVarId) (fuel : Nat := 64) : TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  let (g, L, α, P, c, Q) ← view g
  let rec leaves (e : Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    if e.isAppOfArity sepN 2 then return mkSep (← leaves e.appFn!.appArg!) (← leaves e.appArg!)
    unfoldAtom e
  let Pu ← leaves P
  let ats := atoms Pu
  let isFact (a : Expr) := a.isAppOfArity liftN 1 || a.isAppOfArity exN 2
  let facts := ats.filter isFact
  let others := ats.filter (! isFact ·)
  let P2 := if facts.isEmpty then sepOf others else mkSep facts[0]! (sepOf (facts.eraseIdx! 0 ++ others))
  if P2 == P then
    if facts.isEmpty then return g
  -- `P` to `Pu` by unfolding (definitional), `Pu` to `P2` by AC
  let g ← if P2 == P then pure g else do
    let e ← acEq Pu P2
    let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α P2 c Q)
    let pf ← mkAppOptM ``pre_eq #[L, none, P, P2, Q, c, ← mkExpectedTypeHint e (← mkEq P P2), g2]
    g.assign pf
    pure g2.mvarId!
  if facts.isEmpty then return g
  let a := facts[0]!
  if a.isAppOfArity liftN 1 then
    let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.lift_sep _ fun h => ?_)) g
      | throwError "fsym: lift"
    let lctx ← g'.withContext getLCtx
    let g' ← match lctx.lastDecl with
      | some d => destruct g' d.fvarId
      | none => pure g'
    normPre g' (fuel - 1)
  else
    let n := match a.appArg!.consumeMData with | .lam n .. => n | _ => `x
    let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.ex_sep _ fun x => ?_)) g
      | throwError "fsym: ex"
    let lctx ← g'.withContext getLCtx
    let g' ← match lctx.lastDecl with
      | some d => g'.rename d.fvarId n
      | none => pure g'
    normPre g' (fuel - 1)

/-! ## Programs -/

/-- Simplify the program with `fsym_norm` and the caller's lemmas. -/
def simpProg (g : MVarId) (extra : Array Syntax) : TacticM MVarId := g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let some ext ← getSimpExtension? `fsym_norm | throwError "fsym: no fsym_norm"
  let mut thms ← ext.getTheorems
  for x in extra do
    if let some n := (if x.isIdent then some x.getId else none) then
      if let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo (mkIdent n) catch _ => pure none) then
        thms ← thms.addConst n
        continue
    let e ← Term.elabTerm x none
    thms ← thms.add (.stx (← mkFreshId) x) #[] e
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp c ctx (simprocs := #[← Simp.getSimprocs])
  if r.expr == c then return g
  let newT := mkT L α P r.expr Q
  match r.proof? with
  | none => g.replaceTargetDefEq newT
  | some pf =>
    let f ← withLocalDeclD `c (← inferType c) fun x => mkLambdaFVars #[x] (mkT L α P x Q)
    g.replaceTargetEq newT (← mkCongrArg f pf)

/-- Inline a command: a vtable projection, a generated function, a pure generated helper. -/
partial def unfoldCmd (x : Expr) : MetaM (Option Expr) := do
  let x := x.consumeMData.headBeta
  if x.isAppOfArity ``StateT.lift 5 then
    let y := x.appArg!
    let some y' ← unfoldCmd y | return none
    return some (mkApp x.appFn! y')
  let .const c _ := x.getAppFn | return none
  if (← getProjectionFnInfo? c).isSome then return ← unfold1 x
  if ← isLibrary c then return none
  unfold1 x

def isThrow (c : Expr) : Bool :=
  c.isAppOf ``MonadExcept.throw || c.isAppOf ``MonadExceptOf.throw || c.isAppOf ``throwThe

/-! ## Rules -/

/-- Try a rule on the command `x` of `x >>= f`. Returns the continuation goal and side goals. -/
def tryRule (g : MVarId) (rule : Expr) (x f : Expr) : TacticM (Option (MVarId × List MVarId)) :=
  g.withContext do
  let s ← saveState
  try
    let (_, L, α, P, _, Q) ← view g
    let (args, _, concl) ← forallMetaTelescopeReducing (← inferType rule)
    let concl ← whnfR concl
    unless concl.isAppOfArity ``FTotalTriple 4 do s.restore; return none
    let ca := concl.getAppArgs
    let (β, P₀, cmd, Q₀) := (ca[0]!, ca[1]!, ca[2]!, ca[3]!)
    unless ← unifyKeyed cmd x do s.restore; return none
    let P₀i ← instantiateMVars P₀
    let whole := P₀i.isMVar
    let mut R := mkConst empN
    if whole then
      unless ← isDefEq P₀ P do s.restore; return none
    else
      -- frame inference: each atom of the rule's precondition is an atom of `P`
      let ats := atoms P
      let mut used := Array.replicate ats.size false
      for a in atoms P₀i do
        let mut found := false
        for i in [0:ats.size] do
          unless used[i]! do
            let s' ← saveState
            if ← unifyKeyed a ats[i]! then
              used := used.set! i true; found := true; break
            s'.restore
        unless found do s.restore; return none
      let mut rest := #[]
      for i in [0:ats.size] do
        unless used[i]! do rest := rest.push ats[i]!
      R := sepOf rest
    let sides := (← args.filterM fun a => do
      if ← a.mvarId!.isAssigned then return false
      isProp (← inferType a)).toList.map (·.mvarId!)
    let some left ← solveSides sides | s.restore; return none
    -- every argument must be determined
    for a in args do
      let a ← instantiateMVars a
      if a.hasExprMVar && !(left.any fun m => a == .mvar m) then
        unless ← isProp (← inferType a) do
          trace[fsym] "rule {rule}: undetermined {a}"
          s.restore; return none
    let r ← instantiateMVars (mkAppN rule args)
    let Q₀ ← instantiateMVars Q₀
    let P₀ ← instantiateMVars P₀
    let kTy ← withLocalDeclD `v β fun v => do
      let pre := if whole then mkApp Q₀ v |>.headBeta else mkSep (mkApp Q₀ v |>.headBeta) R
      mkForallFVars #[v] (mkT L α pre (mkApp f v).headBeta Q)
    let k ← mkFreshExprSyntheticOpaqueMVar kTy
    if whole then
      g.assign (← mkAppOptM ``stepAll #[L, β, α, P, Q, x, f, Q₀, r, k])
    else
      let e ← acEq P (mkSep P₀ R)
      let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α (mkSep P₀ R) (← mkAppM ``Bind.bind #[x, f]) Q)
      g.assign (← mkAppOptM ``pre_eq #[L, α, P, mkSep P₀ R, Q, none, e, g2])
      g2.mvarId!.assign (← mkAppOptM ``step #[L, β, α, P₀, R, Q, x, f, Q₀, r, k])
    let n := match f.consumeMData with | .lam n .. => n | _ => `v
    let (_, k') ← k.mvarId!.intro n
    return some (k', left)
  catch ex =>
    trace[fsym] "rule {rule} failed: {ex.toMessageData}"
    s.restore; return none

/-- The registered rules and the caller's. -/
def rules (user : Array Expr) : MetaM (Array Expr) := do
  let reg := fsymRuleExt.getState (← getEnv)
  let mut out := user
  for n in reg.reverse do
    out := out.push (← mkConstWithFreshMVarLevels n)
  return out

/-! ## Returns -/

/-- `Q` with its existentials opened by fresh witnesses: `(Qi, pf : ∀ r, Qi r → Q r)`. -/
partial def instQ (e : Expr) (fuel : Nat := 64) : MetaM (Expr × Expr) := do
  let e := e.consumeMData.headBeta
  let refl := fun e => mkAppOptM ``imp_refl #[e]
  if fuel == 0 then return (e, ← refl e)
  if e.isAppOfArity sepN 2 then
    let (a, pa) ← instQ e.appFn!.appArg! (fuel - 1)
    let (b, pb) ← instQ e.appArg! (fuel - 1)
    return (mkSep a b, ← mkAppM ``imp_sep #[pa, pb])
  if e.isAppOfArity exN 2 then
    let F := e.appArg!
    let w ← mkFreshExprMVar (← whnfD (← inferType F)).bindingDomain!
    let (b, pb) ← instQ (mkApp F w).headBeta (fuel - 1)
    return (b, ← mkAppOptM ``imp_ex #[b, none, F, w, pb])
  if e.isAppOfArity liftN 1 then return (e, ← refl e)
  let e' ← unfoldAtom e
  if e' == e then return (e, ← refl e)
  let (b, pb) ← instQ e' (fuel - 1)
  -- `e'` is `e` unfolded: the proof's type is definitionally the expected one
  return (b, ← mkExpectedTypeHint pb (← mkArrow' b e))
where
  mkArrow' (x y : Expr) : MetaM Expr := do
    withLocalDeclD `r (mkConst ``Zig.Full.Res) fun r => do
      mkForallFVars #[r] (← mkArrow (mkApp x r) (mkApp y r))

/-- Close `EUpd P Q` when `Q` is `P` up to existentials (unification), facts (arithmetic),
`junk` (absorbing `up` atoms) and AC of `⋆`. Unproved facts are left as goals. -/
def closeEntail (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let s ← saveState
  try
    let t ← instantiateMVars (← g.getType)
    let P := t.appFn!.appArg!
    let Q := t.appArg!
    let (Qi, pQ) ← instQ Q
    let pats := atoms P
    let qats := atoms Qi
    let facts := qats.filter (·.isAppOfArity liftN 1)
    let spat := qats.filter (! ·.isAppOfArity liftN 1)
    let junkQ := spat.any (·.isConstOf ``Zig.Full.Auto.junk)
    let spat := spat.filter (! ·.isConstOf ``Zig.Full.Auto.junk)
    let mut used := Array.replicate pats.size false
    let mut M := #[]
    for a in spat do
      let mut found := false
      for i in [0:pats.size] do
        unless used[i]! do
          let s' ← saveState
          if ← unifyKeyed a pats[i]! then
            used := used.set! i true; found := true; M := M.push pats[i]!; break
          s'.restore
      unless found do throwError "fsym: the precondition has no atom for{indentExpr a}"
    let mut L := #[]
    for i in [0:pats.size] do
      unless used[i]! do L := L.push pats[i]!
    unless L.isEmpty || junkQ do throwError "fsym: atoms left over{indentExpr (sepOf L)}"
    -- core : ∀ r, P r → S r, with S the spatial part
    let (S, core) ← if junkQ then do
        let J := mkConst ``Zig.Full.Auto.junk
        -- leftover to junk
        let rec toJunk (xs : List Expr) : MetaM Expr := do
          match xs with
          | [] => mkAppM ``imp_junk_emp #[]
          | [x] =>
            if x.isConstOf ``Zig.Full.Auto.junk then mkAppOptM ``imp_refl #[J]
            else if x.isAppOfArity ``Zig.Full.FAssn.up 1 then mkAppOptM ``imp_junk_one #[x.appArg!]
            else throwError "fsym: cannot drop{indentExpr x}"
          | x :: rest =>
            let pr ← toJunk rest
            if x.isConstOf ``Zig.Full.Auto.junk then mkAppM ``imp_junk_junk #[pr]
            else if x.isAppOfArity ``Zig.Full.FAssn.up 1 then
              mkAppOptM ``imp_junk_up #[sepOf rest.toArray, x.appArg!, pr]
            else throwError "fsym: cannot drop{indentExpr x}"
        let pj ← toJunk L.toList
        let Lx := sepOf L
        if M.isEmpty then
          let e ← acEq P Lx
          pure (J, ← mkAppM ``imp_trans #[← mkAppM ``imp_eq #[e], pj])
        else
          let Pm := sepOf (M.push Lx)
          let S := sepOf (M.push J)
          let e ← acEq P Pm
          -- identity on `M`, `pj` on the last
          let rec frame (ms : List Expr) : MetaM Expr := do
            match ms with
            | [] => pure pj
            | m :: rest => mkAppM ``imp_sep #[← mkAppOptM ``imp_refl #[m], ← frame rest]
          pure (S, ← mkAppM ``imp_trans #[← mkAppM ``imp_eq #[e], ← frame M.toList])
      else do
        let S := sepOf M
        let e ← acEq P S
        pure (S, ← mkAppM ``imp_eq #[e])
    -- facts
    let mut left := []
    let mut body := core
    let mut T := S
    for f in facts.reverse do
      let φ ← instantiateMVars f.appArg!
      let hφ ← mkFreshExprMVar φ
      unless ← arith hφ.mvarId! do left := hφ.mvarId! :: left
      body ← mkAppM ``imp_lift #[hφ, body]
      T := mkSep f T
    -- `T` is `Qi` up to AC
    let T' ← instantiateMVars T
    let Qi ← instantiateMVars Qi
    let eT ← acEq T' Qi
    let pf ← mkAppM ``imp_trans #[← mkAppM ``imp_trans #[body, ← mkAppM ``imp_eq #[eT]], pQ]
    let pf ← instantiateMVars pf
    if pf.hasExprMVar then
      let ms ← getMVars pf
      for m in ms do
        unless left.contains m do
          unless ← isProp (← m.getType) do throwError "fsym: undetermined witness ?{m.name}"
    g.assign (← mkAppM ``eupd_of_imp #[pf])
    return left
  catch ex =>
    trace[fsym] "entailment: {ex.toMessageData}"
    s.restore
    return [g]

/-! ## The walk -/

partial def walk (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  trace[fsym] "walk {fuel}"
  let g ← normPre g
  trace[fsym] "pre done {← g.getType}"
  let g ← simpProg g extra
  trace[fsym] "prog done"
  g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let c := c.consumeMData
  -- return
  if c.isAppOfArity ``Pure.pure 4 then
    let v := c.appArg!
    let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, (mkApp Q v).headBeta])
    g.assign (← mkAppOptM ``ret #[L, none, P, Q, v, h])
    return ← closeEntail h.mvarId!
  -- panic: the branch must be unreachable
  if isThrow c then
    let s ← saveState
    try
      let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.of_false _ ?_)) g | throwError "x"
      if ← closeWith g' (← `(tactic| first | contradiction | omega | (simp only [fsym_arith] at *; omega)))
        then return []
      s.restore
    catch _ => s.restore
    trace[fsym] "reachable panic"
    return [g]
  -- branches
  if c.isAppOfArity ``ite 5 then
    let a := c.getAppArgs
    let (cond, inst, t, e) := (a[1]!, a[2]!, a[3]!, a[4]!)
    let branch (g : MVarId) (h : Expr) (pos : Bool) : TacticM MVarId := do
      let eq ← mkAppOptM (if pos then ``if_pos else ``if_neg) #[cond, inst, h, none, t, e]
      let f ← withLocalDeclD `c (← inferType c) fun x => mkLambdaFVars #[x] (mkT L α P x Q)
      g.replaceTargetEq (mkT L α P (if pos then t else e) Q) (← mkCongrArg f eq)
    let hp ← mkFreshExprMVar cond
    if ← arith hp.mvarId! then
      return ← walk (← branch g (← instantiateMVars hp) true) user extra (fuel - 1)
    let hn ← mkFreshExprMVar (mkNot cond)
    if ← arith hn.mvarId! then
      return ← walk (← branch g (← instantiateMVars hn) false) user extra (fuel - 1)
    let (sp, sn) ← g.byCases cond `hc
    let gp ← sp.mvarId.withContext (branch sp.mvarId (.fvar sp.fvarId) true)
    let gn ← sn.mvarId.withContext (branch sn.mvarId (.fvar sn.fvarId) false)
    let gp ← destruct gp sp.fvarId
    let gn ← destruct gn sn.fvarId
    return (← walk gp user extra (fuel - 1)) ++ (← walk gn user extra (fuel - 1))
  -- cases on a variable
  let discr? : Option Expr ←
    if c.isAppOfArity ``Option.elim 5 then pure (some c.getAppArgs[2]!)
    else match ← matchMatcherApp? c with
      | some m => pure (m.discrs.find? (·.isFVar))
      | none => pure none
  if let some d := discr? then
    if d.isFVar then
      let gs ← g.cases d.fvarId!
      let mut out := []
      for sg in gs do
        let mut g' := sg.mvarId
        -- re-split facts about the variable
        for decl in (← g'.withContext getLCtx) do
          unless decl.isImplementationDetail do
            g' ← destruct g' decl.fvarId <|> pure g'
        out := out ++ (← walk g' user extra (fuel - 1))
      return out
  -- a command
  let (x, f) ← if c.isAppOfArity ``Bind.bind 6 then pure (c.getAppArgs[4]!, c.getAppArgs[5]!)
    else do
      let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.bind_pure _ ?_)) g | throwError "fsym"
      return ← walk g' user extra fuel
  for r in ← rules user do
    if let some (k, left) ← tryRule g r x f then
      return left ++ (← walk k user extra (fuel - 1))
  if let some x' ← unfoldCmd x then
    let c' ← mkAppM ``Bind.bind #[x', f]
    let g' ← g.replaceTargetDefEq (mkT L α P c' Q)
    return ← walk g' user extra (fuel - 1)
  logInfo m!"fsym: no rule for the command{indentExpr x}\nwith the precondition{indentExpr P}"
  return [g]

/-- `fsym`, `fsym [r, …]`: symbolic execution of the goal's program. The `rᵢ` are step rules
(triples, tried before the library's) or simp lemmas for the program. -/
syntax (name := fsymTac) "fsym" (" [" term,* "]")? : tactic

@[tactic fsymTac] def evalFsym : Tactic := fun stx => do
  let args : Array Syntax := match stx[1].getOptional? with
    | some s => s[1].getSepArgs
    | none => #[]
  let mut user := #[]
  let mut extra := #[]
  for a in args do
    let e ← elabTerm a none
    let ty ← instantiateMVars (← inferType e)
    let (_, _, concl) ← forallMetaTelescopeReducing ty
    if (← whnfR concl).isAppOfArity ``FTotalTriple 4 then user := user.push e
    else extra := extra.push a
  let g ← getMainGoal
  let gs ← walk g user extra 400
  replaceMainGoal gs

end Zig.Full.Auto
