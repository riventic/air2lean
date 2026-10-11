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
  let e' := e'.headBeta
  -- a definition by cases on a constructor (`resizePost … true`): reduce the match
  if ← isMatcherApp e' then
    let r ← whnfCore e'
    return some r.headBeta
  return some e'

/-- Reduce the projections of structure values in `e` (`(finv ctx B).tag` to its field). -/
def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let .const c _ := x.getAppFn | return .continue
    let some info ← getProjectionFnInfo? c | return .continue
    if info.fromClass then return .continue
    match ← unfold1 x with
    | some x' => return .visit x'
    | none => return .continue)

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

/-- Unify atoms when the heads agree, without unfolding values. -/
def unifyAtom (a b : Expr) : MetaM Bool := do
  let ka := headKey a
  let kb := headKey b
  if ka != kb && ka != .anonymous && kb != .anonymous then return false
  withReducibleAndInstances (isDefEq a b)

/-! ## Solvers -/

/-- The arithmetic solver for side goals. -/
syntax "fsym_arith" : tactic
macro_rules
  | `(tactic| fsym_arith) => `(tactic| first
      | assumption
      | omega
      | (simp only [fsym_arith, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at *; omega)
      | bv_omega
      | (simp only [fsym_arith, Nat.reduceMod, Nat.reducePow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *; omega))

/-- Run a tactic on a goal; `true` if it closed the goal (else the state is restored). -/
def closeWith (g : MVarId) (tac : Syntax) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← evalTacticAt tac g
    if gs.isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

/-- The user definitions (generated code, invariants) that occur in `e`. -/
def userConsts (e : Expr) : MetaM (Array Name) := do
  let mut out := #[]
  for c in e.getUsedConstants do
    if out.contains c then continue
    if ← isLibrary c then continue
    let some info := (← getEnv).find? c | continue
    unless info.isDefinition do continue
    if (← getProjectionFnInfo? c).isSome then continue
    if isAuxRecursor (← getEnv) c || isMatcherCore (← getEnv) c then continue
    out := out.push c
  return out

/-- The subterms `2 ^ x` (natural numbers, `x` not a literal) of `e`. -/
partial def twoPows (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.isAppOfArity ``HPow.hPow 6 && (e.getAppArgs[4]!.nat? == some 2) &&
        (e.getAppArgs[5]!.nat?).isNone && (e.getArg! 0).isConstOf ``Nat && !acc.contains e
      then acc.push e else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The arithmetic solver; a conjunction (also behind a user definition) is split. Returns the
goals it did not prove. -/
partial def arithGoals (g : MVarId) : TacticM (List MVarId) := g.withContext do
  if ← g.isAssigned then return []
  let t ← instantiateMVars (← g.getType)
  let t' ← whnfR t
  let t' ← if t'.isAppOfArity ``And 2 then pure t' else
    match t.getAppFn with
    | .const c _ => if ← isLibrary c then pure t' else
        match ← unfold1 t with
        | some u => whnfR u
        | none => pure t'
    | _ => pure t'
  if t'.isAppOfArity ``And 2 then
    let g ← g.replaceTargetDefEq t'
    let [g1, g2] ← g.apply (mkConst ``And.intro) | return [g]
    return (← arithGoals g1) ++ (← arithGoals g2)
  if !t.hasFVar && !t.hasMVar then
    if ← closeWith g (← `(tactic| decide)) then return []
  -- `0 < 2 ^ x` for the symbolic powers of two of the goal and the context
  let mut g := g
  let mut pows : Array Expr := #[]
  let mut srcs := #[t]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if ← isProp d.type then srcs := srcs.push (← instantiateMVars d.type)
  for e in srcs do
    for x in twoPows e do
      unless pows.contains x do pows := pows.push x
  for x in pows do
    let pf ← mkAppM ``Nat.two_pow_pos #[x.getAppArgs[5]!]
    g ← g.assert `hpow (← inferType pf) pf
    g ← (·.2) <$> g.intro1
  if ← closeWith g (← `(tactic| fsym_arith)) then return []
  if ← closeWith g (← `(tactic| fsym_fact)) then return []
  -- unfold the user definitions of the goal and the context
  let mut cs ← userConsts t
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if ← isProp d.type then cs := cs ++ (← userConsts (← instantiateMVars d.type))
  let cs' := cs.foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]
  if !cs'.isEmpty then
    let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      cs'.mapM fun c => `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident)
    if ← closeWith g (← `(tactic| (simp only [$ids,*] at *; fsym_arith))) then return []
  return [g]

def arith (g : MVarId) : TacticM Bool := do
  let s ← saveState
  if (← arithGoals g).isEmpty then return true
  s.restore; return false

/-- Prove `x = y` of assertions by AC of `⋆`. -/
def acEq (x y : Expr) : TacticM Expr := do
  let ty ← mkEq x y
  let m ← mkFreshExprMVar ty
  if x == y then return ← mkEqRefl x
  let tac ← `(tactic| first
      | ac_rfl
      | (simp only [Zig.Full.Auto.sep_emp_eq', Zig.Full.Auto.emp_sep_eq']; ac_rfl)
      | simp only [Zig.Full.Auto.sep_emp_eq', Zig.Full.Auto.emp_sep_eq'])
  unless ← closeWith m.mvarId! tac do
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

/-- Prove `ty` by the lemma `n`: its conclusion is unified with `ty`, its hypotheses are proved
from the context (blocks) or by arithmetic. -/
def proveBy (n : Name) (ty : Expr) : TacticM Expr := do
  let f ← mkConstWithFreshMVarLevels n
  let (args, _, concl) ← forallMetaTelescope (← inferType f)
  unless ← isDefEq concl ty do throwError "fsym: {n} does not apply"
  for a in args do
    let a ← instantiateMVars a
    unless a.isMVar do continue
    let t ← instantiateMVars (← inferType a)
    unless ← isProp t do continue
    if (t.eq?.map fun (_, l, _) => l.isAppOf ``Zig.Ptr.block).getD false then
      let some pf ← solveBlock t | throwError "fsym: block of {t}"
      a.mvarId!.assign pf
    else unless ← arith a.mvarId! do throwError "fsym: side condition {t}"
  instantiateMVars (mkAppN f args)

/-- Provider lemmas: `AddrOf` and `Reaches` of one atom. -/
def addrLemmas : List Name := [``AddrOf.known, ``AddrOf.region]
def reachLemmas : List Name := [``Reaches.share, ``Reaches.pts, ``Reaches.region]

/-- Candidates for a provider goal `AddrOf b A P` or `Reaches b K P`: proofs that assign `A`/`K`. -/
def providerCands (t : Expr) : TacticM (Array (TacticM Expr)) := do
  let t ← instantiateMVars t
  let isAddr := t.isAppOfArity ``AddrOf 3
  let P := t.appArg!
  let ats := atoms P
  let mut out := #[]
  for i in [0:ats.size] do
    let a := ats[i]!
    let rest := sepOf (ats.eraseIdx! i)
    for n in (if isAddr then addrLemmas else reachLemmas) do
      out := out.push do
        let ty := mkApp3 t.getAppFn t.getAppArgs[0]! t.getAppArgs[1]! a
        let h ← proveBy n ty
        let e ← acEq P (mkSep a rest)
        let pf ← mkAppM (if isAddr then ``AddrOf.of_atom else ``Reaches.of_atom) #[h, e]
        unless ← isDefEq t (← inferType pf) do throwError "fsym: provider mismatch"
        return pf
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
        catch ex => trace[fsym] "provider candidate: {ex.toMessageData}"
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

/-- One block variable per block: from `x.block = some b₁` and `y.block = some b₂` with
`x.block = y.block` (definitionally or by a fact), `b₂` is replaced by `b₁`. -/
partial def unifyBlocks (g : MVarId) : TacticM MVarId := g.withContext do
  let hyps := (← getLCtx).foldl (fun acc d => if d.isImplementationDetail then acc else acc.push d) #[]
  let mut someEqs := #[]
  let mut blkEqs := #[]
  for d in hyps do
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``Zig.Ptr.block 1 do continue
    if r.isAppOfArity ``Option.some 2 && r.appArg!.isFVar then someEqs := someEqs.push (d, l, r.appArg!)
    else if r.isAppOfArity ``Zig.Ptr.block 1 then blkEqs := blkEqs.push d
  for i in [0:someEqs.size] do
    for j in [i+1:someEqs.size] do
      let (d1, l1, b1) := someEqs[i]!
      let (d2, l2, b2) := someEqs[j]!
      if b1 == b2 then continue
      -- `l1 = l2`
      let link? : Option Expr ← do
        if ← withReducible (isDefEq l1 l2) then pure (some (← mkEqRefl l1))
        else
          let mut found := none
          for d in blkEqs do
            let ty ← instantiateMVars d.type
            let some (_, a, b) := ty.eq? | continue
            if (← withReducible (isDefEq a l1)) && (← withReducible (isDefEq b l2)) then
              found := some d.toExpr; break
            if (← withReducible (isDefEq a l2)) && (← withReducible (isDefEq b l1)) then
              found := some (← mkEqSymm d.toExpr); break
          pure found
      let some link := link? | continue
      -- `some b1 = some b2`
      let e ← mkEqTrans (← mkEqTrans (← mkEqSymm d1.toExpr) link) d2.toExpr
      let pf ← mkAppM ``Option.some.inj #[e]
      let g ← g.assert `hblk (← mkEq b1 b2) pf
      let (h, g) ← g.intro1
      let g ← subst g h
      return ← unifyBlocks g
  return g

/-- Normalize the precondition: unfold, flatten, move facts and existentials into the context. -/
partial def normPre (g : MVarId) (fuel : Nat := 64) : TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  let (g, L, α, P, c, Q) ← view g
  let rec leaves (e : Expr) : MetaM Expr := do
    let e := e.consumeMData.headBeta
    if e.isAppOfArity sepN 2 then return mkSep (← leaves e.appFn!.appArg!) (← leaves e.appArg!)
    unfoldAtom e
  let Pu ← reduceProjs (← leaves P)
  let ats := atoms Pu
  let isFact (a : Expr) := a.isAppOfArity liftN 1 || a.isAppOfArity exN 2
  let facts := ats.filter isFact
  let others := ats.filter (! isFact ·)
  let P2 := if facts.isEmpty then sepOf others else mkSep facts[0]! (sepOf (facts.eraseIdx! 0 ++ others))
  if P2 == P then
    if facts.isEmpty then return ← unifyBlocks g
  -- `P` to `Pu` by unfolding (definitional), `Pu` to `P2` by AC
  let g ← if P2 == P then pure g else do
    let e ← acEq Pu P2
    let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α P2 c Q)
    let pf ← mkAppOptM ``pre_eq #[L, none, P, P2, Q, c, ← mkExpectedTypeHint e (← mkEq P P2), g2]
    g.assign pf
    pure g2.mvarId!
  if facts.isEmpty then return ← unifyBlocks g
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
    let (args, _, concl) ← forallMetaTelescope (← inferType rule)
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
    for a in args do
      if ← a.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← inferType a)
      if (← isClass? ty).isSome then
        if let some inst ← (try some <$> synthInstance ty catch _ => pure none) then
          discard <| isDefEq a inst
    let sides := (← args.filterM fun a => do
      if ← a.mvarId!.isAssigned then return false
      isProp (← inferType a)).toList.map (·.mvarId!)
    let some left ← solveSides sides | do
      trace[fsym] "rule {rule}: side goals failed {← sides.mapM fun g => do instantiateMVars (← g.getType)}"
      s.restore; return none
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

/-! ## Updates into a postcondition: the planner -/

/-- Prove `x = y`: pointers by block and offset, numbers by arithmetic, applications of one
function by congruence (one level at a time). -/
partial def proveEqGoal (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (ty, x, y) := t.eq? | return false
  if ← withReducibleAndInstances (isDefEq x y) then
    g.assign (← mkEqRefl x); return true
  let ty ← whnfR ty
  if ty.isConstOf ``Zig.Ptr then
    return ← closeWith g (← `(tactic| (apply Zig.Full.Auto.ptr_ext' <;>
      first | rfl | fsym_arith | (simp only [fsym_arith] at *; simp only [*]))))
  if ty.isConstOf ``Nat || ty.isConstOf ``Int then return ← arith g
  if ty.isAppOfArity ``BitVec 1 then
    if ← closeWith g (← `(tactic| (apply BitVec.eq_of_toNat_eq; fsym_arith))) then return true
  let (fx, fy) := (x.getAppFn, y.getAppFn)
  unless fx.isConst && fx == fy && x.getAppNumArgs == y.getAppNumArgs do return false
  let s ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| congr 1)) g
    for g' in gs do
      unless ← proveEqGoal g' do s.restore; return false
    return true
  catch _ => s.restore; return false

def proveEq (x y : Expr) : TacticM (Option Expr) := do
  if x == y then return some (← mkEqRefl x)
  let m ← mkFreshExprMVar (← mkEq x y)
  let s ← saveState
  if ← proveEqGoal m.mvarId! then return some (← instantiateMVars m)
  s.restore; return none

/-- Unify a pattern atom `q` (with metavariables) with `p` argument by argument; a
`BitVec.ofNat w ?m` against a value `v` takes `?m := v.toNat`. Arguments that still differ
must be provably equal (checked by the caller). -/
partial def matchArgs (q p : Expr) : MetaM Bool := do
  let q ← instantiateMVars q
  if q.isAppOfArity ``BitVec.ofNat 2 && q.appArg!.isMVar && !p.isAppOfArity ``BitVec.ofNat 2 then
    let v ← mkAppM ``BitVec.toNat #[p]
    return ← isDefEq q.appArg! v
  if ← withReducibleAndInstances (isDefEq q p) then return true
  if q.getAppFn.isConst && q.getAppFn == p.getAppFn && q.getAppNumArgs == p.getAppNumArgs then
    for (x, y) in q.getAppArgs.zip p.getAppArgs do
      unless ← matchArgs x y do return false
    return true
  return !q.hasExprMVar && (q.isFVar == p.isFVar || true) && !(← inferType q).isSort

/-- The planner's state: the atoms of the resource and `EUpd P₀ (sepOf ats)`. -/
structure St where
  ats : Array Expr
  pf : Expr

def St.init (P : Expr) : TacticM St := do
  let ats := atoms P
  return { ats, pf := ← mkAppM ``atom_eq #[← acEq P (sepOf ats)] }

/-- Replace the atoms at `idx` by `outs` (nonempty) by `h : EUpd (sepOf consumed) (sepOf outs)`. -/
def St.step (st : St) (idx : Array Nat) (outs : Array Expr) (h : Expr) : TacticM St := do
  let X := sepOf (idx.map (st.ats[·]!))
  let rest := ((List.range st.ats.size).filter (! idx.contains ·)).toArray.map (st.ats[·]!)
  let newAts := outs ++ rest
  let cur := sepOf st.ats
  let loc ← if rest.isEmpty then
      mkAppM ``eupd_ac #[h, ← acEq cur X, ← acEq (sepOf outs) (sepOf newAts)]
    else
      let R := sepOf rest
      mkAppM ``eupd_frame_ac #[h, ← acEq cur (mkSep X R), ← acEq (mkSep (sepOf outs) R) (sepOf newAts)]
  return { ats := newAts, pf := ← mkAppM ``EUpd.trans #[st.pf, loc] }

def proveArith (ty : Expr) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  if ← arith m.mvarId! then return some (← instantiateMVars m)
  trace[fsym] "arith failed: {ty}"
  return none

def regionArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.FAssn.up 1 && e.appArg!.isAppOfArity ``Zig.regionIn 6 then
    some e.appArg!.getAppArgs else none

def shareArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.bshare 4 then some e.getAppArgs else none

def mkRegion (p A S K a bs : Expr) : MetaM Expr := do
  return mkApp (mkConst ``Zig.Full.FAssn.up) (← mkAppM ``Zig.regionIn #[p, A, S, K, a, bs])

def offNat (p : Expr) : MetaM Expr := do mkAppM ``Int.toNat #[← mkAppM ``Zig.Ptr.off #[p]]

/-- Carve the region atom `q` of the postcondition (bytes possibly unknown; `n?` its size from a
fact) out of a region of the state: split at its start (with its alignment) and at its end. -/
def carve (st : St) (q : Array Expr) (n? : Option Expr) : TacticM (Option St) := do
  let (qp, qA, qS, qK, qa, qbs) := (q[0]!, q[1]!, q[2]!, q[3]!, q[4]!, q[5]!)
  let some (qb, _) ← blockOf qp | return none
  for i in [0:st.ats.size] do
    let some r := regionArgs? st.ats[i]! | continue
    let s0 ← saveState
    let (p, A, S, K, a, bs) := (r[0]!, r[1]!, r[2]!, r[3]!, r[4]!, r[5]!)
    try
      let some (b, _) ← blockOf p | throwError "block"
      unless ← isDefEq b qb do throwError "block"
      unless (← isDefEq qA A) && (← isDefEq qS S) && (← isDefEq qK K) do throwError "labels"
      let po ← mkAppM ``Zig.Ptr.off #[p]
      let qo ← mkAppM ``Zig.Ptr.off #[qp]
      let size ← mkAppM ``Array.size #[bs]
      let some _ ← proveArith (← mkAppM ``LE.le #[po, qo]) | throwError "lo"
      let hiT ← mkAppM ``LE.le #[qo, ← mkAppM ``HAdd.hAdd #[po,
        ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt, size]]]
      let some _ ← proveArith hiT | throwError "hi {hiT}"
      let mut st := st
      let mut j := i
      let mut cur := r
      -- the start
      let zero ← proveArith (← mkEq qo po)
      if zero.isNone then
        let k ← mkAppM ``HSub.hSub #[← offNat qp, ← offNat p]
        let some hk ← proveArith (← mkAppM ``LE.le #[k, size]) | throwError "k"
        let some ha ← proveArith (← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``HAdd.hAdd #[
          ← mkAppM ``HAdd.hAdd #[A, ← offNat p], k], qa]) (mkNatLit 0)) | throwError "align"
        let h ← mkAppOptM ``up_region_split #[p, A, S, K, a, qa, bs, k, hk, ha]
        let p2 ← mkAppM ``Zig.Ptr.add #[p, ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt, k]]
        let bs1 ← mkAppM ``Array.extract #[bs, mkNatLit 0, k]
        let bs2 ← mkAppM ``Array.extract #[bs, k, size]
        st ← st.step #[i] #[← mkRegion p A S K a bs1, ← mkRegion p2 A S K qa bs2] h
        j := 1
        cur := #[p2, A, S, K, qa, bs2]
      -- the end
      let n? := n?.orElse fun _ => none
      let n? ← match n? with
        | some n => pure (some n)
        | none => do
          let qbs ← instantiateMVars qbs
          if qbs.hasExprMVar then pure none else pure (some (← mkAppM ``Array.size #[qbs]))
      if let some n := n? then
        let sz ← mkAppM ``Array.size #[cur[5]!]
        if (← proveArith (← mkEq n sz)).isNone then
          let some hk ← proveArith (← mkAppM ``LE.le #[n, sz]) | throwError "n"
          let some ha ← proveArith (← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``HAdd.hAdd #[
            ← mkAppM ``HAdd.hAdd #[cur[1]!, ← offNat cur[0]!], n], mkNatLit 1]) (mkNatLit 0))
            | throwError "align1"
          let h ← mkAppOptM ``up_region_split #[cur[0]!, cur[1]!, cur[2]!, cur[3]!, cur[4]!,
            mkNatLit 1, cur[5]!, n, hk, ha]
          let c1 ← mkAppM ``Array.extract #[cur[5]!, mkNatLit 0, n]
          let p3 ← mkAppM ``Zig.Ptr.add #[cur[0]!, ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt, n]]
          let c2 ← mkAppM ``Array.extract #[cur[5]!, n, sz]
          st ← st.step #[j] #[← mkRegion cur[0]! cur[1]! cur[2]! cur[3]! cur[4]! c1,
            ← mkRegion p3 cur[1]! cur[2]! cur[3]! (mkNatLit 1) c2] h
          j := 0
          cur := cur.set! 5 c1
      -- alignment
      unless ← isDefEq qa cur[4]! do
        let some hd ← proveArith (← mkAppM ``Dvd.dvd #[qa, cur[4]!]) | throwError "dvd"
        let h ← mkAppOptM ``up_region_weaken #[cur[0]!, cur[1]!, cur[2]!, cur[3]!, cur[4]!, qa,
          cur[5]!, hd]
        st ← st.step #[j] #[← mkRegion cur[0]! cur[1]! cur[2]! cur[3]! qa cur[5]!] h
        j := 0
      -- the bytes
      let qbs ← instantiateMVars qbs
      if qbs.hasExprMVar then
        unless ← isDefEq qbs cur[5]! do throwError "bytes"
      return some st
    catch ex =>
      trace[fsym] "carve: {ex.toMessageData}"
      s0.restore
  return none

/-- Join two adjacent regions of the state (the second at the end of the first). -/
def joinOnce (st : St) : TacticM (Option St) := do
  for i in [0:st.ats.size] do
    let some r1 := regionArgs? st.ats[i]! | continue
    for j in [0:st.ats.size] do
      if i == j then continue
      let some r2 := regionArgs? st.ats[j]! | continue
      let s0 ← saveState
      try
        unless (← isDefEq r1[1]! r2[1]!) && (← isDefEq r1[2]! r2[2]!) && (← isDefEq r1[3]! r2[3]!) do
          throwError "labels"
        let pe ← mkAppM ``Zig.Ptr.add #[r1[0]!, ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt,
          ← mkAppM ``Array.size #[r1[5]!]]]
        let some e ← proveEq r2[0]! pe | throwError "adjacent"
        let r2' ← mkRegion pe r2[1]! r2[2]! r2[3]! r2[4]! r2[5]!
        let some e' ← proveEq st.ats[j]! r2' | throwError "eq"
        let _ := e
        let st ← st.step #[j] #[r2'] (← mkAppM ``atom_eq #[e'])
        -- now `r2'` is at 0, `r1` moved
        let some i' := st.ats.findIdx? (· == st.ats[0]! |> fun _ => false) |> fun _ =>
          (st.ats.toList.findIdx? (fun x => x == mkApp (mkConst ``Zig.Full.FAssn.up)
            (mkAppN (mkConst ``Zig.regionIn) r1))) | throwError "lost"
        let h ← mkAppOptM ``up_region_join #[r1[0]!, r1[1]!, r1[2]!, r1[3]!, r1[4]!, r2[4]!, r1[5]!, r2[5]!]
        let joined ← mkRegion r1[0]! r1[1]! r1[2]! r1[3]! r1[4]! (← mkAppM ``HAppend.hAppend #[r1[5]!, r2[5]!])
        return some (← st.step #[i', 0] #[joined] h)
      catch ex =>
        trace[fsym] "join: {ex.toMessageData}"
        s0.restore
  return none

/-- Shares: join those of one block, split for the postcondition's shares of that block,
weaken to their bounds. -/
def planShares (st : St) (qshares : Array (Array Expr)) : TacticM St := do
  let mut st := st
  -- join
  let mut again := true
  while again do
    again := false
    let ss := (List.range st.ats.size).filterMap fun i => (shareArgs? st.ats[i]!).map (i, ·)
    for (i, x) in ss do
      for (j, y) in ss do
        if i < j && x[0]! == y[0]! && x[3]! == y[3]! then
          let h ← mkAppOptM ``share_join #[x[0]!, x[1]!, x[2]!, x[3]!, y[1]!, y[2]!]
          let out := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, ← mkAppM ``Frac.add #[x[1]!, y[1]!],
            ← mkAppM ``Max.max #[x[2]!, y[2]!], x[3]!]
          st ← st.step #[i, j] #[out] h
          again := true
          break
      if again then break
  -- split, per block
  let blocks := st.ats.filterMap fun x => (shareArgs? x).map (·[0]!)
  for blk in blocks do
    let mut want := 0
    for q in qshares do
      let s0 ← saveState
      if ← isDefEq q[0]! blk then want := want + 1
      s0.restore
    let some i0 := st.ats.findIdx? fun x => (shareArgs? x).any (·[0]! == blk) | continue
    let mut xa := (shareArgs? st.ats[i0]!).get!
    let mut idx := i0
    let mut have_ := 1
    while have_ < want do
      let h ← mkAppOptM ``share_halves #[xa[0]!, xa[1]!, xa[2]!, xa[3]!]
      let hf ← mkAppM ``Frac.half #[xa[1]!]
      let out := mkAppN (mkConst ``Zig.Full.bshare) #[xa[0]!, hf, xa[2]!, xa[3]!]
      st ← st.step #[idx] #[out, out] h
      idx := 0
      xa := xa.set! 1 hf
      have_ := have_ + 1
  -- assign fractions and weaken bounds
  let mut used : Array Nat := #[]
  for q in qshares do
    for i in [0:st.ats.size] do
      if used.contains i then continue
      let some x := shareArgs? st.ats[i]! | continue
      let s0 ← saveState
      if (← isDefEq q[0]! x[0]!) && (← isDefEq q[3]! x[3]!) && (← isDefEq q[1]! x[1]!) then
        let qk ← instantiateMVars q[2]!
        if ← isDefEq qk x[2]! then used := used.push i; break
        if let some hle ← proveArith (← mkAppM ``LE.le #[qk, x[2]!]) then
          let h ← mkAppOptM ``share_weaken #[x[0]!, x[1]!, x[2]!, qk, x[3]!, hle]
          st ← st.step #[i] #[mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, x[1]!, qk, x[3]!]] h
          used := used.map (fun k => if k < i then k + 1 else k) |>.push 0
          break
      s0.restore
  return st

/-- The conjuncts of a fact, through user definitions. -/
partial def conjuncts (φ : Expr) (fuel : Nat := 16) : MetaM (Array Expr) := do
  if fuel == 0 then return #[φ]
  let φ ← instantiateMVars φ
  let w ← whnfR φ
  if w.isAppOfArity ``And 2 then
    return (← conjuncts w.appFn!.appArg! (fuel - 1)) ++ (← conjuncts w.appArg! (fuel - 1))
  if let .const c _ := φ.getAppFn then
    unless ← isLibrary c do
      if let some u ← unfold1 φ then return ← conjuncts u (fuel - 1)
  return #[φ]

/-- Close `EUpd P Q`: open `Q`'s existentials, plan regions and shares, match the remaining
atoms (up to provable equations of their arguments), drop `up` atoms into `junk`, prove `Q`'s
facts by arithmetic. Unproved facts are left as goals; on failure the update goal is left. -/
def closeEntail (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let s ← saveState
  try
    let t ← instantiateMVars (← g.getType)
    let P := t.appFn!.appArg!
    let Q := t.appArg!
    let (Qi, pQ) ← instQ Q
    let qats := atoms Qi
    let facts := qats.filter (·.isAppOfArity liftN 1)
    -- block facts first
    for f in facts do
      let φ ← instantiateMVars f.appArg!
      if (φ.eq?.map fun (_, l, _) => l.isAppOf ``Zig.Ptr.block).getD false then
        discard <| solveBlock φ
    let mut st ← St.init P
    -- pre-assign by the atoms that unify outright
    for a in qats do
      if a.isAppOfArity liftN 1 || (regionArgs? a).isSome || (shareArgs? a).isSome then continue
      for x in st.ats do
        let s' ← saveState
        if ← unifyAtom a x then break
        s'.restore
    for a in qats do
      if a.isAppOfArity liftN 1 || (regionArgs? a).isSome || (shareArgs? a).isSome then continue
      if (← instantiateMVars a).hasExprMVar then
        for x in st.ats do
          if headKey a != headKey x then continue
          let s' ← saveState
          if ← matchArgs a x then
            if (← proveEq x (← instantiateMVars a)).isSome then break
          s'.restore
    -- regions: exact matches first; then carve (joining adjacent regions for a region of
    -- unknown size, which extends as far as the state's bytes go, or when no region holds it)
    let mut exact : Array Nat := #[]
    for a in qats do
      let some q := regionArgs? (← instantiateMVars a) | continue
      -- a region with a size fact is carved (its bytes may change)
      let qbs ← instantiateMVars q[5]!
      let mut sized := false
      for f in facts do
        for φ in ← conjuncts f.appArg! do
          if let some (_, l, _) := φ.eq? then
            if l.isAppOfArity ``Array.size 2 && (← instantiateMVars l.appArg!) == qbs then sized := true
      if sized && qbs.hasExprMVar then continue
      for i in [0:st.ats.size] do
        if (regionArgs? st.ats[i]!).isNone || exact.contains i then continue
        let s' ← saveState
        if ← withReducibleAndInstances (isDefEq a st.ats[i]!) then exact := exact.push i; break
        s'.restore
    for a in qats do
      let some q := regionArgs? (← instantiateMVars a) | continue
      if (← st.ats.anyM fun x => return x == (← instantiateMVars a)) then continue
      -- a size fact `q.bs.size = n`
      let mut n? := none
      let qbs ← instantiateMVars q[5]!
      for f in facts do
        for φ in ← conjuncts f.appArg! do
          if let some (_, l, r) := φ.eq? then
            if l.isAppOfArity ``Array.size 2 && (← instantiateMVars l.appArg!) == qbs then n? := some r
      let mut done := false
      if n?.isNone && (← instantiateMVars q[5]!).hasExprMVar then
        repeat
          let some st' ← joinOnce st | break
          st := st'
      if let some st' ← carve st q n? then st := st'; done := true
      while !done do
        let some st' ← joinOnce st | break
        st := st'
        if let some st' ← carve st q n? then st := st'; done := true
      unless done do throwError "fsym: no region of the state holds{indentExpr a}"
    -- shares
    let qsh ← qats.filterMapM fun a => do return shareArgs? (← instantiateMVars a)
    st ← planShares st qsh
    -- final match
    let spat := qats.filter (! ·.isAppOfArity liftN 1)
    let junkQ := spat.any (·.isConstOf ``Zig.Full.Auto.junk)
    let spat := spat.filter (! ·.isConstOf ``Zig.Full.Auto.junk)
    let mut used : Array Nat := #[]
    for a in spat do
      let a ← instantiateMVars a
      let mut found := false
      for i in [0:st.ats.size] do
        if used.contains i then continue
        let s' ← saveState
        if ← unifyAtom a st.ats[i]! then
          used := used.push i; found := true; break
        s'.restore
      unless found do
        for i in [0:st.ats.size] do
          if used.contains i then continue
          if headKey a != headKey st.ats[i]! then continue
          let s' ← saveState
          if ← matchArgs a st.ats[i]! then
            let a' ← instantiateMVars a
            if let some e ← proveEq st.ats[i]! a' then
              st ← st.step #[i] #[a'] (← mkAppM ``atom_eq #[e])
              used := used.map (fun k => if k < i then k + 1 else k) |>.push 0
              found := true; break
          s'.restore
      unless found do throwError "fsym: the state has no atom for{indentExpr a}"
    let pats := st.ats
    let P := sepOf pats
    let L := ((List.range pats.size).filter (! used.contains ·)).toArray.map (pats[·]!)
    let M := used.map (pats[·]!)
    unless L.isEmpty || junkQ do throwError "fsym: atoms left over{indentExpr (sepOf L)}"
    let (S, core) ← if junkQ then do
        let J := mkConst ``Zig.Full.Auto.junk
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
          pure (J, ← mkAppM ``imp_trans #[← mkAppM ``imp_eq #[← acEq P Lx], pj])
        else
          let rec frame (ms : List Expr) : MetaM Expr := do
            match ms with
            | [] => pure pj
            | m :: rest => mkAppM ``imp_sep #[← mkAppOptM ``imp_refl #[m], ← frame rest]
          pure (sepOf (M.push J), ← mkAppM ``imp_trans #[← mkAppM ``imp_eq #[← acEq P (sepOf (M.push Lx))],
            ← frame M.toList])
      else do
        let S := sepOf M
        pure (S, ← mkAppM ``imp_eq #[← acEq P S])
    let mut left := []
    let mut body := core
    let mut T := S
    for f in facts.reverse do
      let φ ← instantiateMVars f.appArg!
      let hφ ← mkFreshExprMVar φ
      left := (← arithGoals hφ.mvarId!) ++ left
      body ← mkAppM ``imp_lift #[hφ, body]
      T := mkSep f T
    let T' ← instantiateMVars T
    let Qi ← instantiateMVars Qi
    let eT ← acEq T' Qi
    let pf ← mkAppM ``imp_trans #[← mkAppM ``imp_trans #[body, ← mkAppM ``imp_eq #[eT]], pQ]
    let pf ← instantiateMVars pf
    if pf.hasExprMVar then
      for m in ← getMVars pf do
        unless left.contains m do
          unless ← isProp (← m.getType) do throwError "fsym: undetermined witness ?{m.name}"
    g.assign (← mkAppM ``EUpd.trans #[st.pf, ← mkAppM ``eupd_of_imp #[pf]])
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
      if ← closeWith g' (← `(tactic| first | contradiction | omega | (simp only [fsym_arith, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at *; omega)))
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
  -- hypotheses about projections of structure values (`(finv ctx B).fits n k`) are reduced
  let g ← g.withContext do
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless ← isProp d.type do continue
      let ty' ← reduceProjs (← instantiateMVars d.type)
      if ty' != d.type then
        g ← g.replaceLocalDeclDefEq d.fvarId ty'
    pure g
  let gs ← walk g user extra 400
  replaceMainGoal gs

end Zig.Full.Auto
