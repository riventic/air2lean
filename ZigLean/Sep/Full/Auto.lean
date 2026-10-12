import ZigLean.Sep.Full.AutoConc

/-!
# `fsym`: symbolic execution of generated code in the full-state logic

`fsym` proves a goal `FTotalTriple P c Q`, `FTriple P c Q` or `L.T P c Q` (any `FLogic`), or
`CTriple P c Q` (a concurrent function read in one thread: the backend `Bk.conc`, rules in
`AutoConc.lean`), by walking the generated program `c` (`docs/proof-automation.md`):

* **Preconditions** are kept as a flat list of atoms. Definitions that build assertions from
  `⋆`, `⟪φ⟫` and `FAssn.ex` (an invariant, a token, `pshare`, a projection of an `FAllocInv`) are
  unfolded; existentials and facts move into the context (conjunctions are split, equations of a
  variable are substituted, user definitions of facts are unfolded). Atoms are what is left: the
  library's assertions (`up`, `known`, `bshare`, …), `@[fsym_atom]`s and opaque terms.
* **Programs** are normalized with `fsym_norm` (the `MM`/`StateT` layer of generated code, binds,
  trivial results) at the head only (`lazyMethods`: a continuation is normalized once it is the
  head). A call of a generated function (or of a pure generated helper under `StateT.lift`) is
  inlined; a projection of a vtable is reduced.
* **Facts of atoms** (`@[fsym_facts]`): when a step needs more facts, the block, offset and
  alignment of the pointers that the precondition owns memory at are added (`addFacts`).
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
  its facts (by the arithmetic solver), `Junk` (which absorbs `up` atoms) and AC of `⋆`;
  otherwise the update goal is left to the caller.

Every step elaborates to applications of `ZigLean/Sep/Full/AutoRules.lean` and the library's
rules: the kernel checks the result.
-/

namespace Zig.Full.Auto

open Lean Meta Elab Tactic

initialize registerTraceClass `fsym
initialize registerTraceClass `fsym.arith
initialize registerTraceClass `fsym.prof
initialize registerTraceClass `fsym.total

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

/-- The applications in a term (each once, outermost first). -/
partial def subterms (e : Expr) : Array Expr :=
  go e #[]
where go (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a => go a (go f (if acc.contains e then acc else acc.push e))
  | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
  | .mdata _ b => go b acc
  | _ => acc

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
  if c == sepN || c == empN || c == liftN || c == exN || c == ``ite || c == ``dite then return none
  if isFsymAtom (← getEnv) c then return none
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
  -- a `match` on a constructor (an error union after the case split)
  if let .reduced e' ← reduceMatcher? e then return ← unfoldAtom e'.headBeta
  match ← unfold1 e with
  | some e' => if e'.consumeMData.isLambda then return e else unfoldAtom e'
  | none => return e

/-- `unfoldAtom` on each leaf of a separating conjunction. -/
partial def unfoldLeaves (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity sepN 2 then return mkSep (← unfoldLeaves e.appFn!.appArg!) (← unfoldLeaves e.appArg!)
  unfoldAtom e

/-- The logic of a goal (the backend): `L.T` of an `FLogic` `L` (sequential programs), or the
concurrent `CTriple` (`conc`; `L` is the target type `Tgt`). -/
structure Bk where
  conc : Bool
  L : Expr
  deriving Inhabited

/-- Partial correctness: partial (`FTriple`) rules apply too. -/
def Bk.part (B : Bk) : Bool := B.conc || B.L.isConstOf ``FLogic.partial

/-- The backend's version of a structural lemma of `AutoRules.lean` (`C.n` for `CTriple`, with
the same arguments). -/
def Bk.nm (B : Bk) (n : Name) : Name :=
  if B.conc then n.getPrefix ++ `C ++ .mkSimple n.getString! else n

/-- A goal `L.T P c Q` or `CTriple P c Q`: `(B, α, P, c, Q)`; `FTotalTriple`/`FTriple` goals
are restated as `L.T`. -/
def view (g : MVarId) : MetaM (MVarId × Bk × Expr × Expr × Expr × Expr) := do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  if t.isAppOfArity ``FLogic.T 5 then
    let a := t.getAppArgs
    return (g, ⟨false, a[0]!⟩, a[1]!, a[2]!, a[3]!.consumeMData, a[4]!)
  if t.isAppOfArity ``CTriple 5 then
    let a := t.getAppArgs
    return (g, ⟨true, a[0]!⟩, a[1]!, a[2]!, a[3]!.consumeMData, a[4]!)
  for (k, L) in [(``FTotalTriple, ``FLogic.total), (``FTriple, ``FLogic.partial)] do
    if t.isAppOfArity k 4 then
      let a := t.getAppArgs
      let L := mkConst L
      let g' ← g.replaceTargetDefEq (mkAppN (mkConst ``FLogic.T) #[L, a[0]!, a[1]!, a[2]!, a[3]!])
      return (g', ⟨false, L⟩, a[0]!, a[1]!, a[2]!.consumeMData, a[3]!)
  throwError "fsym: expected an FTotalTriple, FTriple, FLogic.T or CTriple goal{indentExpr t}"

def mkT (B : Bk) (α P c Q : Expr) : Expr :=
  mkAppN (mkConst (if B.conc then ``CTriple else ``FLogic.T)) #[B.L, α, P, c, Q]

/-- The kind of a rule's conclusion: a total (`FTotalTriple`) or partial (`FTriple`) triple of a
`MemM` command, or a `CTriple` of a concurrent one; `(kind, command)`. -/
def ruleConcl? (concl : Expr) : Option (Name × Expr) :=
  if concl.isAppOfArity ``FTotalTriple 4 then some (``FTotalTriple, concl.getArg! 2)
  else if concl.isAppOfArity ``FTriple 4 then some (``FTriple, concl.getArg! 2)
  else if concl.isAppOfArity ``CTriple 5 then some (``CTriple, concl.getArg! 3)
  else none

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

/-- Unify when the heads agree. Applications of one constant are unified argument by argument
(without unfolding the constant when the arguments differ: `load (BitVec 64) …` against
`load Ptr …` fails without unfolding `load`). -/
partial def unifyKeyed (a b : Expr) : MetaM Bool := do
  let ka := headKey a
  let kb := headKey b
  if ka != kb && ka != .anonymous && kb != .anonymous then
    -- values (words, numbers, flags) of different heads may still be equal by unfolding
    -- (`os.protReadWrite` and the generated `Packed.toBits (Packed.ofBits 3)`)
    -- ground values only: a pattern with metavariables must not be matched by unfolding
    if (← instantiateMVars a).hasExprMVar || (← instantiateMVars b).hasExprMVar then return false
    let ty ← whnfR (← inferType a)
    unless ty.isAppOfArity ``BitVec 1 || ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool do
      return false
    return ← isDefEq a b
  let a := a.consumeMData
  let b := b.consumeMData
  if let .const ca _ := a.getAppFn then
    if let .const cb _ := b.getAppFn then
      if ca == cb && a.getAppNumArgs == b.getAppNumArgs then
        unless ← isDefEq a.getAppFn b.getAppFn do return false
        for (x, y) in a.getAppArgs.zip b.getAppArgs do
          unless ← unifyKeyed x y do return false
        return true
  isDefEq a b

/-- Unify atoms when the heads agree, without unfolding values. -/
def unifyAtom (a b : Expr) : MetaM Bool := do
  let ka := headKey a
  let kb := headKey b
  if ka != kb && ka != .anonymous && kb != .anonymous then return false
  withReducibleAndInstances (isDefEq a b)

/-! ## Solvers -/

/-- Run a tactic on a goal; `true` if it closed the goal (else the state is restored). -/
def closeWith (g : MVarId) (tac : Syntax) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← evalTacticAt tac g
    if gs.isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

/-- `e` is `2 ^ x` (natural numbers, `x` not a literal). -/
def isSymPow (e : Expr) : Bool :=
  e.isAppOfArity ``HPow.hPow 6 && (e.getAppArgs[4]!.nat? == some 2) &&
    (e.getAppArgs[5]!.nat?).isNone && (e.getArg! 0).isConstOf ``Nat

/-- The subterms `2 ^ x` (`isSymPow`) and `z % 2 ^ x` of `e`. -/
partial def powTerms (e : Expr) : Array Expr × Array Expr :=
  go e (#[], #[])
where
  go (e : Expr) (acc : Array Expr × Array Expr) : Array Expr × Array Expr :=
    let (ps, ms) := acc
    let ps := if isSymPow e && !ps.contains e then ps.push e else ps
    let ms := if e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat && isSymPow e.appArg! &&
        !ms.contains e then ms.push e else ms
    let acc := (ps, ms)
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The hypotheses (propositions) of the context. -/
def propHyps : MetaM (Array LocalDecl) := do
  let mut out := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if ← isProp d.type then out := out.push d
  return out



/-- The caches of one run of `fsym` (theorems are elaborated in parallel: no global state).
* `hyp`: the `fsym_arith` normal form of each hypothesis, by `FVarId` (a hypothesis' type only
  changes up to definitional equality): `none` if unchanged, else the new proposition and its
  proof (over the original hypotheses only).
* `disch`: side conditions the discharger proved; a proof is reused where its free variables
  are in scope.
* `facts`: the facts of the current arithmetic problem (proofs over the goal's hypotheses of
  propositions in normal form), which the discharger works from.
* `probe`: probes (a mask, remainder, case or `if` fact for a term): a proof (reused where in
  scope), or the number of facts it failed with (retried only with more facts).
* `ctx`: the simp context of the arithmetic solver, built at the start of the run before any
  backtracking (adding a theorem may create auxiliary lemmas, which a restored state would
  lose). -/
structure RunCaches where
  hyp : IO.Ref (Std.HashMap FVarId (Option (Expr × Expr)))
  disch : IO.Ref (Std.HashMap Expr (Option Expr))
  facts : IO.Ref (Array Expr)
  probe : IO.Ref (Std.HashMap Expr (Expr ⊕ Nat))
  ctx : IO.Ref (Option (Simp.Context × Simp.SimprocsArray))
  /-- The program simp context (`fsym_norm`, the caller's lemmas, the simprocs). -/
  prog : IO.Ref (Option (Simp.Context × Simp.SimprocsArray))
  /-- The registered rules with the head of their command (`headKey`). -/
  rules : IO.Ref (Option (Array (Name × Name)))
  /-- The simp context that folds generated indirect calls (concurrent bodies). -/
  fold : IO.Ref (Option Simp.Context)
  /-- The facts lemmas (`@[fsym_facts]`) with the head of their assertion (`headKey`). -/
  factLemmas : IO.Ref (Option (Array (Name × Name)))

def RunCaches.new : IO RunCaches :=
  return { hyp := ← IO.mkRef {}, disch := ← IO.mkRef {}, facts := ← IO.mkRef #[],
           probe := ← IO.mkRef {}, ctx := ← IO.mkRef none, prog := ← IO.mkRef none,
           rules := ← IO.mkRef none, fold := ← IO.mkRef none, factLemmas := ← IO.mkRef none }

/-- The caches of the runs in progress, by run id (the option `fsym.run` of a run). -/
initialize fsymRuns : IO.Ref (Std.HashMap Nat RunCaches) ← IO.mkRef {}
initialize fsymRunCounter : IO.Ref Nat ← IO.mkRef 0

/-- The caches of the current run (a fresh set outside a run: `fsym_arith` on its own). -/
def caches : CoreM RunCaches := do
  let id := (← getOptions).get `fsym.run (0 : Nat)
  if id != 0 then
    if let some c := (← fsymRuns.get).get? id then return c
  let c ← RunCaches.new
  if id != 0 then fsymRuns.modify (·.insert id c)
  return c

/-- Run `x` with fresh caches. -/
def withRunCaches {α : Type} (x : TacticM α) : TacticM α := do
  let id ← fsymRunCounter.modifyGet fun n => (n + 1, n + 1)
  fsymRuns.modify (·.insert id (← RunCaches.new))
  try withOptions (·.set `fsym.run id) x
  finally fsymRuns.modify (·.erase id)

/-- The context of a negative cache entry: the number of facts and the last hypothesis (sibling
branches with as many facts are different contexts). -/
def ctxStamp (n : Nat) : MetaM Nat := do
  let last := ((← getLCtx).lastDecl.map (·.fvarId.name.hash)).getD 0
  return (mixHash (hash n) last).toNat

/-- A cached probe for `key`: `run` with `n` facts. -/
def probe (key : Expr) (n : Nat) (run : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  let stamp ← ctxStamp n
  match (← (← caches).probe.get).get? key with
  | some (.inl pf) => if !pf.hasAnyFVar (fun f => !lctx.contains f) then return some pf
  | some (.inr m) => if m == stamp then return none
  | none => pure ()
  let r ← run
  (← caches).probe.modify (·.insert key (match r with | some pf => .inl pf | none => .inr stamp))
  return r

/-- `omega` proves `ty` from `facts` (proof terms), as given; the state is kept clean. -/
def omegaRaw (facts : Array Expr) (ty : Expr) : MetaM (Option Expr) := do
  let h0 ← IO.getNumHeartbeats
  let r ← omegaRaw' facts ty
  let d := ((← IO.getNumHeartbeats) - h0) / 1000
  trace[fsym.prof] "raw {d} {facts.size} {r.isSome}"
  if d > 1000 then trace[fsym.prof] "slow omega {ty} from {← facts.mapM inferType}"
  return r
where
  omegaRaw' (facts : Array Expr) (ty : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  -- `omega` may exhaust the recursion depth on a false goal with many case splits: a failure
  tryCatchRuntimeEx (do
    let m ← mkFreshExprMVar ty
    let before := (← getLCtx).lastDecl.map (·.fvarId)
    let some g ← m.mvarId!.falseOrByContra | return some (← instantiateMVars m)
    g.withContext do
      let neg := match (← getLCtx).lastDecl with
        | some d => if some d.fvarId != before then #[d.toExpr] else #[]
        | none => #[]
      -- `omega`'s case splits on `/` and `%` by literals recurse deeply on a false goal
      withTheReader Core.Context (fun c => { c with maxRecDepth := Nat.max c.maxRecDepth 20000 }) do
        Lean.Elab.Tactic.Omega.omega (neg ++ facts).toList g
    return some (← instantiateMVars m))
    fun _ => do s.restore; return none

/-- A proposition `omega` reads: relations of natural numbers and integers under `¬ ∧ ∨ → ↔`. -/
partial def isArithProp (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  if t.isConstOf ``True || t.isConstOf ``False then return true
  if t.isAppOfArity ``Not 1 then return ← isArithProp t.appArg!
  if t.isAppOfArity ``And 2 || t.isAppOfArity ``Or 2 || t.isAppOfArity ``Iff 2 then
    return (← isArithProp t.appFn!.appArg!) && (← isArithProp t.appArg!)
  if t.isArrow then return (← isArithProp t.bindingDomain!) && (← isArithProp t.bindingBody!)
  let num (ty : Expr) := ty.isConstOf ``Nat || ty.isConstOf ``Int
  if t.isAppOfArity ``Eq 3 || t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``LE.le 4 ||
      t.isAppOfArity ``GT.gt 4 || t.isAppOfArity ``GE.ge 4 || t.isAppOfArity ``Dvd.dvd 4 then
    return num (← whnfR (t.getArg! 0))
  return false

/-- A term `omega` case-splits on: a truncated subtraction, `Int.toNat`, `min`, `max`. -/
def isSplitTerm (e : Expr) : Bool :=
  (e.isAppOfArity ``HSub.hSub 6 && (e.getArg! 0).isConstOf ``Nat) || e.isAppOfArity ``Int.toNat 1 ||
    (e.isAppOfArity ``Min.min 4 && (e.getArg! 0).isConstOf ``Nat) ||
    (e.isAppOfArity ``Max.max 4 && (e.getArg! 0).isConstOf ``Nat)

/-- A fact without case splits for `omega` (the negation of an order is one). -/
def isLinearProp (t : Expr) : Bool :=
  let ord (e : Expr) := e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``LE.le 4 ||
    e.isAppOfArity ``GT.gt 4 || e.isAppOfArity ``GE.ge 4
  let t := if t.isAppOfArity ``Not 1 && ord t.appArg! then t.appArg! else t
  !t.isArrow && !(t.find? fun e => isSplitTerm e || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 ||
    e.isAppOfArity ``Not 1).isSome

/-- The arithmetic operations and relations (with the number of trailing arguments that are
operands): `arithAtoms` looks through them. -/
def arithOps : Std.HashMap Name Nat := Std.HashMap.ofList [
  (``HAdd.hAdd, 2), (``HSub.hSub, 2), (``HMul.hMul, 2), (``HDiv.hDiv, 2), (``HMod.hMod, 2),
  (``HPow.hPow, 2), (``LE.le, 2), (``LT.lt, 2), (``GE.ge, 2), (``GT.gt, 2), (``Dvd.dvd, 2),
  (``Eq, 2), (``Ne, 2), (``Min.min, 2), (``Max.max, 2), (``And, 2), (``Or, 2), (``Iff, 2),
  (``Not, 1), (``Neg.neg, 1), (``Nat.cast, 1), (``Int.ofNat, 1), (``Int.toNat, 1), (``Nat.succ, 1),
  (``OfNat.ofNat, 0), (``subAtom, 2), (``minAtom, 2), (``maxAtom, 2), (``toNatAtom, 1),
  (``HShiftLeft.hShiftLeft, 2), (``HShiftRight.hShiftRight, 2), (``HAnd.hAnd, 2), (``HOr.hOr, 2),
  (``HXor.hXor, 2), (``Int.natAbs, 1), (``Int.subNatNat, 2), (``Int.negSucc, 1), (``Int.emod, 2),
  (``Int.ediv, 2), (``Nat.sub, 2), (``Nat.add, 2), (``Nat.mul, 2), (``Nat.div, 2), (``Nat.mod, 2)]

/-- The atoms of an arithmetic proposition or term: its maximal subterms that are not arithmetic
operations or literals (`omega`'s variables). -/
partial def arithAtoms (e : Expr) (acc : Std.HashSet Expr := {}) : Std.HashSet Expr :=
  let e := e.consumeMData
  match e with
  | .lit _ => acc
  | .forallE _ d b _ => if b.hasLooseBVars then acc.insert e else arithAtoms b (arithAtoms d acc)
  | _ =>
    match e.getAppFn with
    | .const c _ =>
      if e.isConstOf ``True || e.isConstOf ``False then acc
      else match arithOps.get? c with
        | some k => (e.getAppArgs.extract (e.getAppNumArgs - k) e.getAppNumArgs).foldl
            (fun a x => arithAtoms x a) acc
        | none => acc.insert e
    | _ => acc.insert e

/-- The facts relevant to `ty`: those connected to it by shared atoms (transitively), and those
without atoms. All facts for a goal without atoms (`False`: a refutation of the context, which is
how an unreachable branch is closed; a side goal on an unreachable path whose contradiction does
not touch its atoms is left to that refutation). -/
def relevantFacts (facts : Array (Expr × Expr)) (ty : Expr) : Array (Expr × Expr) := Id.run do
  let mut seen := arithAtoms ty
  if seen.isEmpty then return facts
  let fa := facts.map fun (_, t) => (arithAtoms t).toArray
  let mut used := Array.replicate facts.size false
  let mut changed := true
  while changed do
    changed := false
    for i in [0:facts.size] do
      if used[i]! || !(fa[i]!.isEmpty || fa[i]!.any seen.contains) then continue
      used := used.set! i true; changed := true
      seen := fa[i]!.foldl (·.insert ·) seen
  return (facts.zip used).filterMap fun (f, u) => if u then some f else none

/-- `omega` proves `ty` from `facts`: only arithmetic facts; the split terms whose case the
linear facts decide become opaque atoms with linear defining facts (`subAtom`, `toNatAtom`,
`minAtom`, `maxAtom`): `omega` explores no case split for them. -/
def omegaFacts (facts : Array Expr) (ty : Expr) : MetaM (Option Expr) := do
  let mut arith : Array (Expr × Expr) := #[]
  for f in facts do
    let t ← instantiateMVars (← inferType f)
    if ← isArithProp t then arith := arith.push (f, t)
  let ty ← instantiateMVars ty
  arith := relevantFacts arith ty
  let hasSplit := (arith.any fun (_, t) => (t.find? isSplitTerm).isSome) || (ty.find? isSplitTerm).isSome
  unless hasSplit do return ← omegaRaw (arith.map (·.1)) ty
  -- the linear facts, and the facts that the atoms make linear
  let linRef ← IO.mkRef ((arith.filter fun (_, t) => isLinearProp t).map (·.1))
  let atomsRef ← IO.mkRef (({} : Std.HashMap Expr Expr), (#[] : Array Expr))
  let rw (e : Expr) : MetaM Expr := Meta.transform e (post := fun x => do
    unless isSplitTerm x do return .continue
    let (m, defs) ← atomsRef.get
    if let some a := m.get? x then return .done a
    let base := (← linRef.get) ++ defs
    let decide (prop : Expr) : MetaM (Option Expr) :=
      probe (mkApp2 (mkConst `fsym.det) x prop) base.size (omegaRaw base prop)
    let args := x.getAppArgs
    let r : Option (Expr × Expr) ← do
      if x.isAppOfArity ``Int.toNat 1 then
        let v := x.appArg!
        match ← decide (← mkAppM ``LE.le #[mkIntLit 0, v]) with
        | some h => pure (some (mkApp (mkConst ``toNatAtom) v, ← mkAppM ``toNatAtom_eq #[h]))
        | none => pure none
      else
        let (a, b) := (args[args.size - 2]!, args[args.size - 1]!)
        if x.isAppOfArity ``HSub.hSub 6 then
          match ← decide (← mkAppM ``LE.le #[b, a]) with
          | some h => pure (some (mkApp2 (mkConst ``subAtom) a b, ← mkAppM ``subAtom_add #[h]))
          | none =>
            -- truncated to zero
            match ← decide (← mkAppM ``LE.le #[a, b]) with
            | some h => pure (some (mkApp2 (mkConst ``subAtom) a b, ← mkAppM ``subAtom_zero #[h]))
            | none => pure none
        else
          let isMin := x.isAppOfArity ``Min.min 4
          let c := if isMin then ``minAtom else ``maxAtom
          match ← decide (← mkAppM ``LE.le #[a, b]) with
          | some h => pure (some (mkApp2 (mkConst c) a b,
              ← mkAppM (if isMin then ``minAtom_left else ``maxAtom_right) #[h]))
          | none =>
            match ← decide (← mkAppM ``LE.le #[b, a]) with
            | some h => pure (some (mkApp2 (mkConst c) a b,
                ← mkAppM (if isMin then ``minAtom_right else ``maxAtom_left) #[h]))
            | none => pure none
    match r with
    | some (atom, d) =>
      atomsRef.modify fun (m, defs) => (m.insert x atom, defs.push d)
      return .done atom
    | none => return .continue)
  -- twice: a fact made linear joins the base that decides the split terms of the others
  let mut cur := arith
  for _ in [0:2] do
    let mut next : Array (Expr × Expr) := #[]
    for (f, t) in cur do
      if isLinearProp t then next := next.push (f, t); continue
      let t' ← rw t
      let f' ← if t' == t then pure f else mkExpectedTypeHint f t'
      if isLinearProp t' then linRef.modify (·.push f')
      next := next.push (f', t')
    cur := next
  let facts' := cur.map (·.1)
  let ty' ← rw ty
  let (_, defs) ← atomsRef.get
  let some pf ← omegaRaw (facts' ++ defs) ty' | return none
  return some (← mkExpectedTypeHint pf ty)

/-- The subterms `a &&& b` of natural numbers in `e`. -/
partial def natAnds (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.isAppOfArity ``HAnd.hAnd 6 && (e.getArg! 0).isConstOf ``Nat && !acc.contains e
      then acc.push e else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The literal powers of two `L` of the remainders `z % L` of natural numbers in `e`. -/
partial def litPowMods (e : Expr) : Array Nat :=
  go e #[]
where
  go (e : Expr) (acc : Array Nat) : Array Nat :=
    let acc := if e.isAppOfArity ``HMod.hMod 6 && (e.getArg! 0).isConstOf ``Nat then
        match e.appArg!.nat? with
        | some c => if c > 1 && c &&& (c - 1) == 0 && !acc.contains c then acc.push c else acc
        | none => acc
      else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The widths `w` of the terms `x.toNat` (`x : BitVec w`, `w` a literal) of `e`. -/
partial def bvWidths (e : Expr) : Array Nat :=
  go e #[]
where
  go (e : Expr) (acc : Array Nat) : Array Nat :=
    let acc := if e.isAppOfArity ``BitVec.toNat 2 then
        match (e.getArg! 0).nat? with
        | some w => if acc.contains w then acc else acc.push w
        | none => acc
      else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- Facts for `omega` about the symbolic powers of two `2 ^ x` of the target and the facts,
which `omega` treats as atoms: `0 < 2 ^ x`; `2 ^ x < 2 ^ c` from `x < c` (`c` a literal); a mask
`a &&& b` with `b = 2 ^ x - 1` (`a % 2 ^ x`) or, for a word `a` of width `w`,
`b = 2 ^ w - 2 ^ x` (`a - a % 2 ^ x`), by `omega`; and for a remainder `z % 2 ^ x`: it is below
`2 ^ x` and at most `z`, `z - z % 2 ^ x` is a multiple, and it is `z` (`z < 2 ^ x`) or `0`
(`z = 2 ^ x`) where `omega` shows so. Returns the new facts. -/
def extraFacts (facts : Array Expr) (tgt : Expr) : MetaM (Array Expr) := do
  let mut srcs := #[tgt]
  for f in facts do srcs := srcs.push (← instantiateMVars (← inferType f))
  let mut pows := #[]
  let mut ands := #[]
  -- the widths of the words in scope (`2 ^ w - 2 ^ x` masks)
  let mut widths : Array Nat := #[]
  for e in srcs do
    for x in (powTerms e).1 do unless pows.contains x do pows := pows.push x
    for x in natAnds e do unless ands.contains x do ands := ands.push x
    for w in bvWidths e do unless widths.contains w do widths := widths.push w
  let mut out : Array Expr := #[]
  for p in pows do
    let x := p.getAppArgs[5]!
    out := out.push (← mkAppM ``Nat.two_pow_pos #[x])
    -- `2 ^ x ≤ c` for a literal `c`: `x ≤ log2 c`
    for f in facts do
      let ty ← instantiateMVars (← inferType f)
      unless ty.isAppOfArity ``LE.le 4 && ty.appFn!.appArg! == p do continue
      let some c := ty.appArg!.nat? | continue
      let j := c.log2
      let hc ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit c, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit (j + 1)]])
      out := out.push (← mkAppOptM ``le_of_two_pow_le #[x, mkNatLit c, mkNatLit j, f, hc])
    for f in facts do
      let ty ← instantiateMVars (← inferType f)
      let lt := ty.isAppOfArity ``LT.lt 4
      unless lt || ty.isAppOfArity ``LE.le 4 do continue
      unless ty.appFn!.appArg! == x do continue
      let some c := ty.appArg!.nat? | continue
      let lit := mkNatLit (2 ^ c)
      let pf ← if lt then mkAppM ``Nat.pow_lt_pow_right #[← mkAppM ``Nat.one_lt_two #[], f]
        else mkAppM ``Nat.pow_le_pow_right #[← mkAppM ``Nat.two_pos #[], f]
      out := out.push (← mkExpectedTypeHint pf (← mkAppM (if lt then ``LT.lt else ``LE.le) #[p, lit]))
  -- masks
  for t in ands do
    let a := t.appFn!.appArg!
    let b := t.appArg!
    -- a literal high mask `2 ^ w - 2 ^ j`
    if let some bv := b.nat? then
      if bv > 0 then
        let j := Id.run do
          let mut j := 0
          while (bv >>> j) % 2 == 0 do j := j + 1
          return j
        let sum := bv + 2 ^ j
        if sum &&& (sum - 1) == 0 then
          let w := sum.log2
          let base := facts ++ out
          if let some ha ← omegaFacts base (← mkAppM ``LT.lt #[a, mkNatLit (2 ^ w)]) then
            let hj ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit j, mkNatLit w])
            let hb ← mkDecideProof (← mkEq b (← mkAppM ``HSub.hSub #[
              ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit w], ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit j]]))
            out := out.push (← mkAppOptM ``land_high #[a, b, mkNatLit j, mkNatLit w, ha, hj, hb])
            continue
    for p in pows do
      let x := p.getAppArgs[5]!
      let base := facts ++ out
      let found ← probe (mkApp2 (mkConst `fsym.mask) t p) base.size do
        if let some h ← omegaFacts base (← mkEq b (← mkAppM ``HSub.hSub #[p, mkNatLit 1])) then
          pure (some (← mkAppOptM ``land_low #[a, b, x, h]))
        else
          let mut r := none
          for w in widths do
            let some hj ← omegaFacts base (← mkAppM ``LE.le #[x, mkNatLit w]) | continue
            let some h ← omegaFacts base (← mkEq b (← mkAppM ``HSub.hSub #[mkNatLit (2 ^ w), p])) | continue
            let some ha ← omegaFacts base (← mkAppM ``LT.lt #[a, mkNatLit (2 ^ w)]) | continue
            r := some (← mkAppOptM ``land_high #[a, b, x, mkNatLit w, ha, hj, h])
            break
          pure r
      if let some pf := found then out := out.push pf; break
  -- remainders by symbolic powers (also those the masks introduced)
  let mut mods := #[]
  for e in srcs ++ (← out.mapM inferType) do
    for x in (powTerms e).2 do unless mods.contains x do mods := mods.push x
  -- literal power-of-two moduli (`z % 4096`)
  let mut lits : Array Nat := #[]
  for e in srcs do
    for c in litPowMods e do
      unless lits.contains c do lits := lits.push c
  for m in mods do
    let z := m.appFn!.appArg!
    let M := m.appArg!
    -- through a larger literal power of two `L = 2 ^ c` (`x ≤ c`): `z % 2 ^ x = z % L % 2 ^ x`
    for L in lits do
      let c := L.log2
      let x := M.getAppArgs[5]!
      let base := facts ++ out
      let some hx ← probe (mkApp2 (mkConst `fsym.modlit) m (mkNatLit L)) base.size
          (omegaFacts base (← mkAppM ``LE.le #[x, mkNatLit c])) | continue
      let hM ← mkDecideProof (← mkEq (mkNatLit L) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit c]))
      out := out.push (← mkAppOptM ``mod_pow_of_le #[z, x, mkNatLit c, mkNatLit L, hM, hx])
      out := out.push (← mkAppM ``Nat.mod_le #[← mkAppM ``HMod.hMod #[z, mkNatLit L], M])
    let pos ← mkAppM ``Nat.two_pow_pos #[M.getAppArgs[5]!]
    out := out.push (← mkAppM ``Nat.mod_lt #[z, pos])
    out := out.push (← mkAppM ``Nat.mod_le #[z, M])
    out := out.push (← mkAppM ``sub_mod_self_mod #[z, M])
    let base := facts ++ out
    let r ← probe (mkApp (mkConst `fsym.mod) m) base.size do
      if let some h ← omegaFacts base (← mkAppM ``LT.lt #[z, M]) then
        return some (← mkAppM ``Nat.mod_eq_of_lt #[h])
      if let some h ← omegaFacts base (← mkEq z M) then
        return some (← mkAppM ``mod_eq_zero_of_eq #[h])
      return none
    if let some pf := r then out := out.push pf
  return out

/-- `t % M = c` from a fact `u % M = c` with `t = u` (by `omega`): `omega` treats a remainder by
a symbolic `M` as an atom. -/
def modCongr (facts : Array Expr) (tgt : Expr) : MetaM (Option Expr) := do
  let some (_, l, c) := tgt.eq? | return none
  unless l.isAppOfArity ``HMod.hMod 6 && (l.getArg! 0).isConstOf ``Nat do return none
  let M := l.appArg!
  let tt := l.appFn!.appArg!
  for f in facts do
    let ty ← instantiateMVars (← inferType f)
    let some (_, l2, c2) := ty.eq? | continue
    unless l2.isAppOfArity ``HMod.hMod 6 && l2.appArg! == M && c2 == c do continue
    let u := l2.appFn!.appArg!
    let some e ← omegaFacts facts (← mkEq tt u) | continue
    let fn ← withLocalDeclD `x (mkConst ``Nat) fun x => do mkLambdaFVars #[x] (← mkAppM ``HMod.hMod #[x, M])
    let e1 ← mkExpectedTypeHint (← mkCongrArg fn e) (← mkEq l l2)
    return some (← mkEqTrans e1 f)
  return none



/-- The simp context of the arithmetic solver: `fsym_arith` with its simprocs and Lean's. -/
def arithSimpCtx : MetaM (Simp.Context × Simp.SimprocsArray) := do
  if let some c ← (← caches).ctx.get then return c
  let c ← arithSimpCtxCore
  (← caches).ctx.set (some c)
  return c
where arithSimpCtxCore : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let some ext ← getSimpExtension? `fsym_arith | throwError "fsym: no fsym_arith"
  let mut thms ← ext.getTheorems
  -- conditional rewrites (side conditions by `omegaDisch`): no wrap-around first
  for n in [``Zig.toNat_add_of_lt, ``Zig.toNat_sub_of_le, ``BitVec.toNat_mul_of_lt, ``toNat_ofNat_nowrap,
      ``toNat_ofInt_nowrap] do
    thms ← thms.addConst n (prio := 10000)
  for n in [``pow_mod_elim, ``Nat.mod_eq_of_lt, ``Int.emod_eq_of_lt, ``sub_wrap, ``Int.toNat_add,
      ``Int.toNat_add_nat, ``Nat.add_zero, ``Nat.zero_add, ``Int.add_zero, ``Int.zero_add, ``Int.one_mul,
      ``Int.mul_one, ``Nat.div_one, ``Nat.mod_one, ``Nat.min_self, ``Nat.max_self, ``Nat.add_sub_add_left,
      ``Nat.add_sub_add_right, ``Decidable.not_not, ``Bool.not_eq_false, ``beq_eq_false_iff_ne,
      ``bne_eq_false_iff_eq, ``ne_eq, ``eq_self, ``iff_self] do
    thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let mut procs : Simp.SimprocsArray := #[← Simp.getSimprocs]
  if let some pe ← Simp.getSimprocExtension? `fsym_arith then procs := procs.push (← pe.getSimprocs)
  return (ctx, procs)


/-- The discharger of the arithmetic simp set (no wrap-around, `pow_mod_elim`, …): the bound of
a word, else the side goal in normal form by `omega` from the current facts (`dischFacts`);
cached. -/
def omegaDisch : Simp.Discharge := fun e => do
  let r : MetaM (Option Expr) := do
    let e ← instantiateMVars e
    let lctx ← getLCtx
    if let some (some pf) := (← (← caches).disch.get).get? e then
      if !pf.hasAnyFVar (fun f => !lctx.contains f) then return some pf
    let facts ← (← caches).facts.get
    let out ← do
      -- `x.toNat < 2 ^ w`
      let wordBound : MetaM (Option Expr) := do
        unless e.isAppOfArity ``LT.lt 4 do return none
        let x := e.appFn!.appArg!
        unless x.isAppOfArity ``BitVec.toNat 2 do return none
        let pf ← mkAppM ``BitVec.isLt #[x.appArg!]
        if ← isDefEq (← inferType pf) e then return some pf else return none
      match ← wordBound with
      | some pf => pure (some pf)
      | none =>
        let (ctx, procs) ← arithSimpCtx
        let (r, _) ← simp e ctx procs
        if r.expr.isTrue then
          match r.proof? with
          | some eq => pure (some (← mkOfEqTrue eq))
          | none => pure (some (mkConst ``True.intro))
        else
          let extra ← extraFacts facts r.expr
          match ← omegaFacts (facts ++ extra) r.expr with
          | none => pure none
          | some pf => match r.proof? with
            | some eq => pure (some (← mkEqMPR eq pf))
            | none => pure (some pf)
    if let some pf := out then (← caches).disch.modify (·.insert e (some pf))
    return out
  r

/-- The facts of the current context: its hypotheses in normal form, each normalized with the
facts before it (`none`: a hypothesis normalized to `False`, with its proof). -/
def normFacts : MetaM (Array Expr × Option Expr) := do
  let (ctx, procs) ← arithSimpCtx
  let mut facts : Array Expr := #[]
  let lctx ← getLCtx
  -- a cached proof is reused only where its free variables are in scope (`cases` and `subst`
  -- reintroduce the hypotheses it may use)
  let inScope : Option (Expr × Expr) → Bool
    | some (_, pf) => !pf.hasAnyFVar (fun f => !lctx.contains f)
    | none => true
  for d in ← propHyps do
    let r ← match (← (← caches).hyp.get).get? d.fvarId with
      | some r => if inScope r then pure r else normHyp ctx procs facts d
      | none => normHyp ctx procs facts d
    match r with
    | none => facts := facts.push d.toExpr
    | some (t, pf) =>
      if t.isFalse then return (facts, some pf)
      unless t.isTrue do facts := facts.push pf
  return (facts, none)
where normHyp (ctx : Simp.Context) (procs : Simp.SimprocsArray) (facts : Array Expr) (d : LocalDecl) :
    MetaM (Option (Expr × Expr)) := do
  let ty ← instantiateMVars d.type
  (← caches).facts.set facts
  let (r, _) ← simp ty ctx procs (discharge? := some omegaDisch)
  let out ← if r.expr == ty then pure none else
    match r.proof? with
    | some pf => pure (some (r.expr, ← mkEqMP pf d.toExpr))
    | none => pure (some (r.expr, ← mkExpectedTypeHint d.toExpr r.expr))
  (← caches).hyp.modify (·.insert d.fvarId out)
  return out

/-- Close `g` by a hypothesis whose type is the target up to reducible unfolding and instances
(`assumption` unfolds at default transparency: a failed match of terms such as `bs ++ t` or
`(n + 4095) / 4096` unfolds the operations; what it would find beyond reducible unfolding the
arithmetic solver finds from the normalized facts). -/
def assumptionR (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← withReducibleAndInstances (isDefEq d.type t) then
      g.assign d.toExpr; return true
  return false

/-- The arithmetic solver on one goal: its hypotheses as facts in `fsym_arith` normal form
(values of words and pointers as natural numbers, no wrap-around where it cannot happen, user
definitions of values unfolded), the target in normal form, facts about symbolic powers of two
and masks (`extraFacts`), then `omega`; unless `quick`, also the congruence of remainders
(`modCongr`). -/
def arithCore (g : MVarId) (quick := false) : TacticM Bool := g.withContext do
  if ← assumptionR g then return true
  let s ← saveState
  try
    let tgt0 ← instantiateMVars (← g.getType)
    let h0 ← IO.getNumHeartbeats
    let (facts, ff) ← normFacts
    trace[fsym.prof] "normFacts {((← IO.getNumHeartbeats) - h0) / 1000}"
    if let some f := ff then
      g.assign (← mkFalseElim tgt0 f); return true
    (← caches).facts.set facts
    let (ctx, procs) ← arithSimpCtx
    let (r, _) ← simp tgt0 ctx procs (discharge? := some omegaDisch)
    let close (pf : Expr) : MetaM Unit := do
      match r.proof? with
      | some eq => g.assign (← mkEqMPR eq pf)
      | none => g.assign (← mkExpectedTypeHint pf tgt0)
    if r.expr.isTrue then close (mkConst ``True.intro); return true
    let h0 ← IO.getNumHeartbeats
    let extra ← extraFacts facts r.expr
    let all := facts ++ extra
    trace[fsym.prof] "extra {((← IO.getNumHeartbeats) - h0) / 1000} facts {facts.size}+{extra.size}"
    trace[fsym.arith] "omega {r.expr} from {← all.mapM fun f => inferType f}"
    let h1 ← IO.getNumHeartbeats
    let ok ← omegaFacts all r.expr
    trace[fsym.prof] "omegaT {((← IO.getNumHeartbeats) - h1) / 1000} {ok.isSome}"
    if let some pf := ok then close pf; return true
    unless quick do
      if let some pf ← modCongr all r.expr then close pf; return true
    s.restore; return false
  catch ex =>
    trace[fsym.arith] "exception {ex.toMessageData}"
    s.restore; return false

/-- The arithmetic solver; a conjunction (also behind a user definition) is split. Returns the
goals it did not prove. `quick`: a probe (no congruence of remainders, no library facts). -/
partial def arithGoals (g : MVarId) (quick := false) : TacticM (List MVarId) := g.withContext do
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
    return (← arithGoals g1 quick) ++ (← arithGoals g2 quick)
  if !t.hasFVar && !t.hasMVar then
    if ← closeWith g (← `(tactic| decide)) then return []
  if let some (_, x, y) := t.eq? then
    if ← withReducible (isDefEq x y) then g.assign (← mkEqRefl x); return []
  -- `x ≤ x` (a carved region that starts where the state's does)
  if t.isAppOfArity ``LE.le 4 then
    let ty := t.getArg! 0
    if ty.isConstOf ``Nat || ty.isConstOf ``Int then
      if ← withReducible (isDefEq (t.getArg! 2) (t.getArg! 3)) then
        g.assign (← mkAppM (if ty.isConstOf ``Nat then ``Nat.le_refl else ``Int.le_refl) #[t.getArg! 2])
        return []
  if ← arithCore g quick then return []
  unless quick do
    if ← closeWith g (← `(tactic| fsym_fact)) then return []
  return [g]

def arith (g : MVarId) (quick := false) : TacticM Bool := g.withContext do
  -- cached per run: a proof where its free variables are in scope; a failure in the same
  -- context (the same last hypothesis)
  let t ← instantiateMVars (← g.getType)
  let lctx ← getLCtx
  let last := (lctx.lastDecl.map (·.fvarId.name)).getD .anonymous
  let posKey := mkApp (mkConst `fsym.arith) t
  let negKey := mkApp3 (mkConst `fsym.arithNo) t (toExpr quick) (toExpr last)
  let cacheable := !t.hasMVar
  if cacheable then
    match (← (← caches).probe.get).get? posKey with
    | some (.inl pf) => if !pf.hasAnyFVar (fun f => !lctx.contains f) then g.assign pf; return true
    | _ => pure ()
    if ((← (← caches).probe.get).get? negKey).isSome then return false
  let s ← saveState
  let h0 ← IO.getNumHeartbeats
  let ok := (← arithGoals g quick).isEmpty
  trace[fsym.prof] "arith {((← IO.getNumHeartbeats) - h0) / 1000} {ok} {quick}: {t}"
  if ok then
    if cacheable then
      let pf ← instantiateMVars (.mvar g)
      unless pf.hasExprMVar do (← caches).probe.modify (·.insert posKey (.inl pf))
    return true
  s.restore
  if cacheable then (← caches).probe.modify (·.insert negKey (.inr 0))
  return false

/-- `fsym_arith`: the arithmetic solver (`arith`) as a tactic; within a run of `fsym` with the
run's caches, else with its own. -/
elab "fsym_arith" : tactic => do
  let g ← getMainGoal
  let inRun := (← getOptions).get `fsym.run (0 : Nat) != 0
  let ok ← if inRun then arithCore g else withRunCaches do
    discard <| arithSimpCtx
    arith g
  unless ok do throwError "fsym_arith: not proved"
  replaceMainGoal []

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
  -- `(p.add k).block = p.block`: definitional
  if let some (_, l, r) := t.eq? then
    if !l.hasExprMVar && !r.hasExprMVar && r.isAppOf ``Zig.Ptr.block then
      let s ← saveState
      if ← isDefEq l r then return some (← mkEqRefl l)
      s.restore
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

/-- The provider lemmas (`@[fsym_provider]`) whose conclusion is an application of `k`. -/
def providerLemmas (k : Name) : MetaM (Array Name) := do
  (fsymProviderExt.getState (← getEnv)).filterM fun n => do
    return (← getConstInfo n).type.getForallBody.isAppOf k

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
    for n in ← providerLemmas (if isAddr then ``AddrOf else ``Reaches) do
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

/-- The inductive type `tn` if it has several constructors (a type to split by cases). -/
def caseInduct? (tn : Name) : MetaM (Option InductiveVal) := do
  let some (.inductInfo ii) := (← getEnv).find? tn | return none
  return if ii.ctors.length ≥ 2 then some ii else none

/-- `e` is an application of a constructor of an inductive type with several constructors other
than `Bool` and `Nat` (an optional, an error union, an enumeration): `Bool` tests go through `if`,
and `Nat` constructors are arithmetic (literals, `n + 1`), which `fsym_arith` reads. -/
def isCaseCtorApp (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  let some (.ctorInfo ci) := (← getEnv).find? c | return false
  if ci.induct == ``Bool || ci.induct == ``Nat then return false
  return (← caseInduct? ci.induct).isSome

mutual
/-- A fact `t = C …` of a term `t` that is not a variable (a field of the locals, of a witness)
and a constructor application: `t` is replaced by `C …` in the goal and in the other facts,
which are split again, so a `match` on `t` (in the precondition, in a fact) reduces. `none` if
there is nothing to do or the goal does not abstract over `t`. -/
partial def substCtor (g : MVarId) (h : FVarId) (l r : Expr) : TacticM (Option MVarId) := g.withContext do
  let (t, symm) ← if (← isCaseCtorApp r) && !(← isCaseCtorApp l) then pure (l, false)
    else if (← isCaseCtorApp l) && !(← isCaseCtorApp r) then pure (r, true)
    else return none
  -- a field of the locals or of a witness; not a library term (`p.block = some b` is a block fact)
  if let .const c _ := t.getAppFn then
    if ← isLibrary c then return none
  let has (e : Expr) : MetaM Bool := do return ((← instantiateMVars e).find? (· == t)).isSome
  let mut fs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.fvarId == h then continue
    if (← isProp d.type) && (← has d.type) then fs := fs.push d.fvarId
  if fs.isEmpty && !(← has (← g.getType)) then return none
  let s ← saveState
  try
    let (rev, g1) ← g.revert fs (preserveOrder := true)
    let res ← g1.rewrite (← g1.getType) (mkFVar h) symm
    let g2 ← g1.replaceTargetEq res.eNew res.eqProof
    let (xs, g3) ← g2.introNP rev.size
    let mut g := g3
    for x in xs do
      if (← g.withContext x.findDecl?).isSome then g ← destruct g x
    return some g
  catch ex =>
    trace[fsym] "substCtor {t}: {ex.toMessageData}"
    s.restore; return none

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
    if let some g' ← substCtor g h l r then return g'
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
end

/-- The pointer that `p` is derived from by `Ptr.add`/`elem`/`elemSub`/`elemOf`/`elemSubOf`
(same block, `block_add`). -/
partial def ptrBase (p : Expr) : Expr :=
  let p := p.consumeMData
  if p.isAppOfArity ``Zig.Ptr.add 2 || p.isAppOfArity ``Zig.Ptr.elem 3 || p.isAppOfArity ``Zig.Ptr.elemSub 3 ||
      p.isAppOfArity `Zig.Ptr.elemOf 4 || p.isAppOfArity `Zig.Ptr.elemSubOf 4 then
    ptrBase (p.getArg! 0) else p

/-- One block variable per block: from `x.block = some b₁` and `y.block = some b₂` with
`x.block = y.block` (definitionally, also through `Ptr.add`/`Ptr.elem`, or by a fact), `b₂` is
replaced by `b₁`. -/
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
        else if ptrBase l1.appArg! == ptrBase l2.appArg! then
          pure (some (← mkExpectedTypeHint (← mkEqRefl l1) (← mkEq l1 l2)))
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

/-- `if c then X else Y` of assertions where the facts decide `c`: `(X or Y, proof of the
equation)`. An undecided condition is retried only once there are more facts. -/
def decideIte (a : Expr) (quick := true) : TacticM (Option (Expr × Expr)) := do
  let args := a.getAppArgs
  let (c, inst, x, y) := (args[1]!, args[2]!, args[3]!, args[4]!)
  let n ← ctxStamp (← propHyps).size
  let key := mkApp (mkConst `fsym.ite) c
  if let some (.inr m) := (← (← caches).probe.get).get? key then
    if n == m then return none
  let hp ← mkFreshExprMVar c
  if ← arith hp.mvarId! quick then
    return some (← mkAppOptM ``ite_pos_eq #[c, inst, ← instantiateMVars hp, x, y], x)
  let hn ← mkFreshExprMVar (mkNot c)
  if ← arith hn.mvarId! quick then
    return some (← mkAppOptM ``ite_neg_eq #[c, inst, ← instantiateMVars hn, x, y], y)
  (← caches).probe.modify (·.insert key (.inr n))
  return none

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
  -- an assertion-level `if` whose condition the facts decide: take its branch
  for a in ats do
    unless a.isAppOfArity ``ite 5 do continue
    let some (pf, br) ← decideIte a | continue
    let f ← withLocalDeclD `x (mkConst ``Zig.Full.FAssn) fun x => do
      mkLambdaFVars #[x] (Pu.replace fun y => if y == a then some x else none)
    let P' := (mkApp f br).headBeta
    let e ← mkExpectedTypeHint (← mkCongrArg f pf) (← mkEq P P')
    let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α P' c Q)
    g.assign (← mkAppOptM (L.nm ``pre_eq) #[L.L, α, P, P', Q, c, e, g2])
    return ← normPre g2.mvarId! (fuel - 1)
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
    let pf ← mkAppOptM (L.nm ``pre_eq) #[L.L, none, P, P2, Q, c, ← mkExpectedTypeHint e (← mkEq P P2), g2]
    g.assign pf
    pure g2.mvarId!
  if facts.isEmpty then return ← unifyBlocks g
  let a := facts[0]!
  if a.isAppOfArity liftN 1 then
    let [g'] ← evalTacticAt (← `(tactic| refine $(mkIdent (L.nm ``lift_sep)) _ fun h => ?_)) g
      | throwError "fsym: lift"
    let lctx ← g'.withContext getLCtx
    let g' ← match lctx.lastDecl with
      | some d => destruct g' d.fvarId
      | none => pure g'
    normPre g' (fuel - 1)
  else
    let n := match a.appArg!.consumeMData with | .lam n .. => n | _ => `x
    let [g'] ← evalTacticAt (← `(tactic| refine $(mkIdent (L.nm ``ex_sep)) _ fun x => ?_)) g
      | throwError "fsym: ex"
    let lctx ← g'.withContext getLCtx
    let g' ← match lctx.lastDecl with
      | some d => g'.rename d.fvarId n
      | none => pure g'
    normPre g' (fuel - 1)

/-! ## Programs -/

/-- `(f, c)` of the condition `(f == c) = true` of pointers (a generated indirect call's test). -/
def ptrBeq? (cond : Expr) : Option (Expr × Expr) := do
  let cond := cond.consumeMData
  guard (cond.isAppOfArity ``Eq 3 && (cond.getArg! 2).isConstOf ``Bool.true)
  let b := cond.getArg! 1
  guard (b.isAppOfArity ``BEq.beq 4 && (b.getArg! 0).isConstOf ``Zig.Ptr)
  return (b.getArg! 2, b.getArg! 3)

/-- Simp methods that normalize only the **head** of a program, so that a step costs the same on
a large generated body as on a small one. At `x >>= f` only `x` is simplified and the node is
rewritten (`bind_assoc`, `pure_bind`, `ite_bind`, …); the continuation `f` is left as it is (it is
normalized once it is the head: `pure_bind` makes it the head of the result, which simp visits).
`fold?` (concurrent bodies): a generated indirect call `if f == c₁ then x₁ else …` is folded into
`callIndirect` (`callIndirect_fold_one`/`cons`) at its `if`, before simp rewrites its tests. -/
def lazyMethods (procs : Simp.SimprocsArray) (fold? : Option Simp.Context) : Simp.Methods :=
  let m := Simp.mkDefaultMethodsCore procs
  let mFold := Simp.mkDefaultMethodsCore #[]
  /- The node `r₀.expr` rewritten at its root (`post`), else done. -/
  let finish (r₀ : Simp.Result) : Simp.SimpM Simp.Step := do
    match ← m.post r₀.expr with
    | .done r => return .done (← r₀.mkEqTrans r)
    | .visit r | .continue (some r) =>
      if r.expr == r₀.expr then return .done r₀ else return .visit (← r₀.mkEqTrans r)
    | .continue none => return .done r₀
  { m with pre := fun e => do
      let isIte := e.isAppOfArity ``ite 5
      unless isIte || e.isAppOfArity ``Bind.bind 6 do return ← m.pre e
      if isIte then
        if let some fold := fold? then
          if (ptrBeq? (e.getArg! 1)).isSome then
            let (r, _) ← Simp.main e fold (methods := mFold)
            if r.expr != e then return .visit r
      match ← m.pre e with
      | .continue none => pure ()
      | s => return s
      let args := e.getAppArgs
      if isIte then
        -- only the condition: the walk takes a branch, normalized at the next step
        let rc ← Simp.simp args[1]!
        if rc.expr == args[1]! then return ← finish { expr := e }
        try
          let pf ← mkAppM ``ite_congr #[← rc.getProof, ← mkConstFun rc.expr args[3]!,
            ← mkConstFun (mkNot rc.expr) args[4]!]
          finish { expr := (← inferType pf).appArg!, proof? := some pf }
        catch _ => m.pre e
      else
        -- only the command: the continuation is normalized once it is the head
        let rx ← Simp.simp args[4]!
        finish (← Simp.mkCongrFun (← Simp.mkCongrArg (mkAppN e.getAppFn args[:4]) rx) args[5]!) }
where
  /-- `fun _ : p => rfl : ∀ _ : p, x = x`. -/
  mkConstFun (p x : Expr) : MetaM Expr := do
    withLocalDeclD `h p fun h => do mkLambdaFVars #[h] (← mkEqRefl x)

/-- Simplify the head of the program (`lazyMethods`) with `fsym_norm` and the caller's lemmas. -/
def simpProg (g : MVarId) (extra : Array Syntax) : TacticM MVarId := g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let (ctx, procs) ← match ← (← caches).prog.get with
    | some cp => pure cp
    | none => do
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
      -- Lean's simprocs, without the word complement of a literal: its value would make the
      -- program equal to the folded one only by a deep unfolding in the kernel
      let mut procs : Simp.SimprocsArray := #[(← Simp.getSimprocs).erase ``BitVec.reduceNot]
      if let some pe ← Simp.getSimprocExtension? `fsym_norm then procs := procs.push (← pe.getSimprocs)
      (← caches).prog.set (some (ctx, procs))
      pure (ctx, procs)
  let foldCtx : MetaM Simp.Context := do
    if let some f ← (← caches).fold.get then return f
    let thms ← ({} : SimpTheorems).addConst ``Full.callIndirect_fold_one
    let thms ← thms.addConst ``Full.callIndirect_fold_cons
    let f ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    (← caches).fold.set (some f); return f
  let fold? ← if L.conc then some <$> foldCtx else pure none
  let (r, _) ← Simp.main c ctx (methods := lazyMethods procs fold?)
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
  if x.isAppOfArity ``StateT.lift 5 || x.isAppOfArity ``ConcM.liftMem 3 then
    let y := x.appArg!
    let some y' ← unfoldCmd y | return none
    return some (mkApp x.appFn! y')
  let .const c _ := x.getAppFn | return none
  if (← getProjectionFnInfo? c).isSome then return ← unfold1 x
  if ← isLibrary c then return none
  unfold1 x

def isThrow (c : Expr) : Bool :=
  c.isAppOf ``MonadExcept.throw || c.isAppOf ``MonadExceptOf.throw || c.isAppOf ``throwThe

/-! ## Returns -/

/-- `Q` with its existentials opened by fresh witnesses: `(Qi, pf : ∀ r, Qi r → Q r)`. -/
partial def instQ (e : Expr) (fuel : Nat := 64) : TacticM (Expr × Expr) := do
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
  if e.isAppOfArity ``ite 5 then
    let some (pf, br) ← decideIte e false | return (e, ← refl e)
    let (b, pb) ← instQ br (fuel - 1)
    return (b, ← mkAppM ``imp_trans #[pb, ← mkAppM ``imp_eq #[← mkEqSymm pf]])
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

/-- `∀ r, x r → y r`. -/
def mkImp' (x y : Expr) : MetaM Expr :=
  withLocalDeclD `r (mkConst ``Zig.Full.Res) fun r => do
    mkForallFVars #[r] (← mkArrow (mkApp x r) (mkApp y r))

/-- Prove `x = y`: pointers by block and offset, numbers by arithmetic, applications of one
function by congruence (one level at a time). -/
partial def proveEqGoal (g : MVarId) (depth : Nat := 2) (fuel : Nat := 12) : TacticM Bool := g.withContext do
  if fuel == 0 then return false
  let t ← instantiateMVars (← g.getType)
  let some (ty, x, y) := t.eq? | return false
  if ← withReducibleAndInstances (isDefEq x y) then
    g.assign (← mkEqRefl x); return true
  -- an equation of the context, either way round
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
    if (← withReducible (isDefEq l x)) && (← withReducible (isDefEq r y)) then
      g.assign d.toExpr; return true
    if (← withReducible (isDefEq l y)) && (← withReducible (isDefEq r x)) then
      g.assign (← mkEqSymm d.toExpr); return true
  -- an equation under an arithmetic premise of the context
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isArrow do continue
    let some (_, l, r) := ty.bindingBody!.eq? | continue
    let flip ← if (← withReducible (isDefEq l x)) && (← withReducible (isDefEq r y)) then pure false
      else if (← withReducible (isDefEq l y)) && (← withReducible (isDefEq r x)) then pure true
      else continue
    let hφ ← mkFreshExprMVar ty.bindingDomain!
    trace[fsym] "eq: premise {ty.bindingDomain!}"
    unless ← arith hφ.mvarId! (quick := true) do continue
    trace[fsym] "eq: premise proved"
    let e := mkApp d.toExpr (← instantiateMVars hφ)
    g.assign (← if flip then mkEqSymm e else pure e); return true
  -- through an equation `l = y` of the context: `x = l` (of a type without arithmetic)
  if depth > 0 then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
      for (l, r, flip) in [(l, r, false), (r, l, true)] do
        unless ← withReducible (isDefEq r y) do continue
        if l == x then continue
        let s ← saveState
        let m ← mkFreshExprMVar (← mkEq x l)
        if ← proveEqGoal m.mvarId! (depth - 1) (fuel - 1) then
          let e ← if flip then mkEqSymm d.toExpr else pure d.toExpr
          g.assign (← mkEqTrans (← instantiateMVars m) e); return true
        s.restore
  let ty ← whnfR ty
  if ty.isConstOf ``Zig.Ptr then
    return ← closeWith g (← `(tactic| (apply Zig.Full.Auto.ptr_ext' <;>
      first | rfl | fsym_arith | (simp only [fsym_arith] at *; simp only [*]))))
  if ty.isConstOf ``Nat || ty.isConstOf ``Int then return ← arith g (quick := true)
  if ty.isAppOfArity ``BitVec 1 then
    if ← closeWith g (← `(tactic| (apply BitVec.eq_of_toNat_eq; fsym_arith))) then return true
  let (fx, fy) := (x.getAppFn, y.getAppFn)
  unless fx.isConst && fx == fy && x.getAppNumArgs == y.getAppNumArgs do return false
  let s ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| congr 1)) g
    for g' in gs do
      unless ← proveEqGoal g' depth (fuel - 1) do s.restore; return false
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
  return !q.hasExprMVar && !(← inferType q).isSort

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

/-- **A planner extension** (`@[fsym_plan]`): the assertion constants `heads` it plans (their
atoms are not pre-assigned by unification) and `run`, which rearranges the state for the
postcondition's atoms (by `St.step`). -/
structure Planner where
  heads : Array Name
  run : St → Array Expr → TacticM St

instance : Inhabited Planner := ⟨{ heads := #[], run := fun st _ => pure st }⟩

unsafe def evalPlannerUnsafe (n : Name) : TacticM Planner := evalConstCheck Planner ``Planner n

@[implemented_by evalPlannerUnsafe] opaque evalPlanner (n : Name) : TacticM Planner

/-- The registered planner extensions. -/
def planners : TacticM (Array Planner) := do
  (fsymPlanExt.getState (← getEnv)).mapM evalPlanner

def proveArith (ty : Expr) (quick := false) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  if ← arith m.mvarId! quick then return some (← instantiateMVars m)
  trace[fsym] "arith failed: {ty}"
  return none

def regionArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.FAssn.up 1 && e.appArg!.isAppOfArity ``Zig.regionIn 6 then
    some e.appArg!.getAppArgs else none

def shareArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.bshare 4 then some e.getAppArgs else none

/-- The authority over a block's extent: `bauth b S K q`, or `bext b S K` (`q = Frac.one`). -/
def authArgs? (e : Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``Zig.Full.bauth 4 then some e.getAppArgs
  else if e.isAppOfArity ``Zig.Full.bext 3 then some (e.getAppArgs.push (mkConst ``Zig.Full.Frac.one))
  else none

def mkAuth (b S K q : Expr) : Expr := mkAppN (mkConst ``Zig.Full.bauth) #[b, S, K, q]

/-- The state's authority over block `b`, as a `bauth` atom (a `bext` is restated). -/
def St.auth (st : St) (b : Expr) : TacticM (Option (St × Nat × Array Expr)) := do
  for i in [0:st.ats.size] do
    let some x := authArgs? st.ats[i]! | continue
    unless ← isDefEq x[0]! b do continue
    if st.ats[i]!.isAppOfArity ``Zig.Full.bauth 4 then return some (st, i, x)
    let y := mkAuth x[0]! x[1]! x[2]! x[3]!
    let e ← mkExpectedTypeHint (← mkEqRefl y) (← mkEq st.ats[i]! y)
    let st ← st.step #[i] #[y] (← mkAppM ``atom_eq #[e])
    return some (st, 0, x)
  return none

/-- An authority atom at index `i` restated with the fraction `q'` (`e : q = q'`). -/
def St.authEq (st : St) (i : Nat) (x : Array Expr) (q' e : Expr) : TacticM St := do
  let y := mkAuth x[0]! x[1]! x[2]! q'
  let h ← mkAppOptM ``auth_eq #[x[0]!, x[1]!, x[2]!, x[3]!, q', e]
  st.step #[i] #[y] (← mkAppM ``atom_eq #[h])

/-- A share `q` (bound `k`, untagged) out of the authority over its block: the authority's
fraction is `x + q` syntactically or by an equation of the context; an undetermined `q` takes
half of it. -/
def lendShare (st : St) (q : Array Expr) : TacticM (Option St) := do
  let s0 ← saveState
  try
    unless ← isDefEq q[3]! (← mkAppOptM ``Option.none #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]]) do
      throwError "tagged"
    let some (st, i, x) ← st.auth q[0]! | throwError "no authority"
    trace[fsym] "lend: authority {x}"
    let g := x[3]!
    let qf ← instantiateMVars q[1]!
    -- a fraction equal to `qf` whose positivity may be a fact
    let mut alt : Option (Expr × Expr) := none
    -- `g = rest + qf`
    let (st, rest, alt') ← if qf.isMVar then do
        let h := mkAppN (mkConst ``Zig.Full.Frac.half) #[g]
        qf.mvarId!.assign h
        let e ← mkEqSymm (← mkAppM ``Zig.Full.Frac.half_add_half #[g])
        pure (← st.authEq i x (← mkAppM ``Zig.Full.Frac.add #[h, h]) e, h, none)
      else if ← (pure (g.isAppOfArity ``Zig.Full.Frac.add 2) <&&> isDefEq g.appArg! qf) then
        pure (st, g.appFn!.appArg!, none)
      else do
        -- `x + q₀ = g` in the context, with `q₀ = qf`
        let mut found := none
        for d in ← getLCtx do
          if d.isImplementationDetail || found.isSome then continue
          let some (_, l, r) := (← instantiateMVars d.type).eq? | continue
          for (sum, other, flip) in [(l, r, true), (r, l, false)] do
            if found.isSome then continue
            unless sum.isAppOfArity ``Zig.Full.Frac.add 2 do continue
            unless ← withReducible (isDefEq other g) do continue
            trace[fsym] "lend: decompose {sum} = {other}"
            let some e₀ ← proveEq sum.appArg! qf | continue
            trace[fsym] "lend: decomposed"
            -- `g = x + q₀ = x + qf`
            let e1 ← if flip then mkEqSymm d.toExpr else pure d.toExpr
            let xr := sum.appFn!.appArg!
            let e ← mkEqTrans e1 (← mkCongrArg (mkApp (mkConst ``Zig.Full.Frac.add) xr) e₀)
            found := some (← mkAppM ``Zig.Full.Frac.add #[xr, qf], e, (sum.appArg!, e₀))
        let some (sum, e, a) := found | throwError "no decomposition"
        pure (← st.authEq i x sum e, sum.appFn!.appArg!, some a)
    trace[fsym] "lend: rest {rest}"
    let some (st, i, x) ← st.auth q[0]! | throwError "lost"
    let k ← instantiateMVars q[2]!
    let some hk ← proveArith (← mkAppM ``LE.le #[k, x[1]!]) | throwError "bound"
    let hq ← mkFreshExprMVar (← mkAppM ``LT.lt #[← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkNatLit 0, none],
      ← mkAppM ``Zig.Full.Frac.val #[qf]])
    alt := alt'
    unless ← closeWith hq.mvarId! (← `(tactic| fsym_fact)) do
      let some (q₀, e₀) := alt | throwError "positive"
      let h0 ← mkFreshExprMVar (← mkAppM ``LT.lt #[← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkNatLit 0, none],
        ← mkAppM ``Zig.Full.Frac.val #[q₀]])
      unless ← closeWith h0.mvarId! (← `(tactic| fsym_fact)) do throwError "positive"
      hq.mvarId!.assign (← mkAppM ``frac_pos_of_eq #[e₀, ← instantiateMVars h0])
    let h ← mkAppOptM ``auth_lend #[x[0]!, k, x[1]!, x[2]!, rest, qf, hk, ← instantiateMVars hq]
    let sh := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, qf, k, q[3]!]
    return some (← st.step #[i] #[mkAuth x[0]! x[1]! x[2]! rest, sh] h)
  catch ex =>
    trace[fsym] "lend: {ex.toMessageData}"
    s0.restore; return none

def mkRegion (p A S K a bs : Expr) : MetaM Expr := do
  return mkApp (mkConst ``Zig.Full.FAssn.up) (← mkAppM ``Zig.regionIn #[p, A, S, K, a, bs])

def offNat (p : Expr) : MetaM Expr := do mkAppM ``Int.toNat #[← mkAppM ``Zig.Ptr.off #[p]]

/-- `x = y` of byte arrays: `Array` lemmas, then sizes and indices by arithmetic. -/
def proveBytes (x y : Expr) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar (← mkEq x y)
  if ← closeWith m.mvarId! (← `(tactic| (simp only [Array.extract_append, Array.extract_extract,
      Array.extract_size, Array.append_empty, Array.extract_zero, Array.size_append, Array.size_extract,
      Nat.zero_add, Nat.sub_zero, Nat.sub_self, Nat.min_def] <;> first | rfl | (congr 1 <;> fsym_arith) | (simp <;> fsym_arith)))) then
    return some (← instantiateMVars m)
  return none

/-- `fun bs => up (regionIn p A S K a bs)` for the region `r`. -/
def mkLambdaFVarsBytes (_x : Expr) (r : Array Expr) : MetaM Expr := do
  withLocalDeclD `bs (← inferType r[5]!) fun v => do mkLambdaFVars #[v] (← mkRegion r[0]! r[1]! r[2]! r[3]! r[4]! v)

/-- Carve the region atom `q` of the postcondition (bytes possibly unknown; `n?` its size from a
fact) out of a region of the state: split at its start (with its alignment) and at its end. -/
def carve (st : St) (q : Array Expr) (n? : Option Expr) (claimed : Array Expr := #[]) :
    TacticM (Option (St × Expr)) := do
  let (qp, qA, qS, qK, qa, qbs) := (q[0]!, q[1]!, q[2]!, q[3]!, q[4]!, q[5]!)
  let some (qb, _) ← blockOf qp | return none
  for i in [0:st.ats.size] do
    if claimed.contains st.ats[i]! then continue
    let some r := regionArgs? st.ats[i]! | continue
    let s0 ← saveState
    let (p, A, S, K, a, bs) := (r[0]!, r[1]!, r[2]!, r[3]!, r[4]!, r[5]!)
    try
      let some (b, _) ← blockOf p | throwError "block"
      unless ← withReducible (isDefEq b qb) do throwError "block"
      unless ← withReducible (isDefEq qA A) do throwError "address"
      let mut st := st
      let mut i := i
      let mut r := r
      -- the size label and the kind up to its normal form are labels (`EUpd.relabel`)
      unless ← (withReducible (isDefEq qS S) <&&> withReducible (isDefEq qK K)) do
        let S' ← instantiateMVars qS
        let K' ← instantiateMVars qK
        if S'.hasExprMVar || K'.hasExprMVar then throwError "labels"
        let some hK ← proveEq (← mkAppM ``Zig.BlockKind.norm #[K']) (← mkAppM ``Zig.BlockKind.norm #[K])
          | throwError "kinds"
        let h ← mkAppOptM ``EUpd.relabel #[p, A, S, S', K, K', a, bs, hK]
        st ← st.step #[i] #[← mkRegion p A S' K' a bs] h
        i := 0
        r := #[p, A, S', K', a, bs]
      let (S, K) := (r[2]!, r[3]!)
      let po ← mkAppM ``Zig.Ptr.off #[p]
      let qo ← mkAppM ``Zig.Ptr.off #[qp]
      let size ← mkAppM ``Array.size #[bs]
      let some _ ← proveArith (← mkAppM ``LE.le #[po, qo]) | throwError "lo"
      let hiT ← mkAppM ``LE.le #[qo, ← mkAppM ``HAdd.hAdd #[po,
        ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt, size]]]
      let some _ ← proveArith hiT | throwError "hi {hiT}"
      let mut j := i
      let mut cur := r
      -- the start
      let zero ← proveArith (← mkEq qo po) (quick := true)
      if zero.isNone then
        -- an undetermined alignment of a part that starts inside: any (`1`)
        if (← instantiateMVars qa).isMVar then discard <| isDefEq qa (mkNatLit 1)
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
      let n? ← match n? with
        | some n => pure (some n)
        | none => do
          let qbs ← instantiateMVars qbs
          if qbs.hasExprMVar then pure none else pure (some (← mkAppM ``Array.size #[qbs]))
      if let some n := n? then
        let sz ← mkAppM ``Array.size #[cur[5]!]
        if (← proveArith (← mkEq n sz) (quick := true)).isNone then
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
      else if !(← withReducible (isDefEq qbs cur[5]!)) then
        -- known bytes: equal to the carved ones (`Array` lemmas, sizes by arithmetic)
        -- (else the final match proves them equal, argument by argument)
        if let some e ← proveBytes cur[5]! qbs then
          let x := st.ats[j]!
          let y ← mkRegion cur[0]! cur[1]! cur[2]! cur[3]! cur[4]! qbs
          let ex ← mkCongrArg (← mkLambdaFVarsBytes x cur) e
          st ← st.step #[j] #[y] (← mkAppM ``atom_eq #[ex])
          j := 0
      return some (st, st.ats[j]!)
    catch ex =>
      trace[fsym] "carve: {ex.toMessageData}"
      s0.restore
  return none

/-- Join two adjacent regions of the state (the second at the end of the first), except those a
postcondition region has claimed. -/
def joinOnce (st : St) (claimed : Array Expr) : TacticM (Option St) := do
  for i in [0:st.ats.size] do
    if claimed.contains st.ats[i]! then continue
    let some r1 := regionArgs? st.ats[i]! | continue
    for j in [0:st.ats.size] do
      if i == j || claimed.contains st.ats[j]! then continue
      let some r2 := regionArgs? st.ats[j]! | continue
      let s0 ← saveState
      try
        unless ← (withReducible (isDefEq r1[1]! r2[1]!) <&&> withReducible (isDefEq r1[2]! r2[2]!) <&&>
            withReducible (isDefEq r1[3]! r2[3]!)) do
          throwError "labels"
        let pe ← mkAppM ``Zig.Ptr.add #[r1[0]!, ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt,
          ← mkAppM ``Array.size #[r1[5]!]]]
        let some _ ← proveEq r2[0]! pe | throwError "adjacent"
        let r2' ← mkRegion pe r2[1]! r2[2]! r2[3]! r2[4]! r2[5]!
        let some e' ← proveEq st.ats[j]! r2' | throwError "eq"
        let st ← st.step #[j] #[r2'] (← mkAppM ``atom_eq #[e'])
        -- now `r2'` is at 0 and `r1` one further unless it was after `r2`
        let i' := if i < j then i + 1 else i
        let h ← mkAppOptM ``up_region_join #[r1[0]!, r1[1]!, r1[2]!, r1[3]!, r1[4]!, r2[4]!, r1[5]!, r2[5]!]
        let joined ← mkRegion r1[0]! r1[1]! r1[2]! r1[3]! r1[4]! (← mkAppM ``HAppend.hAppend #[r1[5]!, r2[5]!])
        return some (← st.step #[i', 0] #[joined] h)
      catch ex =>
        trace[fsym] "join: {ex.toMessageData}"
        s0.restore
  return none

/-- Shares: join those of one block, split for the postcondition's shares of that block,
weaken to their bounds. -/
def planShares (st : St) (qshares0 : Array (Array Expr)) : TacticM St := do
  let mut st := st
  -- a share of a block of which the state has no share: lent by the block's authority
  for q in qshares0 do
    let q ← q.mapM instantiateMVars
    let mut has := false
    for x in st.ats do
      if let some y := shareArgs? x then
        if ← withReducible (isDefEq y[0]! q[0]!) then has := true; break
    unless has do
      if let some st' ← lendShare st q then st := st'
  -- a postcondition share with a determined fraction: the state's share of that fraction,
  -- raised to the bound (`share_raise` with another share of the block) if it is too low
  let mut reserved : Array Expr := #[]
  let mut fixed : Array (Array Expr) := #[]
  let mut rest : Array (Array Expr) := #[]
  for q in qshares0 do
    let q ← q.mapM instantiateMVars
    if q[1]!.hasExprMVar then rest := rest.push q; continue
    let some i := st.ats.findIdx? fun x => !reserved.contains x && (shareArgs? x).any fun a =>
        a[0]! == q[0]! && a[1]! == q[1]! && a[3]! == q[3]! | rest := rest.push q; continue
    let x := (shareArgs? st.ats[i]!).get!
    let qk := q[2]!
    if qk.hasExprMVar || (← proveArith (← mkAppM ``LE.le #[qk, x[2]!]) (quick := true)).isSome then
      reserved := reserved.push st.ats[i]!; fixed := fixed.push q; continue
    -- raise with another share of the block whose bound suffices
    let mut done := false
    for j in [0:st.ats.size] do
      if j == i || reserved.contains st.ats[j]! then continue
      let some y := shareArgs? st.ats[j]! | continue
      unless y[0]! == x[0]! && y[3]! == x[3]! do continue
      unless (← proveArith (← mkAppM ``LE.le #[qk, y[2]!]) (quick := true)).isSome do continue
      let h ← mkAppOptM ``share_raise #[x[0]!, x[1]!, x[2]!, x[3]!, y[1]!, y[2]!]
      let K ← mkAppM ``Max.max #[x[2]!, y[2]!]
      let o1 := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, x[1]!, K, x[3]!]
      let o2 := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, y[1]!, K, x[3]!]
      st ← st.step #[i, j] #[o1, o2] h
      reserved := reserved.push o1; fixed := fixed.push q; done := true
      break
    -- raise with the block's authority (up to the block's size)
    unless done do
      let s0 ← saveState
      try
        let some (st', ia, xa) ← st.auth x[0]! | throwError "no authority"
        let some hk ← proveArith (← mkAppM ``LE.le #[qk, xa[1]!]) (quick := true) | throwError "size"
        let some ish := st'.ats.findIdx? (· == st.ats[i]!) | throwError "lost"
        let h ← mkAppOptM ``auth_raise #[x[0]!, x[2]!, qk, xa[1]!, xa[2]!, xa[3]!, x[1]!, hk]
        let o := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, x[1]!, qk, x[3]!]
        st ← st'.step #[ia, ish] #[st'.ats[ia]!, o] h
        reserved := reserved.push o; fixed := fixed.push q; done := true
      catch ex =>
        trace[fsym] "raise: {ex.toMessageData}"
        s0.restore
    unless done do rest := rest.push q
  let qshares := fixed ++ rest
  -- join
  let mut again := true
  while again do
    again := false
    let ss := (List.range st.ats.size).filterMap fun i =>
      if reserved.contains st.ats[i]! then none else (shareArgs? st.ats[i]!).map (i, ·)
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
  let blocks := (st.ats.filterMap fun x =>
    if reserved.contains x then none else (shareArgs? x).map (·[0]!)).foldl
    (fun acc b => if acc.contains b then acc else acc.push b) #[]
  for blk in blocks do
    let mut want := 0
    for q in rest do
      let s0 ← saveState
      if ← isDefEq q[0]! blk then want := want + 1
      s0.restore
    let some i0 := st.ats.findIdx? fun x => !reserved.contains x && (shareArgs? x).any (·[0]! == blk)
      | continue
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
        -- above the share's bound: raised with the block's authority
        if let some (st', ia, xa) ← st.auth x[0]! then
          if let some hk ← proveArith (← mkAppM ``LE.le #[qk, xa[1]!]) then
            if st'.ats.size == st.ats.size then
              let ish := i
              let h ← mkAppOptM ``auth_raise #[x[0]!, x[2]!, qk, xa[1]!, xa[2]!, xa[3]!, x[1]!, hk]
              let o := mkAppN (mkConst ``Zig.Full.bshare) #[x[0]!, x[1]!, qk, x[3]!]
              let st2 ← st'.step #[ia, ish] #[st'.ats[ia]!, o] h
              -- the authority is at 0, the share at 1; earlier indices move by the step
              let map (k : Nat) : Nat := if k == ia || k == ish then k else
                k + 2 - (if k > ia then 1 else 0) - (if k > ish then 1 else 0)
              used := (used.map fun k => map k) |>.push 1
              st := st2
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
atoms (up to provable equations of their arguments), drop `up` atoms into `Junk`, prove `Q`'s
facts by arithmetic. Unproved facts are left as goals; on failure the update goal is left. -/
partial def closeEntail (g : MVarId) : TacticM (List MVarId) := g.withContext do
  -- an assertion-level `if` of the state: take the branch the facts decide, else split
  let t ← instantiateMVars (← g.getType)
  let P := t.appFn!.appArg!
  let Q := t.appArg!
  if let some a := (atoms P).find? (·.isAppOfArity ``ite 5) then
    let swap (pf br : Expr) : TacticM (List MVarId) := do
      let f ← withLocalDeclD `x (mkConst ``Zig.Full.FAssn) fun x => do
        mkLambdaFVars #[x] (P.replace fun y => if y == a then some x else none)
      -- the branch's atoms unfolded (definitionally), so that its facts and existentials open
      let P' := (mkApp f (← unfoldLeaves br)).headBeta
      let e ← mkExpectedTypeHint (← mkCongrArg f pf) (← mkEq P P')
      let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P', Q])
      g.assign (← mkAppM ``EUpd.trans #[← mkAppM ``atom_eq #[e], g2])
      closeEntail g2.mvarId!
    if let some (pf, br) ← decideIte a false then return ← swap pf br
    trace[fsym] "state if: split on {a.getArg! 1}"
    let (sp, sn) ← g.byCases (a.getArg! 1) `hc
    let gp ← sp.mvarId.withContext (closeEntail sp.mvarId)
    let gn ← sn.mvarId.withContext (closeEntail sn.mvarId)
    return gp ++ gn
  -- facts and existentials of the state go into the context
  let ats := atoms P
  if let some i := ats.findIdx? fun a => a.isAppOfArity liftN 1 || a.isAppOfArity exN 2 then
    let a := ats[i]!
    let R := sepOf (ats.eraseIdx! i)
    let e ← acEq P (mkSep a R)
    if a.isAppOfArity liftN 1 then
      let φ := a.appArg!
      let k ← mkFreshExprSyntheticOpaqueMVar (← mkArrow φ (← mkAppM ``EUpd #[R, Q]))
      g.assign (← mkAppM ``eupd_pre_eq #[e, ← mkAppM ``eupd_lift_pre #[k]])
      let (h, g2) ← k.mvarId!.intro `h
      let g2 ← destruct g2 h
      -- a block fact of a state atom opened late (a claim in a decided `if`) names a known block
      let g2 ← unifyBlocks g2
      return ← g2.withContext (closeEntail g2)
    else
      let F := a.appArg!
      let β := (← whnfD (← inferType F)).bindingDomain!
      let n := match F.consumeMData with | .lam n .. => n | _ => `x
      let kTy ← withLocalDeclD n β fun x => do
        mkForallFVars #[x] (← mkAppM ``EUpd #[mkSep (mkApp F x).headBeta R, Q])
      let k ← mkFreshExprSyntheticOpaqueMVar kTy
      g.assign (← mkAppM ``eupd_pre_eq #[e, ← mkAppOptM ``eupd_ex_pre #[β, F, R, Q, k]])
      let (_, g2) ← k.mvarId!.intro n
      return ← g2.withContext (closeEntail g2)
  -- an assertion-level `if` of the postcondition that the facts do not decide: split on it
  let s0 ← saveState
  let (Qi, _) ← instQ (← reduceProjs Q)
  let undecided := (atoms Qi).find? (·.isAppOfArity ``ite 5)
  s0.restore
  if let some a := undecided then
    let c := a.getArg! 1
    let known ← (← getLCtx).anyM fun d => do
      let t ← instantiateMVars d.type
      return t == c || t == mkNot c
    if known then trace[fsym] "postcondition if undecided with its condition known: {c}"
    if !c.hasExprMVar && !known then
      trace[fsym] "postcondition if: split on {c}"
      let (sp, sn) ← g.byCases c `hc
      let gp ← sp.mvarId.withContext (closeEntail sp.mvarId)
      let gn ← sn.mvarId.withContext (closeEntail sn.mvarId)
      return gp ++ gn
  let h0 ← IO.getNumHeartbeats
  let r ← closeEntail' g
  trace[fsym.prof] "entail {((← IO.getNumHeartbeats) - h0) / 1000}"
  return r
where closeEntail' (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let s ← saveState
  try
    let t ← instantiateMVars (← g.getType)
    let P := t.appFn!.appArg!
    let Q ← reduceProjs t.appArg!
    let (Qi, pQ) ← instQ Q
    let mut Qi ← reduceProjs Qi
    let mut pQ := pQ
    let mut st ← St.init P
    let exts ← planners
    let planned (a : Expr) : Bool := exts.any fun x => x.heads.any (a.isAppOf ·)
    -- pre-assign by the atoms that unify outright; an atom that unfolds once its witnesses are
    -- assigned (a `match` on an existential) is opened again
    let preassign (st : St) (qats : Array Expr) : TacticM Unit := do
      for a in qats do
        if a.isAppOfArity liftN 1 || (regionArgs? a).isSome || (shareArgs? a).isSome ||
          (authArgs? a).isSome || a.isMVar || a.isAppOfArity ``Zig.Full.known 2 || planned a then continue
        for x in st.ats do
          let s' ← saveState
          if ← unifyAtom a x then break
          s'.restore
      for a in qats do
        if a.isAppOfArity liftN 1 || (regionArgs? a).isSome || (shareArgs? a).isSome ||
          (authArgs? a).isSome || a.isMVar || a.isAppOfArity ``Zig.Full.known 2 || planned a then continue
        if (← instantiateMVars a).hasExprMVar then
          for x in st.ats do
            if headKey a != headKey x then continue
            let s' ← saveState
            if ← matchArgs a x then
              if (← proveEq x (← instantiateMVars a)).isSome then break
            s'.restore
    for _ in [0:3] do
      let qats := atoms Qi
      -- block facts first
      for f in qats.filter (·.isAppOfArity liftN 1) do
        for φ in ← conjuncts (← instantiateMVars f.appArg!) do
          if (φ.eq?.map fun (_, l, _) => l.isAppOf ``Zig.Ptr.block).getD false then
            discard <| solveBlock φ
      preassign st qats
      let Qi1 ← instantiateMVars Qi
      let (Qi2, pQ2) ← instQ Qi1
      let Qi2 ← reduceProjs Qi2
      if Qi2 == Qi1 then break
      pQ ← mkAppM ``imp_trans #[← mkExpectedTypeHint pQ2 (← mkImp' Qi2 Qi1), pQ]
      Qi := Qi2
    let qats := atoms Qi
    let facts := qats.filter (·.isAppOfArity liftN 1)
    -- the labels of an authority (its block's size and kind) from the state's
    for a in qats do
      let a ← instantiateMVars a
      let some qx := authArgs? a | continue
      for x in st.ats do
        let some y := authArgs? x | continue
        let s' ← saveState
        if ← (withReducible (isDefEq qx[0]! y[0]!) <&&> withReducible (isDefEq qx[1]! y[1]!) <&&>
            withReducible (isDefEq qx[2]! y[2]!)) then break
        s'.restore
    -- regions: exact matches first; then carve (joining adjacent regions for a region of
    -- unknown size, which extends as far as the state's bytes go, or when no region holds it)
    let mut exact : Array Nat := #[]
    let mut claimed : Array Expr := #[]
    for a in qats do
      let some q := regionArgs? (← instantiateMVars a) | continue
      -- a region with a size fact is carved (its bytes may change)
      let qbs ← instantiateMVars q[5]!
      let mut sized := false
      for f in facts do
        for φ in ← conjuncts f.appArg! do
          if let some (_, l, _) := φ.eq? then
            if l.isAppOfArity ``Array.size 2 then
              if (← instantiateMVars l.appArg!) == qbs then sized := true
      if sized && qbs.hasExprMVar then continue
      for i in [0:st.ats.size] do
        if (regionArgs? st.ats[i]!).isNone || exact.contains i then continue
        let s' ← saveState
        if ← withReducibleAndInstances (isDefEq a st.ats[i]!) then
          exact := exact.push i; claimed := claimed.push st.ats[i]!; break
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
            if l.isAppOfArity ``Array.size 2 then
              if (← instantiateMVars l.appArg!) == qbs then n? := some r
      let mut done := false
      if n?.isNone && (← instantiateMVars q[5]!).hasExprMVar then
        repeat
          let some st' ← joinOnce st claimed | break
          st := st'
      if let some (st', x) ← carve st q n? claimed then st := st'; claimed := claimed.push x; done := true
      while !done do
        let some st' ← joinOnce st claimed | break
        st := st'
        if let some (st', x) ← carve st q n? claimed then st := st'; claimed := claimed.push x; done := true
      unless done do throwError "fsym: no region of the state holds{indentExpr a}"
    trace[fsym] "plan: regions done"
    -- shares
    let qsh ← qats.filterMapM fun a => do return shareArgs? (← instantiateMVars a)
    st ← planShares st qsh
    trace[fsym] "plan: shares done"
    -- planner extensions (`@[fsym_plan]`)
    for x in exts do st ← x.run st qats
    -- authorities with a determined fraction: the block's untagged shares go back
    for a in qats do
      let a ← instantiateMVars a
      let some qx := authArgs? a | continue
      if qx[3]!.hasExprMVar then continue
      let s1 ← saveState
      let some (st1, i, x) ← st.auth qx[0]! | continue
      let mut st2 := st1
      let mut idx := i
      let mut cur := x
      let mut ok ← proveEq cur[3]! qx[3]!
      while ok.isNone do
        let some j := st2.ats.findIdx? fun y => (shareArgs? y).any fun z =>
            z[0]! == cur[0]! && z[3]!.isAppOfArity ``Option.none 1
          | break
        let z := (shareArgs? st2.ats[j]!).get!
        let h ← mkAppOptM ``auth_unlend #[cur[0]!, z[2]!, cur[1]!, cur[2]!, cur[3]!, z[1]!]
        let g' ← mkAppM ``Zig.Full.Frac.add #[cur[3]!, z[1]!]
        st2 ← st2.step #[idx, j] #[mkAuth cur[0]! cur[1]! cur[2]! g'] h
        idx := 0
        cur := cur.set! 3 g'
        ok ← proveEq g' qx[3]!
      let some e := ok | s1.restore; continue
      st2 ← st2.authEq idx cur qx[3]! e
      -- in the postcondition's form (`bext` is the fraction one)
      unless ← isDefEq st2.ats[0]! a do s1.restore; continue
      let a ← instantiateMVars a
      st2 ← st2.step #[0] #[a] (← mkAppM ``atom_eq #[← mkExpectedTypeHint (← mkEqRefl a)
        (← mkEq st2.ats[0]! a)])
      st := st2
    trace[fsym] "plan: authorities done"
    -- knowledge of a block's address from an owned region of it (`known_of_region`), for each
    -- `known` of the postcondition that the state's knowledge does not cover
    let mut knowUsed : Array Nat := #[]
    for a in qats do
      let a ← instantiateMVars a
      unless a.isAppOfArity ``Zig.Full.known 2 do continue
      let mut have_ := none
      for i in [0:st.ats.size] do
        if knowUsed.contains i || !st.ats[i]!.isAppOfArity ``Zig.Full.known 2 then continue
        let s' ← saveState
        let ok ← unifyAtom a st.ats[i]!
        s'.restore
        if ok then have_ := some i; break
      if let some i := have_ then knowUsed := knowUsed.push i; continue
      for i in [0:st.ats.size] do
        let some r := regionArgs? st.ats[i]! | continue
        let s' ← saveState
        let some (b, hb) ← blockOf r[0]! | continue
        unless ← withReducible (isDefEq b (a.getArg! 0)) <&&> withReducible (isDefEq r[1]! (a.getArg! 1)) do
          s'.restore; continue
        let some hpos ← proveArith (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Array.size #[r[5]!]]) (quick := true)
          | s'.restore; continue
        let h ← mkAppOptM ``known_of_region #[b, r[0]!, r[1]!, r[2]!, r[4]!, r[3]!, r[5]!, hb, hpos]
        st ← st.step #[i] #[st.ats[i]!, mkAppN (mkConst ``Zig.Full.known) #[b, r[1]!]] h
        knowUsed := (knowUsed.map fun k => if k < i then k + 2 else k + 1) |>.push 1
        break
    -- a frame (an undetermined atom of the postcondition) takes what is left
    let frame? := (← qats.mapM instantiateMVars).find? (·.isMVar)
    -- final match
    let spat := (← qats.mapM instantiateMVars).filter fun a => !a.isAppOfArity liftN 1 && !a.isMVar
    let junkQ := spat.any (·.isConstOf ``Zig.Full.Junk)
    let spat := spat.filter (! ·.isConstOf ``Zig.Full.Junk)
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
    -- atoms left over that a drop lemma forgets (`@[fsym_drop]`: knowledge, claims)
    if frame?.isNone then
      let drops := fsymDropExt.getState (← getEnv)
      let mut i := 0
      while i < st.ats.size do
        if used.contains i then i := i + 1; continue
        let x := st.ats[i]!
        let rest := st.ats.eraseIdx! i
        let mut h? := none
        for dn in drops do
          let s' ← saveState
          let lem ← mkConstWithFreshMVarLevels dn
          let (args, _, ty) ← forallMetaTelescope (← inferType lem)
          if ← isDefEq ty (← mkAppM ``EUpd #[mkSep x (sepOf rest), sepOf rest]) then
            let h ← instantiateMVars (mkAppN lem args)
            unless h.hasExprMVar do h? := some h; break
          s'.restore
        let some h := h? | i := i + 1; continue
        let e ← acEq (sepOf st.ats) (mkSep x (sepOf rest))
        st := { ats := rest, pf := ← mkAppM ``EUpd.trans #[st.pf, ← mkAppM ``eupd_pre_eq #[e, h]] }
        used := used.map fun k => if k > i then k - 1 else k
    let pats := st.ats
    let P := sepOf pats
    let mut L := ((List.range pats.size).filter (! used.contains ·)).toArray.map (pats[·]!)
    let mut M := used.map (pats[·]!)
    if let some fr := frame? then
      fr.mvarId!.assign (sepOf L)
      M := M ++ L
      L := #[]
    unless L.isEmpty || junkQ do throwError "fsym: atoms left over{indentExpr (sepOf L)}"
    let (S, core) ← if junkQ then do
        let J := mkConst ``Zig.Full.Junk
        let rec toJunk (xs : List Expr) : MetaM Expr := do
          match xs with
          | [] => mkAppM ``imp_junk_emp #[]
          | [x] =>
            if x.isConstOf ``Zig.Full.Junk then mkAppOptM ``imp_refl #[J]
            else if x.isAppOfArity ``Zig.Full.FAssn.up 1 then mkAppOptM ``imp_junk_one #[x.appArg!]
            else throwError "fsym: cannot drop{indentExpr x}"
          | x :: rest =>
            let pr ← toJunk rest
            if x.isConstOf ``Zig.Full.Junk then mkAppM ``imp_junk_junk #[pr]
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
    trace[fsym] "plan: matched"
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
    let Qf ← instantiateMVars Qi
    let eT ← acEq T' Qf
    let pf ← mkAppM ``imp_trans #[← mkAppM ``imp_trans #[body, ← mkAppM ``imp_eq #[eT]], pQ]
    let pf ← instantiateMVars pf
    if pf.hasExprMVar then
      for m in ← getMVars pf do
        unless left.contains m do
          unless ← isProp (← m.getType) do throwError "fsym: undetermined witness ?{m.name}"
    g.assign (← mkAppM ``EUpd.trans #[st.pf, ← mkAppM ``EUpd.of_imp #[pf]])
    return left
  catch ex =>
    trace[fsym] "entailment: {ex.toMessageData}"
    s.restore
    return [g]

/-! ## Facts of atoms -/

/-- The facts lemmas (`@[fsym_facts]`) about the atom `a`: `(proof of AtomFacts a φ, φ)`. -/
def atomFacts (a : Expr) : MetaM (Array (Expr × Expr)) := do
  -- the lemmas by the head of their assertion, once per run
  let keyed ← match ← (← caches).factLemmas.get with
    | some k => pure k
    | none => do
      let k ← (fsymFactsExt.getState (← getEnv)).filterMapM fun n => withNewMCtxDepth do
        let (_, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels n))
        return if concl.isAppOfArity ``AtomFacts 2 then some (headKey (concl.getArg! 0), n) else none
      (← caches).factLemmas.set (some k)
      pure k
  let mut out := #[]
  for (key, n) in keyed do
    unless key == headKey a do continue
    let s ← saveState
    let f ← mkConstWithFreshMVarLevels n
    let (args, _, concl) ← forallMetaTelescope (← inferType f)
    unless ← withReducibleAndInstances (isDefEq (concl.getArg! 0) a) do s.restore; continue
    for x in args do
      unless ← x.mvarId!.isAssigned do
        if (← isClass? (← inferType x)).isSome then
          if let some i ← (try some <$> synthInstance (← inferType x) catch _ => pure none) then
            discard <| isDefEq x i
    let pf ← instantiateMVars (mkAppN f args)
    let φ ← instantiateMVars (concl.getArg! 1)
    s.restore
    unless pf.hasMVar || φ.hasMVar do out := out.push (pf, φ)
  return out

/-- The context has the fact `ψ`: a block `∃ b, p.block = some b` (`blockOf`), or a hypothesis. -/
def knownFact (ψ : Expr) : MetaM Bool := do
  let s ← saveState
  let r ← do
    if ψ.isAppOfArity ``Exists 2 then
      if let .lam _ _ body _ := ψ.appArg! then
        if let some (_, l, _) := body.eq? then
          if l.isAppOfArity ``Zig.Ptr.block 1 && !l.appArg!.hasLooseBVars then
            return (← blockOf l.appArg!).isSome
    (← getLCtx).anyM fun d => do
      if d.isImplementationDetail then return false
      withReducibleAndInstances (isDefEq d.type ψ)
  s.restore
  return r

/-- Add the facts of the precondition's atoms (`@[fsym_facts]`: the block, offset and alignment
of an owned pointer) that the context lacks, when the walk needs more facts (a rule's side goal,
an undecided `if`, a reachable panic, a return). `none` if there was none to add. -/
partial def addFacts (g : MVarId) (done : Array Expr := #[]) : TacticM (Option MVarId) := g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let ats := atoms P
  for i in [0:ats.size] do
    let a := ats[i]!
    if done.contains a then continue
    for (hX, φ) in ← atomFacts a do
      if ← (← conjuncts φ).allM (fun ψ => knownFact ψ) then continue
      trace[fsym] "facts of {a}: {φ}"
      let R := sepOf (ats.eraseIdx! i)
      let g1 ← if P == mkSep a R then pure g else do
        let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α (mkSep a R) c Q)
        g.assign (← mkAppOptM (L.nm ``pre_eq) #[L.L, none, P, mkSep a R, Q, c, ← acEq P (mkSep a R), g2])
        pure g2.mvarId!
      let k ← mkFreshExprSyntheticOpaqueMVar (← mkArrow φ (mkT L α (mkSep a R) c Q))
      g1.assign (← mkAppM' (← mkAppOptM (L.nm ``pre_fact) #[L.L]) #[hX, k])
      let (h, g2) ← k.mvarId!.intro `hf
      let g2 ← destruct g2 h
      return ← addFacts (← g2.withContext (unifyBlocks g2)) (done.push a)
  return if done.isEmpty then none else some g

/-! ## Rules -/

/-- The command of `x` that sequential rules are about: `c` of a `ConcM.liftMem c`. -/
def memCmd? (x : Expr) : Option Expr :=
  if x.isAppOfArity ``ConcM.liftMem 3 then some x.appArg! else none

/-- Unfold the command `cmd` of a `CTriple` rule until its head is that of the program's command
`x` (a table call `t.call f a` or `(CVTable.dispatch t fns).alloc …` is an indirect call). -/
partial def unfoldToHead (cmd x : Expr) (fuel : Nat := 6) : MetaM Expr := do
  if fuel == 0 || headKey cmd == headKey x then return cmd
  match ← unfold1 cmd with
  | some c' => unfoldToHead c' x (fuel - 1)
  | none => return cmd

/-- Try a rule on the command `x` of `x >>= f`. Returns the continuation goal and side goals.
A sequential rule is total (`FTotalTriple`, every backend) or partial (`FTriple`, the partial
backends); in the concurrent backend it executes a `ConcM.liftMem c` command (about `c`), and a
`CTriple` rule a concurrent command. -/
def tryRule (g : MVarId) (rule : Expr) (x f : Expr) : TacticM (Option (MVarId × List MVarId)) :=
  g.withContext do
  let s ← saveState
  try
    let (_, L, α, P, _, Q) ← view g
    let (args, _, concl) ← forallMetaTelescope (← inferType rule)
    let concl ← whnfR concl
    let some (kind, cmd) := ruleConcl? concl | do
      trace[fsym] "rule {rule}: not a triple {concl}"; s.restore; return none
    let ca := concl.getAppArgs
    let (β, P₀, Q₀) := if kind == ``CTriple then (ca[1]!, ca[2]!, ca[4]!) else (ca[0]!, ca[1]!, ca[3]!)
    -- the command the rule is about, and whether the rule applies in this backend
    let target? : Option Expr :=
      if kind == ``CTriple then (if L.conc && (memCmd? x).isNone then some x else none)
      else if L.conc then memCmd? x
      else if kind == ``FTriple && !L.part then none
      else some x
    let some tx := target? | s.restore; return none
    if kind == ``CTriple then
      let cmd ← unfoldToHead (← instantiateMVars cmd) tx
      unless headKey cmd == headKey tx do s.restore; return none
      unless ← isDefEq cmd tx do
        trace[fsym] "rule {rule}: command{indentExpr cmd}\ndoes not unify with{indentExpr tx}"
        s.restore; return none
    else
      unless ← unifyKeyed cmd tx do s.restore; return none
    trace[fsym] "rule {rule}: command unified"
    let P₀i ← instantiateMVars P₀
    let whole := P₀i.isMVar
    let mut R := mkConst empN
    -- `EUpd P (P₀ ⋆ R)` by the planner, when the rule's precondition is not literally there
    let mut planned : Option Expr := none
    if whole then
      unless ← isDefEq P₀ P do s.restore; return none
    else
      -- frame inference: each atom of the rule's precondition is an atom of `P`
      let ats := atoms P
      let mut used := Array.replicate ats.size false
      let mut literal := true
      let sLit ← saveState
      for a in atoms P₀i do
        let mut found := false
        for i in [0:ats.size] do
          unless used[i]! do
            let s' ← saveState
            if ← unifyAtom a ats[i]! then
              used := used.set! i true; found := true; break
            s'.restore
        unless found do literal := false; break
      if literal then
        let mut rest := #[]
        for i in [0:ats.size] do
          unless used[i]! do rest := rest.push ats[i]!
        R := sepOf rest
      else
        sLit.restore
        let fr ← mkFreshExprMVar (mkConst ``Zig.Full.FAssn)
        let hE ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, mkSep P₀i fr])
        let left ← closeEntail hE.mvarId!
        unless left.isEmpty do
          trace[fsym] "rule {rule}: no plan for its precondition"
          s.restore; return none
        R ← instantiateMVars fr
        planned := some (← instantiateMVars hE)
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
    let mut r ← instantiateMVars (mkAppN rule args)
    let Q₀ ← instantiateMVars Q₀
    let P₀ ← instantiateMVars P₀
    -- the rule in the backend's kind: `FTotalTriple` (sequential, total), `FTriple` (`P.step`,
    -- `C.step`) or `CTriple` (`C.stepC`)
    let mut kind := kind
    if L.conc && kind == ``FTotalTriple then
      r ← mkAppM ``FTotalTriple.toPartial #[r]; kind := ``FTriple
    let (stepN, stepAllN) :=
      if kind == ``CTriple then (``C.stepC, ``C.stepAllC)
      else if L.conc then (``C.step, ``C.stepAll)
      else if kind == ``FTriple then (``P.step, ``P.stepAll)
      else (``step, ``stepAll)
    let kTy ← withLocalDeclD `v β fun v => do
      let pre := if whole then mkApp Q₀ v |>.headBeta else mkSep (mkApp Q₀ v |>.headBeta) R
      mkForallFVars #[v] (mkT L α pre (mkApp f v).headBeta Q)
    let k ← mkFreshExprSyntheticOpaqueMVar kTy
    if let some hE := planned then
      let Q₀R ← withLocalDeclD `v β fun v => do mkLambdaFVars #[v] (mkSep (mkApp Q₀ v).headBeta R)
      let fr ← if kind == ``CTriple then mkAppOptM ``CTriple.frame #[none, none, P₀, R, Q₀, tx, r]
        else mkAppOptM (kind ++ `frame) #[none, P₀, R, Q₀, tx, r]
      let r' ← mkAppM (kind ++ `eupd) #[hE, fr]
      g.assign (← mkAppOptM stepAllN #[L.L, β, α, P, Q, tx, f, Q₀R, r', k])
    else if whole then
      g.assign (← mkAppOptM stepAllN #[L.L, β, α, P, Q, tx, f, Q₀, r, k])
    else
      let e ← acEq P (mkSep P₀ R)
      let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α (mkSep P₀ R) (← mkAppM ``Bind.bind #[x, f]) Q)
      g.assign (← mkAppOptM (L.nm ``pre_eq) #[L.L, α, P, mkSep P₀ R, Q, none, e, g2])
      g2.mvarId!.assign (← mkAppOptM stepN #[L.L, β, α, P₀, R, Q, tx, f, Q₀, r, k])
    let n := match f.consumeMData with | .lam n .. => n | _ => `v
    let (_, k') ← k.mvarId!.intro n
    return some (k', left)
  catch ex =>
    trace[fsym] "rule {rule} failed: {ex.toMessageData}"
    s.restore; return none

/-- The registered rules and the caller's. -/
def rules (user : Array Expr) (x : Expr) : MetaM (Array Expr) := do
  -- the registered rules by the head of their command, once per run
  let keyed ← match ← (← caches).rules.get with
    | some k => pure k
    | none => do
      let mut k := #[]
      for n in (fsymRuleExt.getState (← getEnv)).reverse do
        let key ← withNewMCtxDepth do
          let (_, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels n))
          let concl ← whnfR concl
          -- a `CTriple` rule's command may unfold to the program's (`unfoldToHead`): any key
          pure (match ruleConcl? concl with
            | some (k, c) => if k == ``CTriple then .anonymous else headKey c
            | none => .anonymous)
        k := k.push (key, n)
      (← caches).rules.set (some k)
      pure k
  let kx := headKey ((memCmd? x).getD x)
  let mut out := user
  for (key, n) in keyed do
    if key == kx || key == .anonymous || kx == .anonymous || key == `fvar || kx == `fvar then
      out := out.push (← mkConstWithFreshMVarLevels n)
  return out

/-! ## The walk -/


/-- Rewrite the command `x` of the program `c` (`x >>= f` or `x`) by `eq : x = x'`. -/
def rewriteCmd (g : MVarId) (L : Bk) (α P Q c x x' eq : Expr) : MetaM MVarId := do
  let mot ← withLocalDeclD `z (← inferType x) fun z => do
    let c' := if c.isAppOfArity ``Bind.bind 6 && c.getArg! 4 == x then
        mkAppN c.getAppFn (c.getAppArgs.set! 4 z) else z
    mkLambdaFVars #[z] (mkT L α P c' Q)
  g.replaceTargetEq (mkApp mot x').headBeta (← mkCongrArg mot eq)

mutual
/-- An indirect call `callIndirect f ((p, y) :: arms)` that no rule covers: `y` if the facts show
`f = p`, else both cases (`C.callIndirect_pos`/`_neg`); no arm left is `throw .illegal`, which
must be unreachable. -/
partial def indirectWalk (g : MVarId) (L : Bk) (α P c Q x : Expr) (user : Array Expr)
    (extra : Array Syntax) (fuel : Nat) : TacticM (List MVarId) := g.withContext do
  let a := x.getAppArgs
  let (β, fp, arms) := (a[0]!, a[3]!, a[4]!)
  if arms.isAppOfArity ``List.nil 1 then
    let e ← mkAppOptM ``C.callIndirect_nil #[L.L, β, fp]
    let g' ← rewriteCmd g L α P Q c x (← inferType e).appArg! e
    return ← walk g' user extra (fuel - 1)
  unless arms.isAppOfArity ``List.cons 3 do return [g]
  let hd := arms.getArg! 1
  let rest := arms.getArg! 2
  let (p, y) := (hd.getArg! 2, hd.getArg! 3)
  if let some h ← proveEq fp p then
    let e ← mkAppOptM ``C.callIndirect_pos #[L.L, β, fp, p, y, rest, h]
    return ← walk (← rewriteCmd g L α P Q c x y e) user extra (fuel - 1)
  let eqT ← mkEq fp p
  -- `f ≠ p` (a pointer literal of another function, or by the facts)
  let hn ← mkFreshExprMVar (mkNot eqT)
  if ← arith hn.mvarId! (quick := true) <||> closeWith hn.mvarId! (← `(tactic| decide)) then
    let e ← mkAppOptM ``C.callIndirect_neg #[L.L, β, fp, p, y, rest, ← instantiateMVars hn]
    return ← walk (← rewriteCmd g L α P Q c x (← inferType e).appArg! e) user extra (fuel - 1)
  let (sp, sn) ← g.byCases eqT `hf
  let gp ← sp.mvarId.withContext do
    let e ← mkAppOptM ``C.callIndirect_pos #[L.L, β, fp, p, y, rest, Expr.fvar sp.fvarId]
    rewriteCmd sp.mvarId L α P Q c x y e
  let gn ← sn.mvarId.withContext do
    let e ← mkAppOptM ``C.callIndirect_neg #[L.L, β, fp, p, y, rest, Expr.fvar sn.fvarId]
    rewriteCmd sn.mvarId L α P Q c x (← inferType e).appArg! e
  let gp ← destruct gp sp.fvarId
  return (← walk gp user extra (fuel - 1)) ++ (← walk gn user extra (fuel - 1))

/-- Split on a variable of an inductive type and walk each case. -/
partial def casesWalk (g : MVarId) (d : Expr) (user : Array Expr := #[]) (extra : Array Syntax := #[])
    (fuel : Nat := 0) : TacticM (List MVarId) := do
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

partial def walk (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := do
  if fuel == 0 then
    logInfo m!"fsym: out of fuel (step budget exhausted); goal left open"
    return [g]
  trace[fsym] "walk {fuel}"
  let h0 ← IO.getNumHeartbeats
  let g ← normPre g
  let h1 ← IO.getNumHeartbeats
  trace[fsym] "pre done {← g.getType}"
  let g ← simpProg g extra
  trace[fsym.prof] "pre {(h1-h0)/1000} prog {((← IO.getNumHeartbeats)-h1)/1000}"
  trace[fsym] "prog done {(← g.getType)}"
  g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let c := c.consumeMData
  -- the step again with more facts of the atoms (`addFacts`), if there are any
  let moreFacts : TacticM (Option (List MVarId)) := do
    (← addFacts g).mapM (walk · user extra (fuel - 1))
  -- return
  if c.isAppOfArity ``Pure.pure 4 then
    let v := c.appArg!
    let s ← saveState
    let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, (mkApp Q v).headBeta])
    g.assign (← mkAppOptM (L.nm ``ret) #[L.L, none, P, Q, v, h])
    let left ← closeEntail h.mvarId!
    if left.isEmpty then return []
    -- more facts (of the atoms) may close it
    let s1 ← saveState
    s.restore
    if let some r ← moreFacts then return r
    s1.restore
    return left
  -- panic: the branch must be unreachable
  if isThrow c then
    let s ← saveState
    try
      let [g'] ← evalTacticAt (← `(tactic| refine $(mkIdent (L.nm ``of_false)) _ ?_)) g | throwError "x"
      if ← closeWith g' (← `(tactic| contradiction)) then return []
      if ← arithCore g' then return []
      s.restore
    catch _ => s.restore
    if let some r ← moreFacts then return r
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
    if ← arith hp.mvarId! (quick := true) then
      return ← walk (← branch g (← instantiateMVars hp) true) user extra (fuel - 1)
    let hn ← mkFreshExprMVar (mkNot cond)
    if ← arith hn.mvarId! (quick := true) then
      return ← walk (← branch g (← instantiateMVars hn) false) user extra (fuel - 1)
    if let some r ← moreFacts then return r
    -- a condition that matches on a variable (an error union's tag): split the variable
    let mut found : Option Expr := none
    let cond' ← instantiateMVars cond
    for sub in subterms cond' do
      if let some m ← matchMatcherApp? sub (alsoCasesOn := true) then
        if let some d := m.discrs.find? (·.isFVar) then found := some d; break
    -- a variable of an enumeration-like type (`Option`, `Except`, …) of the condition that the
    -- state matches on too (`match h with …` of an invariant): its cases decide both
    if found.isNone then
      let Pi ← instantiateMVars P
      for d in (Lean.collectFVars {} cond').fvarIds do
        unless Pi.containsFVar d do continue
        let .const tn _ := (← whnfD (← d.getType)).getAppFn | continue
        let some ii ← caseInduct? tn | continue
        unless ii.isRec do found := some (.fvar d); break
    trace[fsym] "branch on {cond'}: split variable {found}"
    if let some d := found then
      return ← casesWalk g d user extra fuel
    let (sp, sn) ← g.byCases cond `hc
    let gp ← sp.mvarId.withContext (branch sp.mvarId (.fvar sp.fvarId) true)
    let gn ← sn.mvarId.withContext (branch sn.mvarId (.fvar sn.fvarId) false)
    let gp ← destruct gp sp.fvarId
    let gn ← destruct gn sn.fvarId
    return (← walk gp user extra (fuel - 1)) ++ (← walk gn user extra (fuel - 1))
  -- cases on a variable; a term (a field of the locals) is generalized first, with its equation
  -- (`substCtor` then replaces it in the facts)
  let discr? : Option Expr ←
    if c.isAppOfArity ``Option.elim 5 then pure (some c.getAppArgs[2]!)
    else match ← matchMatcherApp? c with
      | some m => pure (m.discrs.find? (·.isFVar) <|> m.discrs[0]?)
      | none => pure none
  if let some d := discr? then
    if d.isFVar then return ← casesWalk g d user extra fuel
    if !d.hasLooseBVars && !(← isCaseCtorApp d) then
      if let .const tn _ := (← whnfD (← inferType d)).getAppFn then
        if let some ii ← caseInduct? tn then
          unless ii.isRec do
            -- a goal that does not abstract over `d` (a dependent match): no split
            if let some (xs, g') ← observing? (g.generalize #[{ expr := d, xName? := `o, hName? := `ho }]) then
              return ← casesWalk g' (.fvar xs[0]!) user extra fuel
  -- a command
  let (x, f) ← if c.isAppOfArity ``Bind.bind 6 then pure (c.getAppArgs[4]!, c.getAppArgs[5]!)
    else do
      let [g'] ← evalTacticAt (← `(tactic| refine $(mkIdent (L.nm ``bind_pure)) _ ?_)) g | throwError "fsym"
      return ← walk g' user extra (fuel - 1)
  -- an atomic op's oracle choice: `0` in one thread
  if L.conc && x.isAppOfArity ``ConcM.sync 2 && (x.getArg! 1).isAppOf ``SyncOp.pick then
    let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.C.pick _ ?_)) g | throwError "fsym: pick"
    return ← walk g' user extra (fuel - 1)
  let h2 ← IO.getNumHeartbeats
  -- the first rule whose side goals are all proved; else the first that applies
  let mut partial? : Option (Tactic.SavedState × MVarId × List MVarId) := none
  for r in ← rules user x do
    let h3 ← IO.getNumHeartbeats
    let s ← saveState
    let res ← tryRule g r x f
    let d := ((← IO.getNumHeartbeats) - h3) / 1000
    if d > 300 then trace[fsym.prof] "try {d} {r} {res.isSome}"
    if let some (k, left) := res then
      if left.isEmpty then
        trace[fsym.prof] "rule {((← IO.getNumHeartbeats)-h2)/1000} {r}"
        return ← walk k user extra (fuel - 1)
      trace[fsym] "rule {r}: side goals left {← left.mapM fun g => do instantiateMVars (← g.getType)}"
      if partial?.isNone then partial? := some (← saveState, k, left)
      s.restore
  -- more facts (of the atoms) for the rules' side goals
  let unfolded? ← if partial?.isSome then pure none else unfoldCmd x
  if partial?.isSome || unfolded?.isNone then
    if let some r ← moreFacts then return r
  -- a side condition that the facts do not decide: split on it (the rules' cases)
  if let some (s, _, left) := partial? then
    let s1 ← saveState
    s.restore
    let φs ← left.mapM fun m => do instantiateMVars (← m.getType)
    s1.restore
    if let some φ := φs.find? fun φ => !φ.hasExprMVar && !φ.hasSyntheticSorry then
      let hn ← mkFreshExprMVar (mkNot φ)
      unless ← arith hn.mvarId! (quick := true) do
        trace[fsym] "split on the side condition {φ}"
        let (sp, sn) ← g.byCases φ `hc
        return (← walk sp.mvarId user extra (fuel - 1)) ++ (← walk sn.mvarId user extra (fuel - 1))
    s.restore
    let some (_, k, left) := partial? | return [g]
    return left ++ (← walk k user extra (fuel - 1))
  trace[fsym.prof] "norule {((← IO.getNumHeartbeats)-h2)/1000}"
  -- an indirect call that no rule covers: the arm that the function pointer selects
  if L.conc && x.isAppOfArity ``Full.callIndirect 5 then
    return ← indirectWalk g L α P c Q x user extra fuel
  if let some x' := unfolded? then
    let c' ← mkAppM ``Bind.bind #[x', f]
    let g' ← g.replaceTargetDefEq (mkT L α P c' Q)
    return ← walk g' user extra (fuel - 1)
  logInfo m!"fsym: no rule for the command{indentExpr x}\nwith the precondition{indentExpr P}"
  return [g]

end

/-- `fsym_entail`: close a goal `EUpd P Q` (a frame-preserving update into an assertion) with
the planner of `fsym`; facts of `Q` it cannot prove are left as goals. -/
elab "fsym_entail" : tactic => do
  let g ← getMainGoal
  withRunCaches do
    discard <| arithSimpCtx
    replaceMainGoal (← closeEntail g)

/-- `fsym`, `fsym [r, …]`: symbolic execution of the goal's program. The `rᵢ` are step rules
(triples, tried before the library's) or simp lemmas for the program. -/
syntax (name := fsymTac) "fsym" (" [" term,* "]")? : tactic

@[tactic fsymTac] def evalFsym : Tactic := fun stx => do
  -- `(" [" term,* "]")?`: the optional node holds the three parts (none if absent)
  let args : Array Syntax := if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs else #[]
  let mut user := #[]
  let mut extra := #[]
  for a in args do
    let e ← elabTerm a none
    let ty ← instantiateMVars (← inferType e)
    -- not `forallMetaTelescopeReducing`: a `CTriple` unfolds to a `∀`
    let (_, _, concl) ← forallMetaTelescope ty
    if (ruleConcl? (← whnfR concl)).isSome then user := user.push e
    else extra := extra.push a
  -- a goal `∀ s, CTriple …` (a loop body for `CTriple.loop`): its binders are introduced
  let (_, g) ← (← getMainGoal).intros
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
  withRunCaches do
    discard <| arithSimpCtx
    let h0 ← IO.getNumHeartbeats
    let gs ← walk g user extra 400
    trace[fsym.total] "heartbeats {((← IO.getNumHeartbeats) - h0) / 1000}"
    replaceMainGoal gs

end Zig.Full.Auto
