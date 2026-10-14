import ZigLean.Sep.Full.AutoConc
import ZigLean.Sep.Full.AutoThread
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Parts

/-!
# `fsym`: symbolic execution of generated code in the full-state logic

`fsym` proves a goal `FTotalTriple P c Q`, `FTriple P c Q` or `L.T P c Q` (any `FLogic`),
`CTriple P c Q` (a call of a concurrent function, stop by stop: the backend `Bk.conc`, rules in
`AutoConc.lean`; its `MemM` steps take thread rules, as in `Bk.thr`), or a thread's step `FTTotalTriple P c Q`, `FTTriple P c Q` (`Bk.thr`, rules in
`AutoThread.lean`: a sequential rule applies with the locality of its command, `ofSeq`), by
walking the generated program `c` (`docs/proof-automation.md`); a thread's run in a protocol
`P.WP t c Q G m n` is walked the same way with the context as its state (§The `WP` backend):

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
def isLibrary (c : Name) : MetaM Bool :=
  return isLibraryConst (← getEnv) c

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

/-- `List.map f` over a list literal (or a definition of one) expanded to the literal of the
images, beta-reduced (a
table's arms at a call's arguments, `Table.callOr`). Then `reduceProjs` turns an argument of the
call (`(c, ?n, …).2.1`) into the metavariable itself, which unification assigns the program's
literal as written; left as a projection, unification unfolds the literal (`4#64` to its
structure) to meet it. -/
def expandMapLits (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isHeadBetaTarget then return .visit x.headBeta
    unless x.isAppOfArity ``List.map 4 do return .continue
    -- the list itself may be a definition of the proof (a table `targets := [(c₁, g₁), …]`)
    let l ← whnfD x.appArg!
    unless l.isAppOfArity ``List.cons 3 || l.isAppOfArity ``List.nil 1 do return .continue
    return .visit (← whnfD (mkApp x.appFn! l)))

/-- Raw natural-number literals as numerals (`OfNat.ofNat n`): unification can assign a rule's
argument a raw literal (`BitVec.ofNat 6 ?k =?= 3`, an interface's alignment), which the
precondition's atoms (`2 ^ ?k`) must match as the state writes them. Equal up to `instOfNatNat`. -/
def normNatLits (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x.isAppOfArity ``OfNat.ofNat 3 then return .done x
    if let .lit (.natVal n) := x then return .done (mkNatLit n)
    return .continue)

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

/-- The logic of a goal (the backend): `L.T` of an `FLogic` `L` (sequential programs), the
concurrent `CTriple` (`conc`; `L` is the target type `Tgt`), or `L.T` of a `TLogic` `L` (`thr`: a
thread's step, `AutoThread.lean`). -/
structure Bk where
  conc : Bool
  L : Expr
  thr : Bool := false
  deriving Inhabited

/-- Partial correctness: partial (`FTriple`, `FTTriple`) rules apply too. -/
def Bk.part (B : Bk) : Bool :=
  B.conc || B.L.isConstOf ``FLogic.partial || B.L.isConstOf ``TLogic.partial

/-- The backend's version of a structural lemma of `AutoRules.lean` (`C.n` for `CTriple`, `Th.n`
for a thread logic, with the same arguments). -/
def Bk.nm (B : Bk) (n : Name) : Name :=
  if B.conc then n.getPrefix ++ `C ++ .mkSimple n.getString!
  else if B.thr then n.getPrefix ++ `Th ++ .mkSimple n.getString!
  else n

/-- A goal `L.T P c Q` or `CTriple P c Q`: `(B, α, P, c, Q)`; `FTotalTriple`/`FTriple` goals
are restated as `L.T` of an `FLogic`, `FTTotalTriple`/`FTTriple` goals as `L.T` of a `TLogic`. -/
def view (g : MVarId) : MetaM (MVarId × Bk × Expr × Expr × Expr × Expr) := do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  for (T, conc, thr) in [(``FLogic.T, false, false), (``CTriple, true, false), (``TLogic.T, false, true)] do
    if t.isAppOfArity T 5 then
      let a := t.getAppArgs
      return (g, { conc, L := a[0]!, thr }, a[1]!, a[2]!, a[3]!.consumeMData, a[4]!)
  for (k, T, L, thr) in [(``FTotalTriple, ``FLogic.T, ``FLogic.total, false),
      (``FTriple, ``FLogic.T, ``FLogic.partial, false), (``FTTotalTriple, ``TLogic.T, ``TLogic.total, true),
      (``FTTriple, ``TLogic.T, ``TLogic.partial, true)] do
    if t.isAppOfArity k 4 then
      let a := t.getAppArgs
      let L := mkConst L
      let g' ← g.replaceTargetDefEq (mkAppN (mkConst T) #[L, a[0]!, a[1]!, a[2]!, a[3]!])
      return (g', { conc := false, L, thr }, a[0]!, a[1]!, a[2]!.consumeMData, a[3]!)
  throwError "fsym: expected an FTotalTriple, FTriple, FLogic.T, CTriple, FTTotalTriple, FTTriple or \
    TLogic.T goal{indentExpr t}"

def mkT (B : Bk) (α P c Q : Expr) : Expr :=
  mkAppN (mkConst (if B.conc then ``CTriple else if B.thr then ``TLogic.T else ``FLogic.T))
    #[B.L, α, P, c, Q]

/-- The kind of a rule's conclusion: a total (`FTotalTriple`) or partial (`FTriple`) triple of a
`MemM` command, a thread's (`FTTotalTriple`, `FTTriple`), or a `CTriple` of a concurrent one;
`(kind, command)`. -/
def ruleConcl? (concl : Expr) : Option (Name × Expr) :=
  if concl.isAppOfArity ``CTriple 5 then some (``CTriple, concl.getArg! 3)
  else
    [``FTotalTriple, ``FTriple, ``FTTotalTriple, ``FTTriple].findSome? fun k =>
      if concl.isAppOfArity k 4 then some (k, concl.getArg! 2) else none

/-- `P.WP t x Q G m n` (`Proto.WP`, a thread's run in a protocol: the `WP` backend). -/
def wpN : Name := ``Zig.Conc.Proto.WP

/-- The arguments `#[Tgt, γ, P, α, t, x, Q, G, m, n]` of a `WP` goal. -/
def wpArgs? (e : Expr) : Option (Array Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity wpN 10 then some e.getAppArgs else none

/-- The key of a `WP` rule or command `x`: the head of the command, through `StateT.run` (a
step of a concurrent body `(c : CM σ α).run s`). -/
def wpKey (x : Expr) : Name :=
  let x := x.consumeMData
  let x := if x.isAppOfArity ``StateT.run 5 then x.getArg! 3 else x
  match x.consumeMData.getAppFn with
  | .const c _ => `wp ++ c
  | .fvar _ => `wp.fvar
  | _ => `wp

/-- A thread's rule kind (`FTTotalTriple`, `FTTriple`). -/
def isThreadKind (k : Name) : Bool := k == ``FTTotalTriple || k == ``FTTriple

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
partial def unifyKeyed (a b : Expr) (anyGround := false) : MetaM Bool := do
  let ka := headKey a
  let kb := headKey b
  if ka != kb && ka != .anonymous && kb != .anonymous then
    -- values (words, numbers, flags) of different heads may still be equal by unfolding
    -- (`os.protReadWrite` and the generated `Packed.toBits (Packed.ofBits 3)`)
    -- ground values only: a pattern with metavariables must not be matched by unfolding
    -- proofs are irrelevant (a generated `_proof_1` against the rule's proof argument)
    if ← isProof a then return ← isDefEq a b
    if (← instantiateMVars a).hasExprMVar || (← instantiateMVars b).hasExprMVar then return false
    -- (a `WP` rule's command is a sync op of values of any type: a lock's states `S.unl`)
    unless anyGround do
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
          unless ← unifyKeyed x y anyGround do return false
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
  factLemmas : IO.Ref (Option (Array (Array Name × Name)))
  /-- Failed case probes of split terms (`detProbe`): the fact sets they failed with. -/
  detFail : IO.Ref (Std.HashMap Expr (Array (Std.HashSet Expr)))
  /-- The simp context that turns Boolean tests into propositions (`boolFactCtx`). -/
  boolCtx : IO.Ref (Option Simp.Context)
  /-- Derived fields (`encFieldOf?`) by struct type, field type and offset: `get`, `set` and
  the `EncField` proof (closed terms), or `none`. -/
  fields : IO.Ref (Std.HashMap (Expr × Expr × Nat) (Option (Expr × Expr × Expr)))
  /-- The atoms the planner did not find in the state during the current step (its unknowns
  abstracted): what a view of a state atom may provide (`viewStep`). -/
  wanted : IO.Ref (Array AbstractMVarsResult)
  /-- The program a view retries (`viewStep`): its command must be taken by a rule, not unfolded. -/
  viewProg : IO.Ref (Option Expr)
  /-- The context the caller's terms (`fsym [t]`) were elaborated in (`refreshUser`). -/
  userCtx : IO.Ref LocalContext
  /-- The `WP` backend's simp contexts: concurrent bodies, and hypotheses after a stop. -/
  wpProg : IO.Ref (Option (Simp.Context × Simp.SimprocsArray))
  wpHyp : IO.Ref (Option Simp.Context)
  /-- The substitutions of the run (`destruct`): a local that a fact eliminated, by its value
  (`refreshUser` relates a caller's term to the context after them). -/
  substs : IO.Ref (Std.HashMap FVarId Expr)
  /-- The heads of the assertions that the caller's updates produce (`fsym [u]`, `u : EUpd X Y`):
  a postcondition's atom of such a head is the update's to close, not unfolded (`instQ`), except
  in a return's last attempt, when no update applies (`updUnfold`). -/
  updHeads : IO.Ref (Array Name)
  updUnfold : IO.Ref Bool

def RunCaches.new : IO RunCaches :=
  return { hyp := ← IO.mkRef {}, disch := ← IO.mkRef {}, facts := ← IO.mkRef #[],
           probe := ← IO.mkRef {}, ctx := ← IO.mkRef none, prog := ← IO.mkRef none,
           rules := ← IO.mkRef none, fold := ← IO.mkRef none, factLemmas := ← IO.mkRef none,
           detFail := ← IO.mkRef {}, boolCtx := ← IO.mkRef none, fields := ← IO.mkRef {},
           wanted := ← IO.mkRef #[], viewProg := ← IO.mkRef none, userCtx := ← IO.mkRef {},
           wpProg := ← IO.mkRef none, wpHyp := ← IO.mkRef none, substs := ← IO.mkRef {},
           updHeads := ← IO.mkRef #[], updUnfold := ← IO.mkRef false }

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
  finally
    fsymRuns.modify (·.erase id)
    fsymEvalCache.modify (·.filter fun k _ => k.1 != id)

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

/-- A cached case probe of a split term (`omegaFacts`) from the facts `base`: not retried where
it failed before with a superset of `base` (`omega` proves nothing from fewer facts), in any
context (the facts are proofs: the same term is the same proposition). A skipped probe only
leaves the term to `omega`'s case split. -/
def detProbe (key : Expr) (base : Array Expr) (run : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let failed := ((← (← caches).detFail.get).get? key).getD #[]
  if failed.any fun s => base.all s.contains then return none
  let r ← probe key base.size run
  if r.isNone then
    (← caches).detFail.modify (·.insert key (failed.push (Std.HashSet.ofArray base)))
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
`minAtom`, `maxAtom`): `omega` explores no case split for them. (The facts: arithmetic, relevant
to `ty`, `omegaFacts`.) -/
def omegaFactsOn (arith : Array (Expr × Expr)) (ty : Expr) : MetaM (Option Expr) := do
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
      detProbe (mkApp2 (mkConst `fsym.det) x prop) base (omegaRaw base prop)
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

/-- A fact that `omega` proves by cases: a disjunction, a negated conjunction (pairwise
disjointness of the parts' bytes, `bs.size = 0 ∨ … ∨ …`). -/
def isCaseFact (t : Expr) : Bool :=
  (t.find? fun e => e.isAppOfArity ``Or 2 ||
    (e.isAppOfArity ``Not 1 && e.appArg!.isAppOfArity ``And 2)).isSome

/-- `omega` proves `ty` from `facts`: the relevant arithmetic facts (`relevantFacts`), first
without the facts it would split on (`isCaseFact`: each doubles its search, and most goals do
not need them, ledger #53), then all. -/
def omegaFacts (facts : Array Expr) (ty : Expr) : MetaM (Option Expr) := do
  let mut arith : Array (Expr × Expr) := #[]
  for f in facts do
    let t ← instantiateMVars (← inferType f)
    if ← isArithProp t then arith := arith.push (f, t)
  let ty ← instantiateMVars ty
  arith := relevantFacts arith ty
  let plain := arith.filter fun (_, t) => !isCaseFact t
  if plain.size < arith.size then
    if let some pf ← omegaFactsOn plain ty then return some pf
  omegaFactsOn arith ty

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
      ``bne_eq_false_iff_eq, ``ne_eq, ``eq_self, ``iff_self, ``false_or, ``or_false, ``true_and,
      ``and_true, ``not_false_eq_true, ``not_true_eq_false] do
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

/-- `x = y` up to arithmetic: equal up to reducible unfolding and proof irrelevance, numbers and
words equal by the arithmetic solver, applications of one function equal argument by argument
(`replicate x.toNat b` and `replicate (n + 1) b` with the fact `x.toNat = n + 1`). -/
partial def congrEq (x y : Expr) (fuel : Nat := 8) : TacticM (Option Expr) := do
  if ← withReducibleAndInstances (isDefEq x y) then return some (← mkEqRefl x)
  if fuel == 0 then return none
  let ty ← whnfR (← inferType x)
  if ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isAppOfArity ``BitVec 1 then
    let m ← mkFreshExprMVar (← mkEq x y)
    unless ← arithCore m.mvarId! (quick := true) do return none
    return some (← instantiateMVars m)
  let (fx, fy) := (x.getAppFn, y.getAppFn)
  unless fx.isConst && fy.isConst && fx.constName! == fy.constName! &&
      x.getAppNumArgs == y.getAppNumArgs do return none
  unless ← isDefEq fx fy do return none
  let s ← saveState
  try
    let mut pf ← mkEqRefl fx
    for (a, b) in x.getAppArgs.zip y.getAppArgs do
      if ← withReducibleAndInstances (isDefEq a b) then
        pf ← mkCongrFun pf a
      else
        let some e ← congrEq a b (fuel - 1) | s.restore; return none
        -- a dependent argument (`mkCongr` needs a nondependent function) fails
        pf ← mkCongr pf e
    return some pf
  catch _ => s.restore; return none

/-- Close a goal that is not arithmetic by a hypothesis that is not arithmetic either, equal to
it up to arithmetic in the arguments (`I.fits (n + 1) 0` for `I.fits x.toNat 0` with
`x.toNat = n + 1`, `congrEq`), or up to projections of structure values and unfolding in one
Boolean argument, the others equal (`{ names := ns, .. }.names.contains e = true` by
`Option.all domain.names.contains (some e) = true`). -/
def assumptionEq (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if ← isArithProp t then return false
  let t' ← reduceProjs t
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt ← instantiateMVars d.type
    unless headKey dt == headKey t' && dt.getAppNumArgs == t'.getAppNumArgs do continue
    unless ← isProp dt do continue
    if ← isArithProp dt then continue
    let dt' ← reduceProjs dt
    let s ← saveState
    if let some e ← congrEq dt' t' then
      g.assign (← mkExpectedTypeHint (← mkEqMP e (← mkExpectedTypeHint d.toExpr dt')) t)
      return true
    s.restore
    -- unfolding: one function, one differing argument that is a Boolean test (data terms such
    -- as bytes are equal up to arithmetic by `congrEq`, never by unfolding them)
    if t'.hasExprMVar || !(← withReducible (isDefEq dt'.getAppFn t'.getAppFn)) then
      s.restore; continue
    let pairs := dt'.getAppArgs.zip t'.getAppArgs
    let differ ← pairs.filterM fun (a, b) => return !(← withReducibleAndInstances (isDefEq a b))
    let [(a, b)] := differ.toList | s.restore; continue
    unless (← whnfR (← inferType a)).isConstOf ``Bool do s.restore; continue
    if ← withDefault (isDefEq a b) then
      g.assign (← mkExpectedTypeHint d.toExpr t); return true
    s.restore
  return false

/-- A goal `match d with …` (on a term, not a variable) where a hypothesis `d = c` names the
constructor application `c`: the goal of `c`'s case. -/
def matchCase? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some m ← matchMatcherApp? t | return none
  for d in m.discrs do
    if d.isFVar then continue
    for h in ← getLCtx do
      if h.isImplementationDetail then continue
      let some (_, l, r) := (← instantiateMVars h.type).eq? | continue
      unless l == d do continue
      let .const c _ := r.getAppFn | continue
      let some (.ctorInfo _) := (← getEnv).find? c | continue
      let s ← saveState
      try
        let mot := Expr.lam `x (← inferType d) (← kabstract t d) .default
        -- a dependent `match` (`match h : d with …`) does not abstract over `d`
        unless ← isTypeCorrect mot do s.restore; continue
        let .reduced t' ← reduceMatcher? (mkApp mot r).headBeta | s.restore; continue
        return some (← g.replaceTargetEq t'.headBeta (← mkCongrArg mot h.toExpr))
      catch _ => s.restore
  return none

/-- The arithmetic solver; a conjunction (also behind a user definition) is split. Returns the
goals it did not prove. `quick`: a probe (no congruence of remainders, no library facts, no
hypotheses up to arithmetic). -/
partial def arithGoals (g : MVarId) (quick := false) : TacticM (List MVarId) := g.withContext do
  if ← g.isAssigned then return []
  -- a hypothesis as stated first (an update's `hv : FV.Facts ctx s` that the context has whole:
  -- not split and its parts proved by `omega` over every fact, ledger #53)
  if ← assumptionR g then return []
  let t ← instantiateMVars (← g.getType)
  let t0 ← whnfR t
  let t' ← if t0.isAppOfArity ``And 2 then pure t0 else
    match t.getAppFn with
    | .const c _ => if ← isLibrary c then pure t0 else
        match ← unfold1 t with
        | some u => whnfR u
        | none => pure t0
    | _ => pure t0
  if t'.isAppOfArity ``And 2 then
    let g ← g.replaceTargetDefEq t'
    let [g1, g2] ← g.apply (mkConst ``And.intro) | return [g]
    return (← arithGoals g1 quick) ++ (← arithGoals g2 quick)
  -- a user definition (`w.FirstFacts`): its unfolding, a `match` by the case a hypothesis selects,
  -- or a hypothesis of the unfolded form (`w.Cov` destructured earlier)
  if t' != t0 then
    let s ← saveState
    let g' ← g.replaceTargetDefEq (← reduceProjs t')
    if let some g'' ← matchCase? g' then return ← arithGoals g'' quick
    if ← assumptionR g' then return []
    s.restore
  if !t.hasFVar && !t.hasMVar then
    if ← closeWith g (← `(tactic| decide)) then return []
  if let some (ty, x, y) := t.eq? then
    if ← withReducible (isDefEq x y) then g.assign (← mkEqRefl x); return []
    -- an equation of values that are not numbers (pointers `p.elem 4 i`, structures): one
    -- function, its arguments equal up to arithmetic
    let ty ← whnfR ty
    unless quick || ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isAppOfArity ``BitVec 1 do
      let s ← saveState
      if let some e ← congrEq x y then g.assign e; return []
      s.restore
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
    if ← assumptionEq g then return []
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
  if x == y then return ← mkEqRefl x
  let tac ← `(tactic| first
      | ac_rfl
      | (simp only [Zig.Full.Auto.sep_emp_eq', Zig.Full.Auto.emp_sep_eq']; ac_rfl)
      | simp only [Zig.Full.Auto.sep_emp_eq', Zig.Full.Auto.emp_sep_eq'])
  -- the atoms as variables: `ac_rfl` sees `⋆` only (not the `+` of an atom's bounds, whose
  -- `LawfulIdentity` search unfolds the atom's arguments: a region's written bytes, #46)
  -- (an atom of `y` equal to one of `x` up to reducible unfolding is the same variable)
  let mut ats := (atoms x).foldl (fun acc a => if acc.contains a then acc else acc.push a) #[]
  let mut ys : Array (Expr × Nat) := #[]
  for a in atoms y do
    match ← ats.findIdxM? fun b => return a == b || (← withReducibleAndInstances (isDefEq a b)) with
    | some i => ys := ys.push (a, i)
    | none => ys := ys.push (a, ats.size); ats := ats.push a
  let s ← saveState
  try
    let pf ← withLocalDeclsDND (ats.map fun _ => (`a, mkConst ``Zig.Full.FAssn)) fun vs => do
      let x' := x.replace fun a => (ats.idxOf? a).map (vs[·]!)
      let y' := y.replace fun a => (ys.find? (·.1 == a)).map (vs[·.2]!)
      let m ← mkFreshExprMVar (← mkEq x' y')
      unless ← closeWith m.mvarId! tac do throwError "reorder"
      mkLambdaFVars vs (← instantiateMVars m)
    return ← mkExpectedTypeHint (mkAppN pf ats).headBeta ty
  catch ex => trace[fsym] "acEq over atoms: {ex.toMessageData}"; s.restore
  let m ← mkFreshExprMVar ty
  unless ← closeWith m.mvarId! tac do
    throwError "fsym: cannot reorder{indentExpr x}\nto{indentExpr y}"
  instantiateMVars m

/-- `t` is a block equation `p.block = _` (`solveBlock`'s goals). -/
def isBlockEq (t : Expr) : Bool :=
  (t.eq?.map fun (_, l, _) => l.isAppOf ``Zig.Ptr.block).getD false

/-- Prove `t` (a `_.block = _` goal) from the context, possibly assigning a block variable. -/
def solveBlock (t : Expr) : MetaM (Option Expr) := do
  -- `(p.add k).block = p.block`: definitional
  if let some (_, l, r) := t.eq? then
    if !l.hasExprMVar && !r.hasExprMVar && r.isAppOf ``Zig.Ptr.block then
      let s ← saveState
      if ← isDefEq l r then return some (← mkEqRefl l)
      s.restore
    -- the block of a pointer value (`(⟨some b, o⟩ : Ptr).block`, also through `Ptr.add`):
    -- by evaluation
    if !l.hasExprMVar then
      let v ← whnfD l
      if v.isAppOfArity ``Option.some 2 || v.isAppOfArity ``Option.none 1 then
        let s ← saveState
        if ← isDefEq v r then return some (← mkExpectedTypeHint (← mkEqRefl l) (← instantiateMVars t))
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

/-- The parts of a `⋆`-tree `P` (`emp` dropped), each with a map from `Within X part` to
`Within X P`. With `unfold`, the parts of a part's unfolding (one definition or `match` at a
time, while it is not a raw predicate `fun r => …`) follow it (`P` as a user states it, not yet
flattened by the walk). -/
partial def withinParts (P : Expr) (unfold := false) : MetaM (Array (Expr × (Expr → MetaM Expr))) := do
  let P := P.consumeMData.headBeta
  if P.isAppOfArity sepN 2 then
    let A := P.appFn!.appArg!
    let B := P.appArg!
    let pa := (← withinParts A unfold).map fun (x, k) =>
      (x, fun h : Expr => do mkAppOptM ``Within.sepL #[none, some A, some B, some (← k h)])
    let pb := (← withinParts B unfold).map fun (x, k) =>
      (x, fun h : Expr => do mkAppOptM ``Within.sepR #[none, some B, some A, some (← k h)])
    return pa ++ pb
  if P.isConstOf empN then return #[]
  let mut out := #[(P, pure)]
  if unfold then
    let P' ← match ← reduceMatcher? P with
      | .reduced e => pure (some e.headBeta)
      | _ => unfold1 P
    if let some P' := P' then
      unless P'.consumeMData.isLambda do out := out ++ (← withinParts P' unfold)
  return out

/-- Proofs of `Within X P`, one for each part of `P` that unifies with `X` (`unifyAtom`). -/
def withinCands (X P : Expr) (unfold := false) : MetaM (Array (MetaM Expr)) := do
  return (← withinParts P unfold).map fun (part, k) => do
    unless ← unifyAtom X part do throwError "fsym: not a part"
    k (← mkAppM ``Within.refl #[part])

/-- The unassigned instance arguments of a lemma (`LawfulEnc U`, a class of propositions too)
by synthesis, where it succeeds. -/
def synthInstArgs (args : Array Expr) : MetaM Unit := do
  for a in args do
    if ← a.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType a)
    if (← isClass? ty).isSome then
      if let some inst ← (try some <$> synthInstance ty catch _ => pure none) then
        discard <| isDefEq a inst

/-- The provider kind of a goal `K … P …`: a constant `K` with a lemma `K.of_within`
(`AutoRules.lean` §Providers over the whole precondition). -/
def providerKind? (t : Expr) : MetaM (Option Name) := do
  let .const k _ := t.getAppFn | return none
  return if (← getEnv).contains (k ++ `of_within) then some k else none

/-- The position of a provider goal's assertion `P`: its last argument of type `FAssn` (the
last argument for `AddrOf b A P`, the first for `OwnsPtr P p n`, before the command for
`ThreadLocal P c`). -/
def assnIdx (t : Expr) : MetaM Nat := do
  let args := t.getAppArgs
  let mut i := args.size
  while i > 0 do
    i := i - 1
    if ← withReducible (isDefEq (← inferType args[i]!) (mkConst ``Zig.Full.FAssn)) then return i
  return args.size - 1

/-- The commands among a provider goal's arguments (of type `MemM _`, also unfolded: a
`StateT.lift` of a `Result`): their positions and heads. A provider lemma about another command
does not apply (`providerLemmas`). -/
def cmdHeads (t : Expr) : MetaM (Array (Nat × Name)) := do
  let args := t.getAppArgs
  let mut out := #[]
  for i in [0:args.size] do
    unless (← whnfR (← inferType args[i]!)).isAppOf ``StateT do continue
    if let .const c _ := args[i]!.getAppFn then out := out.push (i, c)
  return out

/-- The provider lemmas (`@[fsym_provider]`) of the kind `k`, for a goal whose assertion is
argument `ip` and whose commands have the heads `cmds`: those about an atom (the conclusion's
assertion is an application; with its `headKey`), and those about the whole precondition (a
variable). -/
def providerLemmas (k : Name) (ip : Nat) (cmds : Array (Nat × Name)) :
    MetaM (Array (Name × Name) × Array Name) := do
  let mut atomL := #[]
  let mut wholeL := #[]
  for n in fsymProviderExt.getState (← getEnv) do
    let body := (← getConstInfo n).type.getForallBody
    unless body.isAppOf k do continue
    let bargs := body.getAppArgs
    let some a := bargs[ip]? | continue
    -- a command of another head
    if cmds.any (fun (i, c) => match (bargs[i]?.map (·.getAppFn) : Option Expr) with
        | some (Expr.const c' _) => c' != c
        | _ => false) then continue
    if a.isBVar then wholeL := wholeL.push n else atomL := atomL.push (n, headKey a)
  return (atomL, wholeL)

/-- The depth of nested provider goals (a provider whose hypotheses are providers). -/
def providerDepth : Nat := 6

/-- Candidates for a provider goal `t` (a `Within X P`, or a provider kind `K … P`): each assigns
`t`'s unknowns and returns a proof with the goals it leaves (hypotheses of the lemma used). -/
def providerCands (t : Expr) (depth : Nat) : TacticM (Array (TacticM (Expr × List MVarId))) := do
  let t ← instantiateMVars t
  if t.isAppOfArity ``Within 2 then
    return (← withinCands t.appFn!.appArg! t.appArg!).map fun (c : MetaM Expr) => return (← c, [])
  let some k ← providerKind? t | return #[]
  let ip ← assnIdx t
  let targs := t.getAppArgs
  let P := targs[ip]!
  let (atomL, wholeL) ← providerLemmas k ip (← cmdHeads t)
  -- the lemma `n` with its conclusion unified with `concl`, and its hypotheses as goals
  let lemmaGoals (n : Name) (concl : Expr) (atom? : Option Expr := none) :
      TacticM (Expr × List MVarId) := do
    let f ← mkConstWithFreshMVarLevels n
    let (args, _, c) ← forallMetaTelescope (← inferType f)
    -- an atom lemma's atom first, up to instances: a pattern such as a region of `Enc.encode ?v`
    -- does not unfold the encoding against other bytes
    if let some part := atom? then
      unless ← withReducibleAndInstances (isDefEq c.getAppArgs[ip]! part) do
        throwError "fsym: {n} does not apply"
    unless ← isDefEq c concl do throwError "fsym: {n} does not apply"
    synthInstArgs args
    let gs ← args.filterM fun a => do
      if ← a.mvarId!.isAssigned then return false
      isProp (← inferType a)
    return (mkAppN f args, gs.toList.map (·.mvarId!))
  let mut out := #[]
  for (part, k') in ← withinParts P do
    for (n, key) in atomL do
      unless key == .anonymous || key == headKey part do continue
      out := out.push do
        let (h, gs) ← lemmaGoals n (mkAppN t.getAppFn (targs.set! ip part)) part
        let pf ← mkAppM (k ++ `of_within) #[h, ← k' (← mkAppM ``Within.refl #[part])]
        unless ← isDefEq t (← inferType pf) do throwError "fsym: provider mismatch"
        return (pf, gs)
  if depth < providerDepth then
    for n in wholeL do
      out := out.push (lemmaGoals n t)
  return out

/-! ## Fields of typed values (`EncField`)

The field rules (`FTotalTriple.encField_load`/`_store`, `Typed.lean`) take an `EncField T U o get
set`: the `U` at byte `o` of a `T`. For a struct that decodes its fields one after the other (the
translator's `do pure { f := ← Enc.decodeAt bs o, … }`, `Slice`'s), `encFieldOf?` reads the
fields off the decoding and proves the field's `EncField` with the steps of `AutoRules.lean`
(`result_bind_eq_pure`, `decode_write_*`); a field inside a field by `EncField.comp`. Any other
encoding gives no field (the rules do not apply). -/

/-- A field of a struct's decoding: its projection, its type, its bytes `[lo, hi)`, whether they
are all of the struct's (a struct of one field that decodes the whole array) and the position
of its decoding in the struct's `do` block. -/
structure FieldInfo where
  proj : Name
  ty : Expr
  lo : Nat
  hi : Nat
  full : Bool
  pos : Nat
  deriving Inhabited

/-- The value of a closed natural-number term (`(16 : Int).toNat`, `0 + Enc.size Slice`). -/
def natVal? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasFVar then return none
  if let some n ← (evalNat e).run then return some n
  let v ← whnfD e
  return v.rawNatLit? <|> v.nat?

/-- The fields of a struct type `T` from its encoding's decoding (`FieldInfo`, in the order of
the structure's fields), or `none` if the decoding is not one field after the other. -/
partial def structFields? (T : Expr) : MetaM (Option (Array FieldInfo)) := do
  let T ← instantiateMVars T
  if T.hasExprMVar || T.hasFVar then return none
  let env ← getEnv
  let .const sn _ := (← whnfR T).getAppFn | return none
  unless isStructure env sn do return none
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Zig.Enc) T) catch _ => pure none)
    | return none
  let some N ← natVal? (mkApp2 (mkConst ``Zig.Enc.size) T inst) | return none
  withLocalDeclD `bs (mkApp (mkConst ``Array [levelZero]) (mkConst ``Zig.Byte)) fun bs => do
    let some dec ← unfoldProjInst? (mkApp3 (mkConst ``Zig.Enc.decode) T inst bs) | return none
    go env sn bs N dec #[]
where
  /-- The bytes `[lo, hi)` that the decoding `x` of a `α` reads, and whether they are all. -/
  readField? (bs : Expr) (N : Nat) (α x : Expr) : MetaM (Option (Nat × Nat × Bool)) := do
    let x := x.consumeMData
    let some n ← natVal? (← mkAppOptM ``Zig.Enc.size #[α, none]) | return none
    if x.isAppOfArity ``Zig.Enc.decodeAt 4 && x.getArg! 2 == bs then
      let some lo ← natVal? (x.getArg! 3) | return none
      return if lo + n ≤ N then some (lo, lo + n, false) else none
    if x.isAppOfArity ``Zig.Enc.decode 3 then
      let a := x.getArg! 2
      if a == bs then return if n == N then some (0, N, true) else none
      if a.isAppOfArity ``Array.extract 4 && a.getArg! 1 == bs then
        let some lo ← natVal? (a.getArg! 2) | return none
        let some hi ← natVal? (a.getArg! 3) | return none
        return if hi == lo + n && hi ≤ N then some (lo, hi, false) else none
    return none
  /-- Walk the decoding: `x >>= fun a => …` reads a field, `pure (mk a₁ … aₙ)` ends. -/
  go (env : Environment) (sn : Name) (bs : Expr) (N : Nat) (e : Expr)
      (acc : Array (Expr × Nat × Nat × Bool × FVarId)) : MetaM (Option (Array FieldInfo)) := do
    let e := e.consumeMData.headBeta
    if e.isAppOfArity ``Bind.bind 6 then
      let α := e.getArg! 2
      let some (lo, hi, full) ← readField? bs N α (e.getArg! 4) | return none
      let .lam n ty body _ := (e.getArg! 5).consumeMData | return none
      return ← withLocalDeclD n ty fun a =>
        go env sn bs N (body.instantiate1 a) (acc.push (α, lo, hi, full, a.fvarId!))
    unless e.isAppOfArity ``Pure.pure 4 do return none
    let v ← whnfR (e.getArg! 3)
    let some ctor := v.getAppFn.constName? | return none
    let some (.ctorInfo ci) := env.find? ctor | return none
    unless ci.induct == sn do return none
    let args := v.getAppArgs[ci.numParams:].toArray
    let names := getStructureFields env sn
    unless args.size == acc.size && names.size == acc.size do return none
    let mut out := #[]
    for j in [0:args.size] do
      let some pos := acc.findIdx? fun r => args[j]! == .fvar r.2.2.2.2 | return none
      if out.any (·.pos == pos) then return none
      let (α, lo, hi, full, _) := acc[pos]!
      let some proj := getProjFnForField? env sn names[j]! | return none
      out := out.push { proj, ty := α, lo, hi, full, pos }
    return some out

/-- Run tactics one after the other on the single goal `g`; `true` if they close it (else the
state is restored). -/
def closeSeq (g : MVarId) (tacs : Array Syntax) : TacticM Bool := do
  let s ← saveState
  try
    let mut gs := [g]
    for t in tacs do
      let [g'] := gs | throwError "fsym: closeSeq"
      gs ← evalTacticAt t g'
    if gs.isEmpty then return true
    s.restore; return false
  catch ex =>
    trace[fsym] "closeSeq: {ex.toMessageData}"
    s.restore; return false

-- the steps name their hypotheses (`hd`, `hₚ`) and the pattern `rfl` across tactics
set_option hygiene false in
/-- The `EncField` of field `j` of the struct `T` (fields `fs`): `get`, `set` and its proof. -/
def encFieldDirect (T : Expr) (fs : Array FieldInfo) (j : Nat) :
    TacticM (Option (Expr × Expr × Expr)) := do
  let f := fs[j]!
  let get ← withLocalDeclD `s T fun s => do mkLambdaFVars #[s] (← mkAppM f.proj #[s])
  let set ← withLocalDeclD `s T fun s => withLocalDeclD `v f.ty fun v => do
    let parts ← fs.mapIdxM fun i g => if i == j then pure v else mkAppM g.proj #[s]
    let Tw ← whnfR T
    let .const sn us := Tw.getAppFn | throwError "fsym: not a structure"
    let ctor := getStructureCtor (← getEnv) sn
    mkLambdaFVars #[s, v] (mkAppN (mkAppN (mkConst ctor.name us) Tw.getAppArgs) parts)
  let ty ← mkAppM ``Zig.Full.EncField #[T, f.ty, mkNatLit f.lo, get, set]
  let pf ← mkFreshExprMVar ty
  let some [gFit, gGet, gSet] ← observing? (evalTacticAt (← `(tactic| refine ⟨?_, ?_, ?_⟩)) pf.mvarId!)
    | return none
  let id (s : String) : Ident := mkIdent (.mkSimple s)
  let (hs, hd, hc, hv) := (id "hs", id "hd", id "hc", id "hv")
  let k := fs.size
  -- the decoding of `s` split into its fields `aₚ` with `hₚ : (decoding of field p) = pure aₚ`
  let split : Array Syntax ← do
    let mut out := #[]
    for p in [0:k] do
      out := out.push (← `(tactic| obtain ⟨$(id s!"a{p}"), $(id s!"h{p}"), $hd⟩ :=
        Zig.result_bind_eq_pure $hd))
    out := out.push (← `(tactic| obtain rfl := Zig.Full.Auto.result_pure_inj $hd))
    pure out
  let hi := id s!"h{f.pos}"
  let getTacs : Array Syntax := #[← `(tactic| intro $(id "bs") $(id "s") $hs $hd)] ++ split ++
    #[← if f.full then `(tactic| exact Zig.Full.Auto.decode_extract_full $hs (by decide) $hi)
      else `(tactic| exact $hi)]
  let mut setTacs : Array Syntax :=
    #[← `(tactic| intro $(id "bs") $(id "cs") $(id "s") $(id "v") $hs $hd $hc $hv)] ++ split
  for p in [0:k] do
    let some g := fs.find? (·.pos == p) | return none
    let step ← if p == f.pos then
        if f.full then `(Zig.Full.Auto.decode_write_full $hs $hc (by decide) $hv)
        else `(Zig.Full.Auto.decode_write_same $hs $hc (by decide) $hv)
      else `(Zig.Full.Auto.decode_write_other $hs $hc (by decide) (by decide) $(id s!"h{p}"))
    setTacs := setTacs.push (← `(tactic| refine Zig.Full.Auto.result_bind_of_pure $step ?_))
  setTacs := setTacs.push (← `(tactic| rfl))
  unless ← closeWith gFit (← `(tactic| decide)) do return none
  unless ← closeSeq gGet getTacs do
    trace[fsym] "field {f.proj}: get not proved"; return none
  unless ← closeSeq gSet setTacs do
    trace[fsym] "field {f.proj}: set not proved"; return none
  let pf ← instantiateMVars pf
  if pf.hasMVar then return none
  return some (get, set, pf)

/-- The `EncField T U o get set` of the struct type `T`: `get`, `set` (beta-reduced) and its
proof, through fields of fields; cached per run. -/
partial def encFieldOf? (T U : Expr) (o : Nat) (fuel : Nat := 8) :
    TacticM (Option (Expr × Expr × Expr)) := do
  -- a value is not a field of itself (a load of the whole value is the `pts` rule's); no
  -- result is cached when the nesting budget ran out
  if fuel == 0 || T == U then return none
  let key := (T, U, o)
  if let some r := (← (← caches).fields.get).get? key then return r
  let r ← go
  (← caches).fields.modify (·.insert key r)
  return r
where go : TacticM (Option (Expr × Expr × Expr)) := do
  let some fs ← structFields? T | do trace[fsym] "fields of {T}: not a struct's decoding"; return none
  let some j := fs.findIdx? fun f => f.lo ≤ o && o < f.hi | return none
  let f := fs[j]!
  if o == f.lo && (← withNewMCtxDepth (isDefEq f.ty U)) then return ← encFieldDirect T fs j
  let some (_, _, h₂) ← encFieldOf? f.ty U (o - f.lo) (fuel - 1) | return none
  -- the outer field through the cache (shared by every field inside it)
  let some (_, _, h₁) ← encFieldOf? T f.ty f.lo fuel | return none
  let pf ← mkAppM ``Zig.Full.EncField.comp #[h₁, h₂]
  let a := (← inferType pf).getAppArgs
  let (get, set) := (← Core.betaReduce a[5]!, ← Core.betaReduce a[6]!)
  let ty ← mkAppM ``Zig.Full.EncField #[T, U, mkNatLit o, get, set]
  return some (get, set, ← mkExpectedTypeHint pf ty)

/-- Prove a side goal `EncField T U o get set` (assigning `get` and `set`). -/
def encFieldGoal (t : Expr) : TacticM (Option Expr) := do
  let a := t.getAppArgs
  let some o ← natVal? a[4]! | do trace[fsym] "field offset {a[4]!}: not a number"; return none
  let some (get, set, pf) ← encFieldOf? (← instantiateMVars a[0]!) (← instantiateMVars a[1]!) o
    | return none
  unless ← isDefEq a[5]! get <&&> isDefEq a[6]! set <&&> isDefEq (← inferType pf) t do return none
  return some pf

/-- The pointer `o` bytes past `q`, as generated code and specifications write it: `q` itself,
or `p.add k` with the offsets added (`q = p.add c`), so that it unifies with the parts' own. -/
def ptrAt (q : Expr) (o : Nat) : MetaM Expr := do
  if o == 0 then return q
  let q' := q.consumeMData
  if q'.isAppOfArity ``Zig.Ptr.add 2 then
    if let some c ← getIntValue? (q'.getArg! 1) then
      if 0 ≤ c then return mkApp2 (mkConst ``Zig.Ptr.add) (q'.getArg! 0) (toExpr (c + o))
  return mkApp2 (mkConst ``Zig.Ptr.add) q (toExpr (o : Int))

-- `readsStruct`'s steps name their hypotheses across tactics
set_option hygiene false in
/-- Solve the side goals of a rule, in order; providers backtrack over their candidates, and the
goals a candidate leaves (depth above 0) are solved before the rest: all of them, or the
candidate fails. Returns the arithmetic goals of the rule left unproved, or `none` if a block,
provider or nested goal fails. -/
partial def solveSides (gs : List MVarId) : TacticM (Option (List MVarId)) :=
  go (gs.map (·, 0))
where
  go : List (MVarId × Nat) → TacticM (Option (List MVarId))
  | [] => return some []
  | (g, depth) :: rest => do
    if ← g.isAssigned then return ← go rest
    let t ← instantiateMVars (← g.getType)
    if t.isAppOfArity ``Within 2 || (← providerKind? t).isSome then
      let mut first? : Option (Tactic.SavedState × List MVarId) := none
      -- a struct's bytes from its fields' (`readsStruct`), after the parts that hold them whole
      let structCand : Array (TacticM (Expr × List MVarId)) :=
        if t.isAppOfArity ``Zig.Full.ReadsAt 4 then #[do
          let some pf ← g.withContext (readsStruct t depth) | throwError "fsym: no fields read"
          return (pf, [])] else #[]
      for cand in (← g.withContext (providerCands t depth)) ++ structCand do
        let s ← saveState
        try
          let (pf, sub) ← g.withContext cand
          g.assign pf
          match ← go (sub.map (·, depth + 1) ++ rest) with
          | some [] => return some []
          | some left => if first?.isNone then first? := some (← saveState, left)
          | none => pure ()
        catch ex => trace[fsym] "provider candidate: {ex.toMessageData}"
        s.restore
      match first? with
      | some (s, left) => s.restore; return some left
      | none => return none
    else if isBlockEq t then
      let some pf ← g.withContext (solveBlock t) | return none
      g.assign pf
      go rest
    else if t.isAppOfArity ``Zig.Full.EncField 7 then
      let some pf ← g.withContext (encFieldGoal t) | return none
      g.assign pf
      go rest
    else
      -- (an instance is synthesized, never searched by the arithmetic solver)
      let ok ← if (← g.withContext (isClass? t)).isSome then
          (do
            let some i ← g.withContext (observing? (synthInstance t)) | pure false
            g.assign i; pure true)
        else arith g
      if depth > 0 && !ok then return none
      let some left ← go rest | return none
      return some (if ok then left else g :: left)
  /-- The bytes of a struct, `ReadsAt q n (fun bs => Enc.decode bs = pure ?v) P` for a struct
  that decodes its fields one after the other (`structFields?`): each field's bytes (a provider
  goal again, so a field is read from the part that owns it, or from its own fields), the
  struct's in bounds from its first field and a bound of the block (`ReadsAt.base`), the fields'
  put in (`ReadsAt.field`), and the struct of the fields' values decoded from them
  (`ReadsAt.mono` with the struct's decoding, `result_bind_of_pure`). -/
  readsStruct (t : Expr) (depth : Nat) : TacticM (Option Expr) := do
    if depth + 1 ≥ providerDepth then return none
    let a := t.getAppArgs
    let (q, n, D, P) := (a[0]!, a[1]!, a[2]!, a[3]!)
    let .lam bn bty body _ := D.consumeMData | return none
    let some (_, lhs, rhs) := body.eq? | return none
    unless lhs.isAppOfArity ``Zig.Enc.decode 3 && rhs.isAppOfArity ``Pure.pure 4 do return none
    let T := lhs.getArg! 0
    let some fs ← structFields? T | return none
    let some N ← natVal? n | return none
    let some i0 := fs.findIdx? (·.lo == 0) | return none
    let Tw ← whnfR T
    let .const sn us := Tw.getAppFn | return none
    let ctor := getStructureCtor (← getEnv) sn
    let decodeIs (U v : Expr) : MetaM Expr := withLocalDeclD bn bty fun bs => do
      mkLambdaFVars #[bs] (← mkEq (← mkAppOptM ``Zig.Enc.decode #[U, none, bs])
        (mkAppN rhs.getAppFn #[rhs.getArg! 0, rhs.getArg! 1, U, v]))
    -- each field's bytes, and a bound of the block
    let mut vs := #[]
    let mut ptrs := #[]
    let mut goals := #[]
    for f in fs do
      let v ← mkFreshExprMVar f.ty
      let qf ← ptrAt q f.lo
      let g ← mkFreshExprMVar (mkAppN (mkConst ``Zig.Full.ReadsAt)
        #[qf, mkNatLit (f.hi - f.lo), ← decodeIs f.ty v, P])
      vs := vs.push v; ptrs := ptrs.push qf; goals := goals.push g
    let some (b, hqb) ← blockOf q | return none
    let K ← mkFreshExprMVar (mkConst ``Nat)
    let gr ← mkFreshExprMVar (← mkAppM ``Zig.Full.Reaches #[b, K, P])
    let qoff ← mkAppM ``Zig.Ptr.off #[q]
    let ga ← mkFreshExprMVar (← mkAppM ``LE.le
      #[← mkAppM ``HAdd.hAdd #[← mkAppM ``Int.toNat #[qoff], n], K])
    let some [] ← go ((goals.toList ++ [gr, ga]).map (·.mvarId!, depth + 1)) | return none
    let mut acc ← mkAppM ``Zig.Full.ReadsAt.base
      #[← instantiateMVars goals[i0]!, hqb, ← instantiateMVars gr, ← instantiateMVars ga]
    for i in [0:fs.size] do
      let f := fs[i]!
      let qb ← mkAppM ``Zig.Ptr.block #[q]
      let qfb ← mkAppM ``Zig.Ptr.block #[ptrs[i]!]
      unless ← isDefEq qfb qb do return none
      let hb ← mkExpectedTypeHint (← mkEqRefl qb) (← mkEq qfb qb)
      let ho ← mkFreshExprMVar (← mkEq (← mkAppM ``Zig.Ptr.off #[ptrs[i]!]) (← mkAppM ``HAdd.hAdd
        #[qoff, ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, mkNatLit f.lo]]))
      unless ← arith ho.mvarId! do return none
      let hk ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (f.lo + (f.hi - f.lo)), n])
      acc ← mkAppM ``Zig.Full.ReadsAt.field #[acc, ← instantiateMVars goals[i]!, hb,
        ← instantiateMVars ho, hk]
    -- the struct of the fields' values, from the struct's decoding
    let vals ← vs.mapM instantiateMVars
    let v := mkAppN (mkConst ctor.name us) (Tw.getAppArgs ++ vals)
    let Dacc := (← inferType acc).getArg! 2
    let hdT ← withLocalDeclD bn bty fun bs => do
      let hs ← mkEq (← mkAppM ``Array.size #[bs]) n
      mkForallFVars #[bs] (← mkArrow hs (← mkArrow (mkApp Dacc bs).headBeta
        (mkApp (← decodeIs T v) bs).headBeta))
    let hd ← mkFreshExprMVar hdT
    let id (s : String) : Ident := mkIdent (.mkSimple s)
    let mut tacs : Array Syntax := #[← `(tactic| intro $(id "bs") $(id "hs") $(id "h"))]
    for i' in [0:fs.size] do
      let i := fs.size - 1 - i'
      tacs := tacs.push (← `(tactic| obtain ⟨$(id s!"h{i}"), $(id "h")⟩ := $(id "h")))
    for p in [0:fs.size] do
      let some i := fs.findIdx? (·.pos == p) | return none
      let hi := id s!"h{i}"
      tacs := tacs.push (← if fs[i]!.full then
          `(tactic| refine Zig.Full.Auto.result_bind_of_pure
            (Zig.Full.decode_of_extract_all $(id "hs") $hi) ?_)
        else `(tactic| refine Zig.Full.Auto.result_bind_of_pure $hi ?_))
    tacs := tacs.push (← `(tactic| rfl))
    unless ← closeSeq hd.mvarId! tacs do
      trace[fsym] "bytes of {T}: the decoding of the fields not proved"; return none
    let pf ← mkAppM ``Zig.Full.ReadsAt.mono #[acc, ← instantiateMVars hd]
    unless ← isDefEq t (← inferType pf) do return none
    return some pf

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

/-- A value that a field's equation substitutes (`substCtor`): a constructor application of a type
with several constructors (`isCaseCtorApp`), or a closed term of a type that is not arithmetic
(`w.M = GMap.empty`: words and numbers stay facts of the arithmetic solver). -/
def isSubstValue (e : Expr) : MetaM Bool := do
  if ← isCaseCtorApp e then return true
  if e.hasFVar || e.hasMVar || e.isLit then return false
  let .const _ _ := e.getAppFn | return false
  let ty ← whnfR (← inferType e)
  if ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool || ty.isAppOf ``BitVec || ty.isSort then
    return false
  return !(← isProp ty)

/-- A fact `o.isSome = true`, `¬o.isSome = true`, `o.isSome = false` (or the same of `isNone`):
the lemma that turns it into `o = none` or `∃ a, o = some a`, and `o`. -/
def optTest? (ty : Expr) : Option (Name × Expr) := do
  let (neg, e) := if ty.isAppOfArity ``Not 1 then (true, ty.appArg!) else (false, ty)
  let (_, l, r) ← e.eq?
  let isSome ← if l.isAppOfArity ``Option.isSome 2 then some true
    else if l.isAppOfArity ``Option.isNone 2 then some false else none
  let val ← if r.isConstOf ``Bool.true then some true
    else if r.isConstOf ``Bool.false then some false else none
  let lem ← match isSome, val, neg with
    | true, true, false => some ``opt_isSome_true
    | true, true, true => some ``opt_not_isSome
    | true, false, false => some ``opt_isSome_false
    | false, true, false => some ``opt_isNone_true
    | false, true, true => some ``opt_not_isNone
    | false, false, false => some ``opt_isNone_false
    | _, _, _ => none
  return (lem, l.appArg!)

/-- A fact `e = true`, `e = false` or `¬e = true` of a Boolean combination `e` of `decide`s. -/
def isBoolTest (ty : Expr) : Bool :=
  let e := if ty.isAppOfArity ``Not 1 then ty.appArg! else ty
  match e.eq? with
  | some (t, l, r) => t.isConstOf ``Bool && (r.isConstOf ``Bool.true || r.isConstOf ``Bool.false) &&
      [``Decidable.decide, ``not, ``and, ``or].any l.isAppOf
  | none => false

/-- The simp context that turns a Boolean test (`isBoolTest`) into a proposition; once per run. -/
def boolFactCtx : MetaM Simp.Context := do
  if let some c ← (← caches).boolCtx.get then return c
  let mut thms : SimpTheorems := {}
  for n in [``Bool.not_eq_true', ``Bool.not_eq_false', ``Bool.not_eq_true, ``Bool.not_eq_false,
      ``decide_eq_true_eq, ``decide_eq_false_iff_not, ``Bool.and_eq_true, ``Bool.or_eq_true,
      ``Decidable.not_not] do
    thms ← thms.addConst n
  let c ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  (← caches).boolCtx.set (some c)
  return c

mutual
/-- A fact `t = C …` of a term `t` that is not a variable (a field of the locals, of a witness)
and a constructor application: `t` is replaced by `C …` in the goal and in the other facts,
which are split again, so a `match` on `t` (in the precondition, in a fact) reduces. `none` if
there is nothing to do or the goal does not abstract over `t`. -/
partial def substCtor (g : MVarId) (h : FVarId) (l r : Expr) : TacticM (Option MVarId) := g.withContext do
  let (t, symm) ← if (← isSubstValue r) && !(← isSubstValue l) then pure (l, false)
    else if (← isSubstValue l) && !(← isSubstValue r) then pure (r, true)
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

/-- A fact `x.1 = C …` about a component of a local pair `x` (a callee's result `r.1 = .br18`,
which `substCtor` does not substitute: `Prod.fst` is the library's): `x` by its components
(`cases`), the projections of the new pair reduced in the facts, which are split again (the
component's equation is then a local's, substituted), so a `match x.1` reduces. -/
partial def etaProj (g : MVarId) (l r : Expr) : TacticM (Option MVarId) := g.withContext do
  let local? (e : Expr) : MetaM (Option FVarId) := do
    let e := e.consumeMData
    let s? ← match e with
      | .proj _ _ s => pure (some s)
      | _ => do
        let .const c _ := e.getAppFn | return none
        let some info ← getProjectionFnInfo? c | return none
        if info.fromClass then return none
        pure (e.getAppArgs[info.numParams]?)
    let some (.fvar x) := s? | return none
    -- (a pair: a generated body's result; a user structure's field goes through `substCtor`,
    -- and the library's other structures keep their facts, `p.block = some b`)
    let ty ← whnfR (← instantiateMVars (← x.getType))
    unless ty.isAppOfArity ``Prod 2 do return none
    return some x
  let x? ← if ← isSubstValue r then local? l else if ← isSubstValue l then local? r else pure none
  let some x := x? | return none
  let s ← saveState
  try
    let gs ← g.cases x
    let some sg := gs[0]? | return none
    (← caches).substs.modify fun m => sg.subst.map.foldl (fun m k v => m.insert k v) m
    let mut g := sg.mvarId
    let mut changed := #[]
    for d in ← g.withContext getLCtx do
      if d.isImplementationDetail then continue
      unless ← g.withContext (isProp d.type) do continue
      let ty ← g.withContext do instantiateMVars d.type
      let ty' ← g.withContext (reduceProjs ty)
      if ty' != ty then
        g ← g.replaceLocalDeclDefEq d.fvarId ty'
        changed := changed.push d.fvarId
    for f in changed do
      if (← g.withContext f.findDecl?).isSome then g ← destruct g f
    return some g
  catch ex =>
    trace[fsym] "etaProj: {ex.toMessageData}"
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
  -- a Boolean test (`(!decide (b = b' ∧ x = y)) = false`, of a pointer `==`): as a proposition
  if isBoolTest ty then
    let (r, _) ← simp ty (← boolFactCtx)
    if r.expr != ty && !r.expr.isFalse then
      if let some (h', g') ← applySimpResultToLocalDecl g h r false then
        return ← destruct g' h'
  -- a test of an optional that is not a constructor: its constructor equation (`opt_*`), next
  -- to the test
  if let some (lem, o) := optTest? ty then
    unless ← isCaseCtorApp o do
      let pf ← mkAppM lem #[mkFVar h]
      let (h', g') ← (← g.assert `hopt (← inferType pf) pf).intro1
      return ← destruct g' h'
  if let some (_, l, r) := ty.eq? then
    if l.isFVar || r.isFVar then
      if let some (fs, g') ← observing? (substEq g h) then
        -- (recorded: a caller's term that names an eliminated local takes its value)
        (← caches).substs.modify fun m => fs.map.foldl (fun m k v => m.insert k v) m
        return g'
    if let some g' ← substCtor g h l r then return g'
    if let some g' ← etaProj g l r then return g'
    return g
  -- a fact of a user structure (`NodeFacts N A sz`): its fields next to it (the fact stays, as
  -- the hypothesis of a lemma), each once
  if let .const c _ := ty.getAppFn then
    let env ← getEnv
    if isStructure env c && (← isProp ty) && !(← isLibrary c) && (← isClass? ty).isNone then
      let mut g := g
      for fn in getStructureFields env c do
        let pf ← g.withContext (mkProjection (mkFVar h) fn)
        let fty ← instantiateMVars (← g.withContext (inferType pf))
        if ← g.withContext ((← getLCtx).anyM fun d => return d.type == fty) then continue
        let (h', g') ← (← g.assert fn fty pf).intro1
        g ← destruct g' h'
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

/-- The continuation of opening an existential `FAssn.ex F` of a precondition: a fresh goal
`∀ x, goal (F x)` (`x` named after `F`'s binder) and that name. -/
def exCont (F : Expr) (goal : Expr → MetaM Expr) : MetaM (Expr × Name) := do
  let β := (← whnfD (← inferType F)).bindingDomain!
  let n := match F.consumeMData with | .lam n .. => n | _ => `x
  let kTy ← withLocalDeclD n β fun x => do mkForallFVars #[x] (← goal (mkApp F x).headBeta)
  return (← mkFreshExprSyntheticOpaqueMVar kTy, n)

/-- `if c then X else Y` of assertions where the facts decide `c`: `(X or Y, proof of the
equation)`. An undecided condition is retried only once there are more facts. -/
def decideIte (a : Expr) (quick := true) : TacticM (Option (Expr × Expr)) := do
  let args := a.getAppArgs
  let (c, inst, x, y) := (args[1]!, args[2]!, args[3]!, args[4]!)
  -- a condition on an unknown (an existential of a postcondition, `?cap.toNat = 0`) is not
  -- decided by a fact of the context, which would fix the unknown (ledger #44): the atoms that
  -- determine it come first (`closeEntail`, branch by branch)
  if (← instantiateMVars c).hasExprMVar then return none
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
  -- the first fact or existential into the context (`lift_sep`, `ex_sep`), built from the parts
  -- of the goal: no elaboration against the goal, which would reduce its program
  let a := facts[0]!
  let R := sepOf (facts.eraseIdx! 0 ++ others)
  if a.isAppOfArity liftN 1 then
    let k ← mkFreshExprSyntheticOpaqueMVar (← mkArrow a.appArg! (mkT L α R c Q))
    g.assign (← mkAppM (L.nm ``lift_sep) #[L.L, k])
    -- (an inaccessible name: the caller's `h` stays the caller's)
    let (h, g') ← k.mvarId!.intro1
    normPre (← destruct g' h) (fuel - 1)
  else
    let (k, n) ← exCont a.appArg! fun Fx => pure (mkT L α (mkSep Fx R) c Q)
    g.assign (← mkAppM (L.nm ``ex_sep) #[L.L, k])
    let (_, g') ← k.mvarId!.intro n
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
`callIndirect` (`callIndirect_fold_one`/`ext`/`cons`) at its `if`, before simp rewrites its tests. -/
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

/-- The caller's simp terms (`fsym [t]` that are not rules) added to `thms`. -/
def addExtra (thms : SimpTheorems) (extra : Array Syntax) : TacticM SimpTheorems := do
  let mut thms := thms
  for x in extra do
    if let some n := (if x.isIdent then some x.getId else none) then
      if let some n ← (try some <$> realizeGlobalConstNoOverloadWithInfo (mkIdent n) catch _ => pure none) then
        -- a definition is unfolded (its equations), a theorem rewrites
        thms ← if ← isProp (← getConstInfo n).type then thms.addConst n else thms.addDeclToUnfold n
        continue
    let e ← Term.elabTerm x none
    thms ← thms.add (.stx (← mkFreshId) x) #[] e
  return thms

/-- Every rewrite carries its proof, also a definitional one (`StateT.run_bind`, a `rfl`
theorem): simp leaves a definitional step to the kernel at a join of its proof (`Eq.trans`),
where it unfolds `StateT.run`/`bind` against the step's continuation, the rest of the program;
on arena `resize` (a `match` on a label after `pure`) that check ran out of 10 GB. -/
def noRflThms (thms : SimpTheorems) : SimpTheorems :=
  let noRfl (ts : Array SimpTheorem) := ts.map ({ · with rfl := false })
  { thms with pre := thms.pre.mapArrays noRfl, post := thms.post.mapArrays noRfl }

/-- The program normal form: `fsym_norm` and the caller's simp terms, with Lean's simprocs. -/
def progCtx (extra : Array Syntax) : TacticM (Simp.Context × Simp.SimprocsArray) := do
  if let some cp ← (← caches).prog.get then return cp
  let some ext ← getSimpExtension? `fsym_norm | throwError "fsym: no fsym_norm"
  let thms := noRflThms (← addExtra (← ext.getTheorems) extra)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  -- Lean's simprocs, without the word complement of a literal: its value would make the
  -- program equal to the folded one only by a deep unfolding in the kernel
  let mut procs : Simp.SimprocsArray := #[(← Simp.getSimprocs).erase ``BitVec.reduceNot]
  if let some pe ← Simp.getSimprocExtension? `fsym_norm then procs := procs.push (← pe.getSimprocs)
  (← caches).prog.set (some (ctx, procs))
  return (ctx, procs)

/-- Simplify the head of the program (`lazyMethods`) with `fsym_norm` and the caller's lemmas. -/
def simpProg (g : MVarId) (extra : Array Syntax) : TacticM MVarId := g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let (ctx, procs) ← progCtx extra
  let foldCtx : MetaM Simp.Context := do
    if let some f ← (← caches).fold.get then return f
    let thms ← ({} : SimpTheorems).addConst ``Full.callIndirect_fold_one
    let thms ← thms.addConst ``Full.callIndirect_fold_ext
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
  -- (an atom that a caller's update produces: the update's, ledger #43)
  if let .const c _ := e.getAppFn then
    let cs ← caches
    if !(← cs.updUnfold.get) && (← cs.updHeads.get).contains c then return (e, ← refl e)
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
  unless fx.isConst && fx == fy && x.getAppNumArgs == y.getAppNumArgs do
    -- a user definition of a value (a struct value `hdr ptr len cap`) against its fields
    for (z, z₂, left) in [(x, y, true), (y, x, false)] do
      let .const c _ := z.getAppFn | continue
      if ← isLibrary c then continue
      let some z' ← unfold1 z | continue
      let s ← saveState
      let g' ← g.replaceTargetDefEq (← if left then mkEq z' z₂ else mkEq z₂ z')
      if ← proveEqGoal g' depth (fuel - 1) then return true
      s.restore
    return false
  -- argument by argument (not `congr 1`, whose closing `rfl` unfolds at default transparency:
  -- `(writeBytes bs o w).size =?= bs.size` evaluated the bytes, 400k heartbeats a return, #46)
  let s ← saveState
  try
    let mut pf ← mkEqRefl fx
    for (a, b) in x.getAppArgs.zip y.getAppArgs do
      if ← withReducibleAndInstances (isDefEq a b) then
        pf ← mkCongrFun pf a
      else
        let m ← mkFreshExprMVar (← mkEq a b)
        unless ← proveEqGoal m.mvarId! depth (fuel - 1) do
          -- a value that is not a number (a list `[x, y].set 0 y` against `[y, y]`): equal by
          -- evaluation, as `congr 1`'s `rfl` did (numbers are the solver's: their unfolding is
          -- what cost, #46)
          let ty ← whnfR (← inferType a)
          if ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isAppOfArity ``BitVec 1 then
            s.restore; return false
          unless ← withDefault (isDefEq a b) do s.restore; return false
          m.mvarId!.assign (← mkEqRefl a)
        pf ← mkCongr pf (← instantiateMVars m)
    g.assign pf
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

def proveArith (ty : Expr) (quick := false) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  if ← arith m.mvarId! quick then return some (← instantiateMVars m)
  trace[fsym] "arith failed: {ty}"
  return none

/-! ### Range laws (`@[fsym_plan]`)

A range law `X … lo m … ⋆ X … m hi … = X … lo hi …` (`RangeLaw`, e.g. `bclaim_split`) lets the
planner treat the atoms of `X` like regions without bytes: an atom of the postcondition is carved
out of a state atom that covers it (the law twice, backwards), adjacent state atoms are joined
first when none covers it (the law forwards). The law's hypotheses are bounds, proved by the
arithmetic solver. -/

/-- `x` with its range bounds replaced by `lo` and `hi`. -/
def RangeLaw.withBounds (law : RangeLaw) (x lo hi : Expr) : Expr :=
  mkAppN x.getAppFn ((x.getAppArgs.set! law.lo lo).set! law.hi hi)

/-- `x` is an atom of the law's head with the law's arity. -/
def RangeLaw.args? (law : RangeLaw) (x : Expr) : Option (Array Expr) :=
  if x.isAppOf law.head && law.lo < x.getAppNumArgs && law.hi < x.getAppNumArgs then
    some x.getAppArgs else none

/-- The law's instance `X lo m ⋆ X m hi = X lo hi` with `X lo hi` unified with `whole` and the
split point `m`; the hypotheses are proved by the arithmetic solver. -/
def RangeLaw.inst (law : RangeLaw) (whole m : Expr) : TacticM (Option Expr) := do
  let lem ← mkConstWithFreshMVarLevels law.decl
  let (args, _, ty) ← forallMetaTelescopeReducing (← inferType lem)
  let some (_, lhs, c) := ty.eq? | return none
  unless ← withReducible (isDefEq c whole) do return none
  unless ← withReducible (isDefEq lhs.appFn!.appArg!.getAppArgs[law.hi]! m) do return none
  for x in args do
    if (← x.mvarId!.isAssigned) then continue
    let xty ← instantiateMVars (← inferType x)
    unless ← isProp xty do return none
    let some h ← proveArith xty (quick := true) | return none
    x.mvarId!.assign h
  let h ← instantiateMVars (mkAppN lem args)
  if h.hasExprMVar then return none
  return some h

/-- The atom `q` (bounds `qlo`, `qhi`) carved out of an unreserved state atom that covers it:
`X lo hi` becomes `X lo qlo ⋆ X qlo qhi ⋆ X qhi hi`. -/
def carveRange (law : RangeLaw) (st : St) (q : Expr) (reserved : Array Expr) :
    TacticM (Option (St × Expr)) := do
  let some qa := law.args? q | return none
  let (qlo, qhi) := (qa[law.lo]!, qa[law.hi]!)
  for i in [0:st.ats.size] do
    let x := st.ats[i]!
    if reserved.contains x then continue
    let some xa := law.args? x | continue
    let s0 ← saveState
    try
      unless ← withReducible (isDefEq (law.withBounds x qlo qhi) q) do throwError "other arguments"
      let some _ ← proveArith (← mkAppM ``LE.le #[qlo, qhi]) (quick := true) | throwError "range"
      let some h1 ← law.inst x qlo | throwError "split at {qlo}"
      let rest := law.withBounds x qlo xa[law.hi]!
      let some h2 ← law.inst rest qhi | throwError "split at {qhi}"
      let st ← st.step #[i] #[law.withBounds x xa[law.lo]! qlo, rest] (← mkAppM ``atom_eq #[← mkEqSymm h1])
      let mid := law.withBounds x qlo qhi
      let st ← st.step #[1] #[mid, law.withBounds x qhi xa[law.hi]!] (← mkAppM ``atom_eq #[← mkEqSymm h2])
      return some (st, mid)
    catch ex =>
      trace[fsym] "range carve ({law.decl}): {ex.toMessageData}"
      s0.restore
  return none

/-- Join two unreserved adjacent state atoms of the law's head (the second from the first's end). -/
def joinRanges (law : RangeLaw) (st : St) (reserved : Array Expr) : TacticM (Option St) := do
  for i in [0:st.ats.size] do
    let x := st.ats[i]!
    if reserved.contains x then continue
    let some xa := law.args? x | continue
    for j in [0:st.ats.size] do
      let y := st.ats[j]!
      if i == j || reserved.contains y then continue
      let some ya := law.args? y | continue
      unless law.withBounds x ya[law.lo]! ya[law.hi]! == y do continue
      let s0 ← saveState
      try
        let m := xa[law.hi]!
        let some e ← proveArith (← mkEq ya[law.lo]! m) (quick := true) | throwError "adjacent"
        -- `y` restated from `x`'s end
        let y' := law.withBounds x m ya[law.hi]!
        let motive ← withLocalDeclD `z (← inferType m) fun z =>
          mkLambdaFVars #[z] (law.withBounds x z ya[law.hi]!)
        let st1 ← st.step #[j] #[y'] (← mkAppM ``atom_eq #[← mkCongrArg motive e])
        let some h ← law.inst (law.withBounds x xa[law.lo]! ya[law.hi]!) m | throwError "join"
        return some (← st1.step #[if i < j then i + 1 else i, 0] #[law.withBounds x xa[law.lo]! ya[law.hi]!]
          (← mkAppM ``atom_eq #[h]))
      catch ex =>
        trace[fsym] "range join ({law.decl}): {ex.toMessageData}"
        s0.restore
  return none

/-- **The range planner**: each determined atom of the postcondition whose head has a range law
is carved out of a state atom that covers it, joining adjacent state atoms when none covers it. -/
def planRanges (st : St) (qats : Array Expr) : TacticM St := do
  let laws := fsymPlanExt.getState (← getEnv)
  if laws.isEmpty then return st
  let mut st := st
  let mut reserved : Array Expr := #[]
  for a in qats do
    let a ← instantiateMVars a
    let some law := laws.find? (a.isAppOf ·.head) | continue
    if a.hasExprMVar || (law.args? a).isNone then continue
    if st.ats.any (fun x => x == a && !reserved.contains x) then reserved := reserved.push a; continue
    let mut done := false
    for _ in [0:16] do
      if let some (st', x) ← carveRange law st a reserved then
        st := st'; reserved := reserved.push x; done := true; break
      let some st' ← joinRanges law st reserved | break
      st := st'
    unless done do trace[fsym] "ranges: no atom of the state covers {a}"
  return st

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
    -- (an undetermined fraction, or half of the authority's: the other half stays, #49)
    let half? ← if qf.isMVar then pure true
      else if qf.isAppOfArity ``Zig.Full.Frac.half 1 then withReducible (isDefEq qf.appArg! g)
      else pure false
    let (st, rest, alt') ← if half? then do
        let h := mkAppN (mkConst ``Zig.Full.Frac.half) #[g]
        if qf.isMVar then qf.mvarId!.assign h
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
        -- the bytes past `n` split off, unless they are none (`n = sz` by the quick solver, else
        -- `sz ≤ n` by the full one: no empty rest)
        let hk? ← if (← proveArith (← mkEq n sz) (quick := true)).isSome then pure none else do
          let some hk ← proveArith (← mkAppM ``LE.le #[n, sz]) | throwError "n"
          pure (if (← proveArith (← mkAppM ``LE.le #[sz, n])).isSome then none else some hk)
        if let some hk := hk? then
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
        unless ← withReducible (isDefEq r1[1]! r2[1]!) do throwError "address"
        let pe ← mkAppM ``Zig.Ptr.add #[r1[0]!, ← mkAppOptM ``Nat.cast #[mkConst ``Int, mkConst ``instNatCastInt,
          ← mkAppM ``Array.size #[r1[5]!]]]
        let some _ ← proveEq r2[0]! pe | throwError "adjacent"
        -- the second's size label and kind as the first's (`EUpd.relabel`, kinds of one normal form)
        let mut st := st
        let mut i := i
        let mut j := j
        let mut r2 := r2
        unless ← (withReducible (isDefEq r1[2]! r2[2]!) <&&> withReducible (isDefEq r1[3]! r2[3]!)) do
          let some hK ← proveEq (← mkAppM ``Zig.BlockKind.norm #[r1[3]!]) (← mkAppM ``Zig.BlockKind.norm #[r2[3]!])
            | throwError "kinds"
          let h ← mkAppOptM ``EUpd.relabel #[r2[0]!, r2[1]!, r2[2]!, r1[2]!, r2[3]!, r1[3]!, r2[4]!, r2[5]!, hK]
          r2 := #[r2[0]!, r2[1]!, r1[2]!, r1[3]!, r2[4]!, r2[5]!]
          st ← st.step #[j] #[← mkRegion r2[0]! r2[1]! r2[2]! r2[3]! r2[4]! r2[5]!] h
          -- (the relabelled region is now first)
          i := if i < j then i + 1 else i
          j := 0
        let r2' ← mkRegion pe r2[1]! r2[2]! r2[3]! r2[4]! r2[5]!
        let some e' ← proveEq st.ats[j]! r2' | throwError "eq"
        st ← st.step #[j] #[r2'] (← mkAppM ``atom_eq #[e'])
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
    -- (a share of an unknown block is matched below, by its fraction and tag)
    if q[0]!.hasExprMVar then continue
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
        -- (bounds up to reducible unfolding, else by arithmetic below: unfolding a bound
        -- `p.off.toNat + (writeBytes bs o w).size` evaluates the bytes, #46)
        if ← withReducibleAndInstances (isDefEq qk x[2]!) then used := used.push i; break
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

/-- The size `n` of the bytes `bs` by a fact `bs.size = n` of a postcondition. -/
def sizeFact? (facts : Array Expr) (bs : Expr) : MetaM (Option Expr) := do
  let mut n? := none
  for f in facts do
    for φ in ← conjuncts f.appArg! do
      if let some (_, l, r) := φ.eq? then
        if l.isAppOfArity ``Array.size 2 then
          if (← instantiateMVars l.appArg!) == bs then n? := some r
  return n?

/-- The unknowns of the bytes of the postcondition's regions that have a size fact. -/
def sizedRegionBytes (qats : Array Expr) : MetaM (Array MVarId) := do
  let facts := qats.filter (·.isAppOfArity liftN 1)
  let mut out := #[]
  for a in qats do
    let some q := regionArgs? (← instantiateMVars a) | continue
    let bs ← instantiateMVars q[5]!
    if bs.hasExprMVar && (← sizeFact? facts bs).isSome then
      out := out ++ (bs.collectMVars {}).result
  return out

/-- An atom of the postcondition (not a region, not a fact) with the size of the unknown bytes
`bs` as an argument (a grant's token `tok p bs.size …`): its position. -/
def sizeArg? (a bs : Expr) : Option Nat :=
  if a.isAppOfArity liftN 1 || (regionArgs? a).isSome then none
  else a.getAppArgs.findIdx? fun x => x.isAppOfArity ``Array.size 2 && x.appArg! == bs

/-- The size of the unknown bytes `bs` of a postcondition region from an atom of the
postcondition that has `bs.size` as an argument (`sizeArg?`): the argument of the state atom of
that head whose other arguments unify with it (they are assigned). -/
def atomSize? (qats sats : Array Expr) (bs : Expr) : MetaM (Option Expr) := do
  for a in qats do
    let a ← instantiateMVars a
    let some k := sizeArg? a bs | continue
    let args := a.getAppArgs
    for x in sats do
      unless headKey x == headKey a && x.getAppNumArgs == args.size do continue
      let s ← saveState
      let xs := x.getAppArgs
      if ← (List.range args.size).allM fun j => do
          if j == k then return true
          withReducible (isDefEq args[j]! xs[j]!) then
        return some xs[k]!
      s.restore
  return none

/-- Note an atom that the planner did not find in the state (its unknowns abstracted): a view
of a state atom may provide it (`viewStep`). -/
def noteWanted (a : Expr) : MetaM Unit := do
  let r ← abstractMVars (← instantiateMVars a)
  let c ← caches
  unless (← c.wanted.get).any (·.expr == r.expr) do c.wanted.modify (·.push r)

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
      let (k, n) ← exCont F fun Fx => mkAppM ``EUpd #[mkSep Fx R, Q]
      g.assign (← mkAppM ``eupd_pre_eq #[e, ← mkAppOptM ``eupd_ex_pre #[none, F, R, Q, k]])
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
    -- a condition on an existential of the postcondition (`if bs.size = 0 then … else …` of an
    -- `∃ bs`): each branch, with its condition as a fact that the planner proves once it has
    -- instantiated the existential (`imp_ite_pos`/`_neg`)
    if c.hasExprMVar then
      -- a branch that closes it, else the first that leaves only facts other than its condition
      let mut part? : Option (Tactic.SavedState × List MVarId) := none
      for pos in [true, false] do
        let s1 ← saveState
        try
          let (Qi, pQ) ← instQ (← reduceProjs Q)
          let some a := (atoms Qi).find? (·.isAppOfArity ``ite 5) | throwError "no if"
          let args := a.getAppArgs
          let (c, inst, t, e) := (args[1]!, args[2]!, args[3]!, args[4]!)
          let cond := if pos then c else mkNot c
          let br := mkSep (mkApp (mkConst liftN) cond) (if pos then t else e)
          let R := sepOf ((atoms Qi).erase a)
          let hbr ← mkAppOptM (if pos then ``imp_ite_pos else ``imp_ite_neg) #[t, e, c, inst]
          let h1 ← mkAppM ``imp_sep #[hbr, ← mkAppOptM ``imp_refl #[R]]
          let h2 ← mkAppM ``imp_eq #[← acEq (mkSep a R) Qi]
          let pf ← mkAppM ``imp_trans #[← mkAppM ``imp_trans #[h1, h2], pQ]
          let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, mkSep br R])
          g.assign (← mkAppM ``EUpd.trans #[g2, ← mkAppM ``EUpd.of_imp #[pf]])
          trace[fsym] "postcondition if on an existential: the {if pos then "then" else "else"} branch"
          let left ← closeEntail g2.mvarId!
          let condI ← instantiateMVars cond
          if ← left.anyM fun m => m.withContext do
              let ty ← instantiateMVars (← m.getType)
              if ty.isAppOfArity ``EUpd 2 then return true
              withNewMCtxDepth <| withReducible <| isDefEq ty condI then
            throwError "branch not closed"
          if left.isEmpty then return []
          if part?.isNone then part? := some (← saveState, left)
        catch ex =>
          trace[fsym] "postcondition if: {ex.toMessageData}"
        s1.restore
      if let some (s2, left) := part? then s2.restore; return left
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
    let laws := fsymPlanExt.getState (← getEnv)
    let planned (a : Expr) : Bool := laws.any (a.isAppOf ·.head)
    -- pre-assign by the atoms that unify outright; an atom that unfolds once its witnesses are
    -- assigned (a `match` on an existential) is opened again. The unknown bytes of a region with
    -- a size fact are the region planner's (`carve`, from the state's current bytes): an atom that
    -- mentions them (a token `I.tok p bs.size …` of the allocation) waits for the final match,
    -- where it matches up to arithmetic.
    let preassign (st : St) (qats : Array Expr) : TacticM Unit := do
      let deferred ← sizedRegionBytes qats
      let skip (a : Expr) : MetaM Bool := do
        if a.isAppOfArity liftN 1 || (regionArgs? a).isSome || (shareArgs? a).isSome ||
          (authArgs? a).isSome || a.isMVar || a.isAppOfArity ``Zig.Full.known 2 || planned a then
          return true
        return ((← instantiateMVars a).collectMVars {}).result.any (deferred.contains ·)
      -- each state atom pre-assigns one atom of the postcondition (two atoms of one head with
      -- unknown arguments, `fee ?u ⋆ fee ?v`, take two atoms of the state)
      let mut taken : Array Nat := #[]
      for a in qats do
        if ← skip a then continue
        for i in [0:st.ats.size] do
          if taken.contains i then continue
          let s' ← saveState
          if ← unifyAtom a st.ats[i]! then taken := taken.push i; break
          s'.restore
      for a in qats do
        if ← skip a then continue
        if (← instantiateMVars a).hasExprMVar then
          for i in [0:st.ats.size] do
            let x := st.ats[i]!
            if taken.contains i || headKey a != headKey x then continue
            let s' ← saveState
            if ← matchArgs a x then
              if (← proveEq x (← instantiateMVars a)).isSome then taken := taken.push i; break
            s'.restore
    for _ in [0:3] do
      let qats := atoms Qi
      -- block facts first (of known pointers: an unknown pointer is the atoms', not the first
      -- of the context in that block); again once the atoms determined pointers
      let blockFacts (φs : Array Expr) : TacticM (Array Expr) := do
        let mut later := #[]
        for φ in φs do
          let φ ← instantiateMVars φ
          if φ.appFn!.appArg!.hasExprMVar then later := later.push φ
          else discard <| solveBlock φ
        return later
      let mut φs := #[]
      for f in qats.filter (·.isAppOfArity liftN 1) do
        φs := φs ++ (← conjuncts (← instantiateMVars f.appArg!)).filter isBlockEq
      let later ← blockFacts φs
      preassign st qats
      discard <| blockFacts later
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
      -- a region with a size fact, or whose size another atom names, is carved (its bytes may
      -- change)
      let qbs ← instantiateMVars q[5]!
      if qbs.hasExprMVar then
        if (← sizeFact? facts qbs).isSome then continue
        if ← qats.anyM fun b => return (sizeArg? (← instantiateMVars b) qbs).isSome then continue
      for i in [0:st.ats.size] do
        if (regionArgs? st.ats[i]!).isNone || exact.contains i then continue
        let s' ← saveState
        if ← withReducibleAndInstances (isDefEq a st.ats[i]!) then
          exact := exact.push i; claimed := claimed.push st.ats[i]!; break
        s'.restore
    for a in qats do
      let some q := regionArgs? (← instantiateMVars a) | continue
      if (← st.ats.anyM fun x => return x == (← instantiateMVars a)) then continue
      -- a size fact `q.bs.size = n`, or the size that another atom names
      let qbs ← instantiateMVars q[5]!
      let n? ← match ← sizeFact? facts qbs with
        | some n => pure (some n)
        | none => if qbs.hasExprMVar then atomSize? qats st.ats qbs else pure none
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
      unless done do
        noteWanted a
        throwError "fsym: no region of the state holds{indentExpr a}"
    trace[fsym] "plan: regions done"
    -- shares
    let qsh ← qats.filterMapM fun a => do return shareArgs? (← instantiateMVars a)
    st ← planShares st qsh
    trace[fsym] "plan: shares done"
    -- range laws (`@[fsym_plan]`)
    st ← planRanges st qats
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
      unless found do
        noteWanted a
        throwError "fsym: the state has no atom for{indentExpr a}"
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

/-- The atoms a facts lemma is about: `X` or the pair `X₁ ⋆ X₂` of `AtomFacts X φ`/`MemFacts X φ`. -/
def factSubjects (X : Expr) : Array Expr :=
  if X.isAppOfArity sepN 2 then #[X.appFn!.appArg!, X.appArg!] else #[X]

/-- The facts lemmas (`@[fsym_facts]`) about the atoms `as` (one atom, or an ordered pair):
`(lemma, proof of AtomFacts X φ or MemFacts X φ for X the atom or `as[0] ⋆ as[1]`, φ, memory
fact)`. A lemma's premises are instances, blocks of pointers (from the context) and arithmetic
(the solver's probe). -/
def atomFacts (as : Array Expr) : TacticM (Array (Name × Expr × Expr × Bool)) := do
  -- the lemmas by the heads of their atoms, once per run
  let keyed ← match ← (← caches).factLemmas.get with
    | some k => pure k
    | none => do
      let k ← (fsymFactsExt.getState (← getEnv)).filterMapM fun n => withNewMCtxDepth do
        let (_, _, concl) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels n))
        return if concl.isAppOfArity ``AtomFacts 2 || concl.isAppOfArity ``MemFacts 2 then
          some ((factSubjects (concl.getArg! 0)).map headKey, n) else none
      (← caches).factLemmas.set (some k)
      pure k
  let keys := as.map headKey
  let X := if as.size == 2 then mkSep as[0]! as[1]! else as[0]!
  let mut out := #[]
  for (key, n) in keyed do
    unless key == keys do continue
    let s ← saveState
    let f ← mkConstWithFreshMVarLevels n
    let (args, _, concl) ← forallMetaTelescope (← inferType f)
    unless ← withReducibleAndInstances (isDefEq (concl.getArg! 0) X) do s.restore; continue
    -- instances, blocks of pointers from the context (`p.block = some b`), arithmetic
    -- (the first premise that fails drops the lemma: no arithmetic after a failed block)
    let mut ok := true
    for x in args do
      unless ← x.mvarId!.isAssigned do
        let ty ← instantiateMVars (← inferType x)
        if (← isClass? ty).isSome then
          if let some i ← (try some <$> synthInstance ty catch _ => pure none) then
            discard <| isDefEq x i
        else if isBlockEq ty then
          match ← solveBlock ty with
          | some pf => discard <| isDefEq x pf
          | none => ok := false; break
        else if !ty.hasExprMVar && (← isProp ty) then
          unless ← arith x.mvarId! (quick := true) do ok := false; break
    unless ok do s.restore; continue
    let pf ← instantiateMVars (mkAppN f args)
    let φ ← instantiateMVars (concl.getArg! 1)
    s.restore
    unless pf.hasMVar || φ.hasMVar do out := out.push (n, pf, φ, concl.isAppOfArity ``MemFacts 2)
  return out

/-- The context has the fact `ψ`: a block `∃ b, p.block = some b` (`blockOf`), or a hypothesis;
or it is an equation of equal terms (two regions with the same labels). -/
def knownFact (ψ : Expr) : MetaM Bool := do
  let s ← saveState
  let r ← do
    if let some (_, l, r) := ψ.eq? then
      if ← withReducible (isDefEq l r) then return true
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

/-- Add the facts of the precondition's atoms and ordered pairs of atoms (`@[fsym_facts]`: the
block, offset and alignment of an owned pointer; a token's grant in its authority's map; two
owned regions apart) that the context lacks, when the walk needs more facts (a rule's side goal,
an undecided `if`, a reachable panic, a return). `none` if there was none to add. A lemma gives
one fact per unordered pair (a symmetric lemma, such as two regions apart, matches both orders). -/
partial def addFacts (g : MVarId) (done : Array Expr := #[])
    (pairs : Array (Name × Expr × Expr) := #[]) : TacticM (Option MVarId) := g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let ats := atoms P
  let n := ats.size
  -- single atoms `[i]`, then ordered pairs `[i, j]`
  let subjects := (List.range n).map (#[·]) ++
    ((List.range n).flatMap fun i => ((List.range n).filter (· != i)).map (#[i, ·]))
  for idx in subjects do
    let as := idx.map (ats[·]!)
    let X := if as.size == 2 then mkSep as[0]! as[1]! else as[0]!
    if done.contains X then continue
    for (lem, hX, φ, mem) in ← atomFacts as do
      if as.size == 2 && pairs.contains (lem, as[1]!, as[0]!) then continue
      if ← (← conjuncts φ).allM (fun ψ => knownFact ψ) then continue
      trace[fsym] "facts of {X}: {φ}"
      let R := sepOf (((List.range n).filter (! idx.contains ·)).toArray.map (ats[·]!))
      let g1 ← if P == mkSep X R then pure g else do
        let g2 ← mkFreshExprSyntheticOpaqueMVar (mkT L α (mkSep X R) c Q)
        g.assign (← mkAppOptM (L.nm ``pre_eq) #[L.L, none, P, mkSep X R, Q, c, ← acEq P (mkSep X R), g2])
        pure g2.mvarId!
      let k ← mkFreshExprSyntheticOpaqueMVar (← mkArrow φ (mkT L α (mkSep X R) c Q))
      g1.assign (← mkAppM' (← mkAppOptM (L.nm (if mem then ``pre_mfact else ``pre_fact)) #[L.L]) #[hX, k])
      let (h, g2) ← k.mvarId!.intro `hf
      let g2 ← destruct g2 h
      let pairs := if as.size == 2 then pairs.push (lem, as[0]!, as[1]!) else pairs
      return ← addFacts (← g2.withContext (unifyBlocks g2)) (done.push X) pairs
  return if done.isEmpty then none else some g

/-- The facts of a state's atoms and ordered pairs (`@[fsym_facts]`, as `addFacts`) that the
context does not have, as an update that keeps the state: `(⟪φ₁⟫ ⋆ … ⋆ P, EUpd P …)`, or
`none` (an entailment's state, `fsym_entail`: facts that a postcondition needs, such as a bound of
owned bytes). -/
def stateFacts (P : Expr) : TacticM (Option (Expr × Expr)) := do
  let ats := atoms P
  let n := ats.size
  let subjects := (List.range n).map (#[·]) ++
    ((List.range n).flatMap fun i => ((List.range n).filter (· != i)).map (#[i, ·]))
  -- each fact as `MemFacts P φ`, then their conjunction
  let mut acc : Option (Expr × Expr) := none
  let mut seen := #[]
  for idx in subjects do
    let as := idx.map (ats[·]!)
    let X := if as.size == 2 then mkSep as[0]! as[1]! else as[0]!
    for (_, hX, φ, mem) in ← atomFacts as do
      if seen.contains φ then continue
      if ← (← conjuncts φ).allM (fun ψ => knownFact ψ) then continue
      seen := seen.push φ
      let R := sepOf (((List.range n).filter (! idx.contains ·)).toArray.map (ats[·]!))
      let h ← if mem then mkAppOptM ``Zig.Full.MemFacts.sepL #[X, R, φ, hX]
        else mkAppOptM ``AtomFacts.mem #[X, R, φ, hX]
      -- (`P` is `X ⋆ R` up to the order of its atoms)
      let h ← mkAppM ``MemFacts.of_eq #[← acEq P (mkSep X R), h]
      acc := some <| ← match acc with
        | none => pure (φ, h)
        | some (ψ, hψ) => do pure (← mkAppM ``And #[ψ, φ], ← mkAppM ``MemFacts.and #[hψ, h])
  let some (φ, h) := acc | return none
  return some (mkSep (mkApp (mkConst liftN) φ) P, ← mkAppM ``Zig.Full.MemFacts.eupd #[h])

/-! ## Rules -/

/-- The command of `x` that sequential rules are about: `c` of a `ConcM.liftMem c`. -/
def memCmd? (x : Expr) : Option Expr :=
  if x.isAppOfArity ``ConcM.liftMem 3 then some x.appArg! else none

/-- Unfold the command `cmd` of a `CTriple` rule until its head is that of the program's command
`x` (a table call `t.call f a` or `(CVTable.dispatch t fns).alloc …` is an indirect call). -/
partial def unfoldToHead (cmd x : Expr) (fuel : Nat := 6) : MetaM Expr := do
  -- a contract about a function `fun a => extCall …` applied to the call's arguments
  let cmd := cmd.headBeta
  if fuel == 0 || headKey cmd == headKey x then return cmd
  match ← unfold1 cmd with
  | some c' => unfoldToHead c' x (fuel - 1)
  | none => return cmd

/-- Run `x`; a heartbeat or recursion limit hit inside it (a runtime exception, which no `catch`
of the walk sees) is reported with `what` (the rule and the command it was trying) and rethrown:
the limit ends the run, at the step that hit it. -/
def reportLimit {α : Type} (what : MessageData) (x : TacticM α) : TacticM α :=
  tryCatchRuntimeEx x fun ex => do
    if ex.isRuntime then
      logError m!"fsym: {if ex.isMaxHeartbeat then "heartbeat" else "recursion depth"} limit in {what}"
    throw ex

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
    -- the command the rule is about, and whether the rule applies in this backend: a thread's
    -- rule only in a thread logic or a call (`CTriple`, whose `MemM` steps are a thread's;
    -- sequential logics read theirs from the sequential rules), a sequential rule there with
    -- the locality of its command (`ofSeq`)
    let target? : Option Expr :=
      if kind == ``CTriple then (if L.conc && (memCmd? x).isNone then some x else none)
      else if isThreadKind kind && !(L.thr || L.conc) then none
      else if L.conc then memCmd? x
      else if (kind == ``FTriple || kind == ``FTTriple) && !L.part then none
      else some x
    let some tx := target? | s.restore; return none
    -- a sequential rule in a thread: its command must be local to the thread that owns the
    -- rule's precondition (`ThreadLocal`, solved last by the locality providers, once `P₀` is
    -- known); a command that no provider is about gets no plan
    let local? := if (L.thr || L.conc) && kind != ``CTriple && !isThreadKind kind then
      some (mkAppN (mkConst ``ThreadLocal) #[β, P₀, tx]) else none
    if let some t := local? then
      let (atomL, wholeL) ← providerLemmas ``ThreadLocal (← assnIdx t) (← cmdHeads t)
      if atomL.isEmpty && wholeL.isEmpty then s.restore; return none
    let local? ← local?.mapM (mkFreshExprMVar ·)
    if kind == ``CTriple then
      -- the projections of an interface's tables and argument tuples (`(env e).alloc f (c, n, …)`)
      -- and the table's arms (`Table.callOr`'s `t.map …`) reduced first, so that a literal
      -- argument unifies as written, not in its unfolded form
      let cmd ← reduceProjs (← unfoldToHead (← instantiateMVars cmd) tx)
      let cmd ← reduceProjs (← expandMapLits cmd)
      unless headKey cmd == headKey tx do s.restore; return none
      unless ← isDefEq cmd tx do
        trace[fsym] "rule {rule}: command{indentExpr cmd}\ndoes not unify with{indentExpr tx}"
        s.restore; return none
    else
      unless ← unifyKeyed cmd tx do s.restore; return none
    trace[fsym] "rule {rule}: command unified"
    let P₀i ← normNatLits (← instantiateMVars P₀)
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
    synthInstArgs args
    let sides := (← args.filterM fun a => do
      if ← a.mvarId!.isAssigned then return false
      isProp (← inferType a)).toList.map (·.mvarId!) ++ (local?.map (·.mvarId!)).toList
    let some left ← solveSides sides | do
      trace[fsym] "rule {rule}: side goals failed {← sides.mapM fun g => do instantiateMVars (← g.getType)}"
      s.restore; return none
    -- every argument must be determined (a proof by a provider too)
    for a in args do
      let a ← instantiateMVars a
      if a.hasExprMVar && !(left.any fun m => a == .mvar m) then
        unless (← isProp (← inferType a)) && (a.collectMVars {}).result.all (left.contains ·) do
          trace[fsym] "rule {rule}: undetermined {a}"
          s.restore; return none
    let mut r ← instantiateMVars (mkAppN rule args)
    let Q₀ ← normNatLits (← instantiateMVars Q₀)
    let P₀ ← normNatLits (← instantiateMVars P₀)
    -- the rule in the backend's kind: `FTotalTriple` (sequential, total), `FTriple` (`P.step`,
    -- `C.step`) or `CTriple` (`C.stepC`)
    let mut kind := kind
    if L.conc && kind == ``FTotalTriple then
      r ← mkAppM ``FTotalTriple.toPartial #[r]; kind := ``FTriple
    -- the sequential rule of a local command as a thread's rule (`ofSeq`)
    if let some hl := local? then
      let (ofSeq, k') := if kind == ``FTriple then (``FTTriple.ofSeq, ``FTTriple)
        else (``FTTotalTriple.ofSeq, ``FTTotalTriple)
      r ← mkAppM ofSeq #[r, ← instantiateMVars hl]; kind := k'
    -- a call (`CTriple`) is partial correctness: its steps are partial thread rules
    if L.conc && kind == ``FTTotalTriple then
      r ← mkAppM ``FTTotalTriple.toPartial #[r]; kind := ``FTTriple
    let (stepN, stepAllN) :=
      if kind == ``CTriple then (``C.stepC, ``C.stepAllC)
      else if L.conc then (``C.step, ``C.stepAll)
      else if L.thr then
        (if kind == ``FTTriple then (``Th.P.step, ``Th.P.stepAll) else (``Th.step, ``Th.stepAll))
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

/-! ## Updates of the caller -/

/-- An update lemma `∀ …, EUpd P Q` (an argument of `fsym [u]`, a planner step at returns). A
local hypothesis that a substitution replaced is none (its rule no longer applies either). -/
def isUpd (e : Expr) : MetaM Bool := do
  try return (← instantiateMVars (← inferType e)).getForallBody.isAppOfArity ``EUpd 2
  catch _ => return false

/-- An unknown of a structure type that no local has (a bundle of the lemma's variables, such
as `v : FV` of a precondition `v.L`) becomes its constructor applied to fresh unknowns, so that
its projections (`v.N`) unify field by field. An unknown of a type that a local has unifies with
it through its projections (`?s.ptr` with `s.ptr`) and stays. -/
def etaStructArgs (args : Array Expr) : MetaM Unit := do
  let env ← getEnv
  for a in args do
    if ← a.mvarId!.isAssigned then continue
    let ty ← whnfD (← inferType a)
    let .const n us := ty.getAppFn | continue
    unless isStructure env n do continue
    if (← isClass? ty).isSome || (← isProp ty) then continue
    if ← (← getLCtx).anyM fun d => do
        return !d.isImplementationDetail && (← withNewMCtxDepth (isDefEq (← whnfD d.type) ty)) then
      continue
    let ctor := mkAppN (mkConst (getStructureCtor env n).name us) ty.getAppArgs
    let (fs, _, _) ← forallMetaTelescope (← inferType ctor)
    discard <| isDefEq a (mkAppN ctor fs)

/-- Apply the caller's update `u : EUpd P₀ Q₀` at a return of `v` into `Q v`: plan
`EUpd P (P₀ ⋆ R)` (the frame `R`; `P₀`'s unknowns from the state, its hypotheses as side goals),
then `EUpd (Q₀ ⋆ R) (Q v)`. Returns the proof of `EUpd P (Q v)` with the goals left, or `none`
if the update does not apply. -/
def tryUpd (u P Qv : Expr) : TacticM (Option (Expr × List MVarId)) := do
  let s ← saveState
  try
    let (args, _, concl) ← forallMetaTelescope (← inferType u)
    let concl ← whnfR concl
    unless concl.isAppOfArity ``EUpd 2 do s.restore; return none
    etaStructArgs args
    -- the precondition unfolded, so that the plan's proof does not mention unknowns that only
    -- the update's hypotheses determine (fields of an expanded structure)
    let P₀ ← reduceProjs (← unfoldLeaves (← instantiateMVars concl.appFn!.appArg!))
    let fr ← mkFreshExprMVar (mkConst ``Zig.Full.FAssn)
    let hE ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, mkSep P₀ fr])
    unless (← closeEntail hE.mvarId!).isEmpty do
      trace[fsym] "update {u}: no plan for its precondition"
      s.restore; return none
    -- the hypotheses, with the projections of expanded structures reduced
    let sides ← (← args.filterM fun a => do
      if ← a.mvarId!.isAssigned then return false
      isProp (← inferType a)).toList.mapM fun a => do
        a.mvarId!.replaceTargetDefEq (← reduceProjs (← instantiateMVars (← inferType a)))
    let some left ← solveSides sides | do
      trace[fsym] "update {u}: side goals failed {← sides.mapM fun g => do instantiateMVars (← g.getType)}"
      s.restore; return none
    for a in args do
      let a ← instantiateMVars a
      if a.hasExprMVar && !(← isProp (← inferType a)) then
        trace[fsym] "update {u}: undetermined {a}; left {← left.mapM fun g => do instantiateMVars (← g.getType)}"
        s.restore; return none
    let R ← instantiateMVars fr
    let Q₀R := mkSep (← instantiateMVars concl.appArg!) R
    let h ← mkExpectedTypeHint (← mkAppOptM ``EUpd.frame #[none, none, R, ← instantiateMVars (mkAppN u args)])
      (← mkAppM ``EUpd #[mkSep (← instantiateMVars P₀) R, Q₀R])
    -- the update's postcondition is the return's (up to the order and `emp`), else the planner
    let (h2, left2) ← try pure (← mkAppM ``atom_eq #[← acEq Q₀R Qv], [])
      catch _ => do
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[Q₀R, Qv])
        pure (m, ← closeEntail m.mvarId!)
    -- (the planner leaves an update goal, possibly per case of a split, where it fails)
    if ← left2.anyM fun m => return (← instantiateMVars (← m.getType)).isAppOfArity ``EUpd 2 then
      trace[fsym] "update {u}: postcondition not reached"
      s.restore; return none
    let pf ← mkAppM ``EUpd.trans #[← instantiateMVars hE, ← mkAppM ``EUpd.trans #[h, h2]]
    return some (pf, left ++ left2)
  catch ex =>
    trace[fsym] "update {u} failed: {ex.toMessageData}"
    s.restore; return none

/-! ## Views of atoms (`@[fsym_view]`)

A view lemma `EUpd X Y` shows the atom `X` as `Y`: an atomic word as a region of plain bytes
(`apts_view`), a region as owned bytes with its facts (`regionIn_view`), owned bytes with those
facts as a region again (`regionIn_fold`). When a step finds no rule because the planner did not
find an atom (`noteWanted`: a rule's precondition, a return's postcondition), the state atoms of
that atom's block whose view provides its head are viewed (`viewStep`) and the step is tried again
on the new state: its facts and existentials open, its regions join with their neighbours, and
the planner carves the atom out of them. -/

/-- The block of an atom's first pointer argument (through `up`), if known. -/
def atomBlock? (a : Expr) : TacticM (Option Expr) := do
  let a ← instantiateMVars a
  let a := if a.isAppOfArity ``Zig.Full.FAssn.up 1 then a.appArg! else a
  for x in a.getAppArgs do
    if x.hasLooseBVars then continue
    unless (← whnfR (← inferType x)).isConstOf ``Zig.Ptr do continue
    if x.hasExprMVar then return none
    return (← blockOf x).map (·.1)
  return none

/-- View the state atoms that provide an atom the planner did not find (`wanted`, from
`noteWanted`): an atom `x` of the head of a view lemma `EUpd X Y` whose `Y` has an atom of the
wanted head, in the wanted atom's block; `Y`'s atoms of that head unify with the wanted one where
they can (a fold's alignment), the lemma's hypotheses are side goals that must all be proved.
`(P', EUpd P P')` for the viewed state `P'`, or `none` if no atom was viewed. For a step's
precondition (`viewStep`) and an entailment's state (`fsym_entail`: bytes as the region a
postcondition names, ledger #48). -/
def viewAtoms (P : Expr) (wanted : Array AbstractMVarsResult) : TacticM (Option (Expr × Expr)) := do
  let lemmas := fsymViewExt.getState (← getEnv)
  if lemmas.isEmpty || wanted.isEmpty then return none
  let s ← saveState
  let mut st ← St.init P
  let mut viewed : Array Expr := #[]
  for wa in wanted do
    let (_, _, w) ← openAbstractMVarsResult wa
    let k := headKey w
    if k == .anonymous || k == `fvar then continue
    -- (an atom of an unknown block names no atoms to view: a one-way view would lose others)
    let some wb ← atomBlock? w | continue
    let mut i := 0
    while i < st.ats.size do
      let x := st.ats[i]!
      let skip ← if viewed.contains x || headKey x == k then pure true
        else match ← atomBlock? x with
          | some xb => pure !(← withReducible (isDefEq xb wb))
          | none => pure true
      if skip then i := i + 1; continue
      let mut y? : Option (Expr × Expr) := none
      for n in lemmas do
        let s' ← saveState
        try
          let lem ← mkConstWithFreshMVarLevels n
          let (args, _, concl) ← forallMetaTelescope (← inferType lem)
          let (X, Y) := (concl.appFn!.appArg!, concl.appArg!)
          unless headKey X == headKey x && (Y.find? (headKey · == k)).isSome do
            throwError "another view"
          unless ← withReducibleAndInstances (isDefEq X x) do throwError "another atom"
          for y in atoms Y do
            if headKey y == k then
              let s2 ← saveState
              unless ← isDefEq y w do s2.restore
          synthInstArgs args
          let sides ← args.filterM fun a => do
            if ← a.mvarId!.isAssigned then return false
            isProp (← inferType a)
          let some [] ← solveSides (sides.toList.map (·.mvarId!)) | throwError "hypotheses"
          let h ← instantiateMVars (mkAppN lem args)
          if h.hasExprMVar then throwError "undetermined"
          trace[fsym] "view {n}: {x}"
          y? := some (← instantiateMVars Y, h)
          break
        catch ex =>
          trace[fsym] "view {n} of {x}: {ex.toMessageData}"
          s'.restore
      let some (Y, h) := y? | i := i + 1; continue
      -- (the view is now first, the atoms before `i` one further: the next is still at `i + 1`)
      st ← st.step #[i] #[Y] h
      viewed := viewed.push Y
      i := i + 1
  if viewed.isEmpty then s.restore; return none
  return some (sepOf st.ats, st.pf)

/-- The goal with the state's atoms viewed (`viewAtoms`), or `none`. -/
def viewStep (g : MVarId) (wanted : Array AbstractMVarsResult) : TacticM (Option MVarId) :=
  g.withContext do
  let (g, L, α, P, c, Q) ← view g
  let some (P', pf) ← viewAtoms P wanted | return none
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkT L α P' c Q)
  g.assign (← mkAppOptM (L.nm ``pre_eupd) #[L.L, none, P, P', Q, c, pf, g'])
  return some g'.mvarId!

/-- A caller's term (`fsym [t]`) in the current step's context. A local of the context it was
elaborated in that the walk replaced (a substitution reintroduces the hypotheses after the
variable it eliminates, with new locals) is the current local of the same name and type, else a
binder of the term: an argument that unification or a side goal supplies, as for an implicit
argument. -/
def refreshUser (e : Expr) : MetaM Expr := do
  unless e.hasFVar do return e
  let lctx ← getLCtx
  let orig ← (← caches).userCtx.get
  -- a local that a substitution eliminated: its value (also through later substitutions)
  let substs ← (← caches).substs.get
  let mut e := e
  for _ in [0:16] do
    let e' := e.replace fun x => match x with
      | .fvar f => if lctx.contains f then none else substs.get? f
      | _ => none
    if e' == e then break
    e := e'
  -- the replaced locals of the term and of their types, in their original order
  let mut stale : Array FVarId := #[]
  let mut todo := (collectFVars {} e).fvarIds.toList
  while !todo.isEmpty do
    let fv := todo.head!
    todo := todo.tail!
    if lctx.contains fv || stale.contains fv then continue
    let some d := orig.find? fv | return e
    stale := stale.push fv
    todo := todo ++ (collectFVars {} d.type).fvarIds.toList
  if stale.isEmpty then return e
  let decls := (stale.filterMap orig.find?).qsort (·.index < ·.index)
  let mut src : Array Expr := #[]
  let mut tgt : Array Expr := #[]
  let mut binders : Array (Name × Expr × Expr) := #[]
  for d in decls do
    let ty := d.type.replaceFVars src tgt
    let same? ← if ty.hasAnyFVar (fun fv => !lctx.contains fv) then pure none else
      lctx.findDeclRevM? fun d' => do
        if d'.isImplementationDetail || d'.userName != d.userName then return none
        let ok ← try withNewMCtxDepth (isDefEq d'.type ty) catch _ => pure false
        return if ok then some d'.toExpr else none
    match same? with
    | some x => src := src.push d.toExpr; tgt := tgt.push x
    | none => binders := binders.push (d.userName, ty, d.toExpr)
  let xs := binders.map (·.2.2)
  let mut body := (e.replaceFVars src tgt).abstract xs
  for i' in [0:binders.size] do
    let i := binders.size - 1 - i'
    let (n, ty, _) := binders[i]!
    body := .lam n (ty.abstract (xs.extract 0 i)) body .default
  return body

/-- The registered rules and the caller's. -/
def rules (user : Array Expr) (x : Expr) (wp := false) : MetaM (Array Expr) := do
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
            | none => match wpArgs? concl with
              | some a => wpKey a[5]!
              | none => .anonymous)
        k := k.push (key, n)
      (← caches).rules.set (some k)
      pure k
  let cmd := (memCmd? x).getD x
  let kx := if wp then wpKey x else headKey cmd
  let mut out ← (← user.mapM refreshUser).filterM fun u => return !(← isUpd u)
  for (key, n) in keyed do
    -- a `WP` rule only in a `WP` walk, by the head of its command
    if (`wp).isPrefixOf key != wp then continue
    if key == kx || key == .anonymous || kx == .anonymous || key == `fvar || kx == `fvar ||
        key == `wp.fvar || kx == `wp.fvar || key == `wp || kx == `wp then
      out := out.push (← mkConstWithFreshMVarLevels n)
  if wp then return out
  -- a load, last: from the bytes the precondition reads (`load_reads`: a struct whose fields
  -- are owned apart, a region that holds a value's encoding)
  if cmd.isAppOfArity ``Zig.load 4 then out := out.push (mkConst ``Zig.Full.FTotalTriple.load_reads)
  return out

/-! ## Stores over parts

A store of a struct whose bytes several parts own (a region and atomic words, one atom per
field) is executed piece by piece (`FTotalTriple.storeBytes_parts`): its encoding
(`Enc.fields N [(o, Enc.encode x), …]`, as the translator writes a struct's `Enc`) is cut at its
fields (`fields_extract`), each field stored as a typed value by the rules of the part that owns
it (a field that is a struct again by its own pieces), the padding between them as bytes. -/

/-- A struct value's encoding `Enc.fields N [(o, cs), …]`: `N`, the list, and each part's
offset, bytes and element. -/
def encParts? (T w : Expr) : MetaM (Option (Nat × Expr × Array (Nat × Expr × Expr))) := do
  let some inst ← (try some <$> synthInstance (mkApp (mkConst ``Zig.Enc) T) catch _ => pure none)
    | return none
  let some e ← unfoldProjInst? (mkApp3 (mkConst ``Zig.Enc.encode) T inst w) | return none
  let e := e.headBeta.consumeMData
  unless e.isAppOfArity ``Zig.Enc.fields 2 do return none
  let some N ← natVal? (e.getArg! 0) | return none
  let lst := e.getArg! 1
  let some (_, xs) := lst.listLit? | return none
  let mut out := #[]
  for x in xs do
    unless x.isAppOfArity ``Prod.mk 4 do return none
    let some o ← natVal? (x.getArg! 2) | return none
    out := out.push (o, x.getArg! 3, x)
  return some (N, lst, out)

mutual
/-- `∀ u : U, (Enc.encode u).size = n`: by `LawfulEnc`, or for a struct from its layout. -/
partial def encSize? (U : Expr) (fuel : Nat) : MetaM (Option (Nat × Expr)) := do
  let some n ← natVal? (← mkAppOptM ``Zig.Enc.size #[U, none]) | return none
  withLocalDeclD `u U fun u => do
    let ty ← mkEq (← mkAppM ``Array.size #[← mkAppOptM ``Zig.Enc.encode #[U, none, u]]) (mkNatLit n)
    if (← (try some <$> synthInstance (← mkAppOptM ``LawfulEnc #[U, none])
        catch _ => pure none)).isSome then
      let pf ← mkAppOptM ``LawfulEnc.size_encode #[U, none, none, u]
      return some (n, ← mkLambdaFVars #[u] (← mkExpectedTypeHint pf ty))
    if fuel == 0 then return none
    let some (N, lst, parts) ← encParts? U u | return none
    unless N == n do return none
    let some (hok, _) ← layoutProof N lst parts (fuel - 1) | return none
    let pf ← mkAppM ``Zig.Full.fields_size #[hok]
    unless ← isDefEq (← inferType pf) ty do return none
    return some (n, ← mkLambdaFVars #[u] (← mkExpectedTypeHint pf ty))

/-- `LayoutOk N (partSizes parts) = true` for the parts of an encoding, with each part's size
and its proof `cs.size = n`. -/
partial def layoutProof (N : Nat) (lst : Expr) (parts : Array (Nat × Expr × Expr)) (fuel : Nat) :
    MetaM (Option (Expr × Array (Nat × Expr))) := do
  let mut sizes := #[]
  for (_, cs, _) in parts do
    unless cs.isAppOfArity ``Zig.Enc.encode 3 do return none
    let some (n, szf) ← encSize? (cs.getArg! 0) fuel | return none
    let sz := (mkApp szf (cs.getArg! 2)).headBeta
    let szT ← mkEq (← mkAppM ``Array.size #[cs]) (mkNatLit n)
    unless ← isDefEq (← inferType sz) szT do return none
    sizes := sizes.push (n, ← mkExpectedTypeHint sz szT)
  let nat := mkConst ``Nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) nat nat
  let consF := mkApp (mkConst ``List.cons [0]) pairTy
  let mut L := mkApp (mkConst ``List.nil [0]) pairTy
  let mut hmap ← mkEqRefl L
  for j' in [0:parts.size] do
    let j := parts.size - 1 - j'
    let mk := mkApp3 (mkConst ``Prod.mk [0, 0]) nat nat (mkNatLit parts[j]!.1)
    hmap ← mkCongr (← mkCongrArg consF (← mkCongrArg mk sizes[j]!.2)) hmap
    L := mkApp2 consF (mkApp mk (mkNatLit sizes[j]!.1)) L
  let hmapT ← mkEq (← mkAppM ``Zig.Full.partSizes #[lst]) L
  unless ← isDefEq (← inferType hmap) hmapT do return none
  let lay := mkApp2 (mkConst ``Zig.Full.LayoutOk) (mkNatLit N) L
  unless ← isDefEq lay (mkConst ``Bool.true) do return none
  let ok ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq lay (mkConst ``Bool.true))
  return some (← mkAppM ``Zig.Full.layoutOk_of_eq #[← mkExpectedTypeHint hmap hmapT, ok], sizes)
end

/-- A rule for the store `x` of a struct whose bytes several parts own, about the whole
precondition `P`: `FTotalTriple P x (fun _ => P')`, with `P'` what the pieces' rules leave
(`FTotalTriple.storeBytes_parts`). `none` if the struct's encoding is not cut into its fields or
a piece has no rule. -/
partial def storeSplitRule? (P x : Expr) (user : Array Expr) (fuel : Nat) :
    TacticM (Option Expr) := do
  unless x.isAppOfArity ``Zig.store 5 do return none
  let a := x.getAppArgs
  let (T, inst, al, q, w) := (a[0]!, a[1]!, a[2]!, a[3]!, a[4]!)
  let some (N, lst, parts) ← encParts? T w | do
    trace[fsym] "store of {T}: its encoding is not one of fields"; return none
  let some (hok, sizes) ← layoutProof N lst parts 4 | do
    trace[fsym] "store of {T}: no layout of its fields"; return none
  let s ← saveState
  try
    let bs := mkApp3 (mkConst ``Zig.Enc.encode) T inst w
    let hsize ← mkAppM ``Zig.Full.fields_size #[hok]
    let hsizeT ← mkEq (← mkAppM ``Array.size #[bs]) (mkNatLit N)
    unless ← isDefEq (← inferType hsize) hsizeT do return none
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat)
      (mkApp (mkConst ``Array [0]) (mkConst ``Zig.Byte))
    -- the pieces in address order: the parts (bytes `cs`, value `x`), the padding between them
    let order := (Array.range parts.size).qsort fun i j => parts[i]!.1 < parts[j]!.1
    let mut pieces : Array (Nat × Nat × Expr × Expr × Option Expr) := #[]
    let mut cur := 0
    for j in order do
      let (o, cs, _) := parts[j]!
      let n := sizes[j]!.1
      if o < cur then return none
      if cur < o then
        let gap ← mkAppM ``Array.extract #[bs, mkNatLit cur, mkNatLit o]
        pieces := pieces.push (cur, o, gap, ← mkEqRefl gap, none)
      let pre ← mkListLit elemTy (parts[:j].toArray.map (·.2.2)).toList
      let post ← mkListLit elemTy (parts[j+1:].toArray.map (·.2.2)).toList
      let whole ← mkAppM ``HAppend.hAppend #[pre, ← mkAppM ``List.cons #[parts[j]!.2.2, post]]
      let hokT ← mkEq (mkApp2 (mkConst ``Zig.Full.LayoutOk) (mkNatLit N)
        (← mkAppM ``Zig.Full.partSizes #[whole])) (mkConst ``Bool.true)
      let e ← mkAppOptM ``Zig.Full.fields_extract_sz #[mkNatLit N, mkNatLit o, mkNatLit n, cs,
        pre, post, ← mkExpectedTypeHint hok hokT, sizes[j]!.2]
      let eT ← mkEq (← mkAppM ``Array.extract #[bs, mkNatLit o, mkNatLit (o + n)]) cs
      unless ← isDefEq (← inferType e) eT do return none
      pieces := pieces.push (o, o + n, cs, ← mkExpectedTypeHint e eT, some (cs.getArg! 2))
      cur := o + n
    if N < cur then return none
    if cur < N then
      let gap ← mkAppM ``Array.extract #[bs, mkNatLit cur, mkNatLit N]
      pieces := pieces.push (cur, N, gap, ← mkEqRefl gap, none)
    -- `Parts q bs 0 pieces` and the pieces' program, from the last piece
    let pieceTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Zig.Ptr)
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkApp (mkConst ``Array [0]) (mkConst ``Zig.Byte)))
    let unit := mkConst ``Unit
    let mut ps := mkApp (mkConst ``List.nil [0]) pieceTy
    let mut hp ← mkAppOptM ``Zig.Full.Parts.nil_intro #[q, bs, mkNatLit N, ← mkEqSymm hsize]
    let mut prog ← mkAppOptM ``Pure.pure #[mkConst ``Zig.MemM, none, unit, mkConst ``Unit.unit]
    for k' in [0:pieces.size] do
      let k := pieces.size - 1 - k'
      let (i, j, cs, e, val?) := pieces[k]!
      let p ← ptrAt q i
      let qb ← mkAppM ``Zig.Ptr.block #[q]
      let pb ← mkAppM ``Zig.Ptr.block #[p]
      unless ← isDefEq pb qb do return none
      let hb ← mkExpectedTypeHint (← mkEqRefl qb) (← mkEq pb qb)
      let ho ← mkFreshExprMVar (← mkEq (← mkAppM ``Zig.Ptr.off #[p]) (← mkAppM ``HAdd.hAdd
        #[← mkAppM ``Zig.Ptr.off #[q], ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, mkNatLit i]]))
      unless ← arith ho.mvarId! do return none
      let hij ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit j])
      hp ← mkAppOptM ``Zig.Full.Parts.cons_intro #[q, p, bs, cs, mkNatLit i, mkNatLit j, ps, hb,
        ← instantiateMVars ho, hij, e, hp]
      ps ← mkAppM ``List.cons #[← mkAppM ``Prod.mk #[p, ← mkAppM ``Prod.mk #[mkNatLit j, cs]], ps]
      let alk := if k == 0 then al else mkNatLit 1
      let cmd ← match val? with
        | some v => mkAppOptM ``Zig.store #[none, none, alk, p, v]
        | none => mkAppOptM ``Zig.storeBytes #[p, alk, cs, mkConst ``Zig.AccessKind.write]
      prog ← mkAppM ``Bind.bind #[cmd, ← withLocalDeclD `u unit fun u => mkLambdaFVars #[u] prog]
    let progT ← mkAppM ``Zig.Full.storeParts #[al, ps]
    unless ← isDefEq prog progT do
      trace[fsym] "store of {T}: the pieces' program"; s.restore; return none
    -- the pieces, each by a rule (a struct's again by its pieces), on the whole precondition
    let lctx ← getLCtx
    let Q ← mkFreshExprMVar (← mkArrow unit (mkConst ``Zig.Full.FAssn))
    let B : Bk := { conc := false, L := mkConst ``FLogic.total }
    let gm ← mkFreshExprSyntheticOpaqueMVar (mkT B unit P prog Q)
    let mut g := gm.mvarId!
    for _ in [0:pieces.size + 1] do
      let (g', _, _, Pc, c, _) ← view g
      g := g'
      if c.isAppOfArity ``Pure.pure 4 then
        let Pc ← instantiateMVars Pc
        if Pc.hasAnyFVar (fun f => !lctx.contains f) then s.restore; return none
        unless ← isDefEq Q (← withLocalDeclD `u unit fun u => mkLambdaFVars #[u] Pc) do
          s.restore; return none
        let hE ← withLocalDeclD `r (mkConst ``Zig.Full.Res) fun r => do
          withLocalDeclD `h (mkApp Pc r) fun h => mkLambdaFVars #[r, h] h
        g.assign (← mkAppOptM ``Zig.Full.Auto.ret #[B.L, none, Pc, Q, mkConst ``Unit.unit,
          ← mkAppM ``EUpd.of_imp #[hE]])
        break
      unless c.isAppOfArity ``Bind.bind 6 do s.restore; return none
      let (xc, fc) := (c.getArg! 4, c.getArg! 5)
      let mut next? : Option MVarId := none
      for r in ← rules user xc do
        let s1 ← saveState
        if let some (k, left) ← tryRule g r xc fc then
          if left.isEmpty then next? := some k; break
        s1.restore
      if next?.isNone && fuel > 0 then
        let s1 ← saveState
        if let some r ← storeSplitRule? Pc xc user (fuel - 1) then
          if let some (k, []) ← tryRule g r xc fc then next? := some k
        if next?.isNone then s1.restore
      let some k := next? | do
        trace[fsym] "store of {T}: no rule for the piece {xc}"; s.restore; return none
      g := k
    let pf ← instantiateMVars gm
    if pf.hasExprMVar then s.restore; return none
    let rule ← mkAppM ``Zig.Full.FTotalTriple.storeBytes_parts
      #[hp, ← mkExpectedTypeHint pf (← mkAppM ``FTotalTriple #[P, progT, ← instantiateMVars Q])]
    return some (← mkExpectedTypeHint rule (← mkAppM ``FTotalTriple #[P, x, ← instantiateMVars Q]))
  catch ex =>
    trace[fsym] "store by pieces failed: {ex.toMessageData}"
    s.restore; return none

/-! ## The walk -/


/-- Rewrite the command `x` of the program `c` (`x >>= f` or `x`) by `eq : x = x'`. -/
def rewriteCmd (g : MVarId) (L : Bk) (α P Q c x x' eq : Expr) : MetaM MVarId := do
  let mot ← withLocalDeclD `z (← inferType x) fun z => do
    let c' := if c.isAppOfArity ``Bind.bind 6 && c.getArg! 4 == x then
        mkAppN c.getAppFn (c.getAppArgs.set! 4 z) else z
    mkLambdaFVars #[z] (mkT L α P c' Q)
  g.replaceTargetEq (mkApp mot x').headBeta (← mkCongrArg mot eq)

/-- A postcondition that the walk infers: an unknown, or an unknown applied to distinct locals
(`?Q x h` after a substitution reverted `x` and `h`). -/
def isUnknownPost (Q : Expr) : MetaM Bool := do
  let Q ← instantiateMVars Q
  let .mvar m := Q.getAppFn | return false
  if ← m.isAssigned then return false
  let args := Q.getAppArgs
  return args.all (·.isFVar) && (args.map (·.fvarId!)).toList.eraseDups.length == args.size

/-- **Post inference.** A return of `v` in the state `P` where the postcondition is the unknown
`Q` (a `MemM` segment of a `WP` walk, whose post the walk computes): `Q` becomes the strongest
post `fun r => ∃ xs, ⟪φs⟫ ⋆ (⟪r = v⟫ ⋆ P)`, with the locals that the walk introduced (the data
`xs` existentially, the facts `φs` as facts, in their order), and the update `EUpd P (Q v)` is
proved with the locals as witnesses. `none` if a local cannot be abstracted (a sort above
`Type`, a fact whose proof the state names) or the post would name a local of the walk that is
not in `Q`'s context (a substitution replaced it). -/
def inferPost (Q P v : Expr) : TacticM (Option Expr) := do
  let Q ← instantiateMVars Q
  -- (an unknown applied to locals, `?Q x h`: a substitution of the walk reverted them; they are
  -- the unknown's, not the walk's)
  let outer := (← Q.getAppFn.mvarId!.getDecl).lctx
  let args := Q.getAppArgs.filterMap fun a => if a.isFVar then some a.fvarId! else none
  let locals := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail || outer.contains d.fvarId || args.contains d.fvarId then acc
    else acc.push d
  let s ← saveState
  try
    -- the bodies of the post at the result `rv`, outermost first (the last is `⟪rv = v⟫ ⋆ P`)
    let bodies (rv : Expr) : MetaM (Array Expr) := do
      let mut b := mkSep (mkApp (mkConst liftN) (← mkEq rv v)) P
      let mut out := #[b]
      for d in locals.reverse do
        if ← isProp d.type then
          if b.containsFVar d.fvarId then throwError "the state names the fact {d.userName}"
          b := mkSep (mkApp (mkConst liftN) d.type) b
        else
          unless (← whnfD (← inferType d.type)) == mkSort Level.one do
            throwError "{d.userName} is not of a type in `Type`"
          b := mkApp2 (mkConst exN) d.type (← mkLambdaFVars #[d.toExpr] b)
        out := out.push b
      return out.reverse
    let post ← withLocalDeclD `r (← inferType v) fun r => do mkLambdaFVars #[r] (← bodies r)[0]!
    unless ← isDefEq Q post do throwError "the post names a local outside its context"
    -- `∀ r, P r → Q v r`: the locals as witnesses, the facts by their hypotheses
    let bs ← bodies v
    let mut pf ← mkAppM ``imp_lift #[← mkEqRefl v, ← mkAppOptM ``imp_refl #[P]]
    for i' in [0:locals.size] do
      let i := locals.size - 1 - i'
      let d := locals[i]!
      pf ← if ← isProp d.type then mkAppM ``imp_lift #[d.toExpr, pf]
        else mkAppOptM ``imp_ex #[P, d.type, ← mkLambdaFVars #[d.toExpr] bs[i + 1]!, d.toExpr, pf]
    let h ← mkAppM ``EUpd.of_imp #[pf]
    return some (← mkExpectedTypeHint h (← mkAppM ``EUpd #[P, mkApp Q v]))
  catch ex =>
    trace[fsym] "post inference: {ex.toMessageData}"
    s.restore; return none

/-- **Branches of a walk whose post it infers** (`isUnknownPost`: a `MemM` segment of a `WP`
walk), split into the goals `gs` (an `if`, the cases of a variable, a side condition): the post
becomes the join of one unknown per branch, `fun v => ∃ b : Bool, if b then Q₁ v else …`
(right-nested), and each branch's goal is about its own unknown (`join_l`, `join_r`), which its
returns infer. So branches that end in different states have one post; the next segment's walk
splits on `b` (a state `if`, `wpSplit`). The goals unchanged if the post is known. -/
def joinPosts (Q : Expr) (gs : List MVarId) : TacticM (List MVarId) := do
  if gs.length < 2 || !(← isUnknownPost Q) then return gs
  let Q ← instantiateMVars Q
  let decl ← Q.getAppFn.mvarId!.getDecl
  let ty ← instantiateMVars (← inferType Q)
  let .forallE _ β _ _ := ty | return gs
  if ty.hasAnyFVar (!decl.lctx.contains ·) then return gs
  let s ← saveState
  -- one unknown per branch, where the post's unknown is
  let qs ← gs.mapM fun _ => mkFreshExprMVarAt decl.lctx decl.localInstances ty
  let join (A B : Expr) : MetaM Expr := withLocalDeclD `v β fun v => do
    let body ← withLocalDeclD `b (mkConst ``Bool) fun b => do
      let c ← mkEq b (mkConst ``Bool.true)
      mkLambdaFVars #[b] (← mkAppM ``ite #[c, mkApp A v, mkApp B v])
    mkLambdaFVars #[v] (mkApp2 (mkConst exN) (mkConst ``Bool) body)
  let rev := qs.reverse
  let mut J := rev.head!
  for q in rev.tail! do J ← join q J
  unless ← isDefEq Q J do s.restore; return gs
  -- branch `i` of `k`: `join_r` `i` times, then `join_l` (not for the last)
  let k := gs.length
  let mut out := []
  for (g, i) in gs.zipIdx do
    let mut g := g
    for j in [0:Nat.min (i + 1) (k - 1)] do
      let (g0, L, _, _, _, _) ← g.withContext (view g)
      let lem := L.nm (if j < i then ``Zig.Full.Auto.join_r else ``Zig.Full.Auto.join_l)
      let [g'] ← g0.apply (← mkConstWithFreshMVarLevels lem) | s.restore; return gs
      g := g'
    out := out ++ [g]
  return out

/-- A rule's side goals left that show it does not apply (ledger #42): an instance that is not
synthesized (`LawfulEnc T` of a type without one: no case split proves it), or a goal without
unknowns whose negation the facts prove (a region rule whose extent is past the region's size).
Such a rule is taken only if no other way applies (a store piece by piece, `storeSplitRule?`,
first; after a split on the side condition its negative case is refuted by the split's fact). -/
def refutedSide (left : List MVarId) : TacticM Bool :=
  left.anyM fun m => m.withContext do
    let φ ← instantiateMVars (← m.getType)
    if (← isClass? φ).isSome then
      return (← observing? (synthInstance φ)).isNone
    if φ.hasExprMVar || φ.hasSyntheticSorry then return false
    let hn ← mkFreshExprMVar (mkNot φ)
    let s ← saveState
    let r ← arith hn.mvarId! (quick := true)
    s.restore
    return r

mutual
/-- An indirect call `callIndirect f ((p, y) :: arms) d` that no rule covers: `y` if the facts
show `f = p`, else both cases (`C.callIndirect_pos`/`_neg`); no arm left is the last arm `d`:
`throw .illegal` (closed: must be unreachable) or the environment's call (open, by its
contract). -/
partial def indirectWalk (g : MVarId) (L : Bk) (α P c Q x : Expr) (user : Array Expr)
    (extra : Array Syntax) (fuel : Nat) : TacticM (List MVarId) := g.withContext do
  let a := x.getAppArgs
  let (β, fp, arms, d) := (a[0]!, a[2]!, a[3]!, a[4]!)
  if arms.isAppOfArity ``List.nil 1 then
    let e ← mkAppOptM ``C.callIndirect_nil #[L.L, β, fp, d]
    let g' ← rewriteCmd g L α P Q c x (← inferType e).appArg! e
    return ← walk g' user extra (fuel - 1)
  unless arms.isAppOfArity ``List.cons 3 do return [g]
  let hd := arms.getArg! 1
  let rest := arms.getArg! 2
  let (p, y) := (hd.getArg! 2, hd.getArg! 3)
  if let some h ← proveEq fp p then
    let e ← mkAppOptM ``C.callIndirect_pos #[L.L, β, fp, p, y, d, rest, h]
    return ← walk (← rewriteCmd g L α P Q c x y e) user extra (fuel - 1)
  let eqT ← mkEq fp p
  -- `f ≠ p` (a pointer literal of another function, or by the facts)
  let hn ← mkFreshExprMVar (mkNot eqT)
  if ← arith hn.mvarId! (quick := true) <||> closeWith hn.mvarId! (← `(tactic| decide)) then
    let e ← mkAppOptM ``C.callIndirect_neg #[L.L, β, fp, p, y, d, rest, ← instantiateMVars hn]
    return ← walk (← rewriteCmd g L α P Q c x (← inferType e).appArg! e) user extra (fuel - 1)
  let (sp, sn) ← g.byCases eqT `hf
  let gp ← sp.mvarId.withContext do
    let e ← mkAppOptM ``C.callIndirect_pos #[L.L, β, fp, p, y, d, rest, Expr.fvar sp.fvarId]
    rewriteCmd sp.mvarId L α P Q c x y e
  let gn ← sn.mvarId.withContext do
    let e ← mkAppOptM ``C.callIndirect_neg #[L.L, β, fp, p, y, d, rest, Expr.fvar sn.fvarId]
    rewriteCmd sn.mvarId L α P Q c x (← inferType e).appArg! e
  let [gp, gn] ← joinPosts Q [gp, gn] | throwError "fsym: join"
  let gp ← destruct gp sp.fvarId
  return (← walk gp user extra (fuel - 1)) ++ (← walk gn user extra (fuel - 1))

/-- Split on a variable of an inductive type and walk each case. -/
partial def casesWalk (g : MVarId) (d : Expr) (user : Array Expr := #[]) (extra : Array Syntax := #[])
    (fuel : Nat := 0) : TacticM (List MVarId) := do
  let (g, _, _, _, _, Q) ← g.withContext (view g)
  casesThen g d (walk · user extra (fuel - 1)) (join := some Q)

/-- Split on a variable of an inductive type, re-split the facts about it, and go on with
`next` in each case (`join`: the post of a walk, joined over the cases if it infers it,
`joinPosts`). -/
partial def casesThen (g : MVarId) (d : Expr) (next : MVarId → TacticM (List MVarId))
    (join : Option Expr := none) : TacticM (List MVarId) := do
  let gs ← g.cases d.fvarId!
  let gs := (gs.map (·.mvarId)).toList
  let gs ← match join with
    | some Q => joinPosts Q gs
    | none => pure gs
  let mut out := []
  for g0 in gs do
    let mut g' := g0
    for decl in (← g'.withContext getLCtx) do
      unless decl.isImplementationDetail do
        g' ← destruct g' decl.fvarId <|> pure g'
    out := out ++ (← next g')
  return out

partial def walk (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := do
  if fuel == 0 then
    logInfo m!"fsym: out of fuel (step budget exhausted); goal left open"
    return [g]
  trace[fsym] "walk {fuel}"
  let h0 ← IO.getNumHeartbeats
  let g ← normPre g
  -- an unreachable case: a fact `False` (a precondition's `match` that reduced to `⟪False⟫`
  -- after a split)
  if let some d ← g.withContext do (← getLCtx).findDeclM? fun d => do
      return if !d.isImplementationDetail && (← instantiateMVars d.type).consumeMData.isFalse then
        some d else none then
    g.withContext do g.assign (← mkFalseElim (← g.getType) d.toExpr)
    return []
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
  -- the step again with the views of the atoms that provide what the planner did not find
  -- (`viewStep`); kept only if the walk gets past the step (not stuck at the same program, nor
  -- at the same return)
  -- (its command taken by a rule, not unfolded: the view was for a rule's precondition)
  let viewed (wanted : Array AbstractMVarsResult) : TacticM (Option (List MVarId)) := do
    let s ← saveState
    let some g' ← viewStep g wanted | return none
    let ref := (← caches).viewProg
    let prev ← ref.get
    ref.set (some c)
    let gs ← try walk g' user extra (fuel - 1) finally ref.set prev
    let stuck ← gs.anyM fun m => do
      let t := (← instantiateMVars (← m.getType)).consumeMData
      if c.isAppOfArity ``Pure.pure 4 && t.isAppOfArity ``EUpd 2 then return true
      let some (_, _, _, _, c', _) ← observing? (view m) | return false
      return c' == c
    if stuck then s.restore; return none
    return some gs
  (← caches).wanted.set #[]
  -- return
  if c.isAppOfArity ``Pure.pure 4 then
    let v := c.appArg!
    -- a postcondition to infer (a `MemM` segment of a `WP` walk): the state
    if ← isUnknownPost Q then
      if let some h ← inferPost Q P v then
        g.assign (← mkAppOptM (L.nm ``ret) #[L.L, none, P, Q, v, h])
        return []
    let Qv := (mkApp Q v).headBeta
    let s ← saveState
    let entail : TacticM (List MVarId) := do
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, Qv])
      g.assign (← mkAppOptM (L.nm ``ret) #[L.L, none, P, Q, v, h])
      closeEntail h.mvarId!
    let left ← entail
    if left.isEmpty then return []
    let s1 ← saveState
    -- an update of the caller's (`fsym [u]`): one that closes it, else the first that applies
    let mut part? : Option (Tactic.SavedState × List MVarId) := none
    for u in user do
      let u ← refreshUser u
      unless ← isUpd u do continue
      s.restore
      let some (pf, left) ← reportLimit m!"the update {u} at a return" (tryUpd u P Qv) | continue
      g.assign (← mkAppOptM (L.nm ``ret) #[L.L, none, P, Q, v, pf])
      if left.isEmpty then return []
      trace[fsym] "update {u}: goals left {← left.mapM fun g => do instantiateMVars (← g.getType)}"
      if part?.isNone then part? := some (← saveState, left)
    let wanted ← (← caches).wanted.get
    -- more facts (of the atoms) may close it, or views of its atoms
    s.restore
    if let some r ← moreFacts then return r
    if part?.isNone then
      if let some r ← viewed wanted then return r
    if let some (s2, left) := part? then s2.restore; return left
    -- no update applies here: the caller's atoms unfolded as any other
    let unfold := (← caches).updUnfold
    if !(← (← caches).updHeads.get).isEmpty && !(← unfold.get) then
      s.restore
      unfold.set true
      let left' ← try entail finally unfold.set false
      if left'.isEmpty then return []
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
    let [gp, gn] ← joinPosts Q [gp, gn] | throwError "fsym: join"
    -- (one branch after the other: the substitutions of a branch's fact are recorded for the
    -- caller's terms of that branch's walk, `refreshUser`)
    let lp ← walk (← destruct gp sp.fvarId) user extra (fuel - 1)
    return lp ++ (← walk (← destruct gn sn.fvarId) user extra (fuel - 1))
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
  -- a body's `match` on a variable as the command (`StateT.run (match x with …) s`: a callee's
  -- result, `.error`/`.ok`, ledger #20/#35): split the variable
  let cmd := if c.isAppOfArity ``Bind.bind 6 then c.getArg! 4 else c
  if cmd.isAppOfArity ``StateT.run 5 then
    if let some m ← matchMatcherApp? (cmd.getArg! 3).consumeMData then
      if let some d := m.discrs.find? (·.isFVar) then
        return ← casesWalk g d user extra fuel
  -- a command
  let (x, f) ← if c.isAppOfArity ``Bind.bind 6 then pure (c.getAppArgs[4]!, c.getAppArgs[5]!)
    else do
      -- (applied, not elaborated: the post may be an unknown, `inferPost`)
      let [g'] ← g.apply (← mkConstWithFreshMVarLevels (L.nm ``bind_pure)) | throwError "fsym"
      return ← walk g' user extra (fuel - 1)
  -- an atomic op's oracle choice: a pick rule (the options at an owned word), else every choice
  if L.conc && x.isAppOfArity ``ConcM.sync 2 && (x.getArg! 1).isAppOf ``SyncOp.pick then
    -- (only the rules about a pick of the same count function: no unfolding of other counts)
    let countHead := fun (e : Expr) => (e.find? (·.isAppOf ``SyncOp.pick)).map (·.appArg!.getAppFn)
    for r in ← rules user x do
      unless countHead (← inferType r) == countHead x do continue
      let s ← saveState
      if let some (k, []) ← tryRule g r x f then return ← walk k user extra (fuel - 1)
      s.restore
    let [g'] ← evalTacticAt (← `(tactic| refine Zig.Full.Auto.C.pick _ fun _ => ?_)) g | throwError "fsym: pick"
    return ← walk g' user extra (fuel - 1)
  let h2 ← IO.getNumHeartbeats
  -- the first rule whose side goals are all proved; else the first that applies
  let mut partial? : Option (Tactic.SavedState × MVarId × List MVarId) := none
  let mut refuted? : Option (Tactic.SavedState × MVarId × List MVarId) := none
  for r in ← rules user x do
    let h3 ← IO.getNumHeartbeats
    let s ← saveState
    let res ← reportLimit m!"the rule {r} on the command{indentExpr x}" (tryRule g r x f)
    let d := ((← IO.getNumHeartbeats) - h3) / 1000
    if d > 300 then trace[fsym.prof] "try {d} {r} {res.isSome}"
    if let some (k, left) := res then
      if left.isEmpty then
        trace[fsym.prof] "rule {((← IO.getNumHeartbeats)-h2)/1000} {r}"
        return ← walk k user extra (fuel - 1)
      trace[fsym] "rule {r}: side goals left {← left.mapM fun g => do instantiateMVars (← g.getType)}"
      if partial?.isNone || refuted?.isNone then
        -- (a rule whose side goal is refuted is the last choice: `refutedSide`)
        if ← refutedSide left then
          if refuted?.isNone then refuted? := some (← saveState, k, left)
        else if partial?.isNone then partial? := some (← saveState, k, left)
      s.restore
  -- a store of a struct whose bytes several parts own: piece by piece (`storeSplitRule?`)
  if partial?.isNone then
    let s ← saveState
    if let some rule ← storeSplitRule? P ((memCmd? x).getD x) user 3 then
      if let some (k, left) ← tryRule g rule x f then
        return left ++ (← walk k user extra (fuel - 1))
    s.restore
    -- (a refuted rule only for a command that cannot be inlined either)
    if (← unfoldCmd x).isNone then partial? := refuted?
  let wanted ← (← caches).wanted.get
  -- more facts (of the atoms) for the rules' side goals
  -- (a rule whose command unified but whose precondition the planner did not find: with more
  -- facts, then with views, before the command is unfolded)
  let unfolded? ← if partial?.isSome || (← (← caches).viewProg.get) == some c then pure none
    else unfoldCmd x
  if partial?.isSome || unfolded?.isNone || !wanted.isEmpty then
    if let some r ← moreFacts then return r
  -- a side condition that the facts do not decide: split on it (the rules' cases)
  if let some (s, _, left) := partial? then
    let s1 ← saveState
    s.restore
    let φs ← left.mapM fun m => do instantiateMVars (← m.getType)
    s1.restore
    -- (never an instance: it is synthesized or not, `refutedSide`)
    if let some φ ← φs.findM? fun φ => return !φ.hasExprMVar && !φ.hasSyntheticSorry &&
        (← isClass? φ).isNone then
      let hn ← mkFreshExprMVar (mkNot φ)
      unless ← arith hn.mvarId! (quick := true) do
        trace[fsym] "split on the side condition {φ}"
        let (sp, sn) ← g.byCases φ `hc
        let [gp, gn] ← joinPosts Q [sp.mvarId, sn.mvarId] | throwError "fsym: join"
        return (← walk gp user extra (fuel - 1)) ++ (← walk gn user extra (fuel - 1))
    s.restore
    let some (_, k, left) := partial? | return [g]
    return left ++ (← walk k user extra (fuel - 1))
  trace[fsym.prof] "norule {((← IO.getNumHeartbeats)-h2)/1000}"
  -- views of the atoms that provide what a rule's precondition wanted
  if let some r ← viewed wanted then return r
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

/-! ## The `WP` backend: a thread's run in a protocol

A goal `P.WP t x Q G m n` has no assertion: the state of the walk is the context (the
protocol's invariant `P.inv (upd G t g) m`, the thread's part `FOwned own rO m` and what
it owns, the facts of the memory). The walk is `walk`'s: the program in normal form
(`fsym_norm` and the steps of a concurrent body, `CNorm`), results, `if`s and `match`es split
or decided by the facts, and each command by a rule (the caller's, then the `@[fsym]` rules
whose conclusion is a `WP` of the command). A rule's hypotheses are of three kinds:
* **continuations** (they name the rule's post `Q`, which is the goal's: the rest of the
  program after the command): their binders are introduced (a product by its components, a
  fact split: `∧`, `∃`, `∨` by cases, equations substituted), an `∃` gets a witness that its
  side goals fix by unification, and the walk goes on; a rule with a fixed post goes through
  `WP.mono`, with its post as the hypothesis of the continuation;
* **segments**: a thread triple `FTTriple Pa x ?Qa` of a `MemM` step, walked by the thread
  backend with its precondition from the context and its postcondition inferred
  (`inferPost`);
* **side goals**, by assumption (up to reducible unfolding, fixing unknowns), arithmetic and
  providers (`solveSides`), after the caller's simp terms, `upd_self` and the memory's
  equations of the context (`m'.threads = m.threads`) rewrote them; automatic arguments
  (`autoParam`) by their own tactic. -/

/-- The simp context of a concurrent body: the program normal form, without the unfoldings of
concurrent commands (`atomicRmwAsC` as an oracle pick and a `MemM` op is the solo reading of
the `CTriple` backend; in a `WP` walk such a command is a stop that a rule of the protocol
takes), and with the steps of `CM` (`CNorm`). -/
def wpCtx (extra : Array Syntax) : TacticM (Simp.Context × Simp.SimprocsArray) := do
  if let some cp ← (← caches).wpProg.get then return cp
  let (ctx, procs) ← progCtx extra
  let isConc (n : Name) : MetaM Bool := do
    let some ci := (← getEnv).find? n | return false
    forallTelescope ci.type fun _ r => return r.isAppOf ``Zig.CM || r.isAppOf ``Zig.ConcM
  let mut arr := #[]
  for thms in ctx.simpTheorems do
    let mut thms := thms
    for n in thms.toUnfold.toList do
      if ← isConc n then thms := thms.eraseCore (.decl n)
    arr := arr.push thms
  let mut thms : SimpTheorems := {}
  for n in [``Zig.CNorm.run_ite, ``Zig.CNorm.run_throw, ``Zig.CNorm.throw_bind,
      ``Zig.CNorm.run_get, ``Zig.CNorm.run_modify, ``Zig.CNorm.run_pickC, ``Zig.CNorm.pick_assoc,
      ``Zig.CNorm.liftMem_pure, ``Zig.CNorm.liftMem_lift_pure, ``Zig.CNorm.liftMem_lift_throw] do
    thms ← thms.addConst n
  let ctx' ← Simp.mkContext (simpTheorems := arr.push (noRflThms thms))
    (congrTheorems := ← getSimpCongrTheorems)
  (← caches).wpProg.set (some (ctx', procs))
  return (ctx', procs)

/-- The simp context of a stop's hypotheses and side goals: the caller's simp terms, the ghost
values of a thread (`upd_self`, `upd_upd`), the facts and witnesses of an assertion that holds
of a resource (a segment's post: `ex_apply`, `sep_lift`). -/
def wpHypCtx (extra : Array Syntax) : TacticM Simp.Context := do
  if let some c ← (← caches).wpHyp.get then return c
  let mut thms ← addExtra {} extra
  for n in [``Zig.Conc.upd_self, ``Zig.Conc.Proto.upd_upd, ``ex_apply, ``Zig.Full.sep_lift,
      -- Boolean tests of generated code as propositions, and the logic left after them
      ``bne_iff_ne, ``beq_iff_eq, ``ne_eq, ``eq_self_iff_true, ``Bool.false_eq_true,
      ``ite_true, ``ite_false, ``and_true, ``true_and, ``and_false, ``false_and, ``or_false,
      ``false_or, ``not_false_eq_true, ``not_true_eq_false] do
    thms ← thms.addConst n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  (← caches).wpHyp.set (some ctx)
  return ctx

/-- The goal `P.WP t x' Q G m n` from the arguments `a` of `P.WP t x Q G m n` and `x = x'`. -/
def wpRewrite (g : MVarId) (a : Array Expr) (x' eq : Expr) : MetaM MVarId := do
  let mot ← withLocalDeclD `z (← inferType a[5]!) fun z =>
    mkLambdaFVars #[z] (mkAppN (mkConst wpN) (a.set! 5 z))
  g.replaceTargetEq (mkAppN (mkConst wpN) (a.set! 5 x')) (← mkCongrArg mot eq)

/-- The program of a `WP` goal in normal form (lazily: its first command). -/
def wpSimp (g : MVarId) (extra : Array Syntax) : TacticM MVarId := g.withContext do
  let some a := wpArgs? (← instantiateMVars (← g.getType)) | return g
  let (ctx, procs) ← wpCtx extra
  let (r, _) ← Simp.main a[5]! ctx (methods := lazyMethods procs none)
  if r.expr == a[5]! then return g
  match r.proof? with
  | none => g.replaceTargetDefEq (mkAppN (mkConst wpN) (a.set! 5 r.expr))
  | some pf => wpRewrite g a r.expr pf

/-- The equations of the context that relate a field of a local to another term
(`m'.threads = m.threads`, `m'.current = t`: what a step keeps of the memory). -/
def fieldEqs : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, l, _) := (← instantiateMVars d.type).eq? | continue
    let .const c _ := l.getAppFn | continue
    unless (← getProjectionFnInfo? c).isSome && l.appArg!.isFVar do continue
    out := out.push d.toExpr
  return out

/-- The forms of a side goal that a hypothesis may have: as stated, and with the projections of
structure values reduced (as the context at entry, `evalFsym`; a stop's hypothesis keeps its
folded form, `proto.inv G m`). -/
def goalForms (g : MVarId) : MetaM (Array Expr) := do
  let t0 ← instantiateMVars (← g.getType)
  let t ← reduceProjs t0
  return if t == t0 then #[t0] else #[t0, t]

/-- `t` is the type of the hypothesis `d` up to reducible unfolding (state kept on success). -/
def hypIs (ts : Array Expr) (d : LocalDecl) : MetaM Bool := do
  for t in ts do
    let s ← saveState
    if ← withReducibleAndInstances (isDefEq t d.type) then return true
    s.restore
  return false

/-- `g` by a hypothesis, up to reducible unfolding (unknowns of `g` may be fixed). -/
def wpAssumption (g : MVarId) : MetaM Bool := g.withContext do
  let ts ← goalForms g
  let ds := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
  for d in ds.reverse do
    if ← hypIs ts d then
      g.assign d.toExpr; return true
  return false

/-- An automatic argument (`(h : T := by tac)`): its tactic. -/
def runAutoParam (g : MVarId) : TacticM Bool := do
  let ty ← g.getType
  let some (.const decl _) := ty.getAutoParamTactic? | return false
  let .ok stx := Lean.Elab.evalSyntaxConstant (← getEnv) (← getOptions) decl | return false
  let g ← g.replaceTargetDefEq ty.appFn!.appArg!
  closeWith g stx

/-- A thread triple (a `MemM` segment of a run). -/
def isSegment (t : Expr) : Bool :=
  t.isAppOfArity ``FTTriple 4 || t.isAppOfArity ``FTTotalTriple 4

/-- Does `e` mention a `WP`? -/
def hasWP (e : Expr) : Bool := (e.find? (·.isConstOf wpN)).isSome

/-- Does `e` mention a step's run (`(x.run m).run = …`: a hypothesis kept as it is)? -/
def hasRun (e : Expr) : Bool :=
  (e.find? fun e => e.isAppOf ``StateT.run || e.isAppOf ``ExceptT.run).isSome

mutual

/-- Split a hypothesis of a stop: `∧`, `∃` (a product witness by its components), `∨` by cases;
the rest by `destruct` (equations substituted, user definitions unfolded). The equation of a
step's run (`(x.run m).run = …`) stays. -/
partial def wpSplit (g : MVarId) (h : FVarId) (keep := false) : TacticM (List MVarId) :=
  g.withContext do
  let ty0 ← instantiateMVars (← h.getType)
  let ty ← whnfR ty0
  if hasRun ty then return [g]
  -- (`keep`: a hypothesis of the context or of a stop, a protocol's invariant `P.inv G m`: the
  -- parts of a copy, the fact stays whole, the hypothesis of the protocol's lemmas)
  if keep then
    let ty' ← if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then pure (some ty)
      else if let .const c _ := ty0.getAppFn then
        (if ← isLibrary c then pure none else unfold1 ty0)
      else pure none
    if let some ty' := ty' then
      let w ← whnfR ty'
      if w.isAppOfArity ``And 2 || w.isAppOfArity ``Exists 2 then
        let (h', g') ← (← g.assert `hu ty' (mkFVar h)).intro1
        return ← g'.withContext (wpSplit g' h')
  if ty.isAppOfArity ``Or 2 then
    let gs ← g.cases h
    return ← gs.toList.flatMapM fun sg => wpSplit sg.mvarId sg.fields[0]!.fvarId!
  -- an assertion's `if` at a resource (the join of a segment's branches, `joinPosts`): by cases
  -- on its condition, the hypothesis the branch's assertion
  if ty.getAppFn.isConstOf ``ite && ty.getAppNumArgs ≥ 5 then
    let a := ty.getAppArgs
    let (c, inst, x, y) := (a[1]!, a[2]!, a[3]!, a[4]!)
    let (sp, sn) ← g.byCases c `hb
    let mut out := []
    for (sg, pos) in [(sp, true), (sn, false)] do
      let g' ← sg.mvarId.withContext do
        let mut eq ← mkAppOptM (if pos then ``if_pos else ``if_neg) #[c, inst, some (.fvar sg.fvarId), none, x, y]
        for r in a.extract 5 a.size do eq ← mkCongrFun eq r
        let tyNew := mkAppN (if pos then x else y) (a.extract 5 a.size) |>.headBeta
        let res ← sg.mvarId.replaceLocalDecl h tyNew eq
        pure (res.mvarId, res.fvarId)
      out := out ++ (← wpHyp g'.1 g'.2 #[])
    return out
  if ty.isAppOfArity ``And 2 then
    let gs ← g.cases h
    let some sg := gs[0]? | return []
    let f1 := sg.fields[1]!.fvarId!
    return ← (← wpSplit sg.mvarId sg.fields[0]!.fvarId!).flatMapM fun g' => do
      -- (a substitution of the first part renames the second: followed by `substs`)
      let mut f := f1
      for _ in [0:16] do
        if (← g'.withContext f.findDecl?).isSome then return ← wpSplit g' f
        let some (.fvar f') := (← (← caches).substs.get).get? f | break
        f := f'
      pure [g']
  if ty.isAppOfArity ``Exists 2 then
    let gs ← g.cases h
    let some sg := gs[0]? | return []
    return ← wpSplit sg.mvarId sg.fields[1]!.fvarId!
  return [← destruct g h]

/-- A new hypothesis of a stop: normalized by the caller's simp terms and the ghost values'
lemmas (`upd_self`), then split. -/
partial def wpHyp (g : MVarId) (h : FVarId) (extra : Array Syntax) : TacticM (List MVarId) :=
  g.withContext do
  let ty ← instantiateMVars (← h.getType)
  if hasRun ty then return [g]
  let (r, _) ← simp ty (← wpHypCtx extra)
  if r.expr == ty then return ← wpSplit g h (keep := true)
  let some (h', g') ← applySimpResultToLocalDecl g h r false | return []
  wpSplit g' h' (keep := true)

/-- A proposition of a run: introduced (a hypothesis split), an `∃` with an unknown witness, an
`∧` part by part (the part without a run first: it may fix a witness), a `WP` walked, else an
atom (`wpAtom`). The goals left. -/
partial def wpGoal (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := g.withContext do
  if ← g.isAssigned then return []
  let t0 ← instantiateMVars (← g.getType)
  let t ← whnfR t0
  if (wpArgs? t).isSome then
    let g ← if t == t0 then pure g else g.replaceTargetDefEq t
    return ← wpWalk g user extra fuel
  if let .forallE _ ty _ _ := t then
    let g ← if t == t0 then pure g else g.replaceTargetDefEq t
    let (h, g) ← g.intro1P
    let tyi ← whnfR (← instantiateMVars ty)
    if tyi.isAppOfArity ``Prod 2 then
      let gs ← g.cases h
      return ← gs.toList.flatMapM (wpGoal ·.mvarId user extra fuel)
    if ← isProp ty then
      return ← (← wpHyp g h extra).flatMapM (wpGoal · user extra fuel)
    return ← wpGoal g user extra fuel
  if t.isAppOfArity ``Exists 2 then
    -- (an unreachable case needs no witness)
    if ← closeWith g (← `(tactic| contradiction)) then return []
    let (β, p) := (t.getArg! 0, t.getArg! 1)
    let w ← mkFreshExprMVar β
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp p w).headBeta
    g.assign (← mkAppOptM ``Exists.intro #[β, p, w, g'])
    let left ← wpGoal g'.mvarId! user extra fuel
    -- a witness that the proof does not need (a case closed by a contradiction): any
    if !(← w.mvarId!.isAssigned) &&
        !(← left.anyM fun m => return ((← m.getType).find? (· == w)).isSome) then
      if let some d ← (try some <$> mkDefault β catch _ => pure none) then
        w.mvarId!.assign d
    return left
  if t.isAppOfArity ``And 2 then
    let a ← mkFreshExprSyntheticOpaqueMVar (t.getArg! 0)
    let b ← mkFreshExprSyntheticOpaqueMVar (t.getArg! 1)
    g.assign (← mkAppM ``And.intro #[a, b])
    let (x, y) := if hasWP (t.getArg! 0) then (b, a) else (a, b)
    let lx ← wpGoal x.mvarId! user extra fuel
    return lx ++ (← wpGoal y.mvarId! user extra fuel)
  if t.isConstOf ``True then g.assign (mkConst ``True.intro); return []
  -- a disjunction (a post over branches that end in different states): a side that is proved
  -- whole, else the solver on the disjunction
  if t.isAppOfArity ``Or 2 then
    for (i, side) in [(0, ``Or.inl), (1, ``Or.inr)] do
      let s ← saveState
      let a ← mkFreshExprSyntheticOpaqueMVar (t.getArg! i)
      if (← wpGoal a.mvarId! user extra fuel).isEmpty then
        g.assign (← mkAppOptM side #[t.getArg! 0, t.getArg! 1, a]); return []
      s.restore
  wpAtom g user extra fuel

/-- An atomic proposition: by a hypothesis, arithmetic and providers; else rewritten by the
caller's simp terms, the ghost values' lemmas and the memory's equations and tried again; else
a user definition unfolded. -/
partial def wpAtom (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := g.withContext do
  if ← wpAssumption g then return []
  let t ← instantiateMVars (← g.getType)
  if t.isFalse then
    if ← closeWith g (← `(tactic| contradiction)) then return []
  if !t.hasExprMVar then
    let s ← saveState
    if let some [] ← solveSides [g] then return []
    -- (a partial solution assigned `g`: undone, the next tries need it open)
    s.restore
  let ctx ← wpHypCtx extra
  let mut thms := ctx.simpTheorems
  let mut eqs : SimpTheorems := {}
  for e in ← fieldEqs do eqs ← eqs.add (.fvar e.fvarId!) #[] e
  let ctx ← Simp.mkContext (simpTheorems := thms.push eqs) (congrTheorems := ← getSimpCongrTheorems)
  let s ← saveState
  try
    let (r, _) ← simp t ctx (simprocs := #[← Simp.getSimprocs])
    if r.expr != t then
      if r.expr.isTrue then
        g.assign (← mkOfEqTrue (← r.getProof)); return []
      let g' ← applySimpResultToTarget g t r
      return ← wpGoal g' user extra fuel
  catch _ => s.restore
  if let .const c _ := t.getAppFn then
    unless ← isLibrary c do
      if let some t' ← unfold1 t then
        return ← wpGoal (← g.replaceTargetDefEq t') user extra fuel
  return [g]

/-- The side goals of a rule, with their unknowns (a ghost value at a stop, a segment's
precondition): a determined goal is solved (`strict`: completely); a goal with unknowns takes
each hypothesis that unifies with it (and the rest must follow), or waits for the others to fix
its unknowns (`budget` waits in all), or goes to the solver. `none` if no choice works. -/
partial def wpSides (todo : List MVarId) (strict : Bool) (budget : Nat) (user : Array Expr)
    (extra : Array Syntax) (fuel : Nat) : TacticM (Option (List MVarId)) := do
  match todo with
  | [] => return some []
  | sg :: rest =>
    if ← sg.isAssigned then return ← wpSides rest strict budget user extra fuel
    let ts ← sg.withContext (goalForms sg)
    let solve : TacticM (Option (List MVarId)) := do
      let l ← wpGoal sg user extra fuel
      if strict && !l.isEmpty then return none
      if ← l.anyM fun m => return (← instantiateMVars (← m.getType)).hasExprMVar then return none
      return (← wpSides rest strict budget user extra fuel).map (l ++ ·)
    if !ts[0]!.hasExprMVar then return ← solve
    let hyps ← sg.withContext do
      let lctx ← getLCtx
      return lctx.foldl (init := (#[] : Array LocalDecl)) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d
    for d in hyps do
      let s ← saveState
      if ← sg.withContext (hypIs ts d) then
        sg.assign d.toExpr
        if let some l ← wpSides rest strict budget user extra fuel then return some l
      s.restore
    if budget > 0 && !rest.isEmpty then
      return ← wpSides (rest ++ [sg]) strict (budget - 1) user extra fuel
    let s ← saveState
    let r ← solve
    if r.isNone then s.restore
    return r

/-- A rule `r` on the command `x` of the goal `g` (arguments `a`): `none` if it does not apply,
else the goals left. -/
partial def wpRule (g : MVarId) (a : Array Expr) (r x : Expr) (user : Array Expr)
    (extra : Array Syntax) (fuel : Nat) : TacticM (Option (List MVarId)) := g.withContext do
  let s ← saveState
  let prep ← try
      let (args, _, concl) ← forallMetaTelescope (← inferType r)
      let some ca := wpArgs? (← instantiateMVars concl) | throwError "not a WP rule"
      -- (a projection of a structure value: `impl.lock p io` of a contract, the program's
      -- function)
      unless ← unifyKeyed (← reduceProjs (← instantiateMVars ca[5]!)) x (anyGround := true) do
        throwError "command"
      trace[fsym] "WP rule {r}: command unified"
      for i in [2, 4, 7, 8, 9] do
        unless ← isDefEq ca[i]! a[i]! do throwError "argument {i} of the WP"
      -- the rule's post an unknown (also one that a caller's term abstracted over its
      -- hypotheses, `?Q hg hok hi`): the goal's
      let Qr ← instantiateMVars ca[6]!
      let qh := Qr.getAppFn
      let qid? ← if qh.isMVar then
          (do if ← qh.mvarId!.isAssigned then pure none else pure (some qh.mvarId!)) else pure none
      if let some q := qid? then
        let lam ← forallBoundedTelescope (← q.getType) (some Qr.getAppNumArgs) fun xs _ =>
          mkLambdaFVars xs a[6]!
        unless ← isDefEq qh lam do throwError "post"
      synthInstArgs args
      let mut sides := #[]
      let mut autos := #[]
      let mut segs := #[]
      let mut conts := #[]
      for arg in args do
        if ← arg.mvarId!.isAssigned then continue
        let ty ← arg.mvarId!.getType
        if ty.isAppOfArity ``autoParam 2 then autos := autos.push arg.mvarId!; continue
        unless ← isProp ty do continue
        if let some q := qid? then
          if (ty.find? (· == .mvar q)).isSome then conts := conts.push arg.mvarId!; continue
        if isSegment (← instantiateMVars ty).consumeMData then segs := segs.push arg.mvarId!; continue
        sides := sides.push arg.mvarId!
      trace[fsym] "WP rule {r}: post {Qr}, {sides.size} side goals, {segs.size} segments, {conts.size} continuations"
      -- side goals (they fix the unknowns of the segments' preconditions and of witnesses):
      -- all proved if a choice of the unknowns does it, else the first choice that leaves
      -- goals of the caller
      let s1 ← saveState
      let budget := 2 * sides.size
      let left ← match ← wpSides sides.toList true budget user extra fuel with
        | some l => pure l
        | none =>
          s1.restore
          let some l ← wpSides sides.toList false budget user extra fuel
            | throwError "side goals not proved {← sides.mapM fun m => do instantiateMVars (← m.getType)}"
          pure l
      let mut left := left
      for ap in autos do
        unless (← ap.isAssigned) || (← runAutoParam ap) do throwError "automatic argument"
      -- the `MemM` segments: the thread backend, the post inferred
      for sg in segs do
        let ty ← instantiateMVars (← sg.getType)
        if (ty.getArg! 1).hasExprMVar then throwError "the precondition of the segment is unknown"
        trace[fsym] "WP rule {r}: segment{indentExpr ty}"
        left := left ++ (← walk sg user extra fuel)
      for arg in args do
        let ai ← instantiateMVars arg
        if ai.hasExprMVar && !(← isProp (← inferType arg)) then throwError "undetermined {ai}"
      pure (some (← instantiateMVars (mkAppN r args), qid?.isSome, Qr, conts, left))
    catch ex =>
      trace[fsym] "WP rule {r}: {ex.toMessageData}"
      pure none
  let some (pf, direct, Qr, conts, left) := prep | s.restore; return none
  trace[fsym] "WP rule {r} applies"
  if direct then
    g.assign pf
    return some (left ++ (← conts.toList.flatMapM (wpGoal · user extra fuel)))
  -- a fixed post: into the goal's (`WP.mono`)
  let Qr ← instantiateMVars Qr
  let (tG, tM) := (← inferType a[7]!, ← inferType a[8]!)
  let hTy ← withLocalDeclD `r a[3]! fun v => do
    withLocalDeclD `G tG fun G' => withLocalDeclD `m tM fun m' =>
      withLocalDeclD `d (mkConst ``Nat) fun d => do
        mkForallFVars #[v, G', m', d]
          (← mkArrow (mkApp4 Qr v G' m' d).headBeta (mkApp4 a[6]! v G' m' d).headBeta)
  let hm ← mkFreshExprSyntheticOpaqueMVar hTy
  g.assign (← mkAppM ``Zig.Conc.Proto.WP.mono #[hm, pf])
  return some (left ++ (← wpGoal hm.mvarId! user extra fuel))

/-- The walk of a `WP` goal. -/
partial def wpWalk (g : MVarId) (user : Array Expr) (extra : Array Syntax) (fuel : Nat) :
    TacticM (List MVarId) := do
  if fuel == 0 then
    logInfo m!"fsym: out of fuel (step budget exhausted); goal left open"
    return [g]
  let g ← wpSimp g extra
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some a := wpArgs? t | wpGoal g user extra (fuel - 1)
  let x := a[5]!.consumeMData.headBeta
  trace[fsym] "WP walk {fuel}: {x}"
  let next (g : MVarId) := wpGoal g user extra (fuel - 1)
  -- a result, a map, a bind: the structural rules
  for (test, lem) in [(x.isAppOfArity ``Pure.pure 4, ``Zig.Conc.Proto.WP.pure'),
      (x.isAppOfArity ``Functor.map 6, ``Zig.Conc.Proto.WP.map),
      (x.isAppOfArity ``Bind.bind 6, ``Zig.Conc.Proto.WP.bind)] do
    if test then
      return ← (← g.apply (← mkConstWithFreshMVarLevels lem)).flatMapM next
  -- a panic: the branch must be unreachable
  if isThrow x then
    let s ← saveState
    let g' ← g.exfalso
    if ← closeWith g' (← `(tactic| contradiction)) <||> arithCore g' then return []
    -- (the goal stays the panic's, not the `False` that `exfalso` assigned it to)
    s.restore
    trace[fsym] "reachable panic"
    return [g]
  -- an `if`: decided by the facts, else both branches
  if x.isAppOfArity ``ite 5 then
    let xa := x.getAppArgs
    let (cond, inst, tb, eb) := (xa[1]!, xa[2]!, xa[3]!, xa[4]!)
    let branch (g : MVarId) (h : Expr) (pos : Bool) : TacticM MVarId := do
      let eq ← mkAppOptM (if pos then ``if_pos else ``if_neg) #[cond, inst, h, none, tb, eb]
      wpRewrite g a (if pos then tb else eb) eq
    -- decided by arithmetic, or by the context (a Boolean test of a stop's case: `r ≠ unl`)
    let decide? (φ : Expr) : TacticM (Option Expr) := do
      let h ← mkFreshExprMVar φ
      if ← arith h.mvarId! (quick := true) then return some (← instantiateMVars h)
      let s ← saveState
      let h ← mkFreshExprSyntheticOpaqueMVar φ
      if (← wpGoal h.mvarId! user extra 0).isEmpty then return some (← instantiateMVars h)
      s.restore; return none
    if let some hp ← decide? cond then
      return ← wpWalk (← branch g hp true) user extra (fuel - 1)
    if let some hn ← decide? (mkNot cond) then
      return ← wpWalk (← branch g hn false) user extra (fuel - 1)
    let (sp, sn) ← g.byCases cond `hc
    let gp ← sp.mvarId.withContext (branch sp.mvarId (.fvar sp.fvarId) true)
    let gn ← sn.mvarId.withContext (branch sn.mvarId (.fvar sn.fvarId) false)
    -- (one branch after the other: the substitutions of a branch's fact are recorded for the
    -- caller's terms of that branch's walk, `refreshUser`)
    let lp ← wpWalk (← destruct gp sp.fvarId) user extra (fuel - 1)
    return lp ++ (← wpWalk (← destruct gn sn.fvarId) user extra (fuel - 1))
  -- a `match` (also of a step of a concurrent body, `(match … : CM σ α).run s`): split
  let inner := if x.isAppOfArity ``StateT.run 5 then x.getArg! 3 else x
  if let some mt ← matchMatcherApp? inner then
    let some d := mt.discrs.find? (·.isFVar) <|> mt.discrs[0]? | return [g]
    if d.isFVar then return ← casesThen g d (wpWalk · user extra (fuel - 1))
    if !d.hasLooseBVars && !(← isCaseCtorApp d) then
      if let some (xs, g') ← observing? (g.generalize #[{ expr := d, xName? := `o, hName? := `ho }]) then
        return ← casesThen g' (.fvar xs[0]!) (wpWalk · user extra (fuel - 1))
  -- a command: the caller's rules, then the registered ones
  for r in ← rules user x (wp := true) do
    if let some left ← reportLimit m!"the WP rule {r} on the command{indentExpr x}"
        (wpRule g a r x user extra fuel) then
      return left
  -- a generated function: inlined
  if let .const c _ := inner.getAppFn then
    unless ← isLibrary c do
      if let some inner' ← unfold1 inner then
        let x' := if x.isAppOfArity ``StateT.run 5 then mkAppN x.getAppFn (x.getAppArgs.set! 3 inner')
          else inner'
        return ← wpWalk (← g.replaceTargetDefEq (mkAppN (mkConst wpN) (a.set! 5 x'))) user extra (fuel - 1)
  logInfo m!"fsym: no WP rule for the command{indentExpr x}"
  return [g]

end

/-- `fsym` on a `WP` goal: the hypotheses split, then the walk. -/
def wpEntry (g : MVarId) (user : Array Expr) (extra : Array Syntax) : TacticM (List MVarId) := do
  -- the simp contexts first, outside every backtracking point: building one elaborates the
  -- caller's terms (auxiliary lemmas in the environment, which a restore would drop while the
  -- run's cache keeps the context)
  discard <| g.withContext (wpCtx extra)
  discard <| g.withContext (wpHypCtx extra)
  let mut gs := [g]
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    unless ← g.withContext (isProp d.type) do continue
    gs ← gs.flatMapM fun g => g.withContext do
      if (← getLCtx).contains d.fvarId then wpSplit g d.fvarId (keep := true) else pure [g]
  gs.flatMapM (wpWalk · user extra 400)

/-- `fsym_entail`: close a goal `EUpd P Q` (a frame-preserving update into an assertion) with
the planner of `fsym`; facts of `Q` it cannot prove are left as goals. A goal `Within X P` (`X`
is one of the separated parts of `P`, through definitions of `P` that unfold to `⋆`) is closed by
finding `X`. -/
elab "fsym_entail" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  if t.isAppOfArity ``Within 2 then
    for c in ← withinCands t.appFn!.appArg! t.appArg! (unfold := true) do
      let s ← saveState
      try
        let pf ← c
        if ← isDefEq (← g.getType) (← inferType pf) then
          g.assign pf; replaceMainGoal []; return
      catch _ => pure ()
      s.restore
    throwError "fsym_entail: {t.appFn!.appArg!} is not a part of{indentExpr t.appArg!}"
  -- the state's user definitions unfolded (as a walk's precondition, `normPre`; ledger #43)
  let (g, t) ← if t.isAppOfArity ``EUpd 2 then g.withContext do
      let P' ← unfoldLeaves t.appFn!.appArg!
      if P' == t.appFn!.appArg! then pure (g, t) else
        let t' := mkApp2 t.appFn!.appFn! P' t.appArg!
        pure (← g.replaceTargetDefEq t', t')
    else pure (g, t)
  withRunCaches do
    discard <| arithSimpCtx
    let s ← saveState
    (← caches).wanted.set #[]
    let left ← closeEntail g
    if left.isEmpty then replaceMainGoal []; return
    -- the state with the views of its atoms that provide what the planner did not find (owned
    -- bytes as the region the postcondition names, ledger #48) and the facts of its atoms (a
    -- bound of owned bytes), then once more: taken if it closes more
    let wanted ← (← caches).wanted.get
    let s1 ← saveState
    s.restore
    unless t.isAppOfArity ``EUpd 2 do s1.restore; replaceMainGoal left; return
    let left2? ← g.withContext do
      let mut P := t.appFn!.appArg!
      let mut pf? : Option Expr := none
      if let some (P', h) ← viewAtoms P wanted then P := P'; pf? := some h
      if let some (P', h) ← stateFacts P then
        P := P'
        pf? := some (← match pf? with | some h0 => mkAppM ``EUpd.trans #[h0, h] | none => pure h)
      let some pf := pf? | return none
      let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``EUpd #[P, t.appArg!])
      g.assign (← mkAppM ``EUpd.trans #[pf, g2])
      return some (← closeEntail g2.mvarId!)
    let isUpd (m : MVarId) : TacticM Bool := return (← instantiateMVars (← m.getType)).isAppOfArity ``EUpd 2
    if let some left2 := left2? then
      unless ← left2.anyM isUpd do
        if (← left.anyM isUpd) || left2.length < left.length then replaceMainGoal left2; return
    s1.restore
    replaceMainGoal left

/-- `fsym`, `fsym [r, …]`: symbolic execution of the goal's program. The `rᵢ` are step rules
(triples, tried before the library's), updates `EUpd P Q` (at a return the planner does not
close: `P` planned out of the state, `Q` into the postcondition; `tryUpd`) or simp lemmas for the
program. -/
syntax (name := fsymTac) "fsym" (" [" term,* "]")? : tactic

@[tactic fsymTac] def evalFsym : Tactic := fun stx => withMainContext do
  -- `(" [" term,* "]")?`: the optional node holds the three parts (none if absent)
  let args : Array Syntax := if stx[1].getNumArgs == 3 then stx[1][1].getSepArgs else #[]
  -- the caller's terms in the goal's context (its local `have`s), which `refreshUser` relates
  -- to the context of each later step
  let userCtx ← getLCtx
  let mut user := #[]
  let mut extra := #[]
  for a in args do
    -- an update lemma by name keeps its implicit arguments (fresh at each return)
    let c? ← if a.isIdent && ((← getLCtx).findFromUserName? a.getId).isNone then
        try some <$> mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload a) catch _ => pure none
      else pure none
    if let some c := c? then
      if ← isUpd c then user := user.push c; continue
      -- a rule by name: the constant (elaborating it would run its automatic arguments, `hnone`
      -- of `WP.callRC`, before the step fixes their unknowns)
      if ← withNewMCtxDepth do
          let (_, _, concl) ← forallMetaTelescope (← inferType c)
          return (ruleConcl? (← whnfR concl)).isSome || (wpArgs? concl).isSome then
        user := user.push c; continue
    -- the term's unknowns (implicit arguments) become its leading binders, so that each use
    -- instantiates them afresh in the context of that step (where the walk's witnesses live)
    let e ← instantiateMVars (← elabTerm a none)
    let e ← if e.hasExprMVar then pure (← abstractMVars e (levels := false)).expr else pure e
    let ty ← instantiateMVars (← inferType e)
    -- not `forallMetaTelescopeReducing`: a `CTriple` unfolds to a `∀`
    let (_, _, concl) ← forallMetaTelescope ty
    if (ruleConcl? (← whnfR concl)).isSome || (wpArgs? concl).isSome || (← isUpd e) then
      user := user.push e
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
  -- facts of user structures (`NodeFacts N A sz`): their fields next to them (`destruct`)
  let g ← g.withContext do
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let .const c _ := (← whnfR (← instantiateMVars d.type)).getAppFn | continue
      unless isStructure (← getEnv) c && (← isProp d.type) && !(← isLibrary c) do continue
      if (← isClass? d.type).isSome then continue
      g ← destruct g d.fvarId
    pure g
  withRunCaches do
    discard <| arithSimpCtx
    (← caches).userCtx.set userCtx
    -- the user definitions that the caller's updates produce (`own CI γ e ctx` of `own_empty`)
    for u in user do
      unless ← isUpd u do continue
      let heads ← withNewMCtxDepth do
        let (_, _, concl) ← forallMetaTelescope (← inferType u)
        (atoms concl.appArg!).filterMapM fun a => do
          let .const c _ := a.getAppFn | return none
          if ← isLibrary c then return none
          return some c
      (← caches).updHeads.modify (· ++ heads)
    let h0 ← IO.getNumHeartbeats
    let gs ← if (wpArgs? (← instantiateMVars (← g.getType))).isSome then wpEntry g user extra
      else walk g user extra 400
    trace[fsym.total] "heartbeats {((← IO.getNumHeartbeats) - h0) / 1000}"
    -- (an unknown of the proof that no goal left names: an engine fault, shown before the
    -- kernel rejects the proof)
    let us ← (← getMVars (mkMVar g)).filterM fun u => return !gs.contains u && !(← u.isDelayedAssigned)
    unless us.isEmpty do
      logError m!"fsym: the proof has unknowns {← us.mapM fun u => do instantiateMVars (← u.getType)}"
    replaceMainGoal gs

end Zig.Full.Auto
