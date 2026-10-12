import ZigLean.Sep.Total
import ZigLean.RecTemplate
import Lean

/-!
# Invariant/measure templates for generated loops

`LoopTemplate body again inv post` packages the one obligation a `Zig.loop` needs: from the
invariant `inv s n`, one run of the body is a `TotalTriple` that either repeats with a smaller
ghost measure `n' < n` and the invariant, or exits with `post`. `n` is a natural-number measure
that the invariant carries, so it can count list nodes or remaining queue items that the locals
alone do not give; a measure on the locals is `inv s n := ⌜n = μ s⌝ ∗ I s`.

`LoopTemplate.total` proves the whole loop by strong induction on the measure, through
`TotalTriple.loop_ghost`; `LoopTemplate.partial` projects the ordinary `Triple`. The step is
stated as a separation triple, so a client never mentions the frame heap of the loop proof.

`loop_template inv post` applies the template to a `TotalTriple` or `Triple` goal about
`(Zig.loop body again).run s` and leaves exactly three named goals:

* `step`: the body preserves `inv` and decreases the measure, or establishes `post`;
* `entry`: the precondition gives `inv s n` for some measure `n`;
* `exit`: `post` gives the goal's postcondition; closed automatically when it is the same
  assertion (up to `intro`/`exact`), so only real premises remain.

`loop_template? inv post` does the same and reports the remaining premises with their types.

Nested loops: the translator emits an inner loop as `Zig.loop inner again'` inside the outer
loop's body def. `LoopTemplate.run` gives the inner loop's run from its own template, so the
outer `step` proof uses it like any other step of the body.

`loop_template?` without arguments (or `loop_template? _ post`) only prints bounded inference
suggestions (loop-carried locals, a measure and bound for a counter loop, `post` generalized
over the counter); see "Bounded invariant and measure inference" below.
-/

namespace Zig

open Assn

/-- The assertion after one body run: repeat with the invariant at a smaller measure, or exit. -/
def loopNext {σ ε : Type} (again : ε → Bool) (inv : σ → Nat → Assn) (post : ε → σ → Assn)
    (n : Nat) (r : ε × σ) : Assn :=
  if again r.1 then Assn.ex fun n' => ⌜n' < n⌝ ∗ inv r.2 n' else post r.1 r.2

theorem loopNext_repeat {σ ε : Type} {again : ε → Bool} {inv : σ → Nat → Assn}
    {post : ε → σ → Assn} {n n' : Nat} {e : ε} {s : σ} {h : Heap} (ha : again e = true)
    (hlt : n' < n) (hi : inv s n' h) : loopNext again inv post n (e, s) h := by
  simp only [loopNext, ha, ↓reduceIte]
  exact ⟨n', sep_lift.mpr ⟨hlt, hi⟩⟩

theorem loopNext_exit {σ ε : Type} {again : ε → Bool} {inv : σ → Nat → Assn}
    {post : ε → σ → Assn} {n : Nat} {e : ε} {s : σ} {h : Heap} (ha : again e = false)
    (hp : post e s h) : loopNext again inv post n (e, s) h := by
  simpa only [loopNext, ha, Bool.false_eq_true, ↓reduceIte] using hp

/-- The invariant/measure template of a loop: one body run, as a total triple. -/
structure LoopTemplate {σ ε : Type} (body : MM σ ε) (again : ε → Bool)
    (inv : σ → Nat → Assn) (post : ε → σ → Assn) : Prop where
  step : ∀ s n, TotalTriple (inv s n) (body.run s) (loopNext again inv post n)

namespace LoopTemplate

variable {σ ε : Type} {body : MM σ ε} {again : ε → Bool} {inv : σ → Nat → Assn}
  {post : ε → σ → Assn}

/-- The loop terminates from any state satisfying the invariant at some measure. -/
theorem total (t : LoopTemplate body again inv post) (s : σ) :
    TotalTriple (Assn.ex (inv s)) ((Zig.loop body again).run s) (fun r => post r.1 r.2) := by
  apply TotalTriple.ex
  intro n
  apply TotalTriple.loop_ghost body again inv post _ s n
  intro hF s n m h hd hm hi hs
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hnext, hs'⟩ := t.step s n m h hF hd hm hi hs
  refine ⟨e, s', m', h', hr, hd', hm', hs', ?_⟩
  cases ha : again e
  · simpa only [loopNext, ha, Bool.false_eq_true, ↓reduceIte] using hnext
  · simp only [loopNext, ha, ↓reduceIte] at hnext ⊢
    obtain ⟨n', hn'⟩ := hnext
    exact ⟨n', (sep_lift.mp hn').1, (sep_lift.mp hn').2⟩

theorem «partial» (t : LoopTemplate body again inv post) (s : σ) :
    Triple (Assn.ex (inv s)) ((Zig.loop body again).run s) (fun r => post r.1 r.2) :=
  (t.total s).toPartial

/-! ### Nested loops

The translator emits an inner loop as `Zig.loop inner again'` inside the outer loop's body,
over the same locals. Its template gives the inner loop's run from any state in which its
invariant holds; the outer step uses that run like any other step of the body. -/

/-- The run of a templated loop from inside an enclosing body: it returns, preserves the frame
and establishes `post`. Used to discharge an inner loop in the outer loop's `step`. -/
theorem run (t : LoopTemplate body again inv post) {s : σ} {n : Nat} {m : Mem} {h hF : Heap}
    (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF) (hi : inv s n h) (hs : m.Seq) :
    ∃ e s' m' h', ((Zig.loop body again).run s).run m = pure ((e, s'), m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ post e s' h' ∧ m'.Seq := by
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hp, hs'⟩ := t.total s m h hF hd hm ⟨n, hi⟩ hs
  exact ⟨e, s', m', h', hr, hd', hm', hp, hs'⟩

end LoopTemplate

/-- The target of `loop_template` on a total goal; the three premises are the named goals. -/
theorem TotalTriple.loop_template {σ ε : Type} {body : MM σ ε} {again : ε → Bool} {s : σ}
    {P : Assn} {Q : ε × σ → Assn} (inv : σ → Nat → Assn) (post : ε → σ → Assn)
    (step : LoopTemplate body again inv post) (entry : ∀ h, P h → ∃ n, inv s n h)
    (exit : ∀ e s' h, post e s' h → Q (e, s') h) :
    TotalTriple P ((Zig.loop body again).run s) Q :=
  (step.total s).conseq entry (fun r h hp => exit r.1 r.2 h hp)

/-- The target of `loop_template` on a partial goal. The measure still has to decrease. -/
theorem Triple.loop_template {σ ε : Type} {body : MM σ ε} {again : ε → Bool} {s : σ}
    {P : Assn} {Q : ε × σ → Assn} (inv : σ → Nat → Assn) (post : ε → σ → Assn)
    (step : LoopTemplate body again inv post) (entry : ∀ h, P h → ∃ n, inv s n h)
    (exit : ∀ e s' h, post e s' h → Q (e, s') h) :
    Triple P ((Zig.loop body again).run s) Q :=
  (TotalTriple.loop_template inv post step entry exit).toPartial

end Zig

namespace Zig.LoopTemplateTactic

open Lean Elab Tactic Meta

/-- Apply the template to the main goal; returns the remaining premises (other goals untouched). -/
def applyTemplate (inv post : Term) : TacticM (List MVarId) := do
  let g :: others ← getGoals | throwError "loop_template: no goals"
  let rule ← match (← whnfR (← g.getType)).getAppFn.constName? with
    | some ``Zig.TotalTriple => pure (mkIdent ``Zig.TotalTriple.loop_template)
    | some ``Zig.Triple => pure (mkIdent ``Zig.Triple.loop_template)
    | _ => throwError "loop_template: the goal is not a TotalTriple or Triple about \
        (Zig.loop body again).run s"
  let goals ← evalTacticAt (← `(tactic| refine $rule $inv $post ?step ?entry ?exit)) g
  -- Plain tags, so `case step` and the report name the premises without macro scopes.
  for g in goals do
    g.setTag (← g.getTag).eraseMacroScopes
  -- Close `exit` when the template's `post` is already the goal's postcondition.
  let mut rest := #[]
  for g in goals do
    if (← g.getTag) == `exit then
      let tac ← `(tactic| (intro _ _ _ hp; exact hp))
      match ← observing? (evalTacticAt tac g) with
      | some [] => pure ()
      -- Reduce `(e, s').1`-style projections left by instantiating the goal's postcondition.
      | _ => rest := rest ++ ((← observing? (evalTacticAt (← `(tactic| dsimp only)) g)).getD [g]).toArray
    else
      rest := rest.push g
  setGoals (rest.toList ++ others)
  return rest.toList

/-- The remaining goals, one line each: `tag : type`. -/
def reportPremises (goals : List MVarId) : TacticM Unit := do
  let lines ← goals.mapM fun g => do
    let d ← g.getDecl
    return m!"{d.userName} : {← instantiateMVars d.type}"
  logInfo (m!"loop_template remaining premises ({goals.length}):" ++
    MessageData.joinSep (lines.map (m!"\n  " ++ ·)) m!"")

/-! ### Bounded invariant and measure inference

`loop_template?` without an invariant reads the loop body (one definition unfolding, no
evaluation) and prints suggestions; it proves nothing and leaves the goal unchanged. It follows
only the generated shapes: locals read by `(← get).f`, writes by `modify (fun s => { s with … })`,
checked `Zig.add`/`Zig.sub` steps of a local by a positive literal `k`, loads, and
`Zig.lt`/`le`/`gt`/`ge` guards.

* A counter that steps towards a fixed bound (every write is a step the same way): a measure and
  a bound invariant, in `Nat` for an unsigned guard and in `Int` for a signed one. The slack is
  `k - 1` for a strict guard and `k` otherwise, so the invariant survives the last step.
* The side premise of the step: the checked add or sub must not overflow on a repeat. It is
  reported as discharged by the guard (`k = 1` under a strict guard) or as a premise to supply
  (`bound + k - 1 < 2^w`, `k ≤ bound + 1`, and their signed forms).
* A counter that is also reset to a value from outside the loop (a reset counter): its own
  measure can grow, so it gets none. With another counter that has a measure `μ`, the
  lexicographic candidate `μ s * (R + 1) + μ' s` is suggested, where `μ'` is the reset counter's
  measure and `R` its largest value; it is valid when every path that resets the counter steps
  the other one.
* A local written only from a load (a pointer that follows a link: a list walk): a ghost measure
  is suggested, the number of nodes from that local in the invariant's representation predicate.
* Given a postcondition (`loop_template? _ post`), the postcondition with the bound replaced by
  the counter.

A nested loop's body, calls, other memory shapes and other side premises are not followed and
are reported as such. -/

/-- What inference knows about a value of the loop body. -/
inductive Src where
  | state
  | field (f : Name)
  /-- `f + k` (`up`) or `f - k` by a checked `Zig.add`/`Zig.sub` of the literal `k > 0`. -/
  | step (f : Name) (up : Bool) (k : Nat)
  | outer (e : Expr)
  /-- A value read from memory. -/
  | loaded
  | other
  deriving Inhabited

structure Facts where
  vals : Std.HashMap FVarId Src := {}
  locals : FVarIdSet := {}
  writes : Array (Name × Src) := #[]
  guards : Array (Name × Bool × Src × Src) := #[]
  seen : Array Expr := #[]
  nested : Array Expr := #[]

abbrev InferM := StateRefT Facts MetaM

def bindLocal (n : Name) (ty : Expr) (src : Src) (k : Expr → InferM Unit) : InferM Unit :=
  withLocalDeclD n ty fun x => do
    modify fun st => { st with locals := st.locals.insert x.fvarId!,
                               vals := st.vals.insert x.fvarId! src }
    k x

/-- Classify a value of the body. -/
partial def classify (structName : Name) (e : Expr) : InferM Src := do
  let e := e.consumeMData.headBeta
  let st ← get
  if let .fvar x := e then
    if let some s := st.vals[x]? then return s
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    if c == ``Pure.pure && args.size == 4 then return ← classify structName args[3]!
    if c == ``MonadState.get || c == ``MonadStateOf.get || c == ``StateT.get || c == ``getThe then
      return .state
    if (c == ``Zig.add || c == ``Zig.sub) && args.size == 4 then
      if let some k := Zig.RecTemplate.litNat? args[3]! then
        if k > 0 then
          if let .field f ← classify structName args[2]! then return .step f (c == ``Zig.add) k
    if c == ``Zig.load && args.size == 4 then return .loaded
    if let some info ← getProjectionFnInfo? c then
      if c.getPrefix == structName && args.size == info.numParams + 1 then
        if let .state ← classify structName args[info.numParams]! then return .field (.mkSimple c.getString!)
    -- A lifted computation (`liftM`, `monadLift`): classify the lifted value.
    if let some inner := args.back? then
      if c == ``MonadLiftT.monadLift || c == ``liftM || c == ``StateT.lift then
        return ← classify structName inner
  | .proj s i x =>
    if s == structName then
      if let .state ← classify structName x then
        return .field (getStructureFields (← getEnv) s)[i]!
  | _ => pure ()
  if !e.hasLooseBVars && !(e.hasAnyFVar st.locals.contains) then return .outer e
  return .other

/-- Walk the body: binders get their classification, guards and writes are recorded. -/
partial def walk (structName ctor : Name) (e : Expr) : InferM Unit := do
  let e := e.consumeMData
  match e with
  | .lam n ty b _ => bindLocal n ty .other fun x => walk structName ctor (b.instantiate1 x)
  | .letE n ty v b _ => do
    walk structName ctor v
    let src ← classify structName v
    bindLocal n ty src fun x => walk structName ctor (b.instantiate1 x)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := fn then
      if c == ``Bind.bind && args.size == 6 then
        walk structName ctor args[4]!
        if let .lam n ty b _ := args[5]!.consumeMData then
          let src ← classify structName args[4]!
          return ← bindLocal n ty src fun x => walk structName ctor (b.instantiate1 x)
      if c == ``modify && args.size == 4 then
        if let .lam n ty b _ := args[3]!.consumeMData then
          return ← bindLocal n ty .state fun x => walk structName ctor (b.instantiate1 x)
      if c == ``Zig.loop && args.size == 7 then
        modify fun st => { st with nested := st.nested.push args[5]! }
        return
      -- A guard appears in both the `if` condition and its `Decidable` instance; record it once.
      if [``Zig.lt, ``Zig.le, ``Zig.gt, ``Zig.ge].contains c && args.size == 4 &&
          !(← get).seen.contains e then
        modify fun st => { st with seen := st.seen.push e }
        if let some signed := args[1]!.constName? then
          let a ← classify structName args[2]!
          let b ← classify structName args[3]!
          modify fun st => { st with guards := st.guards.push (c, signed == ``Bool.true, a, b) }
      if c == ctor then
        let fields := getStructureFields (← getEnv) structName
        let nParams := args.size - fields.size
        for f in fields, i in [0:fields.size] do
          match ← classify structName args[nParams + i]! with
          | .field f' => if f' != f then modify fun st => { st with writes := st.writes.push (f, .field f') }
          | src => modify fun st => { st with writes := st.writes.push (f, src) }
    walk structName ctor fn
    for a in args do walk structName ctor a
  | .proj _ _ x => walk structName ctor x
  | _ => pure ()

/-- A counter candidate of a guard: the local, its direction, its largest step, the bound,
whether the guard is signed and strict, and whether the local is also reset. -/
structure Counter where
  f : Name
  up : Bool
  k : Nat
  bound : Expr → MetaM Expr
  boundShown : MessageData
  signed : Bool
  strict : Bool
  reset : Bool
  op : Name

/-- Suggestions for the loop in the goal; `post?` is the user's postcondition, if any. -/
def inferReport (g : MVarId) (post? : Option Expr) : MetaM MessageData := g.withContext do
  let some loop := (← instantiateMVars (← g.getType)).find? (·.isAppOfArity ``Zig.loop 7)
    | throwError "loop_template?: the goal does not mention a Zig.loop"
  let body := loop.getArg! 5
  let σ ← whnfR (← instantiateMVars (← inferType body)).getAppArgs[0]!
  let some structName := σ.getAppFn.constName? | throwError "loop_template?: locals type {σ}"
  unless isStructure (← getEnv) structName do
    throwError "loop_template?: {structName} is not a structure"
  let ctorVal := getStructureCtor (← getEnv) structName
  let fields := getStructureFields (← getEnv) structName
  let some unfolded ← unfoldDefinition? body
    | throwError "loop_template?: cannot unfold the loop body {body}"
  let ((), facts) ← (walk structName ctorVal.name unfolded).run {}
  let written := fields.filter fun f => facts.writes.any (·.1 == f)
  let unchanged := fields.filter (!written.contains ·)
  let writesOf (f : Name) : Array Src :=
    facts.writes.filterMap fun (w : Name × Src) => if w.1 == f then some w.2 else none
  let stepsOf (f : Name) : Array (Bool × Nat) := (writesOf f).filterMap fun
    | .step f' up k => if f' == f then some (up, k) else none
    | _ => none
  -- The direction and the largest step of `f`, if every step goes the same way; `reset`: the
  -- other writes set it to a value from outside the loop.
  let counter (f : Name) : Option (Bool × Nat × Bool) :=
    let ws := writesOf f
    let ss := stepsOf f
    let resets := ws.filter fun | .outer _ => true | _ => false
    match ss[0]? with
    | some (up, _) =>
      if ss.all (·.1 == up) && ss.size + resets.size == ws.size then
        some (up, ss.foldl (fun (k : Nat) (st : Bool × Nat) => Nat.max k st.2) 0, !resets.isEmpty)
      else none
    | none => none
  let width (f : Name) : MetaM (Option Nat) := withLocalDeclD `s σ fun s => do
    let t ← whnf (← inferType (← mkProjection s f))
    if t.isAppOfArity ``BitVec 1 then evalNat t.appArg! else pure none
  let names (xs : Array Name) := if xs.isEmpty then m!"(none)" else
    MessageData.joinSep (xs.toList.map (m!"{·}")) m!", "
  let mut lines : Array MessageData := #[
    m!"loop-carried locals (written by the body): {names written}",
    m!"unchanged locals: {names unchanged}"]
  let mut found := false
  let mut plain : Array (Counter × Expr) := #[]
  let mut resets : Array Counter := #[]
  for (op, signed, a, b) in facts.guards do
    -- Normalize to `lo < hi` / `lo ≤ hi`.
    let (lo, hi, strict) := if op == ``Zig.lt || op == ``Zig.le then (a, b, op == ``Zig.lt)
      else (b, a, op == ``Zig.gt)
    -- The counter moves towards the bound by a checked step.
    let pick : Option (Name × Bool × Nat × Bool × Src) :=
      (match lo with
        | .field f => (counter f).bind fun (up, k, r) => if up then some (f, up, k, r, hi) else none
        | _ => none) <|>
      (match hi with
        | .field f => (counter f).bind fun (up, k, r) => if up then none else some (f, up, k, r, lo)
        | _ => none)
    let some (f, up, k, reset, bnd) := pick
      | lines := lines.push m!"guard {op}: no local steps towards a fixed bound, no measure inferred"
        continue
    let bound? : Option ((Expr → MetaM Expr) × MessageData) := match bnd with
      | .outer e => some (fun _ => pure e, m!"{e}")
      | .field f' => if unchanged.contains f' then some ((mkProjection · f'), m!"s.{f'}") else none
      | _ => none
    let some (bound, shown) := bound?
      | lines := lines.push m!"guard {op}: the bound of {f} changes in the loop, no measure inferred"
        continue
    let c : Counter := { f, up, k, bound, boundShown := shown, signed, strict, reset, op }
    if reset then
      resets := resets.push c
      continue
    -- The slack keeps the invariant after the last step: `k - 1` (strict) or `k`.
    let slack := if strict then k - 1 else k
    let (measure, inv) ← withLocalDeclD `s σ fun s => do
      let conv := if signed then ``BitVec.toInt else ``BitVec.toNat
      let cv ← mkAppM conv #[← mkProjection s f]
      let bv ← mkAppM conv #[← bound s]
      let addSlack (x : Expr) : MetaM Expr :=
        if slack == 0 then pure x
        else if signed then mkAppM ``HAdd.hAdd #[x, toExpr (slack : Int)]
        else pure (mkNatAdd x (mkNatLit slack))
      let (lo, hi) ← if up then pure (cv, ← addSlack bv) else pure (bv, ← addSlack cv)
      let m ← if signed then mkAppM ``Int.toNat #[← mkAppM ``HSub.hSub #[hi, lo]]
        else pure (mkNatSub hi lo)
      pure (← mkLambdaFVars #[s] m, ← mkLambdaFVars #[s] (← mkAppM ``LE.le #[lo, hi]))
    found := true
    plain := plain.push (c, measure)
    lines := lines.push m!"measure candidate: {measure}"
    lines := lines.push m!"bound invariant candidate: {inv}"
    -- The side premise of the step on a repeat.
    let w? ← width f
    let stepShown := m!"{f} {if up then "+" else "-"} {k}"
    let side : Option MessageData := match w?, signed, up, strict with
      | _, _, _, true => if k == 1 then none else match signed, up with
        | false, true => some m!"{shown}.toNat + {k - 1} < 2^{w?.getD 0}"
        | false, false => some m!"{k} ≤ {shown}.toNat + 1"
        | true, true => some m!"{shown}.toInt + {k - 1} < 2^{w?.getD 1 - 1}"
        | true, false => some m!"-2^{w?.getD 1 - 1} ≤ {shown}.toInt + 1 - {k}"
      | _, false, true, false => some m!"{shown}.toNat + {k} < 2^{w?.getD 0}"
      | _, false, false, false => some m!"{k} ≤ {shown}.toNat"
      | _, true, true, false => some m!"{shown}.toInt + {k} < 2^{w?.getD 1 - 1}"
      | _, true, false, false => some m!"-2^{w?.getD 1 - 1} ≤ {shown}.toInt - {k}"
    lines := lines.push <| match side with
      | none => m!"side premise of the step {stepShown}: discharged by the guard (no overflow)"
      | some p => m!"side premise of the step {stepShown} (no overflow on a repeat): {p}"
    -- With a postcondition: replace a bound from outside the loop by the counter.
    if let (some post, .outer be) := (post?, bnd) then
      let postT ← inferType post
      let cand ← forallBoundedTelescope postT (some 2) fun xs _ => do
        let some s := xs[1]? | return none
        let app := mkAppN post xs
        let app := (← unfoldDefinition? app).getD app
        let field ← mkProjection s f
        unless ← isDefEq (← inferType field) (← inferType be) do return none
        let replaced := (← instantiateMVars app).headBeta.replace fun t =>
          if t == be then some field else none
        if replaced == app.headBeta then return none
        some <$> mkLambdaFVars xs replaced
      if let some cand := cand then
        lines := lines.push m!"postcondition with {be} replaced by {f}: {cand}"
  -- Reset counters: lexicographic with a counter that has a measure.
  for c in resets do
    let outer := plain.find? fun (p, _) => p.f != c.f
    match outer, c.signed with
    | some (p, μ), false =>
      let slack := if c.strict then c.k - 1 else c.k
      let lex ← withLocalDeclD `s σ fun s => do
        let plus (x : Expr) := if slack == 0 then x else mkNatAdd x (mkNatLit slack)
        let cv ← mkAppM ``BitVec.toNat #[← mkProjection s c.f]
        let b0 ← mkAppM ``BitVec.toNat #[← c.bound s]
        let bv := plus b0
        let inner := if c.up then mkNatSub bv cv else mkNatSub (plus cv) b0
        -- The reset counter's measure is at most `R` (its unsigned bound plus the slack, or
        -- the width's range when it counts down).
        let range ← if c.up then pure bv else do
          -- `c.f + slack - b0 < 2^w + slack`.
          let some w ← width c.f | pure (mkNatLit 0)
          pure (mkNatLit (2 ^ w + slack))
        mkLambdaFVars #[s] (mkNatAdd (mkNatMul (μ.beta #[s]) (mkNatAdd range (mkNatLit 1))) inner)
      found := true
      lines := lines.push m!"{c.f} steps towards its bound but is also reset; valid if every path \
        that resets {c.f} steps {p.f}:"
      lines := lines.push m!"lexicographic measure candidate: {lex}"
    | _, _ =>
      lines := lines.push m!"guard {c.op}: {c.f} steps towards its bound but is also reset, and no \
        other counter has a measure: no measure inferred"
  -- Pointer-chasing locals: a ghost measure.
  let chasing := written.filter fun f =>
    let ws := writesOf f
    !ws.isEmpty && ws.all fun | .loaded => true | _ => false
  for f in chasing do
    lines := lines.push m!"{f} is written from a load (a list walk): ghost measure candidate: the \
      number of nodes from s.{f} in the invariant's representation predicate, \
      e.g. inv s n := ∃ zs, ⌜zs.length = n⌝ ∗ list s.{f} zs"
  unless found do
    lines := lines.push m!"measure: no counter measure inferred; supply a ghost measure, e.g. the \
      number of remaining items"
  for n in facts.nested do
    lines := lines.push m!"nested loop {n}: not followed; give it its own template (LoopTemplate.run)"
  lines := lines.push m!"not inferred: side premises of other operations (overflow and range \
    bounds), the values of the other carried locals, memory shapes"
  return m!"loop_template? suggestions (unchecked, nothing is proved):" ++
    MessageData.joinSep (lines.toList.map (m!"\n  " ++ ·)) m!""

end Zig.LoopTemplateTactic

/-- Apply the invariant/measure template; leaves the named goals `step`, `entry`, `exit`. -/
elab "loop_template " inv:term:max post:term:max : tactic => do
  discard <| Zig.LoopTemplateTactic.applyTemplate inv post

/-- `loop_template`, reporting the remaining premises with their types.

Without arguments, or with `_` for the invariant, it only prints inference suggestions from the
loop body (and from `post`, if given); the goal is unchanged. -/
syntax "loop_template?" (ppSpace colGt term:max ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| loop_template? $inv $post) => do
    if inv.raw.isOfKind ``Lean.Parser.Term.hole then
      let g ← Lean.Elab.Tactic.getMainGoal
      let post ← g.withContext do
        Lean.instantiateMVars (← Lean.Elab.Term.elabTerm post none)
      Lean.logInfo (← Zig.LoopTemplateTactic.inferReport g post)
    else
      Zig.LoopTemplateTactic.reportPremises (← Zig.LoopTemplateTactic.applyTemplate inv post)
  | `(tactic| loop_template?) => do
    Lean.logInfo (← Zig.LoopTemplateTactic.inferReport (← Lean.Elab.Tactic.getMainGoal) none)
