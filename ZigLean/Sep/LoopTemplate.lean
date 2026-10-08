import ZigLean.Sep.Total
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

/-- An inner loop followed by the rest `k` of the enclosing body: the continuation only has to
start from the inner loop's `post`. -/
theorem bind {β : Type} {k : ε → MM σ β} {Q : β × σ → Assn}
    (t : LoopTemplate body again inv post) (hk : ∀ e s', TotalTriple (post e s') ((k e).run s') Q)
    (s : σ) : TotalTriple (Assn.ex (inv s)) ((Zig.loop body again >>= k).run s) Q := by
  rw [StateT.run_bind]
  exact TotalTriple.bind (t.total s) fun r => hk r.1 r.2

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
checked `Zig.add`/`Zig.sub` steps of a local by a literal, and unsigned `Zig.lt`/`le`/`gt`/`ge`
guards. From a counter that steps towards a bound it suggests a measure and a bound invariant;
given a postcondition (`loop_template? _ post`) it also suggests the postcondition with that
bound replaced by the counter. A nested loop's body, calls, memory and any other shape are not
followed and are reported as such. -/

/-- What inference knows about a value of the loop body. -/
inductive Src where
  | state
  | field (f : Name)
  | step (f : Name) (up : Bool)
  | outer (e : Expr)
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
    if (c == ``Zig.add || c == ``Zig.sub) && args.size == 4 && args[3]!.isAppOf ``OfNat.ofNat then
      if let .field f ← classify structName args[2]! then return .step f (c == ``Zig.add)
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
  -- The direction of `f`, if every write of `f` steps it the same way by a literal.
  let direction (f : Name) : Option Bool :=
    let ws := facts.writes.filterMap fun (w : Name × Src) => if w.1 == f then some w.2 else none
    let dirs := ws.filterMap fun
      | .step f' up => if f' == f then some up else none
      | _ => none
    if dirs.size == ws.size then dirs[0]?.filter fun up => dirs.all (· == up) else none
  let names (xs : Array Name) := if xs.isEmpty then m!"(none)" else
    MessageData.joinSep (xs.toList.map (m!"{·}")) m!", "
  let mut lines : Array MessageData := #[
    m!"loop-carried locals (written by the body): {names written}",
    m!"unchanged locals: {names unchanged}"]
  let mut found := false
  for (op, signed, a, b) in facts.guards do
    -- Normalize to `lo < hi` / `lo ≤ hi`.
    let (lo, hi, strict) := if op == ``Zig.lt || op == ``Zig.le then (a, b, op == ``Zig.lt)
      else (b, a, op == ``Zig.gt)
    if signed then
      lines := lines.push m!"guard {op}: signed comparison, no measure inferred"
      continue
    -- The counter moves towards the bound by a checked step; the bound does not change.
    let pick : Option (Name × Bool × Src) := match lo, hi with
      | .field f, b => if direction f == some true then some (f, true, b) else none
      | b, .field f => if direction f == some false then some (f, false, b) else none
      | _, _ => none
    let some (f, up, bnd) := pick
      | lines := lines.push m!"guard {op}: no local steps towards a fixed bound, no measure inferred"
        continue
    let bound? : Option (Expr → MetaM Expr) := match bnd with
      | .outer e => some fun _ => pure e
      | .field f' => if unchanged.contains f' then some (mkProjection · f') else none
      | _ => none
    let some bound := bound?
      | lines := lines.push m!"guard {op}: the bound of {f} changes in the loop, no measure inferred"
        continue
    found := true
    let slack := if strict then 0 else 1
    let (measure, inv) ← withLocalDeclD `s σ fun s => do
      let c ← mkAppM ``BitVec.toNat #[← mkProjection s f]
      let b ← mkAppM ``BitVec.toNat #[← bound s]
      let b := if slack == 0 then b else mkNatAdd b (mkNatLit slack)
      let (lo, hi) := if up then (c, b) else (b, c)
      pure (← mkLambdaFVars #[s] (mkNatSub hi lo), ← mkLambdaFVars #[s] (← mkAppM ``LE.le #[lo, hi]))
    lines := lines.push m!"measure candidate: {measure}"
    lines := lines.push m!"bound invariant candidate: {inv}"
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
  unless found do
    lines := lines.push m!"measure: not inferred (no unsigned counter steps towards a fixed bound); \
      supply a ghost measure, e.g. the number of remaining items"
  for n in facts.nested do
    lines := lines.push m!"nested loop {n}: not followed; give it its own template (LoopTemplate.run)"
  lines := lines.push m!"not inferred: side premises (overflow and range bounds), the values of the \
    other carried locals, memory shapes"
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
