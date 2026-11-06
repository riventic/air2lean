import ZigLean.Sep.Full.AutoAll

/-!
# Inferred posts and missed atoms (P09-E2, P09-E3)

The engine outputs of `fsym` that the invariant generator reads (`docs/invariant-synthesis.md`,
stage S1), in each backend that walks a memory program:

* **The strongest post at function ends** (P09-E2): a goal whose postcondition is an unknown gets
  the join of its returns' states, with the walk's locals existential and its facts as facts,
  also where a case split substituted a variable the unknown takes (`?Q true v`). The report
  lists it under `posts` (`kind` `return`).
* **The strongest post at a loop's exits** (P09-E2): a loop with a registered invariant and no
  registered exit post (`@[fsym_inv]`, no `B.post`) continues from the join of its step's exits,
  so the caller's `match` on the exit label needs no hand post. The report lists it (`kind`
  `loop_exit`, `program` the loop).
* **The missed atoms of a failed plan** (P09-E3): a stop with no rule (and an invariant that does
  not hold at a loop's entry) lists the rules whose precondition had no plan, each with the atoms
  of its precondition that the state did not provide and their unknowns.

The theorems are kernel-checked; incomplete walks are inspected as goals, never admitted.
-/

namespace SepAuto.Infer
open Lean Meta Elab Tactic Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Zig.Full.Auto.Report

/-! ## Function ends -/

/-- Two returns with different states. -/
def pick (p : Ptr) (b : Bool) : MemM (BitVec 64) := do
  let v ← Zig.load (BitVec 64) 8 p
  if b then pure 0 else pure v

/-- The post of `pick` is inferred in the total, partial and thread logics (kernel-checked: the
inferred post is the witness). -/
theorem pick_total (p : Ptr) (v : BitVec 64) (b : Bool) :
    ∃ Q, FTotalTriple (up (pts p 8 v)) (pick p b) Q := by
  apply Exists.intro
  unfold pick
  fsym

theorem pick_partial (p : Ptr) (v : BitVec 64) (b : Bool) :
    ∃ Q, FTriple (up (pts p 8 v)) (pick p b) Q := by
  apply Exists.intro
  unfold pick
  fsym

theorem pick_thread (p : Ptr) (v : BitVec 64) (b : Bool) :
    ∃ Q, FTTotalTriple (up (pts p 8 v)) (pick p b) Q := by
  apply Exists.intro
  unfold pick
  fsym

theorem pick_thread_partial (p : Ptr) (v : BitVec 64) (b : Bool) :
    ∃ Q, FTTriple (up (pts p 8 v)) (pick p b) Q := by
  apply Exists.intro
  unfold pick
  fsym

private def w64 : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

/-- The goal `T (up (pts p 8 v)) (pick p b) ?Q`: no residual, the post determined and closed,
a join of the two returns (an `∃` over the branch), each the cell and the result's equation; the
report names it, also as JSON. -/
private def inferPick (T : Name) : TacticM Unit := do
  withLocalDeclD `p (mkConst ``Zig.Ptr) fun p => withLocalDeclD `v w64 fun v =>
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    let Q ← mkFreshExprMVar (← mkArrow w64 (mkConst ``Zig.Full.FAssn))
    let pre ← mkAppM ``FAssn.up #[← mkAppM ``Zig.pts #[p, mkNatLit 8, v]]
    let prog ← deltaExpand (← mkAppM ``pick #[p, b]) (· == ``pick)
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM T #[pre, prog, Q])
    let (gs, report) ← runReport g.mvarId!
    unless gs.isEmpty do throwError "{T}: residuals left: {line report}"
    let q ← instantiateMVars Q
    if q.hasExprMVar then throwError "{T}: the post is not determined: {q}"
    Meta.check (← instantiateMVars g)
    let .lam _ _ body _ := q | throwError "{T}: the post is not a function: {q}"
    unless body.isAppOfArity ``FAssn.ex 2 && (body.getArg! 0).isConstOf ``Bool do
      throwError "{T}: the post is not the join of the two returns: {q}"
    unless report.status == "complete" && report.posts.size == 1 &&
        report.posts[0]!.kind == "return" && report.posts[0]!.program.isNone do
      throwError "{T}: the inferred post is not reported: {line report}"
    let .ok json := Json.parse ((line report).drop "fsym-report ".length).toString
      | throwError "invalid JSON report line: {line report}"
    let .ok posts := json.getObjValAs? (Array Json) "posts"
      | throwError "no JSON posts: {line report}"
    unless posts.size == 1 && (posts[0]!.getObjValAs? String "kind").toOption == some "return" do
      throwError "wrong JSON posts: {line report}"

example : True := by
  run_tac inferPick ``FTotalTriple
  run_tac inferPick ``FTriple
  run_tac inferPick ``FTTotalTriple
  run_tac inferPick ``FTTriple
  trivial

/-! ## Loop exits -/

structure Locals where
  i : BitVec 32
  deriving Inhabited

inductive Exit where
  | ret
  | brk
  | rep

def again : Exit → Bool
  | .rep => true
  | _ => false

/-- `while (i < n) : (i += 1) { *p += 1; }` -/
def fill.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := do
  let i ← pure ((← get).i)
  if Zig.lt false i n then (do
    let v ← Zig.load (BitVec 64) 8 p
    let v' ← Zig.add false v (1 : BitVec 64)
    Zig.store (α := BitVec 64) 8 p v'
    let i' ← Zig.add false ((← get).i) (1 : BitVec 32)
    modify (fun s => { s with i := i' })
    pure .rep)
  else (do
    pure .brk)

/-- The invariant and the measure; **no exit post** is registered. -/
@[fsym_inv] def fill.loop.inv (p : Ptr) (n : BitVec 32) (v0 : BitVec 64) (s : Locals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v0.toNat + n.toNat < 2 ^ 64⟫ ⋆
    (FAssn.ex fun v : BitVec 64 => ⟪v.toNat = v0.toNat + s.i.toNat⟫ ⋆ up (pts p 8 v))

@[fsym_inv] def fill.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

/-- The caller matches on the exit's label: only the strongest post at the exits says it is `brk`
(the invariant with `again r.1 = false` would leave `ret` open, a panic). -/
def fill (p : Ptr) (n : BitVec 32) : MemM Unit := do
  let e ← ((do
    modify (fun s => { s with i := (0 : BitVec 32) })
    match ← ((do
      Zig.loop (fill.loop p n) again) : MM Locals Exit) with
    | .brk => (do
      pure .ret)
    | e => pure e) : MM Locals Exit).run' (default : Locals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

theorem fill_total (R : FAssn) (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 v) ⋆ R) (fill p n)
      (fun _ => (FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) ⋆ R) := by
  unfold fill
  fsym

theorem fill_partial (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTriple (up (pts p 8 v)) (fill p n)
      (fun _ => FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) := by
  unfold fill
  fsym

theorem fill_thread (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTTotalTriple (up (pts p 8 v)) (fill p n)
      (fun _ => FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) := by
  unfold fill
  fsym

theorem fill_thread_partial (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + n.toNat < 2 ^ 64) :
    FTTriple (up (pts p 8 v)) (fill p n)
      (fun _ => FAssn.ex fun w : BitVec 64 => ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)) := by
  unfold fill
  fsym

section
-- The claims below are quoted inside `run_tac`: unhygienic, so they name the example's variables.
set_option hygiene false

set_option linter.unusedVariables false in
/-- The inferred exit post is reported (`loop_exit`, with the loop), and it is no stronger than
the step: a caller's post that claims one more increment is not proved. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + n.toNat < 2 ^ 64) : True := by
  run_tac withMainContext do
    let report (post : Lean.Term) : TacticM (List MVarId × Result) := do
      let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v)) (fill p n) $post)) none
      let g ← mkFreshExprSyntheticOpaqueMVar (← deltaExpand ty (· == ``fill))
      runReport g.mvarId!
    let (gs, r) ← report (← `(fun _ => FAssn.ex fun w : BitVec 64 =>
      ⟪w.toNat = v.toNat + n.toNat⟫ ⋆ up (pts p 8 w)))
    unless gs.isEmpty && r.posts.size == 1 && r.posts[0]!.kind == "loop_exit" &&
        r.posts[0]!.program.bind (·.head) == some "StateT.run" do
      throwError "the exit post is not reported: {line r}"
    let (gs, r) ← report (← `(fun _ => FAssn.ex fun w : BitVec 64 =>
      ⟪w.toNat = v.toNat + n.toNat + 1⟫ ⋆ up (pts p 8 w)))
    unless !gs.isEmpty && r.residuals.all (·.origin.condition == "postcondition") do
      throwError "a post stronger than the exits was proved: {line r}"
  trivial

end

/-! ## Missed atoms -/

section
set_option hygiene false

set_option linter.unusedVariables false in
/-- A load from a state without the cell stops with no rule; the report names the load rules
whose plan failed, each with the atom it missed (the cell at `p`) and that atom's unknowns. -/
example (p : Ptr) : True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple emp (Zig.load (BitVec 32) 4 p) (fun _ => emp))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, r) ← runReport g.mvarId!
    unless gs.length == 1 && r.residuals.size == 1 &&
        r.residuals[0]!.origin.reason == "no_rule" do
      throwError "the load did not stop with no rule: {line r}"
    let plans := r.residuals[0]!.origin.plans
    let cell (m : Missing) := m.atom.head == some "Zig.Full.FAssn.up" &&
      (m.atom.text.splitOn "pts p").length > 1 && !m.unknowns.isEmpty &&
      m.unknowns.all (·.name.startsWith "?u")
    unless plans.any (·.missing.any cell) do
      throwError "no plan names the missed cell: {line r}"
    let .ok json := Json.parse ((line r).drop "fsym-report ".length).toString
      | throwError "invalid JSON report line: {line r}"
    let .ok residuals := json.getObjValAs? (Array Json) "residuals"
      | throwError "no JSON residuals: {line r}"
    let .ok origin := residuals[0]!.getObjVal? "origin" | throwError "no JSON origin: {line r}"
    let .ok jplans := origin.getObjValAs? (Array Json) "plans" | throwError "no JSON plans: {line r}"
    unless jplans.size == plans.size do throwError "wrong JSON plans: {line r}"
  trivial

/-- A body whose invariant owns a cell at `q`, which the state at the entry does not have. -/
def absent.loop (p : Ptr) (n : BitVec 32) : MM Locals Exit := fill.loop p n

set_option linter.unusedVariables false in
@[fsym_inv] def absent.loop.inv (p : Ptr) (n : BitVec 32) (q : Ptr) (v0 : BitVec 64) (s : Locals) :
    FAssn :=
  up (pts q 8 v0) ⋆ (FAssn.ex fun v : BitVec 64 => up (pts p 8 v))

@[fsym_inv] def absent.loop.meas (n : BitVec 32) (s : Locals) : Nat :=
  n.toNat - s.i.toNat

set_option linter.unusedVariables false in
/-- An invariant that does not hold at the entry for want of an atom: the loop rule's plan names
a cell it missed (the state has one cell, the invariant two). -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64) : True := by
  run_tac withMainContext do
    let ty ← elabTerm (← `(FTotalTriple (up (pts p 8 v))
      ((Zig.loop (absent.loop p n) again).run { i := 0 }) (fun _ => up (pts p 8 v)))) none
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let (gs, r) ← runReport g.mvarId!
    unless gs.length == 1 && r.residuals.size == 1 &&
        r.residuals[0]!.origin.reason == "invariant_not_established" do
      throwError "the entry was not reported: {line r}"
    let loopRule (pl : Plan) := pl.rule.head == some "Zig.Full.FTotalTriple.loop_measure" &&
      pl.missing.any fun m => (m.atom.text.splitOn "pts ").length > 1
    unless r.residuals[0]!.origin.plans.any loopRule do
      throwError "the loop rule's plan does not name the missed cell: {line r}"
  trivial

end

end SepAuto.Infer
