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

def applyTemplate (inv post : Term) : TacticM Unit := do
  evalTactic (← `(tactic| first
    | refine Zig.TotalTriple.loop_template $inv $post ?step ?entry ?exit
    | refine Zig.Triple.loop_template $inv $post ?step ?entry ?exit
    | fail "loop_template: the goal is not a TotalTriple or Triple about (Zig.loop body again).run s"))
  let goals ← getGoals
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
  setGoals rest.toList

/-- The remaining goals, one line each: `tag : type`. -/
def reportPremises : TacticM Unit := do
  let goals ← getGoals
  let lines ← goals.mapM fun g => do
    let d ← g.getDecl
    return m!"{d.userName} : {← instantiateMVars d.type}"
  logInfo (m!"loop_template remaining premises ({goals.length}):" ++
    MessageData.joinSep (lines.map (m!"\n  " ++ ·)) m!"")

end Zig.LoopTemplateTactic

/-- Apply the invariant/measure template; leaves the named goals `step`, `entry`, `exit`. -/
elab "loop_template " inv:term:max post:term:max : tactic =>
  Zig.LoopTemplateTactic.applyTemplate inv post

/-- `loop_template`, reporting the remaining premises with their types. -/
elab "loop_template? " inv:term:max post:term:max : tactic => do
  Zig.LoopTemplateTactic.applyTemplate inv post
  Zig.LoopTemplateTactic.reportPremises
