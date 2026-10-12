import Lean
import ZigLean.Conc.Logic
import ZigLean.Conc.Progress
import ZigLean.Conc.PtrAtomic
import ZigLean.Mem.Halts

/-!
# Turn budgets of a thread

A thread's run is a tree (`CoN`, `ZigLean/Conc/Basic.lean`); the scheduler gives it one turn
at each sync op. `Turns R dispatch Q B tree`: every path of `tree` ends with a result (never "no
result") within `B` turns, and each value at the end satisfies `Q` with the budget and the depth
that are left. At a stop the thread goes on from any memory that satisfies the rely `R` (`R`
holds of every memory a scheduler turn can resume the thread in; `ZigLean/Conc/Returns.lean`
derives it from a strict protocol's invariant).

- **Costs** (`opCost`). A `yield`, `choose`, `pick`, `asyncChoice`, `join` or `wake` is one turn.
  A `spawn tgt` (`Turns.spawn`) costs `k + 2`: its own turn, the new thread's first turn and
  the new thread's budget `k`, which the spawner shows (`dispatch tgt` within `k` turns from
  every memory of the rely). So a spawn moves budget to the new thread and the sum over all
  threads never grows. A futex `wait` and a deferred task (`spawnGated`, `gate`) have no cost:
  a thread that reaches one has no budget (fail closed). A sleeping wait is resumed only by
  another thread, so its turns are not a property of the waiting thread alone.
- **`Stops R dispatch x Q m B`**: from the memory `m`, every depth `n ≥ B` of `x` keeps budget
  `B`, and every result leaves a budget `B'` no larger than the depth that is left, with `Q`.
  The rules (`Stops.bind`, `Stops.liftMem`, `Stops.sync`, `Stops.spawnC'`, the `CM` lifts,
  `Stops.loop`) follow the program; `stops` walks generated code with them. A module supplies
  the budgets, the loop invariants and their measures.
-/

namespace Zig
namespace Conc

variable {Tgt : Type}

/-- The turns of a sync op other than a spawn (see the module doc). `none`: no turn budget. -/
def opCost : SyncOp Tgt → Option Nat
  | .yield | .choose _ | .pick _ | .asyncChoice | .join _ | .wake .. => some 1
  | .spawn _ | .wait .. | .gate | .spawnGated _ => none

theorem opCost_pos {op : SyncOp Tgt} {c : Nat} (h : opCost op = some c) : 1 ≤ c := by
  cases op <;> simp [opCost] at h <;> omega

/-- A tree whose paths end with a result within `B` turns (see the module doc). -/
inductive Turns (R : Mem → Prop) (dispatch : Tgt → ConcM Tgt Unit) :
    {β : Type} → (β → Mem → Nat → Nat → Prop) → Nat → {n : Nat} → CoN Tgt (β × Mem) n → Prop
  | error {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n : Nat} {e : Error} :
      Turns R dispatch Q B (n := n) (.leaf (some (.error e)))
  | ok {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n : Nat} {b : β} {m : Mem} :
      Q b m B n → Turns R dispatch Q B (n := n) (.leaf (some (.ok (b, m))))
  | step {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n c : Nat} {op : SyncOp Tgt} {m : Mem}
      {k : op.Resp → Mem → CoN Tgt (β × Mem) n} :
      opCost op = some c → c ≤ B → (∀ r m', R m' → Turns R dispatch Q (B - c) (k r m')) →
      Turns R dispatch Q B (.sync op m k)
  | spawn {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n kk : Nat} {tgt : Tgt} {m : Mem}
      {k : Except ErrName ThreadId → Mem → CoN Tgt (β × Mem) n} :
      (∀ m' d, R m' → kk ≤ d →
        Turns R dispatch (fun (_ : Unit) _ _ _ => True) kk (dispatch tgt d m')) →
      kk + 2 ≤ B → (∀ r m', R m' → Turns R dispatch Q (B - (kk + 2)) (k r m')) →
      Turns R dispatch Q B (.sync (.spawn tgt) m k)

namespace Turns

variable {R R' : Mem → Prop} {dispatch : Tgt → ConcM Tgt Unit}

theorem mono {β : Type} {Q Q' : β → Mem → Nat → Nat → Prop} (hR : ∀ m, R' m → R m)
    (hq : ∀ b m B d, Q b m B d → Q' b m B d) {B n : Nat} {x : CoN Tgt (β × Mem) n}
    (h : Turns R dispatch Q B x) : Turns R' dispatch Q' B x := by
  induction h with
  | error => exact .error
  | ok hq' => exact .ok (hq _ _ _ _ hq')
  | step hc hle _ ih => exact .step hc hle fun r m' hr => ih r m' (hR m' hr) hq
  | spawn _ hle _ ihk ih =>
    exact .spawn (fun m' d hr hd => ihk m' d (hR m' hr) hd fun _ _ _ _ h => h) hle
      fun r m' hr => ih r m' (hR m' hr) hq

/-- Sequencing: the rest `f` of a result runs with the budget and the depth that are left. -/
theorem bind {β γ : Type} {Q₁ : β → Mem → Nat → Nat → Prop} {Q₂ : γ → Mem → Nat → Nat → Prop}
    {f : β → (k : Nat) → Mem → CoN Tgt (γ × Mem) k}
    (hf : ∀ b m B d, Q₁ b m B d → Turns R dispatch Q₂ B (f b d m)) {B n : Nat}
    {x : CoN Tgt (β × Mem) n} (h : Turns R dispatch Q₁ B x) :
    Turns R dispatch Q₂ B (x.bind fun (b, m) k => f b k m) := by
  induction h with
  | error => exact .error
  | ok hq => exact hf _ _ _ _ hq
  | step hc hle _ ih => exact .step hc hle fun r m' hr => ih r m' hr hf
  | spawn hk hle _ _ ih => exact .spawn hk hle fun r m' hr => ih r m' hr hf

theorem not_none {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n : Nat}
    (h : Turns R dispatch Q B (n := n) (.leaf none)) : False := by
  cases h

/-- A stop at an op other than a spawn within budget `B`. -/
theorem step_inv {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n : Nat} {op : SyncOp Tgt}
    {m : Mem} {k : op.Resp → Mem → CoN Tgt (β × Mem) n}
    (h : Turns R dispatch Q B (.sync op m k)) (hop : ∀ tgt, op ≠ .spawn tgt) :
    ∃ c, opCost op = some c ∧ c ≤ B ∧ ∀ r m', R m' → Turns R dispatch Q (B - c) (k r m') := by
  cases h with
  | step hc hle hk => exact ⟨_, hc, hle, hk⟩
  | spawn => exact absurd rfl (hop _)

/-- A stop at a spawn within budget `B`: the new thread's budget `kk` and the rest. -/
theorem spawn_inv {β : Type} {Q : β → Mem → Nat → Nat → Prop} {B n : Nat} {tgt : Tgt}
    {m : Mem} {k : Except ErrName ThreadId → Mem → CoN Tgt (β × Mem) n}
    (h : Turns R dispatch Q B (.sync (.spawn tgt) m k)) :
    ∃ kk, (∀ m' d, R m' → kk ≤ d →
        Turns R dispatch (fun (_ : Unit) _ _ _ => True) kk (dispatch tgt d m')) ∧
      kk + 2 ≤ B ∧ ∀ r m', R m' → Turns R dispatch Q (B - (kk + 2)) (k r m') := by
  cases h with
  | step hc => simp [opCost] at hc
  | spawn hkid hle hk => exact ⟨_, hkid, hle, hk⟩

end Turns

/-- From the memory `m`, every depth `n ≥ B` of `x` ends within budget `B`; a result leaves a
budget `B'` no larger than the depth that is left, with `Q` (see the module doc). -/
def Stops (R : Mem → Prop) (dispatch : Tgt → ConcM Tgt Unit) {α : Type} (x : ConcM Tgt α)
    (Q : α → Mem → Nat → Prop) (m : Mem) (B : Nat) : Prop :=
  ∀ n, B ≤ n → Turns R dispatch (fun a m' B' d => B' ≤ d ∧ Q a m' B') B (x n m)

namespace Stops

variable {R : Mem → Prop} {dispatch : Tgt → ConcM Tgt Unit} {α β σ : Type} {m : Mem} {B : Nat}
  {Q : α → Mem → Nat → Prop}

theorem mono {Q' : α → Mem → Nat → Prop} {x : ConcM Tgt α} (h : Stops R dispatch x Q m B)
    (hq : ∀ a m B, Q a m B → Q' a m B) : Stops R dispatch x Q' m B := fun n hn =>
  Turns.mono (fun _ h => h) (fun _ _ _ _ ⟨h1, h2⟩ => ⟨h1, hq _ _ _ h2⟩) (h n hn)

theorem pure' {a : α} (h : Q a m B) : Stops R dispatch (pure a : ConcM Tgt α) Q m B := fun n hn => by
  show Turns R dispatch _ B (n := n) (.leaf (some (.ok (a, m))))
  exact .ok ⟨hn, h⟩

theorem bind {x : ConcM Tgt α} {f : α → ConcM Tgt β} {Q : β → Mem → Nat → Prop}
    (h : Stops R dispatch x (fun a m' B' => Stops R dispatch (f a) Q m' B') m B) :
    Stops R dispatch (x >>= f) Q m B := fun n hn =>
  Turns.bind (f := fun a k m => f a k m) (fun _ _ _ d ⟨hd, hs⟩ => hs d hd) (h n hn)

theorem map {x : ConcM Tgt α} {g : α → β} {Q : β → Mem → Nat → Prop}
    (h : Stops R dispatch x (fun a m' B' => Q (g a) m' B') m B) : Stops R dispatch (g <$> x) Q m B := by
  rw [map_eq_pure_bind]
  exact bind (h.mono fun _ _ _ hq => pure' hq)

theorem discard' {x : ConcM Tgt α} {Q : PUnit → Mem → Nat → Prop}
    (h : Stops R dispatch x (fun _ m' B' => Q () m' B') m B) : Stops R dispatch (discard x) Q m B :=
  map h

theorem throw' (e : Error) : Stops R dispatch (throw e : ConcM Tgt α) Q m B := fun n _ => by
  show Turns R dispatch _ B (n := n) (.leaf (some (.error e)))
  exact .error

/-- A step in `MemM`: no stop. It must have a result (`MemM.Halts`). -/
theorem liftMem {x : MemM α} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q a m' B) :
    Stops R dispatch (ConcM.liftMem x : ConcM Tgt α) Q m B := by
  intro n hn
  show Turns R dispatch _ B (.leaf (x.run m))
  have hh := hx m
  unfold Result.Halts at hh
  match hr : (x.run m).run, hh with
  | some (.error e), _ =>
    rw [show x.run m = ExceptT.mk (some (.error e)) from hr]; exact .error
  | some (.ok (a, m')), _ =>
    rw [show x.run m = ExceptT.mk (some (.ok (a, m'))) from hr]
    exact .ok ⟨hn, h a m' hr⟩

theorem monadLift' {x : MemM α} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q a m' B) :
    Stops R dispatch (monadLift x : ConcM Tgt α) Q m B := liftMem hx h

/-- A sync op with a cost `c` within the budget: the thread goes on from every memory of the
rely, with `c` turns less. -/
theorem sync {op : SyncOp Tgt} {Q : op.Resp → Mem → Nat → Prop} {c : Nat}
    (hc : opCost op = some c) (hle : c ≤ B) (h : ∀ r m', R m' → Q r m' (B - c)) :
    Stops R dispatch (ConcM.sync op) Q m B := by
  intro n hn
  have h1 := opCost_pos hc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show Turns R dispatch _ B (.sync op m fun r m' => .leaf (some (.ok (r, m'))))
  exact .step hc hle fun r m' hr => .ok ⟨by omega, h r m' hr⟩

/-- `Thread.spawn` of `tgt` whose run keeps the budget `k` from every memory of the rely:
`k + 2` turns. -/
theorem spawn {tgt : Tgt} {k : Nat} {Q : Except ErrName ThreadId → Mem → Nat → Prop}
    (hkid : ∀ m', R m' → Stops R dispatch (dispatch tgt) (fun _ _ _ => True) m' k)
    (hle : k + 2 ≤ B) (h : ∀ r m', R m' → Q r m' (B - (k + 2))) :
    Stops R dispatch (ConcM.sync (.spawn tgt)) Q m B := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  show Turns R dispatch _ B (.sync (.spawn tgt) m fun r m' => .leaf (some (.ok (r, m'))))
  exact .spawn (fun m' d hr hd => Turns.mono (fun _ h => h) (fun _ _ _ _ _ => trivial)
    (hkid m' hr d hd)) hle
    fun r m' hr => .ok ⟨by omega, h r m' hr⟩

/-- A spin hint: one turn. -/
theorem spinLoopHint' {Q : Unit → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ m', R m' → Q () m' (B - 1)) : Stops R dispatch (Zig.spinLoopHint : ConcM Tgt Unit) Q m B :=
  sync rfl hle fun _ m' hr => h m' hr

/-- Fail closed: a futex wait has no turn budget, whatever the budget: its turns depend on
another thread's wake (a retry loop around it can starve). -/
theorem not_wait {p : Ptr} {e : BitVec 32} {Q : Unit → Mem → Nat → Prop} :
    ¬ Stops R dispatch (ConcM.sync (Tgt := Tgt) (.wait p e)) Q m B := by
  intro h
  obtain ⟨c, hc, -⟩ := Turns.step_inv (h (B + 1) (by omega)) (by intro _ h; cases h)
  simp [opCost] at hc

/-! ### The body monad of a concurrent function (`CM`) -/

theorem liftM' {x : MemM α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q (a, s) m' B) :
    Stops R dispatch ((liftM x : CM Tgt σ α).run s) Q m B := by
  show Stops R dispatch (ConcM.liftMem x >>= fun a => pure (a, s)) Q m B
  exact bind (liftMem hx fun a m' hr => pure' (h a m' hr))

theorem callMC' {x : MemM α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q (a, s) m' B) :
    Stops R dispatch ((callMC x : CM Tgt σ α).run s) Q m B := liftM' hx h

theorem callRC' {x : Result α} {s : σ} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a, x.run = some (.ok a) → Q (a, s) m B) :
    Stops R dispatch ((callRC x : CM Tgt σ α).run s) Q m B := by
  show Stops R dispatch (ConcM.liftMem (StateT.lift x) >>= fun a => pure (a, s)) Q m B
  refine bind (liftMem (MemM.Halts.lift' hx) fun a m' hr => pure' ?_)
  obtain ⟨ha, rfl⟩ := Proto.MemM.lift_ok hr
  exact h a ha

/-- A sync op of the body. -/
theorem liftSync {op : SyncOp Tgt} {s : σ} {Q : op.Resp × σ → Mem → Nat → Prop} {c : Nat}
    (hc : opCost op = some c) (hle : c ≤ B) (h : ∀ r m', R m' → Q (r, s) m' (B - c)) :
    Stops R dispatch ((StateT.lift (ConcM.sync op) : CM Tgt σ op.Resp).run s) Q m B := by
  show Stops R dispatch (ConcM.sync op >>= fun a => pure (a, s)) Q m B
  exact bind (sync hc hle fun r m' hr => pure' (h r m' hr))

theorem pickC' {count : Mem → Nat} {s : σ} {Q : Nat × σ → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ c m', R m' → Q (c, s) m' (B - 1)) :
    Stops R dispatch ((pickC count : CM Tgt σ Nat).run s) Q m B := liftSync rfl hle h

/-- `Thread.spawn` of a target with a budget `k` (`Stops.spawn`): `k + 2` turns. -/
theorem spawnC' {tgt : Tgt} {k : Nat} {s : σ} {Q : Except ErrName ThreadId × σ → Mem → Nat → Prop}
    (hkid : ∀ m', R m' → Stops R dispatch (dispatch tgt) (fun _ _ _ => True) m' k)
    (hle : k + 2 ≤ B) (h : ∀ r m', R m' → Q (r, s) m' (B - (k + 2))) :
    Stops R dispatch ((spawnC tgt : CM Tgt σ (Except ErrName ThreadId)).run s) Q m B := by
  show Stops R dispatch (ConcM.sync (.spawn tgt) >>= fun a => pure (a, s)) Q m B
  exact bind (spawn hkid hle fun r m' hr => pure' (h r m' hr))

theorem joinC' {tid : ThreadId} {s : σ} {Q : Unit × σ → Mem → Nat → Prop} (hle : 1 ≤ B)
    (h : ∀ m', R m' → Q ((), s) m' (B - 1)) :
    Stops R dispatch ((joinC tid : CM Tgt σ Unit).run s) Q m B := by
  show Stops R dispatch (((fun _ => ()) <$> ConcM.sync (Tgt := Tgt) (.join tid)) >>= fun a =>
    pure (a, s)) Q m B
  exact bind (map (sync rfl hle fun _ m' hr => pure' (h m' hr)))

/-! ### A body by its `run` (what `stops` walks) -/

section Run

variable {s : σ}

theorem runBind {x : CM Tgt σ α} {f : α → CM Tgt σ β} {Q : β × σ → Mem → Nat → Prop}
    (h : Stops R dispatch (x.run s) (fun p m' B' => Stops R dispatch ((f p.1).run p.2) Q m' B') m B) :
    Stops R dispatch ((x >>= f).run s) Q m B := by
  rw [StateT.run_bind]; exact bind h

theorem run' {x : CM Tgt σ α} (h : Stops R dispatch (x.run s) (fun p m' B' => Q p.1 m' B') m B) :
    Stops R dispatch (x.run' s) Q m B := by
  rw [StateT.run'_eq]; exact map h

theorem runPure {a : α} {Q : α × σ → Mem → Nat → Prop} (h : Q (a, s) m B) :
    Stops R dispatch ((pure a : CM Tgt σ α).run s) Q m B := by
  rw [StateT.run_pure]; exact pure' h

theorem runGet {Q : σ × σ → Mem → Nat → Prop} (h : Q (s, s) m B) :
    Stops R dispatch ((get : CM Tgt σ σ).run s) Q m B := by
  rw [StateT.run_get]; exact pure' h

theorem runSet {s' : σ} {Q : PUnit × σ → Mem → Nat → Prop} (h : Q (⟨⟩, s') m B) :
    Stops R dispatch ((set s' : CM Tgt σ PUnit).run s) Q m B := by
  rw [StateT.run_set]; exact pure' h

theorem runModify {g : σ → σ} {Q : PUnit × σ → Mem → Nat → Prop} (h : Q (⟨⟩, g s) m B) :
    Stops R dispatch ((modify g : CM Tgt σ PUnit).run s) Q m B := by
  rw [StateT.run_modify]; exact pure' h

theorem runThrow (e : Error) {Q : α × σ → Mem → Nat → Prop} :
    Stops R dispatch ((throw e : CM Tgt σ α).run s) Q m B := fun n _ => by
  show Turns R dispatch _ B (n := n) (.leaf (some (.error e)))
  exact .error

theorem runLift {x : ConcM Tgt α} {Q : α × σ → Mem → Nat → Prop}
    (h : Stops R dispatch x (fun a m' B' => Q (a, s) m' B') m B) :
    Stops R dispatch ((StateT.lift x : CM Tgt σ α).run s) Q m B := by
  rw [StateT.run_lift]; exact bind (h.mono fun _ _ _ hq => pure' hq)

theorem runMonadLift {x : MemM α} {Q : α × σ → Mem → Nat → Prop} (hx : x.Halts)
    (h : ∀ a m', (x.run m).run = some (.ok (a, m')) → Q (a, s) m' B) :
    Stops R dispatch ((monadLift x : CM Tgt σ α).run s) Q m B := liftM' hx h

end Run

open Lean Elab Tactic Meta in
/-- Introduce a binder of the goal as it is (no unfolding: `Stops` is itself a `∀`). -/
elab "intro_pi" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isForall do throwError "intro_pi: no binder"
  let (_, g') ← g.intro1
  replaceMainGoal [g']

open Lean Elab Tactic Meta in
/-- The budget of a spawned thread: a local hypothesis (a module's lemma about the target)
applied to the goal, its other premises by `assumption`. -/
elab "kid_budget" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      let s ← saveState
      try
        let (args, _, concl) ← forallMetaTelescope (← instantiateMVars ldecl.type)
        unless ← withAssignableSyntheticOpaque (isDefEq concl target) do throwError "no match"
        for a in args do
          let a := a.mvarId!
          unless ← a.isAssigned do a.assumption
        g.assign (mkAppN ldecl.toExpr args)
        replaceMainGoal []
        return
      catch _ => s.restore
    throwError "kid_budget: no local budget lemma applies"

open Lean Elab Tactic Meta in
/-- Run a tactic; fail if it left the goal unchanged. -/
elab "with_progress " t:tactic : tactic => do
  let g ← getMainGoal
  let before ← instantiateMVars (← g.getType)
  evalTactic t
  if let [g'] ← getGoals then
    if (← instantiateMVars (← g'.getType)) == before then throwError "with_progress: no progress"

/-- A leaf step of `stops`; extend with `macro_rules`. -/
syntax "stops_leaf" : tactic

macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible exact trivial)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible exact Stops.runThrow _)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible exact Stops.throw' _)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.runPure)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.runGet)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.runSet)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.runModify)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.pure')
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.callMC'); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.callRC'); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.runMonadLift); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.liftM'); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.monadLift'); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.liftMem); (focus halts; done))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.spawnC'); (focus intro_pi; intro_pi; kid_budget; done); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.joinC'); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.pickC'); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.spinLoopHint'); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.sync); (focus rfl); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| (with_reducible apply Stops.liftSync); (focus rfl); (focus omega))
macro_rules | `(tactic| stops_leaf) => `(tactic| with_reducible apply Stops.runLift)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicLoadC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicStoreC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicRmwC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicLoadAsC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicStoreAsC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicRmwAsC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgAsC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgWeakC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgWeakAsC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicLoadPtrC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicStorePtrC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.atomicXchgPtrC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgPtrC)
macro_rules | `(tactic| stops_leaf) => `(tactic| with_progress unfold Zig.cmpxchgWeakPtrC)

open Lean Elab Tactic Meta in
/-- Beta-reduce the head of the goal (a continuation applied to its arguments). -/
elab "head_beta" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' := t.headBeta
  if t == t' then throwError "head_beta: no redex"
  replaceMainGoal [← g.replaceTargetDefEq t']

/-- `stops`: walks a concurrent function with the `Stops` rules: sequencing, the body's `run`,
steps in `MemM` (with `halts`), sync ops within the budget (`omega`), branches (`split`). It
stops at a loop (`Stops.loop` needs the module's invariant and measure) and at a goal it cannot
close. -/
syntax "stops" : tactic

/-- One step of `stops`. -/
syntax "stops_step" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| stops) => do
    -- A work list, not `repeat`: a generated function takes thousands of steps.
    let mut todo ← getGoals
    let mut stuck : List MVarId := []
    while true do
      match todo with
      | [] => break
      | g :: rest =>
        if ← g.isAssigned then
          todo := rest
          continue
        setGoals [g]
        let ok ← try evalTactic (← `(tactic| stops_step)); pure true catch _ => pure false
        if ok then
          todo := (← getGoals) ++ rest
        else
          stuck := stuck ++ [g]
          todo := rest
    setGoals stuck

macro_rules
  | `(tactic| stops_step) => `(tactic| first
      | with_reducible apply Stops.runBind
      | with_reducible apply Stops.bind
      | with_reducible apply Stops.run'
      | with_reducible apply Stops.map
      | with_reducible apply Stops.discard'
      | stops_leaf
      | intro_pi
      | (head_beta; try dsimp only)
      | dsimp only
      | split
      | omega)

/-! ### Loops -/

/-- A loop (`Zig.loop`) whose repeats make the measure `meas` smaller, with the invariant `inv`
on the locals, the memory and the budget. -/
theorem loop {ε : Type} (body : CM Tgt σ ε) (again : ε → Bool) (inv : σ → Mem → Nat → Prop)
    (meas : σ → Nat) (post : ε × σ → Mem → Nat → Prop)
    (step : ∀ s m B, inv s m B → Stops R dispatch (body.run s) (fun r m' B' =>
      if again r.1 then inv r.2 m' B' ∧ meas r.2 < meas s else post r m' B') m B) :
    ∀ s m B, inv s m B → Stops R dispatch ((Zig.loop body again).run s) post m B := by
  intro s
  induction hk : meas s using Nat.strongRecOn generalizing s with
  | _ k ih =>
  intro m B hi
  rw [Zig.loop.eq_1, StateT.run_bind]
  refine bind ((step s m B hi).mono ?_)
  rintro ⟨e, s'⟩ m' B' hq
  cases ha : again e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hq ⊢
    exact pure' hq
  · simp only [ha, ↓reduceIte] at hq ⊢
    exact ih (meas s') (hk ▸ hq.2) s' rfl m' B' hq.1

end Stops

end Conc
end Zig
