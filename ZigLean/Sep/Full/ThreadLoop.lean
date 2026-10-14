import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Thread

/-!
# Loops in a thread (`FTTriple`, `FTTotalTriple`)

The loop rules of `ZigLean/Sep/Full/Loop.lean` for a thread's step: the same obligation (one run
of the body from the invariant repeats with it, or exits with `post`), stated and proved with the
thread triples. A loop of a thread is a rule for `fsym` in a thread logic (or a call) as a
sequential loop rule is in the sequential logics; its body's steps are walked by `fsym` as a
thread's steps, so each body run is local to the thread by the rules it uses.

A sequential loop rule does not give a thread's loop through `ofSeq`: its `ThreadLocal` side goal
is about the rule's precondition, while each run of the body is local only under the invariant at
that run, which the locality goal does not carry. The thread rules here take the invariant, and a
total thread loop rule is a sequential one too (`FTTotalTriple.toFTotalTriple`).

* `FTTotalTriple.loop_ghost`, `loop_ghost_ex`, `loop_measure`: total correctness (ghost measure,
  measure on the locals).
* `FTTriple.loop`: partial correctness by fixpoint induction (`FTTriple.admissible_run`).
-/

namespace Zig
namespace Full

open FAssn Lean.Order

variable {α σ ε : Type}

/-! ## Partial correctness -/

/-- `FTTriple P · Q` is admissible (`FTriple.admissible` for a thread's step). -/
theorem FTTriple.admissible {P : FAssn} {Q : α → FAssn} :
    Lean.Order.admissible (fun c : MemM α => FTTriple P c Q) :=
  admissible_pi_apply (β := fun _ : Mem => Result (α × Mem))
    (fun m o => ∀ r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
      match o.run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m')
    fun _ => by
      change Lean.Order.admissible fun x : FlatOrder none => _
      exact admissible_flatOrder _ fun _ _ _ _ _ _ => trivial

/-- The same over functions of the locals (`MM`). -/
theorem FTTriple.admissible_run {P : σ → FAssn} {Q : σ → ε × σ → FAssn} :
    Lean.Order.admissible (fun x : MM σ ε => ∀ s, FTTriple (P s) (x.run s) (Q s)) :=
  admissible_pi_apply (β := fun _ => MemM (ε × σ)) (fun s x => FTTriple (P s) x (Q s))
    fun _ => FTTriple.admissible

/-- **A thread's loop with an invariant** (partial correctness, `FTriple.loop`). -/
theorem FTTriple.loop {body : MM σ ε} {again : ε → Bool} (inv : σ → FAssn) (post : ε × σ → FAssn)
    (step : ∀ s, FTTriple (inv s) (body.run s) (fun r => if again r.1 then inv r.2 else post r)) :
    ∀ s, FTTriple (inv s) ((Zig.loop body again).run s) post := by
  refine Zig.loop.fixpoint_induct body again (fun l => ∀ s, FTTriple (inv s) (l.run s) post)
    FTTriple.admissible_run ?_
  intro l hl s
  rw [StateT.run_bind]
  refine FTTriple.bind (step s) fun ⟨e, s'⟩ => ?_
  cases h : again e
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    exact FTTriple.ret' _ fun _ x => x
  · simp only [↓reduceIte]
    exact hl s'

/-! ## Total correctness -/

/-- **A thread's loop with an invariant and a ghost measure** (`FTotalTriple.loop_ghost`). -/
theorem FTTotalTriple.loop_ghost {body : MM σ ε} {again : ε → Bool} (inv : σ → Nat → FAssn)
    (post : ε × σ → FAssn)
    (step : ∀ s n, FTTotalTriple (inv s n) (body.run s) (floopNext again inv post n)) :
    ∀ s n, FTTotalTriple (inv s n) ((Zig.loop body again).run s) post := by
  intro s n
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    rw [loop_run]
    refine FTTotalTriple.bind (step s n) fun ⟨e, s'⟩ => ?_
    cases h : again e
    · simp only [floopNext, h, Bool.false_eq_true, ↓reduceIte]
      exact FTTotalTriple.ret _
    · simp only [floopNext, h, ↓reduceIte]
      exact FTTotalTriple.ex fun n' => FTTotalTriple.lift fun hlt => ih n' hlt s'

/-- The loop from the invariant at some measure. -/
theorem FTTotalTriple.loop_ghost_ex {body : MM σ ε} {again : ε → Bool} (inv : σ → Nat → FAssn)
    (post : ε × σ → FAssn)
    (step : ∀ s n, FTTotalTriple (inv s n) (body.run s) (floopNext again inv post n)) (s : σ) :
    FTTotalTriple (FAssn.ex (inv s)) ((Zig.loop body again).run s) post :=
  FTTotalTriple.ex fun n => FTTotalTriple.loop_ghost inv post step s n

/-- **A thread's loop with an invariant and a measure on the locals**
(`FTotalTriple.loop_measure`). -/
theorem FTTotalTriple.loop_measure {body : MM σ ε} {again : ε → Bool} (I : σ → FAssn)
    (μ : σ → Nat) (post : ε × σ → FAssn)
    (step : ∀ s, FTTotalTriple (I s) (body.run s)
      (fun r => if again r.1 then ⟪μ r.2 < μ s⟫ ⋆ I r.2 else post r)) :
    ∀ s, FTTotalTriple (I s) ((Zig.loop body again).run s) post := by
  intro s
  have h := FTTotalTriple.loop_ghost (again := again) (fun s n => ⟪n = μ s⟫ ⋆ I s) post
    (fun s n => FTTotalTriple.lift fun hn => (step s).conseq (fun _ h => h) fun r x hx => by
      obtain ⟨e, s'⟩ := r
      cases ha : again e
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hx; exact floopNext_exit ha hx
      · simp only [ha, ↓reduceIte] at hx
        obtain ⟨hlt, hi⟩ := sep_lift.mp hx
        exact floopNext_repeat ha (n' := μ s') (by omega) (sep_lift.mpr ⟨rfl, hi⟩)) s (μ s)
  exact h.conseq (fun r hr => sep_lift.mpr ⟨rfl, hr⟩) fun _ _ h => h

end Full
end Zig
