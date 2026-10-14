import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Thread

/-!
# Loops in the full-state logic (`docs/one-logic.md`, library `Full/Loop`)

A generated loop is `Zig.loop body again` over the function's locals (`MM σ ε`). One obligation
proves it: from the invariant `inv s n`, one run of the body either repeats with the invariant at a
smaller ghost measure `n' < n`, or exits with `post` (`floopNext`). The measure lives in the
invariant, so it can count what the locals alone do not give (the rest of a list, the free slots
of a buffer); a measure on the locals is `FTotalTriple.loop_measure`.

* `FTotalTriple.loop_ghost`: total correctness, by strong induction on the measure.
* `FTotalTriple.loop_dispatch`: a dispatch loop (labelled `switch`, `continue :sw`): the invariant
  indexed by the selector's state, the measure `B * data + rank` (lexicographic for ranks below `B`).
* `FTriple.loop`: partial correctness without a measure, by fixpoint induction
  (`FTriple.admissible`, `FTriple.admissible_run`).
* `FTriple.admissible_fun` is the same for the members of a recursive group (`partial_fixpoint`):
  the partial recursion rule.
* `FTTriple.loop`: the partial rule for a thread's step (`FTTriple`), by the same fixpoint
  induction (`FTTriple.admissible`): a loop of a thread is local when each run of its body is.

Each is a rule, not a template or tactic (docs/proof-framework.md): it takes the body's step as a
triple, which a client proves with `fsym`, and never mentions the frame. They replace the legacy
`ZigLean/Sep/Loop.lean` and its loop templates (deleted).
-/

namespace Zig
namespace Full

open FAssn Lean.Order

variable {α σ ε : Type}

/-! ## Unfolding a loop -/

theorem loop_run (body : MM σ ε) (again : ε → Bool) (s : σ) :
    (Zig.loop body again).run s = body.run s >>= fun r =>
      if again r.1 then (Zig.loop body again).run r.2 else pure r := by
  conv => lhs; rw [Zig.loop]
  rw [StateT.run_bind]
  congr 1; funext r; obtain ⟨e, s'⟩ := r
  cases again e <;> rfl

/-! ## Partial correctness: fixpoint induction -/

/-- `FTriple P · Q` is admissible: a property of a program's run that holds when it has no
result is kept by least upper bounds (fixpoint induction, `partial_fixpoint`). -/
theorem FTriple.admissible {P : FAssn} {Q : α → FAssn} :
    Lean.Order.admissible (fun c : MemM α => FTriple P c Q) :=
  admissible_pi_apply (β := fun _ : Mem => Result (α × Mem))
    (fun m o => ∀ r rF, Holds m r rF → P r → m.FSeq →
      match o.run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq)
    fun _ => by
      change Lean.Order.admissible fun x : FlatOrder none => _
      exact admissible_flatOrder _ fun _ _ _ _ _ => trivial

/-- The same over functions of the locals (`MM`, the body monad of a generated function). -/
theorem FTriple.admissible_run {P : σ → FAssn} {Q : σ → ε × σ → FAssn} :
    Lean.Order.admissible (fun x : MM σ ε => ∀ s, FTriple (P s) (x.run s) (Q s)) :=
  admissible_pi_apply (β := fun _ => MemM (ε × σ)) (fun s x => FTriple (P s) x (Q s))
    fun _ => FTriple.admissible

/-- The same for a function of arguments (a member of a `partial_fixpoint` group): the
recursion rule of partial correctness. -/
theorem FTriple.admissible_fun {A : Type} {P : A → FAssn} {Q : A → α → FAssn} :
    Lean.Order.admissible (fun f : A → MemM α => ∀ a, FTriple (P a) (f a) (Q a)) :=
  admissible_pi_apply (β := fun _ => MemM α) (fun a x => FTriple (P a) x (Q a))
    fun _ => FTriple.admissible

/-- **A loop with an invariant** (partial correctness): if one run of the body from the invariant
returns to it when it repeats and establishes `post` when it exits, the loop does. No measure: a
loop that never exits has no result, which partial correctness allows. -/
theorem FTriple.loop {body : MM σ ε} {again : ε → Bool} (inv : σ → FAssn) (post : ε × σ → FAssn)
    (step : ∀ s, FTriple (inv s) (body.run s) (fun r => if again r.1 then inv r.2 else post r)) :
    ∀ s, FTriple (inv s) ((Zig.loop body again).run s) post := by
  refine Zig.loop.fixpoint_induct body again (fun l => ∀ s, FTriple (inv s) (l.run s) post)
    FTriple.admissible_run ?_
  intro l hl s
  rw [StateT.run_bind]
  refine FTriple.bind (step s) fun ⟨e, s'⟩ => ?_
  cases h : again e
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    exact FTriple.ret' _ fun _ x => x
  · simp only [↓reduceIte]
    exact hl s'

/-! ## A thread's loops: fixpoint induction -/

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

theorem FTTriple.admissible_run {P : σ → FAssn} {Q : σ → ε × σ → FAssn} :
    Lean.Order.admissible (fun x : MM σ ε => ∀ s, FTTriple (P s) (x.run s) (Q s)) :=
  admissible_pi_apply (β := fun _ => MemM (ε × σ)) (fun s x => FTTriple (P s) x (Q s))
    fun _ => FTTriple.admissible

/-- **A thread's loop with an invariant** (partial correctness, `FTriple.loop` for `FTTriple`). -/
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

/-! ## Total correctness: a ghost measure -/

/-- The assertion after one body run: repeat with the invariant at a smaller measure, or exit. -/
def floopNext (again : ε → Bool) (inv : σ → Nat → FAssn) (post : ε × σ → FAssn) (n : Nat)
    (r : ε × σ) : FAssn :=
  if again r.1 then FAssn.ex fun n' => ⟪n' < n⟫ ⋆ inv r.2 n' else post r

theorem floopNext_repeat {again : ε → Bool} {inv : σ → Nat → FAssn} {post : ε × σ → FAssn}
    {n n' : Nat} {e : ε} {s : σ} {r : Res} (ha : again e = true) (hlt : n' < n) (hi : inv s n' r) :
    floopNext again inv post n (e, s) r := by
  simp only [floopNext, ha, ↓reduceIte]
  exact ⟨n', sep_lift.mpr ⟨hlt, hi⟩⟩

theorem floopNext_exit {again : ε → Bool} {inv : σ → Nat → FAssn} {post : ε × σ → FAssn}
    {n : Nat} {e : ε} {s : σ} {r : Res} (ha : again e = false) (hp : post (e, s) r) :
    floopNext again inv post n (e, s) r := by
  simpa only [floopNext, ha, Bool.false_eq_true, ↓reduceIte] using hp

/-- **A loop with an invariant and a ghost measure** (total correctness): one run of the body
from `inv s n` repeats with `inv s' n'` for some `n' < n`, or exits with `post`. -/
theorem FTotalTriple.loop_ghost {body : MM σ ε} {again : ε → Bool} (inv : σ → Nat → FAssn)
    (post : ε × σ → FAssn)
    (step : ∀ s n, FTotalTriple (inv s n) (body.run s) (floopNext again inv post n)) :
    ∀ s n, FTotalTriple (inv s n) ((Zig.loop body again).run s) post := by
  intro s n
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    rw [loop_run]
    refine FTotalTriple.bind (step s n) fun ⟨e, s'⟩ => ?_
    cases h : again e
    · simp only [floopNext, h, Bool.false_eq_true, ↓reduceIte]
      exact FTotalTriple.ret _
    · simp only [floopNext, h, ↓reduceIte]
      exact FTotalTriple.ex fun n' => FTotalTriple.lift fun hlt => ih n' hlt s'

/-- The loop from the invariant at some measure. -/
theorem FTotalTriple.loop_ghost_ex {body : MM σ ε} {again : ε → Bool} (inv : σ → Nat → FAssn)
    (post : ε × σ → FAssn)
    (step : ∀ s n, FTotalTriple (inv s n) (body.run s) (floopNext again inv post n)) (s : σ) :
    FTotalTriple (FAssn.ex (inv s)) ((Zig.loop body again).run s) post :=
  FTotalTriple.ex fun n => FTotalTriple.loop_ghost inv post step s n

/-- **A loop with an invariant and a measure on the locals** (total correctness): one run of the
body from `I s` repeats with `I s'` and `μ s' < μ s`, or exits with `post`. -/
theorem FTotalTriple.loop_measure {body : MM σ ε} {again : ε → Bool} (I : σ → FAssn) (μ : σ → Nat)
    (post : ε × σ → FAssn)
    (step : ∀ s, FTotalTriple (I s) (body.run s)
      (fun r => if again r.1 then ⟪μ r.2 < μ s⟫ ⋆ I r.2 else post r)) :
    ∀ s, FTotalTriple (I s) ((Zig.loop body again).run s) post := by
  intro s
  have h := FTotalTriple.loop_ghost (again := again) (fun s n => ⟪n = μ s⟫ ⋆ I s) post
    (fun s n => FTotalTriple.lift fun hn => (step s).post fun r x hx => by
      obtain ⟨e, s'⟩ := r
      cases ha : again e
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hx; exact floopNext_exit ha hx
      · simp only [ha, ↓reduceIte] at hx
        obtain ⟨hlt, hi⟩ := sep_lift.mp hx
        exact floopNext_repeat ha (n' := μ s') (by omega) (sep_lift.mpr ⟨rfl, hi⟩)) s (μ s)
  exact h.pre fun r hr => sep_lift.mpr ⟨rfl, hr⟩

/-- **A dispatch loop** (a labelled `switch` whose prongs `continue :sw`; the selector is the
locals field `dispatchValueN`, read by `sel`), total correctness: the invariant is indexed by the
selector's state, and the measure combines the consumed data and the state's rank as
`B * data + rank`, which is the lexicographic order of (data, rank) when every rank is below `B`.
One run of the body from `inv (sel s) s` repeats with `inv (sel s') s'` at a smaller measure (less
data, or the same data and a lower-ranked state), or exits with `post`. The measure is one
number, so `fsym` decides the step's measure goal by arithmetic. -/
theorem FTotalTriple.loop_dispatch {κ : Type} {body : MM σ ε} {again : ε → Bool} (sel : σ → κ)
    (inv : κ → σ → FAssn) (data : σ → Nat) (rank : κ → Nat) (B : Nat) (post : ε × σ → FAssn)
    (step : ∀ s, FTotalTriple (inv (sel s) s) (body.run s)
      (fun r => if again r.1 then
          ⟪B * data r.2 + rank (sel r.2) < B * data s + rank (sel s)⟫ ⋆ inv (sel r.2) r.2
        else post r)) :
    ∀ s, FTotalTriple (inv (sel s) s) ((Zig.loop body again).run s) post :=
  FTotalTriple.loop_measure (fun s => inv (sel s) s) (fun s => B * data s + rank (sel s)) post step

end Full
end Zig
