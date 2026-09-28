import ZigLean.Sep.Triple

/-!
# Loops over memory

`loopMM_spec` is `Zig.loop_spec` (`ZigLean/Loop.lean`) for a loop body that uses memory: the
invariant is on the locals and the memory. `loop_sep_spec` states the invariant as an assertion
on the part of the memory that the loop owns; the rest (the frame `hF`) is unchanged. The
`_ghost` forms take the measure from the invariant, not from the locals: a walk over a list ends
because the rest of the list gets shorter.
-/

namespace Zig

open Assn

theorem loopMM_run {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (s : σ) (m : Mem) :
    ((loop body again).run s).run m =
      (do
        let ((e, s'), m') ← (body.run s).run m
        if again e then ((loop body again).run s').run m' else pure ((e, s'), m')) := by
  conv => lhs; rw [loop]
  simp only [StateT.run, bind, StateT.bind]
  congr 1
  funext r
  rcases r with ⟨⟨e, s'⟩, m'⟩
  cases again e <;> rfl

theorem loopMM_spec {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (inv : σ → Mem → Prop)
    (meas : σ → Nat) (post : ε → σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then inv s' m' ∧ meas s' < meas s else post e s' m')) :
    ∀ s m, inv s m → ∃ e s' m', ((loop body again).run s).run m = pure ((e, s'), m') ∧
      post e s' m' := by
  intro s
  induction h : meas s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    intro m hs
    obtain ⟨e, s', m', hrun, hnext⟩ := step s m hs
    rw [loopMM_run]
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hnext
      refine ⟨e, s', m', ?_, hnext⟩
      simp [hrun, ha, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]
    · simp only [ha, ↓reduceIte] at hnext
      obtain ⟨hinv, hlt⟩ := hnext
      obtain ⟨e₂, s₂, m₂, hr, hpost⟩ := ih (meas s') (h ▸ hlt) s' rfl m' hinv
      refine ⟨e₂, s₂, m₂, ?_, hpost⟩
      simp [hrun, ha, hr, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]

/-- `loopMM_spec` with the measure in the invariant: a number that each repeat makes smaller (the
length of the rest of a list, which the locals alone do not give). -/
theorem loopMM_ghost {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (inv : σ → Mem → Nat → Prop)
    (post : ε → σ → Mem → Prop)
    (step : ∀ s m n, inv s m n → ∃ e s' m', (body.run s).run m = pure ((e, s'), m') ∧
      (if again e then ∃ n' < n, inv s' m' n' else post e s' m')) :
    ∀ s m n, inv s m n → ∃ e s' m', ((loop body again).run s).run m = pure ((e, s'), m') ∧
      post e s' m' := by
  intro s m n
  induction n using Nat.strongRecOn generalizing s m with
  | _ n ih =>
    intro hs
    obtain ⟨e, s', m', hrun, hnext⟩ := step s m n hs
    rw [loopMM_run]
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hnext
      refine ⟨e, s', m', ?_, hnext⟩
      simp [hrun, ha, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]
    · simp only [ha, ↓reduceIte] at hnext
      obtain ⟨n', hlt, hinv⟩ := hnext
      obtain ⟨e₂, s₂, m₂, hr, hpost⟩ := ih n' hlt s' m' hinv
      refine ⟨e₂, s₂, m₂, ?_, hpost⟩
      simp [hrun, ha, hr, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure]

/-- A loop with the invariant `I s`, an assertion on the part of the memory that the loop owns.
The frame `hF` stays unchanged. -/
theorem loop_sep_spec {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (I : σ → Assn)
    (meas : σ → Nat) (post : ε → σ → Assn) (hF : Heap)
    (step : ∀ s m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s h → m.SingleThread →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
        m'.heap = h' ∪ hF ∧ m'.SingleThread ∧
        (if again e then I s' h' ∧ meas s' < meas s else post e s' h')) :
    ∀ s m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s h → m.SingleThread →
      ∃ e s' m' h', ((loop body again).run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ post e s' h' ∧ m'.SingleThread := by
  intro s m h hd hm hi hst
  have := loopMM_spec body again
    (fun s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ I s h ∧ m.SingleThread) meas
    (fun e s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ post e s h ∧ m.SingleThread)
    (fun s m ⟨h, hd, hm, hi, hst⟩ => by
      obtain ⟨e, s', m', h', hr, hd', hm', hst', hn⟩ := step s m h hd hm hi hst
      refine ⟨e, s', m', hr, ?_⟩
      split
      · rename_i ha; simp only [ha, ↓reduceIte] at hn; exact ⟨⟨h', hd', hm', hn.1, hst'⟩, hn.2⟩
      · rename_i ha; simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn
        exact ⟨h', hd', hm', hn, hst'⟩)
    s m ⟨h, hd, hm, hi, hst⟩
  obtain ⟨e, s', m', hr, h', hd', hm', hp, hst'⟩ := this
  exact ⟨e, s', m', h', hr, hd', hm', hp, hst'⟩

/-- `loop_sep_spec` with the measure in the invariant (`loopMM_ghost`). -/
theorem loop_sep_ghost {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (I : σ → Nat → Assn)
    (post : ε → σ → Assn) (hF : Heap)
    (step : ∀ s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.SingleThread →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
        m'.heap = h' ∪ hF ∧ m'.SingleThread ∧
        (if again e then ∃ n' < n, I s' n' h' else post e s' h')) :
    ∀ s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.SingleThread →
      ∃ e s' m' h', ((loop body again).run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ post e s' h' ∧ m'.SingleThread := by
  intro s n m h hd hm hi hst
  have := loopMM_ghost body again
    (fun s m n => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ I s n h ∧ m.SingleThread)
    (fun e s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ post e s h ∧ m.SingleThread)
    (fun s m n ⟨h, hd, hm, hi, hst⟩ => by
      obtain ⟨e, s', m', h', hr, hd', hm', hst', hn⟩ := step s n m h hd hm hi hst
      refine ⟨e, s', m', hr, ?_⟩
      split
      · rename_i ha; simp only [ha, ↓reduceIte] at hn
        obtain ⟨n', hlt, hi'⟩ := hn; exact ⟨n', hlt, h', hd', hm', hi', hst'⟩
      · rename_i ha; simp only [ha, Bool.false_eq_true, ↓reduceIte] at hn
        exact ⟨h', hd', hm', hn, hst'⟩)
    s m n ⟨h, hd, hm, hi, hst⟩
  obtain ⟨e, s', m', hr, h', hd', hm', hp, hst'⟩ := this
  exact ⟨e, s', m', h', hr, hd', hm', hp, hst'⟩

end Zig
