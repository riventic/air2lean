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
    (step : ∀ s m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s h → m.Seq →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
        m'.heap = h' ∪ hF ∧ m'.Seq ∧
        (if again e then I s' h' ∧ meas s' < meas s else post e s' h')) :
    ∀ s m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s h → m.Seq →
      ∃ e s' m' h', ((loop body again).run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ post e s' h' ∧ m'.Seq := by
  intro s m h hd hm hi hst
  have := loopMM_spec body again
    (fun s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ I s h ∧ m.Seq) meas
    (fun e s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ post e s h ∧ m.Seq)
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
    (step : ∀ s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.Seq →
      ∃ e s' m' h', (body.run s).run m = pure ((e, s'), m') ∧ Heap.Disjoint h' hF ∧
        m'.heap = h' ∪ hF ∧ m'.Seq ∧
        (if again e then ∃ n' < n, I s' n' h' else post e s' h')) :
    ∀ s n m h, Heap.Disjoint h hF → m.heap = h ∪ hF → I s n h → m.Seq →
      ∃ e s' m' h', ((loop body again).run s).run m = pure ((e, s'), m') ∧
        Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ post e s' h' ∧ m'.Seq := by
  intro s n m h hd hm hi hst
  have := loopMM_ghost body again
    (fun s m n => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ I s n h ∧ m.Seq)
    (fun e s m => ∃ h, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧ post e s h ∧ m.Seq)
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

/-- Partial correctness of a loop over memory: when every successful body run from the invariant
re-establishes it, or `post` on the exit, every successful run of the loop ends in `post`. No
measure and no successful step are needed: a body that fails or does not return makes the loop
fail or not return, which the statement does not constrain. By fixpoint induction (`Zig.loop`
is a `partial_fixpoint`); used where a step can fail, for example through a callback contract
that allows any error (E02, `tests/roadmap/callbacks`). -/
theorem loopMM_partial {σ ε : Type} (body : MM σ ε) (again : ε → Bool) (inv : σ → Mem → Prop)
    (post : ε → σ → Mem → Prop)
    (step : ∀ s m, inv s m → ∀ e s' m', (body.run s).run m = pure ((e, s'), m') →
      if again e then inv s' m' else post e s' m') :
    ∀ s m, inv s m → ∀ e s' m', ((loop body again).run s).run m = pure ((e, s'), m') →
      post e s' m' := by
  refine loop.fixpoint_induct body again (motive := fun v => ∀ s m, inv s m → ∀ e s' m',
    (v.run s).run m = pure ((e, s'), m') → post e s' m') ?_ ?_
  · apply Lean.Order.admissible_pi_apply (P := fun s v => ∀ m, inv s m → ∀ e s' m',
      (StateT.run v m) = pure ((e, s'), m') → post e s' m')
    intro s
    apply Lean.Order.admissible_pi_apply (P := fun m v => inv s m → ∀ e s' m',
      v = pure ((e, s'), m') → post e s' m')
    intro m
    apply Lean.Order.admissible_pi
    intro _
    apply Lean.Order.admissible_pi
    intro e
    apply Lean.Order.admissible_pi
    intro s'
    apply Lean.Order.admissible_pi
    intro m'
    exact Lean.Order.Option.admissible_eq_some _ _
  · intro v ih s m hs e s' m' hrun
    have unfold : (((do let e ← body; if again e then v else pure e : MM σ ε).run s).run m) =
        ((body.run s).run m >>= fun r =>
          if again r.1.1 then (v.run r.1.2).run r.2 else pure r) := by
      simp only [StateT.run, bind, StateT.bind]
      congr 1
      funext r
      rcases r with ⟨⟨e, s'⟩, m'⟩
      cases again e <;> rfl
    rw [unfold] at hrun
    generalize hb : (body.run s).run m = rb at hrun
    match rb, hb, hrun with
    | .mk none, _, hrun => simp [bind, ExceptT.bind, ExceptT.mk] at hrun; cases hrun
    | .mk (some (.error _)), _, hrun =>
      simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at hrun; cases hrun
    | .mk (some (.ok ((e₁, s₁), m₁))), hb, hrun =>
      have hstep := step s m hs e₁ s₁ m₁ hb
      have hrun : (if again e₁ = true then (v.run s₁).run m₁ else pure ((e₁, s₁), m₁)) =
          pure ((e, s'), m') := hrun
      cases ha : again e₁
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hstep hrun
        have hr : some (Except.ok ((e₁, s₁), m₁)) = some (Except.ok ((e, s'), m')) := hrun
        simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
        exact hstep
      · simp only [ha, ↓reduceIte] at hstep hrun
        exact ih s₁ m₁ hstep e s' m' hrun

/-! ### Inverting a successful run of a body over memory

What a successful run of `x >>= f`, `get`, `modify` or a lifted `MemM` call in `MM` did: the
steps of a partial-correctness proof (`loopMM_partial`) walk a generated body with them. -/

namespace MM

variable {σ α β : Type}

theorem run_bind_ok {x : MM σ α} {f : α → MM σ β} {s s'' : σ} {m m'' : Mem} {r : β}
    (h : (((x >>= f).run s).run m) = pure ((r, s''), m'')) :
    ∃ a s' m', ((x.run s).run m) = pure ((a, s'), m') ∧
      (((f a).run s').run m') = pure ((r, s''), m'') := by
  simp only [StateT.run_bind] at h
  generalize hx : (x.run s).run m = rx at h
  match rx, hx, h with
  | .mk none, _, h => simp [bind, ExceptT.bind, ExceptT.mk] at h; cases h
  | .mk (some (.error _)), _, h =>
    simp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] at h; cases h
  | .mk (some (.ok ((a, s'), m'))), _, h =>
    exact ⟨a, s', m', rfl, by simpa [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] using h⟩

theorem run_pure_ok {a r : α} {s s' : σ} {m m' : Mem}
    (h : (((pure a : MM σ α).run s).run m) = pure ((r, s'), m')) : r = a ∧ s' = s ∧ m' = m := by
  have h : some (Except.ok ((a, s), m)) = some (Except.ok ((r, s'), m')) := h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm, h.2.symm⟩

theorem run_callM_ok {x : MemM α} {a : α} {s s' : σ} {m m' : Mem}
    (h : (((callM x : MM σ α).run s).run m) = pure ((a, s'), m')) :
    s' = s ∧ x.run m = pure (a, m') := by
  simp only [callM, StateT.run_lift] at h
  rw [StateT.run_bind] at h
  generalize hx : x.run m = rx at h
  match rx, hx, h with
  | .mk none, _, h => cases h
  | .mk (some (.error _)), _, h => cases h
  | .mk (some (.ok (a', m₁))), hx, h =>
    have h : some (Except.ok ((a', s), m₁)) = some (Except.ok ((a, s'), m')) := h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem run_get_ok {a s s' : σ} {m m' : Mem}
    (h : (((get : MM σ σ).run s).run m) = pure ((a, s'), m')) : a = s ∧ s' = s ∧ m' = m := by
  have h : some (Except.ok ((s, s), m)) = some (Except.ok ((a, s'), m')) := h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm, h.2.symm⟩

theorem run_modify_ok {f : σ → σ} {s s' : σ} {m m' : Mem} {u : PUnit}
    (h : (((modify f : MM σ PUnit).run s).run m) = pure ((u, s'), m')) : s' = f s ∧ m' = m := by
  have h : some (Except.ok ((PUnit.unit, f s), m)) = some (Except.ok ((u, s'), m')) := h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.2.symm, h.2.symm⟩

/-- A lifted pure computation (`Zig.Result`, for example an overflow-checked add) leaves the
locals and the memory alone. -/
theorem run_liftR_ok {r : Result α} {a : α} {s s' : σ} {m m' : Mem}
    (h : (((liftM r : MM σ α).run s).run m) = pure ((a, s'), m')) :
    r = pure a ∧ s' = s ∧ m' = m := by
  match hr : r, h with
  | .mk none, h => cases h
  | .mk (some (.error _)), h => cases h
  | .mk (some (.ok a')), h =>
    have h : some (Except.ok ((a', s), m)) = some (Except.ok ((a, s'), m')) := h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- A function body is `body.run' locals`: a successful run had some final locals. -/
theorem run'_ok {x : MM σ α} {s : σ} {a : α} {m m' : Mem}
    (h : (x.run' s).run m = pure (a, m')) : ∃ s', ((x.run s).run m) = pure ((a, s'), m') := by
  simp only [StateT.run'_eq, StateT.run_map] at h
  generalize hx : (x.run s).run m = rx at h
  match rx, hx, h with
  | .mk none, _, h => cases h
  | .mk (some (.error _)), _, h => cases h
  | .mk (some (.ok ((a', s'), m₁))), _, h =>
    have h : some (Except.ok (a', m₁)) = some (Except.ok (a, m')) := h
    simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s', rfl⟩

theorem run_lift_ok {x : MemM α} {a : α} {s s' : σ} {m m' : Mem}
    (h : (((StateT.lift x : MM σ α).run s).run m) = pure ((a, s'), m')) :
    s' = s ∧ x.run m = pure (a, m') :=
  run_callM_ok (x := x) h

end MM

end Zig
