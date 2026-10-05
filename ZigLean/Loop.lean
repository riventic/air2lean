import ZigLean.Basic

/-!
# Reasoning about `Zig.loop`

`loop_spec` turns a loop proof into one proof about a single iteration: an invariant `inv`,
a measure `m` that each repeating iteration makes smaller, and a post-condition `post` on the
exit that ends the loop.
-/

namespace Zig

theorem loop_run {σ ε : Type} (body : M σ ε) (again : ε → Bool) (s : σ) :
    (loop body again).run s =
      (do let (e, s') ← body.run s
          if again e then (loop body again).run s' else pure (e, s')) := by
  conv => lhs; rw [loop]
  simp only [StateT.run, bind, StateT.bind]
  congr 1
  funext p
  rcases p with ⟨e, s'⟩
  cases again e <;> rfl

theorem loop_spec {σ ε : Type} (body : M σ ε) (again : ε → Bool)
    (inv : σ → Prop) (m : σ → Nat) (post : ε × σ → Prop)
    (step : ∀ s, inv s → ∃ e s', body.run s = pure (e, s') ∧
      (if again e then inv s' ∧ m s' < m s else post (e, s'))) :
    ∀ s, inv s → ∃ r, (loop body again).run s = pure r ∧ post r := by
  intro s
  induction h : m s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    intro hs
    obtain ⟨e, s', hrun, hnext⟩ := step s hs
    rw [loop_run, hrun]
    cases ha : again e
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hnext
      exact ⟨(e, s'), by simp [ha], hnext⟩
    · simp only [ha, ↓reduceIte] at hnext
      obtain ⟨hinv, hlt⟩ := hnext
      obtain ⟨r, hr, hpost⟩ := ih (m s') (h ▸ hlt) s' rfl hinv
      exact ⟨r, by simp [ha, hr], hpost⟩

/-- A target-specific dispatch loop uses the same iterator as an ordinary AIR loop.
`dispatch` recognizes only this target's exits; the body's selector update belongs to `σ`.
An invariant and decreasing measure must include that selector whenever needed. -/
theorem loop_dispatch_spec {σ ε α : Type} (body : M σ ε) (dispatch : ε → Option α)
    (inv : σ → Prop) (measure : σ → Nat) (post : ε × σ → Prop)
    (step : ∀ s, inv s → ∃ e s', body.run s = pure (e, s') ∧
      (match dispatch e with
       | some _ => inv s' ∧ measure s' < measure s
       | none => post (e, s'))) :
    ∀ s, inv s → ∃ r, (loop body (fun e => (dispatch e).isSome)).run s = pure r ∧ post r := by
  apply loop_spec body (fun e => (dispatch e).isSome) inv measure post
  intro s hs
  obtain ⟨e, s', hrun, hstep⟩ := step s hs
  refine ⟨e, s', hrun, ?_⟩
  cases h : dispatch e <;> simpa [h] using hstep

end Zig
