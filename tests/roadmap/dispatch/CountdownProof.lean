import countdown

/-! Kernel-checked loop invariants and termination measures for the *generated* nested
dispatch state machine `countdown` (Emitter.lean). check.sh compiles the fresh translation to
`countdown.olean`; these proofs use `Zig.loop_spec` and no compiler proof axioms. -/
namespace Dispatch.CountdownProof
open Dispatch

/-- Inner invariant: the `remaining` slot mirrors the inner selector; `acc + 2 * remaining`
is fixed; the outer selector is untouched. Measure: the inner selector. -/
def innerInv (n d : BitVec 8) (s : countdownLocals) : Prop :=
  s.local1 = s.dispatchValue8 ∧ s.local3 + 2 * s.local1 = 2 * n ∧ s.dispatchValue5 = d

theorem inner_step (n d : BitVec 8) (s : countdownLocals) (hs : innerInv n d s) :
    ∃ e s', countdown.loop8.run s = pure (e, s') ∧
      (if countdown.again8 e then innerInv n d s' ∧ s'.dispatchValue8.toNat < s.dispatchValue8.toNat
       else e = .dispatch5 1 ∧ s'.local3 = 2 * n ∧ s'.dispatchValue5 = d) := by
  obtain ⟨h1, h3, h5⟩ := hs
  unfold countdown.loop8
  by_cases h0 : s.dispatchValue8 = 0
  · refine ⟨.dispatch5 1, s, ?_, ?_⟩
    · simp [zig_unfold, h0]
    · simp only [countdown.again8, Bool.false_eq_true, ↓reduceIte]
      rw [h1, h0] at h3
      exact ⟨trivial, by simpa using h3, h5⟩
  · refine ⟨.dispatch8 (s.local1 - 1),
      { s with local1 := s.local1 - 1, local3 := s.local3 + 2, dispatchValue8 := s.local1 - 1 },
      ?_, ?_⟩
    · obtain ⟨l1, l3, d5, d8⟩ := s
      simp only at h0 h1
      subst h1
      have h0' : ¬l1 = 0#8 := h0
      simp [zig_unfold, h0', Zig.subWrap, Zig.addWrap]
    · simp only [countdown.again8, ↓reduceIte]
      refine ⟨⟨rfl, ?_, h5⟩, ?_⟩
      · bv_omega
      · rw [← h1] at h0 ⊢; bv_omega

/-- Outer invariant: either still in the counting state with the initial captures, or in
the `done` state holding the result. Measure: the remaining outer transitions. -/
def outerInv (n : BitVec 8) (s : countdownLocals) : Prop :=
  (s.dispatchValue5 = 0 ∧ s.local1 = n ∧ s.local3 = 0) ∨ (s.dispatchValue5 = 1 ∧ s.local3 = 2 * n)

theorem outer_step (n : BitVec 8) (s : countdownLocals) (hs : outerInv n s) :
    ∃ e s', countdown.loop5.run s = pure (e, s') ∧
      (if countdown.again5 e then
          outerInv n s' ∧ 1 - s'.dispatchValue5.toNat < 1 - s.dispatchValue5.toNat
       else e = .ret (2 * n)) := by
  unfold countdown.loop5
  obtain ⟨l1, l3, d5, d8⟩ := s
  rcases hs with ⟨h5, h1, h3⟩ | ⟨h5, h3⟩ <;> simp only at h5 h3 <;> subst h5 h3
  · simp only at h1
    subst h1
    obtain ⟨⟨e, s'⟩, hrun, he, h3', h5'⟩ := Zig.loop_spec countdown.loop8 countdown.again8
      (innerInv l1 0) (fun s => s.dispatchValue8.toNat)
      (fun r => r.1 = .dispatch5 1 ∧ r.2.local3 = 2 * l1 ∧ r.2.dispatchValue5 = 0)
      (fun s hs => inner_step l1 0 s hs)
      { local1 := l1, local3 := 0, dispatchValue5 := 0, dispatchValue8 := l1 }
      ⟨rfl, by simp, rfl⟩
    simp only at he h3' h5'
    subst he
    refine ⟨.dispatch5 1, { s' with dispatchValue5 := 1 }, ?_, ?_⟩
    · simp [zig_unfold] at hrun
      simp [zig_unfold, hrun]
    · simp [countdown.again5, outerInv, h3']
  · refine ⟨.ret (2 * n), { local1 := l1, local3 := 2 * n, dispatchValue5 := 1, dispatchValue8 := d8 }, ?_, ?_⟩
    · simp [zig_unfold]
    · simp [countdown.again5]

/-- The nested dispatch state machine terminates for every input with `2 * n` (wrapping). -/
theorem countdown_spec (n : BitVec 8) : countdown n = pure (2 * n) := by
  obtain ⟨⟨e, s'⟩, hrun, he⟩ := Zig.loop_spec countdown.loop5 countdown.again5 (outerInv n)
    (fun s => 1 - s.dispatchValue5.toNat) (fun r => r.1 = .ret (2 * n))
    (fun s hs => outer_step n s hs)
    { local1 := n, local3 := 0, dispatchValue5 := 0,
      dispatchValue8 := (default : countdownLocals).dispatchValue8 }
    (Or.inl ⟨rfl, rfl, rfl⟩)
  simp only at he
  subst he
  unfold countdown
  simp [zig_unfold] at hrun
  simp [zig_unfold, hrun]

end Dispatch.CountdownProof
