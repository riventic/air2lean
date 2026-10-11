import IdleLoop.Turns

/-!
# One scheduler turn between stops

From a state `At (f + 1) mp wp s`, one turn of `Sched.go` under any oracle `o` ends the run with
a value, has no result only when no turns are left, or reaches a state `At f mp' wp' s'` with a
later oracle index. The worker's turns move it along its loop; `main`'s turns store and join.
-/

namespace IdleLoop.Client

open Zig Zig.Conc Zig.Conc.Proto

theorem choose_snd (o : Nat → Nat) (s : Sched.State Tgt Unit) (n : Nat) :
    (s.choose o n).2 = { s with step := s.step + 1, trace := s.trace.push n } := rfl

theorem choose_fst (o : Nat → Nat) (s : Sched.State Tgt Unit) (n : Nat) :
    (s.choose o n).1 = if n = 0 then 0 else o s.step % n := rfl

/-- The scheduler's choice among `main` and the worker. -/
theorem pick_two (o : Nat → Nat) (s : Sched.State Tgt Unit) (h : s.ready = #[0, 1]) :
    (s.ready[(s.choose o s.ready.size).1]! = 0 ∧ o s.step % 2 = 0) ∨
      (s.ready[(s.choose o s.ready.size).1]! = 1 ∧ o s.step % 2 = 1) := by
  rw [choose_fst, h]
  rcases Nat.mod_two_eq_zero_or_one (o s.step) with h2 | h2 <;> simp [h2]

theorem pick_one (o : Nat → Nat) (s : Sched.State Tgt Unit) {t : Nat} (h : s.ready = #[t]) :
    s.ready[(s.choose o s.ready.size).1]! = t := by
  rw [choose_fst, h]; simp [Nat.mod_one]

/-- What a worker turn does to the worker's stop. -/
def WNext (o : Nat → Nat) (step : Nat) (mp : MainAt) (wp wp' : WorkerAt) : Prop :=
  (wp = .start → wp' = .load) ∧ (wp = .spin → wp' = .yld) ∧ (wp = .yld → wp' = .load) ∧
  (wp = .load → mp = .store → wp' = .spin) ∧
  (wp = .load → mp = .join → o (step + 1) = 0 → wp' = .done)

theorem ready_ne {f : Nat} {mp : MainAt} {wp : WorkerAt} {s : Sched.State Tgt Unit}
    (hA : At f mp wp s) :
    (mp = .store ∧ s.ready = #[0, 1]) ∨ (mp = .join ∧ wp ≠ .done ∧ s.ready = #[1]) ∨
      (mp = .join ∧ wp = .done ∧ s.ready = #[0]) := by
  obtain ⟨d, dw, hm, hk, hi, -, -, hdone⟩ := hA
  cases mp with
  | store =>
    exact .inl ⟨rfl, ready_store hm hk (fun h => by cases hdone h)⟩
  | join =>
    by_cases hw : wp = .done
    · subst hw; exact .inr (.inr ⟨rfl, rfl, ready_done hm hk⟩)
    · exact .inr (.inl ⟨rfl, hw, ready_join hm hk hw hi.thr⟩)

theorem kid_set {S : Sched.State Tgt Unit} {x : Sched.TS Tgt Unit} (ts : Sched.TS Tgt Unit)
    (hk : S.kids = #[x]) : { S with kids := S.kids.set! 0 ts } = { S with kids := #[ts] } := by
  rw [hk]; rfl

/-- **A worker turn.** -/
theorem wstep (o : Nat → Nat) {f : Nat} {mp : MainAt} {wp : WorkerAt} {s : Sched.State Tgt Unit}
    (hA : At (f + 1) mp wp s) (hw : wp ≠ .done) (hne : s.ready.isEmpty = false)
    (hsel : s.ready[(s.choose o s.ready.size).1]! = 1) :
    ∃ wp' s', At f mp wp' s' ∧ s.step < s'.step ∧
      (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = (Sched.go ⟨.any, .available⟩ dispatch o f s').1 ∧ WNext o s.step mp wp wp' := by
  obtain ⟨d, dw, hm, hk, hi, hd, hdw, -⟩ := hA
  obtain ⟨dw', rfl⟩ : ∃ dw', dw = dw' + 1 := ⟨dw - 1, by omega⟩
  have hk0 : ∀ p, workerTS wp (dw' + 1) = .paused p → s.kids[0]? = some (.paused p) := by
    intro p hp; rw [hk, ← hp]; rfl
  let S₁ : Sched.State Tgt Unit := { s with step := s.step + 1, trace := s.trace.push s.ready.size }
  have hk₁ : (atT S₁ 1).kids = #[workerTS wp (dw' + 1)] := hk
  cases wp with
  | done => exact absurd rfl hw
  | start =>
    rw [go_kid o hne hsel (hk0 _ rfl), choose_snd, tt_start]
    refine ⟨.load, { atT S₁ 1 with kids := #[workerTS .load dw'] },
      ⟨d, dw', hm, rfl, hi.cur 1, by omega, by omega, fun h => by cases h⟩,
      by show s.step < s.step + 1; omega,
      by rw [← kid_set _ hk₁], fun _ => rfl, by simp, by simp, by simp, by simp⟩
  | spin =>
    rw [go_kid o hne hsel (hk0 _ rfl), choose_snd, tt_spin]
    refine ⟨.yld, { atT S₁ 1 with kids := #[workerTS .yld dw'] },
      ⟨d, dw', hm, rfl, hi.cur 1, by omega, by omega, fun h => by cases h⟩,
      by show s.step < s.step + 1; omega,
      by rw [← kid_set _ hk₁], by simp, fun _ => rfl, by simp, by simp, by simp⟩
  | yld =>
    rw [go_kid o hne hsel (hk0 _ rfl), choose_snd, tt_yld]
    have hk₂ : ((atT S₁ 1).choose o 2).2.kids = #[workerTS .yld (dw' + 1)] := hk
    refine ⟨.load, { ((atT S₁ 1).choose o 2).2 with kids := #[workerTS .load dw'] },
      ⟨d, dw', hm, rfl, hi.cur 1, by omega, by omega, fun h => by cases h⟩,
      by show s.step < s.step + 1 + 1; omega, by rw [← kid_set _ hk₂], by simp, by simp,
      fun _ => rfl, by simp,
      by simp⟩
  | load =>
    rw [go_kid o hne hsel (hk0 _ rfl), choose_snd]
    let S₂ := ((atT S₁ 1).choose o (loadCnt (atT S₁ 1).mem)).2
    obtain ⟨m', ⟨⟨-, -, hi'⟩, htt, hnot⟩ | ⟨m'', -, hi'', hst, htt⟩⟩ := tt_load o f dw' S₁ hi
    · rw [htt]
      have hk₂ : ({ S₂ with mem := m' } : Sched.State Tgt Unit).kids =
          #[workerTS .load (dw' + 1)] := hk
      refine ⟨.spin, { S₂ with mem := m', kids := #[workerTS .spin dw'] },
        ⟨d, dw', hm, rfl, hi', by omega, by omega, fun h => by cases h⟩,
        by show s.step < s.step + 1 + 1; omega,
        by rw [← kid_set _ hk₂], by simp, by simp, by simp, fun _ _ => rfl, fun _ hj ho => ?_⟩
      exfalso
      apply hnot
      refine ⟨by subst hj; rfl, ?_⟩
      simp only [choose_fst, atT, S₁, ho]
      split <;> simp
    · rw [htt]
      have hj : mp = .join := by cases mp <;> simp_all [MainAt.stored]
      subst hj
      have hk₂ : ({ S₂ with mem := m'' } : Sched.State Tgt Unit).kids =
          #[workerTS .load (dw' + 1)] := hk
      refine ⟨.done, { S₂ with mem := m'', kids := #[workerTS .done f] },
        ⟨d, f, hm, rfl, hi'', by omega, by omega, fun _ => rfl⟩,
        by show s.step < s.step + 1 + 1; omega,
        by rw [← kid_set _ hk₂]; rfl, by simp, by simp, by simp, by simp, fun _ _ _ => rfl⟩

/-- **`main`'s store turn.** With no depth left the run has no result. -/
theorem mstore (o : Nat → Nat) {f : Nat} {wp : WorkerAt} {s : Sched.State Tgt Unit}
    (hA : At (f + 1) .store wp s) (hne : s.ready.isEmpty = false)
    (hsel : s.ready[(s.choose o s.ready.size).1]! = 0) :
    (f = 0 ∧ (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = none) ∨
      ∃ s', At f .join wp s' ∧ s.step < s'.step ∧
        (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = (Sched.go ⟨.any, .available⟩ dispatch o f s').1 := by
  obtain ⟨d, dw, hm, hk, hi, hd, hdw, hdone⟩ := hA
  rw [go_main o hne hsel hm, choose_snd]
  cases d with
  | zero =>
    left
    obtain ⟨e, he, rfl⟩ := tt_store_zero o f { s with step := s.step + 1, trace := s.trace.push s.ready.size } hi
    rw [he]
    exact ⟨by omega, rfl⟩
  | succ d =>
    right
    obtain ⟨m', -, hi', htt⟩ := tt_store o f d
      { s with step := s.step + 1, trace := s.trace.push s.ready.size } hi
    rw [htt]
    let S₂ := ((atT { s with step := s.step + 1, trace := s.trace.push s.ready.size } 0).choose o
      (storeCnt (atT { s with step := s.step + 1, trace := s.trace.push s.ready.size } 0).mem)).2
    exact ⟨{ S₂ with mem := m', main := .paused (mainP .join d) },
      ⟨d, dw, rfl, hk, hi', by omega, by omega, fun _ => rfl⟩,
      by show s.step < s.step + 1 + 1; omega, rfl⟩

/-- **`main`'s join turn**, after the worker ended: the run ends. -/
theorem mjoin (o : Nat → Nat) {f : Nat} {s : Sched.State Tgt Unit}
    (hA : At (f + 1) .join .done s) (hne : s.ready.isEmpty = false)
    (hsel : s.ready[(s.choose o s.ready.size).1]! = 0) :
    ∃ M, (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = some (.ok ((), M)) := by
  obtain ⟨d, dw, hm, hk, hi, -, -, -⟩ := hA
  rw [go_main o hne hsel hm]
  obtain ⟨M, htt⟩ := tt_join o f d ((s.choose o s.ready.size).2) hi
  rw [htt]
  exact ⟨_, rfl⟩

/-- **One turn**, for every oracle. -/
theorem turn (o : Nat → Nat) {f : Nat} {mp : MainAt} {wp : WorkerAt} {s : Sched.State Tgt Unit}
    (hA : At (f + 1) mp wp s) :
    (f = 0 ∧ (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = none) ∨
      (∃ M, (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = some (.ok ((), M))) ∨
      ∃ mp' wp' s', At f mp' wp' s' ∧ s.step < s'.step ∧
        (Sched.go ⟨.any, .available⟩ dispatch o (f + 1) s).1 = (Sched.go ⟨.any, .available⟩ dispatch o f s').1 := by
  rcases ready_ne hA with ⟨rfl, hr⟩ | ⟨rfl, hw, hr⟩ | ⟨rfl, rfl, hr⟩
  · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
    rcases pick_two o s hr with ⟨hsel, -⟩ | ⟨hsel, -⟩
    · rcases mstore o hA hne hsel with h | ⟨s', hA', hs, he⟩
      · exact .inl h
      · exact .inr (.inr ⟨_, _, s', hA', hs, he⟩)
    · have hw : wp ≠ .done := fun h => by obtain ⟨-, -, -, -, -, -, -, h'⟩ := hA; cases h' h
      obtain ⟨wp', s', hA', hs, he, -⟩ := wstep o hA hw hne hsel
      exact .inr (.inr ⟨_, _, s', hA', hs, he⟩)
  · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
    obtain ⟨wp', s', hA', hs, he, -⟩ := wstep o hA hw hne (pick_one o s hr)
    exact .inr (.inr ⟨_, _, s', hA', hs, he⟩)
  · have hne : s.ready.isEmpty = false := by rw [hr]; rfl
    exact .inr (.inl (mjoin o hA hne (pick_one o s hr)))

end IdleLoop.Client
