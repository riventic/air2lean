import IdleLoop.Shape

/-!
# Scheduler turns of the client
-/

namespace IdleLoop.Client

open Zig Zig.Conc Zig.Conc.Proto

/-! ## One scheduler step -/


theorem go_kid (o : Nat → Nat) {f : Nat} {s : Sched.State Tgt Unit} {p : Sched.Paused Tgt Unit}
    (hne : s.ready.isEmpty = false)
    (ht : s.ready[(s.choose o s.ready.size).1]! = 1)
    (hk : s.kids[0]? = some (.paused p)) :
    (Sched.go dispatch o (f + 1) s).1 =
      match (Sched.turnTrace dispatch f o 1 (s.choose o s.ready.size).2 p).1 with
      | .error e => Sched.outOf e
      | .ok (ts, _, s') => (Sched.go dispatch o f { s' with kids := s'.kids.set! 0 ts }).1 := by
  rw [Sched.go]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  generalize hc : s.choose o s.ready.size = cs at ht ⊢
  obtain ⟨i, s₁⟩ := cs
  have hk₁ : s₁.kids = s.kids := by
    have := congrArg Prod.snd hc; simp only [Sched.State.choose] at this; rw [← this]
  simp only at ht ⊢
  rw [ht]
  simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, hk₁, hk]
  split <;> (rename_i h; rw [h])

theorem go_main (o : Nat → Nat) {f : Nat} {s : Sched.State Tgt Unit} {p : Sched.Paused Tgt Unit}
    (hne : s.ready.isEmpty = false)
    (ht : s.ready[(s.choose o s.ready.size).1]! = 0)
    (hm : s.main = .paused p) :
    (Sched.go dispatch o (f + 1) s).1 =
      match (Sched.turnTrace dispatch f o 0 (s.choose o s.ready.size).2 p).1 with
      | .error e => Sched.outOf e
      | .ok (_, some v, s') => some (.ok (v, s'.mem))
      | .ok (ts, none, s') => (Sched.go dispatch o f { s' with main := ts }).1 := by
  rw [Sched.go]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  generalize hc : s.choose o s.ready.size = cs at ht ⊢
  obtain ⟨i, s₁⟩ := cs
  have hm₁ : s₁.main = s.main := by
    have := congrArg Prod.snd hc; simp only [Sched.State.choose] at this; rw [← this]
  simp only at ht ⊢
  rw [ht]
  simp only [↓reduceIte, hm₁, hm]
  split <;> (rename_i h; rw [h])

theorem ready_store {s : Sched.State Tgt Unit} {d dw : Nat} {wp : WorkerAt}
    (hm : s.main = .paused (mainP .store d)) (hk : s.kids = #[workerTS wp dw]) (hw : wp ≠ .done) :
    s.ready = #[0, 1] := by
  cases wp <;> simp_all [Sched.State.ready, mainP, workerTS, Sched.canGo]

theorem ready_join {s : Sched.State Tgt Unit} {d dw : Nat} {wp : WorkerAt}
    (hm : s.main = .paused (mainP .join d)) (hk : s.kids = #[workerTS wp dw]) (hw : wp ≠ .done)
    (ht : s.mem.threads = thr0) :
    s.ready = #[1] := by
  cases wp <;> simp_all [Sched.State.ready, mainP, workerTS, Sched.canGo, Thread.joinValid, thr0,
    Sched.State.isDone]

theorem ready_done {s : Sched.State Tgt Unit} {d dw : Nat}
    (hm : s.main = .paused (mainP .join d)) (hk : s.kids = #[workerTS .done dw]) :
    s.ready = #[0] := by
  simp_all [Sched.State.ready, mainP, workerTS, Sched.canGo, Sched.State.isDone]

/-! ## The worker's turns -/

/-- The scheduler's copy of the memory at a turn of thread `t`. -/
abbrev atT (S : Sched.State Tgt Unit) (t : ThreadId) : Sched.State Tgt Unit :=
  { S with mem := { S.mem with current := t } }

theorem tt_start (o : Nat → Nat) (f d : Nat) (S : Sched.State Tgt Unit) :
    (Sched.turnTrace dispatch f o 1 S ⟨d + 1, .yield, fun _ m => dispatch .worker (d + 1) m⟩).1 =
      .ok (workerTS .load d, none, atT S 1) := by
  show Sched.settle 1 (atT S 1) (dispatch .worker (d + 1) (atT S 1).mem) = _
  rw [worker_succ]; rfl

theorem tt_spin (o : Nat → Nat) (f d : Nat) (S : Sched.State Tgt Unit) :
    (Sched.turnTrace dispatch f o 1 S ⟨d + 1, .yield, fun _ m => wSpun (d + 1) m⟩).1 =
      .ok (workerTS .yld d, none, atT S 1) := rfl

theorem tt_yld (o : Nat → Nat) (f d : Nat) (S : Sched.State Tgt Unit) :
    (Sched.turnTrace dispatch f o 1 S ⟨d + 1, .choose 2, fun _ m => wLoop (d + 1) m⟩).1 =
      .ok (workerTS .load d, none, ((atT S 1).choose o 2).2) := by
  show Sched.settle 1 ((atT S 1).choose o 2).2 (wLoop (d + 1) (atT S 1).mem) = _
  rw [wLoop_succ]; rfl

/-- The worker's load turn: the load reads 0 (to the spin hint) or 1 (the check, then its
end). After the store, option 0 reads 1. -/
theorem tt_load (o : Nat → Nat) (f d : Nat) {st : Bool} (S : Sched.State Tgt Unit)
    (hi : Inv st S.mem) :
    let S₁ := ((atT S 1).choose o (loadCnt (atT S 1).mem)).2
    let c := ((atT S 1).choose o (loadCnt (atT S 1).mem)).1
    ∃ m', ((m'.current = 1 ∧ m'.threads = S.mem.threads ∧ Inv st m') ∧
      ((Sched.turnTrace dispatch f o 1 S ⟨d + 1, .pick loadCnt, fun c m => wAfter c (d + 1) m⟩).1 =
        .ok (workerTS .spin d, none, { S₁ with mem := m' }) ∧ ¬ (st = true ∧ c = 0)) ∨
      (∃ m'', m''.threads = S.mem.threads ∧ Inv true m'' ∧ st = true ∧
        (Sched.turnTrace dispatch f o 1 S ⟨d + 1, .pick loadCnt, fun c m => wAfter c (d + 1) m⟩).1 =
          .ok (.done, some (), { S₁ with mem := m'' }))) := by
  intro S₁ c
  have hic : Inv st (atT S 1).mem := hi.cur 1
  obtain ⟨v, m', hl⟩ := ok_of (nn_atomicLoadAt c .acquire 4 fPtr)
    (load_noErr hic (by exact (by decide : 1 < 2)) (choice_lt _ _))
  obtain ⟨hc', hth, hi', hv, hnew⟩ := step_load hic rfl hl
  refine ⟨m', ?_⟩
  have htt : (Sched.turnTrace dispatch f o 1 S ⟨d + 1, .pick loadCnt, fun c m => wAfter c (d + 1) m⟩).1 =
      Sched.settle 1 S₁ (wAfter c (d + 1) (atT S 1).mem) := rfl
  rcases hv with rfl | ⟨rfl, hst, hle⟩
  · left
    refine ⟨⟨hc', hth, hi'⟩, ?_, fun ⟨h1, h2⟩ => absurd (hnew h1 h2) (by decide)⟩
    rw [htt, wAfter_zero hl]; rfl
  · right
    subst hst
    obtain ⟨hrun, hir⟩ := read_run hi' hc' hle
    refine ⟨m'.recordAt 0 0 4 .read, by rw [← hth]; rfl, hir, rfl, ?_⟩
    rw [htt, wAfter_one hl]
    show Sched.settle 1 S₁ (check (d + 1) m') = _
    rw [check_run hi' hc' hle]
    have hj : joinedAll 1 (m'.recordAt 0 0 4 .read) := by
      intro r hr hs
      have ht : (m'.recordAt 0 0 4 .read).threads = thr0 := hir.thr
      rw [ht] at hr
      simp [thr0] at hr
      rcases hr with rfl | rfl <;> cases hs
    simp only [Sched.settle, checkJoined_of hj]

/-! ## `main`'s turns -/

theorem tt_store (o : Nat → Nat) (f d : Nat) (S : Sched.State Tgt Unit) (hi : Inv false S.mem) :
    let S₁ := ((atT S 0).choose o (storeCnt (atT S 0).mem)).2
    ∃ m', m'.threads = S.mem.threads ∧ Inv true m' ∧
      (Sched.turnTrace dispatch f o 0 S (mainP .store (d + 1))).1 =
        .ok (.paused (mainP .join d), none, { S₁ with mem := m' }) := by
  intro S₁
  have hic : Inv false (atT S 0).mem := hi.cur 0
  obtain ⟨u, m', hs⟩ := ok_of (nn_atomicStoreAt
    ((atT S 0).choose o (storeCnt (atT S 0).mem)).1 .release 4 fPtr (1 : BitVec 32))
    (store_noErr hic (by exact (by decide : 0 < 2)) (choice_lt _ _))
  cases u
  obtain ⟨-, hth, hi'⟩ := step_store hic rfl hs
  refine ⟨m', hth, hi', ?_⟩
  have htt : (Sched.turnTrace dispatch f o 0 S (mainP .store (d + 1))).1 = Sched.settle 0 S₁
      (mainStore ((atT S 0).choose o (storeCnt (atT S 0).mem)).1 1 (d + 1) (atT S 0).mem) := rfl
  rw [htt, mainStore_succ hs]; rfl

theorem tt_store_zero (o : Nat → Nat) (f : Nat) (S : Sched.State Tgt Unit) (hi : Inv false S.mem) :
    ∃ e, (Sched.turnTrace dispatch f o 0 S (mainP .store 0)).1 = .error e ∧ e = none := by
  have hic : Inv false (atT S 0).mem := hi.cur 0
  obtain ⟨u, m', hs⟩ := ok_of (nn_atomicStoreAt
    ((atT S 0).choose o (storeCnt (atT S 0).mem)).1 .release 4 fPtr (1 : BitVec 32))
    (store_noErr hic (by exact (by decide : 0 < 2)) (choice_lt _ _))
  refine ⟨none, ?_, rfl⟩
  have htt : (Sched.turnTrace dispatch f o 0 S (mainP .store 0)).1 =
      Sched.settle 0 ((atT S 0).choose o (storeCnt (atT S 0).mem)).2
      ((CoN.leaf ((atomicStoreAt ((atT S 0).choose o (storeCnt (atT S 0).mem)).1 .release 4 fPtr
        (1 : BitVec 32)).run (atT S 0).mem)).bind fun (a, m') k => syncJoin 1 k m') := rfl
  rw [htt, show (atomicStoreAt ((atT S 0).choose o (storeCnt (atT S 0).mem)).1 .release 4 fPtr
    (1 : BitVec 32)).run (atT S 0).mem = ExceptT.mk (some (.ok (u, m'))) from hs]
  rfl

theorem tt_join (o : Nat → Nat) (f d : Nat) (S : Sched.State Tgt Unit) (hi : Inv true S.mem) :
    ∃ M, (Sched.turnTrace dispatch f o 0 S (mainP .join d)).1 = .ok (.done, some (), M) := by
  have hth : (atT S 0).mem.threads = thr0 := hi.thr
  obtain ⟨m', hj⟩ := join_run (m := (atT S 0).mem) (tid := 1) (rec := { spawner := 0, joined := false })
    (by rw [hth]; rfl) rfl rfl
  obtain ⟨rec, hr, -, rfl⟩ := join_eq hj
  rw [hth] at hr
  simp only [thr0] at hr
  have hrec : rec = { spawner := 0, joined := false } := by simpa using hr.symm
  subst hrec
  simp only [Sched.turnTrace, mainP, Sched.State.onMem, hj, Sched.settle, bind, Except.bind]
  rw [checkJoined_of (t := 0) ?hja]
  · exact ⟨_, rfl⟩
  · intro r hm _
    have ht : S.mem.threads = thr0 := hi.thr
    simp only [ht, thr0] at hm
    simp at hm
    rcases hm with rfl | rfl <;> rfl

end IdleLoop.Client
