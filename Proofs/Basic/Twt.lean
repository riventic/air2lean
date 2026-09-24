import Proofs.Basic.Proofs

/-!
# Proof about `examples/basic/basic.zig`'s `totalWeightedTardiness`

`tPre jobs k` is the sum of the first `k` job durations (like `psum`, for `Job.duration`).
`wt jobs k` is the weighted tardiness of job `k`, given the jobs before it set the start time.
`twtPre jobs k` is the sum of `wt` over the first `k` jobs.
-/

open Basic

/-- Sum of the first `k` job durations, as a natural number. -/
def tPre (jobs : Array Job) (k : Nat) : Nat :=
  (((jobs.toList.take k).map Job.duration).map BitVec.toNat).sum

/-- Weighted tardiness of job `k`, given the jobs before it. -/
def wt (jobs : Array Job) (k : Nat) : Nat :=
  (tPre jobs k + jobs[k]!.duration.toNat - jobs[k]!.due.toNat) * jobs[k]!.weight.toNat

/-- Sum of weighted tardiness of the first `k` jobs. -/
def twtPre (jobs : Array Job) (k : Nat) : Nat :=
  ((List.range k).map (wt jobs)).sum

theorem tPre_le (jobs : Array Job) (k : Nat) : tPre jobs k ≤ k * 2 ^ 32 := by
  unfold tPre
  have h := list_sum_le ((jobs.toList.take k).map Job.duration)
  have hlen : ((jobs.toList.take k).map Job.duration).length ≤ k := by simp [Nat.min_le_left]
  exact Nat.le_trans h (Nat.mul_le_mul_right _ hlen)

theorem tPre_succ (jobs : Array Job) (k : Nat) (hk : k < jobs.size) :
    tPre jobs (k + 1) = tPre jobs k + jobs[k].duration.toNat := by
  unfold tPre
  rw [List.map_map, Zig.sum_take_succ _ _ _ (by simpa using hk)]; simp

theorem tPre_mono (jobs : Array Job) {k k' : Nat} (h : k ≤ k') :
    tPre jobs k ≤ tPre jobs k' := by
  have hd : k + (k' - k) = k' := by omega
  unfold tPre
  rw [← hd, List.take_add, List.map_append, List.map_append, List.sum_append]
  omega

theorem twtPre_succ (jobs : Array Job) (k : Nat) :
    twtPre jobs (k + 1) = twtPre jobs k + wt jobs k := by
  unfold twtPre
  simp [List.range_succ]

/-- `wt jobs k` fits in `u32`: `hw` covers the tardy case, and the non-tardy case is `0`. -/
theorem wt_lt (jobs : Array Job) (k : Nat)
    (hw : jobs[k]!.due.toNat < tPre jobs k + jobs[k]!.duration.toNat → wt jobs k < 2 ^ 32) :
    wt jobs k < 2 ^ 32 := by
  by_cases h : jobs[k]!.due.toNat < tPre jobs k + jobs[k]!.duration.toNat
  · exact hw h
  · unfold wt
    have hz : tPre jobs k + jobs[k]!.duration.toNat - jobs[k]!.due.toNat = 0 := by omega
    rw [hz]; omega

theorem twtPre_le (jobs : Array Job)
    (hw : ∀ k < jobs.size, jobs[k]!.due.toNat < tPre jobs k + jobs[k]!.duration.toNat →
      wt jobs k < 2 ^ 32)
    (k : Nat) (hk : k ≤ jobs.size) : twtPre jobs k ≤ k * 2 ^ 32 := by
  induction k with
  | zero => simp [twtPre]
  | succ n ih =>
    have hn : n < jobs.size := by omega
    have hi := ih (by omega)
    have hwn : wt jobs n < 2 ^ 32 := wt_lt jobs n (hw n hn)
    rw [twtPre_succ]
    omega

theorem twt_loop_step (jobs : Array Job) (hs : jobs.size < 2 ^ 32)
    (ht : tPre jobs jobs.size < 2 ^ 32)
    (hw : ∀ k < jobs.size, jobs[k]!.due.toNat < tPre jobs k + jobs[k]!.duration.toNat →
      wt jobs k < 2 ^ 32)
    (s : totalWeightedTardinessLocals) (hi : s.i.toNat ≤ jobs.size)
    (htv : s.t.toNat = tPre jobs s.i.toNat) (hcv : s.cost.toNat = twtPre jobs s.i.toNat) :
    ∃ e s', (totalWeightedTardiness.loop14 jobs).run s = pure (e, s') ∧
      (if totalWeightedTardiness.again14 e then
          (s'.i.toNat ≤ jobs.size ∧ s'.t.toNat = tPre jobs s'.i.toNat ∧
            s'.cost.toNat = twtPre jobs s'.i.toNat) ∧
            jobs.size - s'.i.toNat < jobs.size - s.i.toNat
        else e = .br13 ∧ s'.cost.toNat = twtPre jobs jobs.size) := by
  have hm : jobs.size % 18446744073709551616 = jobs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.i.toNat < jobs.size
  · have htsum : tPre jobs s.i.toNat + jobs[s.i.toNat].duration.toNat < 2 ^ 32 := by
      have e1 := tPre_succ jobs s.i.toNat hlt
      have e2 := tPre_mono jobs (k := s.i.toNat + 1) (k' := jobs.size) (by omega)
      omega
    have h1_wt : s.t.toNat + jobs[s.i.toNat].duration.toNat < 2 ^ 32 := by
      rw [htv]; exact htsum
    have hwk : wt jobs s.i.toNat < 2 ^ 32 := wt_lt jobs s.i.toNat (hw s.i.toNat hlt)
    have hji : jobs[s.i.toNat]! = jobs[s.i.toNat] := getElem!_pos jobs s.i.toNat hlt
    have hwt_eq : wt jobs s.i.toNat =
        (s.t.toNat + jobs[s.i.toNat].duration.toNat - jobs[s.i.toNat].due.toNat) *
          jobs[s.i.toNat].weight.toNat := by
      unfold wt; rw [hji, ← htv]
    have h2_wt : (s.t.toNat + jobs[s.i.toNat].duration.toNat - jobs[s.i.toNat].due.toNat) *
        jobs[s.i.toNat].weight.toNat < 2 ^ 32 := hwt_eq ▸ hwk
    obtain ⟨wtr, hwtr_eq, hwtr_val⟩ := weightedTardiness_ok jobs[s.i.toNat] s.t h1_wt h2_wt
    have hwtr_wt : wtr.toNat = wt jobs s.i.toNat := hwtr_val.trans hwt_eq.symm
    have hp := twtPre_le jobs hw s.i.toNat (by omega)
    have hwtrlt := wtr.isLt
    have hwtrmod : wtr.toNat % 18446744073709551616 = wtr.toNat := Nat.mod_eq_of_lt (by omega)
    have hTadd : ¬ 4294967296 ≤ s.t.toNat + jobs[s.i.toNat].duration.toNat := by omega
    have hCadd : ¬ 18446744073709551616 ≤ s.cost.toNat + wtr.toNat := by omega
    have hIinc : ¬ 18446744073709551615 ≤ s.i.toNat := by omega
    refine ⟨.rep14,
      { t := s.t + jobs[s.i.toNat].duration, cost := s.cost + wtr.setWidth 64, i := s.i + 1 },
      ?_, ?_⟩
    · unfold totalWeightedTardiness.loop14
      simp [zig_unfold, Zig.len, Zig.index, hlt, hm, hwtr_eq, hwtrmod, hTadd, hCadd, hIinc]
    · have hi' : (s.i + 1).toNat = s.i.toNat + 1 :=
        Zig.toNat_add_one _ (by omega)
      have ht' : (s.t + jobs[s.i.toNat].duration).toNat =
          s.t.toNat + jobs[s.i.toNat].duration.toNat := by
        rw [BitVec.toNat_add]; omega
      have hc' : (s.cost + wtr.setWidth 64).toNat = s.cost.toNat + wtr.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_setWidth]; omega
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show (s.i + 1).toNat ≤ jobs.size
        rw [hi']; omega
      · show (s.t + jobs[s.i.toNat].duration).toNat = tPre jobs (s.i + 1).toNat
        rw [ht', hi', tPre_succ jobs s.i.toNat hlt, ← htv]
      · show (s.cost + wtr.setWidth 64).toNat = twtPre jobs (s.i + 1).toNat
        rw [hc', hi', twtPre_succ, hcv, hwtr_wt]
      · show jobs.size - (s.i + 1).toNat < jobs.size - s.i.toNat
        rw [hi']; omega
  · have heq : s.i.toNat = jobs.size := by omega
    refine ⟨.br13, s, ?_, ?_⟩
    · unfold totalWeightedTardiness.loop14
      simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · exact ⟨rfl, heq ▸ hcv⟩

/-- `totalWeightedTardiness` never panics when the jobs and every prefix / per-job weighted
tardiness fit in their Zig types, and returns the exact weighted tardiness sum. -/
theorem totalWeightedTardiness_spec (jobs : Array Job)
    (hs : jobs.size < 2 ^ 32)
    (ht : tPre jobs jobs.size < 2 ^ 32)
    (hw : ∀ k < jobs.size, jobs[k]!.due.toNat < tPre jobs k + jobs[k]!.duration.toNat →
      wt jobs k < 2 ^ 32) :
    ∃ r, totalWeightedTardiness jobs = pure r ∧ r.toNat = twtPre jobs jobs.size := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec (totalWeightedTardiness.loop14 jobs)
    totalWeightedTardiness.again14
    (fun s => s.i.toNat ≤ jobs.size ∧ s.t.toNat = tPre jobs s.i.toNat ∧
      s.cost.toNat = twtPre jobs s.i.toNat)
    (fun s => jobs.size - s.i.toNat)
    (fun r => r.1 = .br13 ∧ r.2.cost.toNat = twtPre jobs jobs.size)
    (fun s hs' => twt_loop_step jobs hs ht hw s hs'.1 hs'.2.1 hs'.2.2)
    { t := 0, cost := 0, i := 0 } (by simp [tPre, twtPre])
  subst he
  refine ⟨s'.cost, ?_, ?_⟩
  · unfold totalWeightedTardiness
    change Zig.loop (totalWeightedTardiness.loop14 jobs) totalWeightedTardiness.again14
      { t := 0, cost := 0, i := 0 } = some (Except.ok (totalWeightedTardinessExit.br13, s')) at hrun
    simp only [zig_unfold]
    rw [hrun]
    simp [zig_unfold]
  · exact hpost
