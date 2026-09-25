import Proofs.Basic.Common

/-!
# Proofs about `examples/basic/basic.zig`

Each theorem is about the generated code in `Gen.lean`, so it holds for the Zig function to the
extent the translation is faithful (see the differential tests in `tests/diff/`).
-/

open Basic

theorem tardiness_spec (a b : BitVec 32) :
    tardiness a b = pure (if b.toNat < a.toNat then a - b else 0) := by
  unfold tardiness
  by_cases h : b.toNat < a.toNat
  · have : ¬ a.toNat < b.toNat := by omega
    simp [zig_unfold, h, this]
  · simp [zig_unfold, h]

theorem scale_spec (a : BitVec 32) (b : BitVec 8) :
    scale a b = if a.toNat * b.toNat ≥ 2 ^ 32 then throw .overflow
                else pure (a * b.setWidth 32) := by
  unfold scale
  have hb : b.toNat % 4294967296 = b.toNat := Nat.mod_eq_of_lt (by have := b.isLt; omega)
  by_cases h : a.toNat * b.toNat ≥ 2 ^ 32
  · have h' : 4294967296 ≤ a.toNat * b.toNat := h
    simp [zig_unfold, hb, h']
  · have h' : ¬ 4294967296 ≤ a.toNat * b.toNat := h
    simp [zig_unfold, hb, h']

theorem classify_le_two (x : BitVec 8) : ∃ r, classify x = pure r ∧ r.toNat ≤ 2 := by
  unfold classify
  by_cases h0 : x = 0
  · exact ⟨0, by simp [zig_unfold, h0], by decide⟩
  · have h0' : ¬ x = 0#8 := h0
    by_cases h9 : x.toNat ≤ 9
    · refine ⟨1, ?_, by decide⟩
      have h1 : 1 ≤ x.toNat := by
        have : x.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      simp [zig_unfold, h0', Zig.le, BitVec.ule, h1, h9]
    · refine ⟨2, ?_, by decide⟩
      simp [zig_unfold, h0', Zig.le, BitVec.ule, h9]

theorem weightedTardiness_ok (j : Job) (start : BitVec 32)
    (h1 : start.toNat + j.duration.toNat < 2 ^ 32)
    (h2 : (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat < 2 ^ 32) :
    ∃ r, weightedTardiness j start = pure r ∧
      r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat := by
  unfold weightedTardiness
  have hw := j.weight.isLt
  have hwm : j.weight.toNat % 4294967296 = j.weight.toNat := Nat.mod_eq_of_lt (by omega)
  have hadd : ¬ 4294967296 ≤ start.toNat + j.duration.toNat := by omega
  have hsum : (start + j.duration).toNat = start.toNat + j.duration.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h1
  by_cases hlt : j.due.toNat < start.toNat + j.duration.toNat
  · have hsub : (start + j.duration - j.due).toNat = start.toNat + j.duration.toNat - j.due.toNat := by
      rw [BitVec.toNat_sub, hsum]; omega
    have hmul : ¬ 4294967296 ≤ (start + j.duration - j.due).toNat * j.weight.toNat := by
      rw [hsub]; omega
    refine ⟨(start + j.duration - j.due) * j.weight.setWidth 32, ?_, ?_⟩
    · have hmod : (4294967296 - j.due.toNat + (start.toNat + j.duration.toNat)) % 4294967296
          = start.toNat + j.duration.toNat - j.due.toNat := by omega
      have hm : ¬ 4294967296 ≤ (4294967296 - j.due.toNat + (start.toNat + j.duration.toNat)) % 4294967296
          * j.weight.toNat := by rw [hmod]; omega
      simp [zig_unfold, tardiness_spec, hadd, hsum, hlt, hwm, hm]
    · rw [BitVec.toNat_mul, BitVec.toNat_setWidth, hsub, Nat.mod_eq_of_lt (a := j.weight.toNat) (by omega)]
      exact Nat.mod_eq_of_lt h2
  · refine ⟨0, ?_, ?_⟩
    · simp [zig_unfold, tardiness_spec, hadd, hsum, hlt, hwm]
    · have hz : start.toNat + j.duration.toNat - j.due.toNat = 0 := by omega
      simp [zig_unfold, hz]

theorem sum_loop_step (xs : Array (BitVec 32)) (hs : xs.size < 2 ^ 32) (s : sumLocals)
    (hk : s.local5.toNat ≤ xs.size) (ht : s.total.toNat = psum xs s.local5.toNat) :
    ∃ e s', (sum.loop10 xs (Zig.len xs)).run s = pure (e, s') ∧
      (if sum.again10 e then
          (s'.local5.toNat ≤ xs.size ∧ s'.total.toNat = psum xs s'.local5.toNat) ∧
            xs.size - s'.local5.toNat < xs.size - s.local5.toNat
        else e = .br9 ∧ s'.total.toNat = psum xs xs.size) := by
  unfold sum.loop10
  have hm : xs.size % 18446744073709551616 = xs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.local5.toNat < xs.size
  · have hx := xs[s.local5.toNat].isLt
    have hx' : xs[s.local5.toNat].toNat % 18446744073709551616 = xs[s.local5.toNat].toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hp := psum_le xs s.local5.toNat
    have hadd : ¬ 18446744073709551616 ≤ s.total.toNat + xs[s.local5.toNat].toNat := by
      have : s.local5.toNat * 2 ^ 32 + 2 ^ 32 ≤ 2 ^ 64 := by omega
      omega
    have hinc : ¬ 18446744073709551615 ≤ s.local5.toNat := by omega
    refine ⟨.rep10, { total := s.total + xs[s.local5.toNat].setWidth 64, local5 := s.local5 + 1 },
      ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, hx', hadd, hinc, StateT.lift]
    · have h5 : (s.local5 + 1).toNat = s.local5.toNat + 1 := by
        rw [BitVec.toNat_add]; simp [zig_unfold]; omega
      have htot : (s.total + xs[s.local5.toNat].setWidth 64).toNat
          = s.total.toNat + xs[s.local5.toNat].toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_setWidth, hx']; omega
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h5]; omega
      · rw [h5, htot, psum_succ xs _ hlt, ht]
      · rw [h5]; omega
  · have heq : s.local5.toNat = xs.size := by omega
    refine ⟨.br9, s, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm]
    · simp only [sum.again10, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, heq ▸ ht⟩

/-- `sum` never panics for fewer than 2^32 elements, and returns the exact sum. -/
theorem sum_spec (xs : Array (BitVec 32)) (hs : xs.size < 2 ^ 32) :
    ∃ r, sum xs = pure r ∧ r.toNat = (xs.toList.map BitVec.toNat).sum := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec (sum.loop10 xs (Zig.len xs))
    sum.again10
    (fun s => s.local5.toNat ≤ xs.size ∧ s.total.toNat = psum xs s.local5.toNat)
    (fun s => xs.size - s.local5.toNat)
    (fun r => r.1 = .br9 ∧ r.2.total.toNat = psum xs xs.size)
    (fun s hs' => sum_loop_step xs hs s hs'.1 hs'.2)
    { total := 0, local5 := 0 } (by simp [zig_unfold, psum])
  subst he
  refine ⟨s'.total, ?_, ?_⟩
  · unfold sum
    change Zig.loop (sum.loop10 xs (Zig.len xs)) sum.again10 { total := 0, local5 := 0 }
      = some (Except.ok (sumExit.br9, s')) at hrun
    simp only [StateT.run', bind, pure, StateT.bind, StateT.pure,
      ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.map, Functor.map,
      modify, modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Option.bind]
    rw [hrun]
    simp [zig_unfold]
  · rw [hpost, psum, List.take_of_length_le (by simp)]
