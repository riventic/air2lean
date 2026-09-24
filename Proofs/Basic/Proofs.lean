import Proofs.Basic.Gen

/-!
# Proofs about `examples/basic/basic.zig`

Each theorem is about the generated code in `Gen.lean`, so it holds for the Zig function to the
extent the translation is faithful (see the differential tests in `tests/diff/`).
-/

open Basic

-- Unfold the `StateT`/`ExceptT`/`Option` layers of generated code down to plain values.
attribute [local simp] StateT.run' StateT.run bind pure StateT.bind StateT.pure StateT.map
  ExceptT.bind ExceptT.pure ExceptT.mk ExceptT.bindCont ExceptT.map Functor.map liftM monadLift
  MonadLift.monadLift StateT.lift throw throwThe MonadExcept.throw MonadExceptOf.throw ExceptT.lift
  Option.bind get getThe MonadState.get MonadStateOf.get StateT.get modify modifyGet
  MonadState.modifyGet MonadStateOf.modifyGet StateT.modifyGet Zig.call

theorem tardiness_spec (a b : BitVec 32) :
    tardiness a b = pure (if b.toNat < a.toNat then a - b else 0) := by
  unfold tardiness
  by_cases h : b.toNat < a.toNat
  · have : ¬ a.toNat < b.toNat := by omega
    simp [h, this]
  · simp [h]

theorem scale_spec (a : BitVec 32) (b : BitVec 8) :
    scale a b = if a.toNat * b.toNat ≥ 2 ^ 32 then throw .overflow
                else pure (a * b.setWidth 32) := by
  unfold scale
  have hb : b.toNat % 4294967296 = b.toNat := Nat.mod_eq_of_lt (by have := b.isLt; omega)
  by_cases h : a.toNat * b.toNat ≥ 2 ^ 32
  · have h' : 4294967296 ≤ a.toNat * b.toNat := h
    simp [hb, h']
  · have h' : ¬ 4294967296 ≤ a.toNat * b.toNat := h
    simp [hb, h']

theorem classify_le_two (x : BitVec 8) : ∃ r, classify x = pure r ∧ r.toNat ≤ 2 := by
  unfold classify
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0], by decide⟩
  · have h0' : ¬ x = 0#8 := h0
    by_cases h9 : x.toNat ≤ 9
    · refine ⟨1, ?_, by decide⟩
      have h1 : 1 ≤ x.toNat := by
        have : x.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      simp [h0', Zig.le, BitVec.ule, h1, h9]
    · refine ⟨2, ?_, by decide⟩
      simp [h0', Zig.le, BitVec.ule, h9]

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
      simp [tardiness_spec, hadd, hsum, hlt, hwm, hm]
    · rw [BitVec.toNat_mul, BitVec.toNat_setWidth, hsub, Nat.mod_eq_of_lt (a := j.weight.toNat) (by omega)]
      exact Nat.mod_eq_of_lt h2
  · refine ⟨0, ?_, ?_⟩
    · simp [tardiness_spec, hadd, hsum, hlt, hwm]
    · have hz : start.toNat + j.duration.toNat - j.due.toNat = 0 := by omega
      simp [hz]
