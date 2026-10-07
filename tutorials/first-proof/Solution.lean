import Proofs.Basic.Proofs

/-! Exercise solution: a job that finishes exactly at its due time has zero tardiness. -/

namespace FirstProof

open Basic

/-- If a job finishes by its due time, it returns zero without panicking. -/
theorem on_time_zero (endTime due : BitVec 32)
    (onTime : endTime.toNat ≤ due.toNat) :
    tardiness endTime due = pure 0 := by
  rw [tardiness_spec]
  simp [Nat.not_lt.mpr onTime]

theorem exactly_on_time (endTime due : BitVec 32)
    (sameTime : endTime.toNat = due.toNat) :
    tardiness endTime due = pure 0 := by
  exact on_time_zero endTime due (Nat.le_of_eq sameTime)

end FirstProof
