import Proofs.Basic.Proofs

/-! Negative control: Lean must reject this file. An on-time job has tardiness 0, not 1, so
the proof of `on_time_zero` cannot establish `pure 1`. -/
-- expect-error: unsolved goals

namespace FirstProof

open Basic

/-- If a job finishes by its due time, it returns zero without panicking. -/
theorem on_time_zero (endTime due : BitVec 32)
    (onTime : endTime.toNat ≤ due.toNat) :
    tardiness endTime due = pure 1 := by
  rw [tardiness_spec]
  simp [Nat.not_lt.mpr onTime]

end FirstProof
