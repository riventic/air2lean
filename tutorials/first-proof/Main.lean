import Proofs.Basic.Proofs

/-!
First proof: an on-time job has zero tardiness.

From the repository root:
  lake build Proofs.Basic.Proofs
  lake env lean tutorials/first-proof/Main.lean

See docs/getting-started.md for the source, model, and exercise.
-/

namespace FirstProof

open Basic

/-- If a job finishes by its due time, it returns zero without panicking. -/
theorem on_time_zero (endTime due : BitVec 32)
    (onTime : endTime.toNat ≤ due.toNat) :
    tardiness endTime due = pure 0 := by
  rw [tardiness_spec]
  simp [Nat.not_lt.mpr onTime]

end FirstProof
