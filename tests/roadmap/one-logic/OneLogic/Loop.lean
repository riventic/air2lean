import ZigLean.Sep.Full.AutoAll

/-!
# Loops in the full-state logic (`ZigLean/Sep/Full/Loop.lean`), library-only

A generated-style loop over its locals: the body's step is proved by `fsym`, the loop by the
library's rules (total: a measure on the locals; partial: the invariant alone).
-/

namespace OneLogic.Loop

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Count a word down to zero: `while (n != 0) n -= 1`. -/
def body : MM (BitVec 64) Bool := do
  let n ← get
  if n == 0 then pure false
  else
    let n' ← callR (Zig.sub false n 1)
    set n'
    pure true

/-- One run of the body keeps `R`; a repeat makes the counter smaller. -/
theorem body_step (R : FAssn) : ∀ s : BitVec 64, FTotalTriple R (body.run s)
    (fun r => if (fun b : Bool => b) r.1 then ⟪r.2.toNat < s.toNat⟫ ⋆ R else ⟪r.2 = 0⟫ ⋆ R) := by
  intro s
  unfold body
  fsym

/-- The loop returns, with the counter at zero (total correctness, measure on the locals). -/
theorem loop_total (R : FAssn) (s : BitVec 64) :
    FTotalTriple R ((Zig.loop body fun b : Bool => b).run s) (fun r => ⟪r.2 = 0⟫ ⋆ R) :=
  FTotalTriple.loop_measure (fun _ => R) BitVec.toNat (fun r => ⟪r.2 = 0⟫ ⋆ R) (body_step R) s

/-- Partial correctness from the invariant alone (fixpoint induction). -/
theorem loop_partial (R : FAssn) (s : BitVec 64) :
    FTriple R ((Zig.loop body fun b : Bool => b).run s) (fun _ => R) :=
  FTriple.loop (fun _ => R) (fun _ => R)
    (fun s => (body_step R s).toPartial.post fun r _ h => by
      by_cases hb : r.1 <;> simp only [hb, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
        exact (sep_lift.mp h).2) s

end OneLogic.Loop
