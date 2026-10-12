import Proofs.Threads.Disjoint
import ZigLean.Conc.Returns

/-!
# Concurrent termination and turn cost (P05, P06)

Every schedule of the generated `disjoint a b` returns `a + b` (wrapping) within **6 scheduler
turns** (`disjoint_returnsWithin`), and 6 is tight (`disjoint_not_within_five`). The proof is
`Proto.returnsWithin` (`ZigLean/Conc/Returns.lean`): the strict protocol proof of
`Proofs/Threads/Disjoint.lean` (no error, no deadlock, the result) and turn budgets that `stops`
walks from the generated code: `writeFlag` has no stop (budget 0), `main` spawns twice
(`0 + 2` each: the spawn, the kid's first turn) and joins twice. The rely is `True`: no budget
depends on memory. No fairness premise: the bound holds for every oracle. Turns are model
scheduler turns (THR-01), not time (SEM-05).
-/

open Zig Zig.Conc Threads

namespace Threads.Termination

theorem writeFlag_stops (c : Ptr) (m : Mem) :
    Stops (fun _ => True) dispatch (dispatch (.writeFlag c)) (fun _ _ _ => True) m 0 := by
  unfold dispatch; stops

theorem disjoint_stops (a b : BitVec 32) (m : Mem) :
    Stops (fun _ => True) dispatch (disjoint a b) (fun _ _ _ => True) m 6 := by
  have := writeFlag_stops
  unfold disjoint; stops

/-- **`disjoint a b` returns `a + b` within 6 turns under every schedule** (`available`
spawns). -/
theorem disjoint_returnsWithin (env : Env) (henv : env.spawn = .available) (σ : Placement)
    (a b : BitVec 32) :
    Total.ReturnsWithin 6 env dispatch (disjoint a b) (mem0 σ) (fun v _ => v = .ok (a + b)) := by
  intro o fuel hf
  obtain ⟨v, m', hr, G, d, hq⟩ := (Disjoint.proto a b).returnsWithin env
    (Proto.of_available henv) dispatch (fun _ => .none) rfl Disjoint.dispatch_spec
    (fun _ _ _ _ hq => hq.2) rfl (Disjoint.main_spec σ) (R := fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (disjoint_stops a b _) o fuel hf
  exact ⟨v, m', hr, hq.1⟩

/-- The bound is tight: the schedule that always picks option 0 needs a sixth turn. The kernel
computes the run. -/
theorem disjoint_not_within_five :
    ¬ Total.ReturnsWithin 5 ⟨.any, .available⟩ dispatch (disjoint 1 2) (mem0 .fresh)
      (fun _ _ => True) := by
  intro h
  obtain ⟨v, m', hr, -⟩ := h (fun _ => 0) 5 (Nat.le_refl _)
  have : (Sched.run ⟨.any, .available⟩ dispatch 5 (fun _ => 0) (disjoint 1 2) (mem0 .fresh)).run.isNone
    = true := by decide +kernel
  rw [hr] at this
  cases this

end Threads.Termination
