import Proofs.Atomics.PtrPublish
import ZigLean.Conc.Returns

/-!
# Pointer publication returns within 6 turns (P05, P06)

`publishRead` (`Proofs/Atomics/PtrPublish.lean`) synchronizes through a release store and an
acquire load of an atomic pointer slot, and a join. Every schedule returns 0 or 42 within
**6 scheduler turns** (`publishRead_returnsWithin`): `Proto.returnsWithin`
(`ZigLean/Conc/Returns.lean`) on the strict protocol proof (`main_spec`, `dispatch_spec`) and
turn budgets that `stops` walks: the producer has one stop (its release store, budget 1), and
`main` spawns it (`1 + 2`), loads the slot twice (one turn each) and joins (one turn). The
allocator's `create`/`destroy` and every memory step have a result (`MemM.Halts`). The rely is
`True`; no fairness premise: the bound holds for every oracle. Turns are model scheduler turns
(THR-01), not time (SEM-05).
-/

open Zig Zig.Conc Atomics.PtrPublish

namespace Atomics.PtrPublish.Termination

theorem producer_stops (s : Ptr) (m : Mem) :
    Stops (fun _ => True) dispatch (dispatch (.producer s)) (fun _ _ _ => True) m 1 := by
  show Stops _ _ (producer s) _ _ _
  unfold producer; stops

theorem publishRead_stops (m : Mem) :
    Stops (fun _ => True) dispatch publishRead (fun _ _ _ => True) m 6 := by
  have := producer_stops
  unfold publishRead; stops

/-- **`publishRead` returns 0 or 42 within 6 turns under every schedule** (`available`
spawns). -/
theorem publishRead_returnsWithin (env : Env) (henv : env.spawn = .available) :
    Total.ReturnsWithin 6 env dispatch publishRead mem0 (fun v _ => v = 0 ∨ v = 42) := by
  intro o fuel hf
  obtain ⟨v, m', hr, G, d, hq⟩ := proto.returnsWithin env (Proto.of_available henv) dispatch G0
    rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl main_spec (R := fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ _ => trivial) (publishRead_stops _) o fuel hf
  exact ⟨v, m', hr, hq.1⟩

end Atomics.PtrPublish.Termination
