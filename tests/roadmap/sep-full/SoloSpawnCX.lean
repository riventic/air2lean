import ZigLean.Sep.Full.Conc
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Witness

/-!
# A non-solo op has no in-thread reading: regressions (`docs/architecture-audit/structure-2026-10-13.md` #1)

`CTriple P x Q` reads `x` in the caller's thread (`Sched.soloTree`). Only a solo op (`yield`, a
`choose`, an oracle `pick`) has an answer there (`Sched.soloResp`). A spawn, a join, a futex wait
or wake, a gate or an async choice has none, and the reading fails closed with `.illegal`. Before
the fix the reading answered a spawn with `.ok 0` (the caller's id) and a join or a wait at once,
so `CTriple emp (sync (.spawn t)) (fun r => ⟪r = .ok 0⟫)` was provable, although natively a spawn
never returns the caller's id and the spawned thread runs.

1. `spawn_illegal`: the in-thread reading of a spawn is `.illegal`.
2. `no_triple`: no `CTriple` with an admissible precondition (`FAdmit`) holds across a non-solo
   op, whatever its postcondition.
3. `no_spawn_triple`: the old statement is false:
   `¬ CTriple emp (sync (.spawn t)) (fun r => ⟪r = .ok 0⟫)`.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.SoloSpawnCX

open Zig Zig.Full Zig.Full.FAssn Zig.Sched Zig.Witness

/-- **The in-thread reading of a spawn fails closed.** -/
theorem spawn_illegal {Tgt : Type} (t : Tgt) (n : Nat) (m : Mem) :
    ((soloRun (n + 1) (ConcM.sync (.spawn t) : ConcM Tgt (Except ErrName ThreadId))).run m).run =
      some (.error .illegal) := rfl

/-- **No `CTriple` with an admissible precondition holds across a non-solo op.** -/
theorem no_triple {Tgt : Type} (op : SyncOp Tgt) (hop : SyncOp.Solo op = false) {P : FAssn}
    {Q : op.Resp → FAssn} (hP : FAdmit P) : ¬ CTriple P (ConcM.sync op) Q := by
  intro h
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := hP
  have := h 1 m r rF hh hp hs
  rw [CTriple.run_eq] at this
  have e : soloTree (ConcM.sync op 1 m) = some (.error .illegal) :=
    soloTree_none (soloResp_eq_none hop)
  rw [e] at this
  cases this

/-- The memory at program start with no globals holds `emp`. -/
theorem emp_admit : FAdmit emp := by
  have h := (initRes_holds Placement.fresh [] (by simp)).1
  exact ⟨_, _, _, h, ⟨rfl, rfl, rfl⟩, Mem.init_fseq _ [] (by decide), trivial⟩

/-- **The old statement is false**: a spawn does not return the caller's id. -/
theorem no_spawn_triple {Tgt : Type} (t : Tgt) :
    ¬ CTriple FAssn.emp (ConcM.sync (.spawn t) : ConcM Tgt (Except ErrName ThreadId))
      (fun r => ⟪r = .ok 0⟫) :=
  no_triple (.spawn t) rfl emp_admit

end Zig.Full.SoloSpawnCX

#print axioms Zig.Full.SoloSpawnCX.spawn_illegal
#print axioms Zig.Full.SoloSpawnCX.no_triple
#print axioms Zig.Full.SoloSpawnCX.no_spawn_triple
