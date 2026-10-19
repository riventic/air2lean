import ZigLean.Mem.Witness
import ZigLean.Sep.Cost

/-!
# Non-vacuity witnesses: legacy loop counts

Concrete arguments for the premises of `LoopRuns.run` (`ZigLean/Sep/Cost.lean`,
`docs/claim-strength.md`), retired with the tick-cost lane (L8, `docs/legacy-retirement.md`).
The legacy triple rules (`Triple`, `TotalTriple`) have none: their heads are reserved claim-head
names, so no claim rests on them.
-/

namespace Zig.Witness

/-- A loop whose body leaves at once. -/
abbrev exitBody : MM Unit Unit := pure ()

nonvacuity_witness LoopRuns.run :=
  ⟨Unit, Unit, exitBody, fun _ => false, (), {}, 1, (), (), {}, LoopRuns.exit rfl rfl, trivial⟩

end Zig.Witness
