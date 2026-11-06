import ZigLean.Mem.Basic

/-!
# The value or the error of a run

Readers of a finished run, for statements about one schedule: `Witness.okVal` is the `u32` of a
run of a function `!u32`, `Witness.errOf` the error a run ends in. The kernel computes goals
stated with them once the run's loops are unfolded (`docs/proof-tools.md`, concrete runs of
programs with loops).
-/

namespace Zig.Witness

/-- The `u32` of a run of a function `!u32`: a completed run of a concurrent program, for a
statement about one schedule. -/
def okVal (r : Result (Except ErrName (BitVec 32) × Mem)) : Option Nat :=
  match r.run with
  | some (.ok (.ok v, _)) => some v.toNat
  | _ => none

/-- The error of a run, if it ends in one: for a statement that a schedule fails. -/
def errOf {α : Type} (r : Result α) : Option Error :=
  match r.run with
  | some (.error e) => some e
  | _ => none

theorem errOf_eq_some {α : Type} {r : Result α} {e : Error} : errOf r = some e ↔ r.run = some (.error e) := by
  unfold errOf
  split <;> simp_all

end Zig.Witness
