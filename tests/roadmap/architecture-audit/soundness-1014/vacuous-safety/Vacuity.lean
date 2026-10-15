import ZigLean
import ZigLean.Sep.Full.Logic

/-! Audit 2026-10-14, finding S1 (`probe.py`). Mirrors the shapes of
`tests/roadmap/architecture-audit/claims/AuditClaims/{Gen,Vacuous}.lean` and shows, kernel-checked,
that the theorems accepted by `scripts/claims.py check` as `safety` goals (scoped domain), and
counted by `project.py absence_claims` as `no-panic: proved`, are vacuous, while the root panics. -/

open Zig Zig.Full

namespace Audit1014.Vacuity

def root (x : BitVec 8) : Zig.Result (BitVec 8) := Zig.add false x 1
def spin : Zig.MemM Unit := fun _ => ExceptT.mk none

/-- Same statement as `AuditClaims.unsat_pre`. -/
theorem unsat_pre (x : BitVec 8) (hx : x.toNat > 300) : root x = pure (x + 1) := by
  have := x.isLt; omega

/-- Its premise telescope is empty: the `nonvacuity` companion statement is false. -/
theorem unsat_pre_vacuous : ¬ ∃ (x : BitVec 8), x.toNat > 300 := by
  rintro ⟨x, hx⟩; have := x.isLt; omega

/-- And the root does panic: `no-panic` is false for `root`. -/
theorem root_panics : root 255 = throw Error.overflow := by
  have h : BitVec.uaddOverflow (255 : BitVec 8) 1 = true := by decide
  unfold root; simp only [Zig.add, Bool.false_eq_true, ite_false, h, ite_true, Zig.Error.ifSafe_true]

/-- Same statement as `AuditClaims.total_false_pre`. -/
theorem total_false_pre (Q : Unit → FAssn) : FTotalTriple (fun _ => False) spin Q :=
  ⟨fun _ _ _ _ hp _ => hp.elim, fun _ _ _ _ hp _ => hp.elim⟩

/-- Its precondition holds in no memory (so its `.nonvacuous` companion is false). -/
theorem total_false_pre_vacuous : ¬ ∃ (m : Mem) (r rF : Res), Holds m r rF ∧ (fun _ => False) r ∧ m.FSeq :=
  fun ⟨_, _, _, _, h, _⟩ => h

/-- `spin` never returns from any memory. -/
theorem spin_never (m : Mem) : (spin.run m).run = none := rfl

end Audit1014.Vacuity

#print axioms Audit1014.Vacuity.unsat_pre_vacuous
#print axioms Audit1014.Vacuity.root_panics
#print axioms Audit1014.Vacuity.total_false_pre_vacuous
#print axioms Audit1014.Vacuity.spin_never
