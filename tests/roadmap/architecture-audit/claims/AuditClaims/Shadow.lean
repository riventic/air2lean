import AuditClaims.Gen

/-!
C8: head-constant spoofing. `AuditClaims.Gen` (like every real `Gen.lean`) imports only `ZigLean`,
which does not define `Zig.TotalTriple`. A contract audited with `--module` (as
`scripts/project.py check` does) can therefore declare its own `Zig.TotalTriple`, and
`scripts/claims.py` classifies by the exact kernel *name* only.
-/

namespace Zig

def TotalTriple {α : Type} (_P : Prop) (_c : Result α) (_Q : α → Prop) : Prop := True

end Zig

namespace AuditClaims

/-- Classified `total_correctness` and bound `direct` to `root`, although `root 255` panics. -/
theorem spoofed_total : Zig.TotalTriple True (root 255) (fun _ => False) := trivial

end AuditClaims
