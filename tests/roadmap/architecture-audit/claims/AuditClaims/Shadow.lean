import AuditClaims.Gen

/-!
C8: head-constant spoofing. `AuditClaims.Gen` (like every real `Gen.lean`) imports only `ZigLean`,
which does not define `Zig.Full.FTotalTriple`. A contract audited with `--module` (as
`scripts/project.py check` does) can therefore declare its own `Zig.Full.FTotalTriple`, and
`scripts/claims.py` classified by the exact kernel *name* only.
-/

namespace Zig.Full

def FTotalTriple {α : Type} (_P : Prop) (_c : Result α) (_Q : α → Prop) : Prop := True

end Zig.Full

namespace AuditClaims

/-- Classified `total_correctness` and bound `direct` to `root`, although `root 255` panics. -/
theorem spoofed_total : Zig.Full.FTotalTriple True (root 255) (fun _ => False) := trivial

end AuditClaims
