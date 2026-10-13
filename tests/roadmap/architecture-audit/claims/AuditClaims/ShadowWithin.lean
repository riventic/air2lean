import AuditClaims.Gen

/-!
S2/H2: a contract defines a second registered claim head that `ZigLean` does not import, from a
different defining module than `Shadow.lean`'s: the total thread triple `Zig.Full.FTTotalTriple`
(`ZigLean.Sep.Full.Thread`). The audit environment imports every registered head
(`tools/Assurance.lean`), so the audit fails with a name clash; and the head's pinned module and
fingerprint would still distinguish this declaration from the real one.
-/

namespace Zig.Full

def FTTotalTriple {α : Type} (_P : Prop) (_c : Result α) (_Q : α → Prop) : Prop := True

end Zig.Full

namespace AuditClaims

theorem spoofed_within (x : BitVec 8) : Zig.Full.FTTotalTriple True (root x) (fun _ => False) := trivial

end AuditClaims
