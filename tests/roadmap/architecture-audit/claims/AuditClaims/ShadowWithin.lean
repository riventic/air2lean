import AuditClaims.Gen

/-!
S2/H2: a contract defines a claim head that the audit environment does not import, so there is
no name clash: `Zig.TotalTripleWithin` (the bounded total head of `codex/roadmap-batch8`, not on
this branch). It is unregistered here (unclassified); once registered, its pinned module and
fingerprint still distinguish this declaration from the real one.
-/

namespace Zig

def TotalTripleWithin {α : Type} (_B : Nat) (_P : Prop) (_c : Result α) (_Q : α → Prop) : Prop := True

end Zig

namespace AuditClaims

theorem spoofed_within (x : BitVec 8) : Zig.TotalTripleWithin 0 True (root x) (fun _ => False) := trivial

end AuditClaims
