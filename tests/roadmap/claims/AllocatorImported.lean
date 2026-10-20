import tests.roadmap.claims.AllocatorApplications

/-! A selected client imports its concrete contract and creation companions from another module.
Opt-in declaration auditing must retain those reported roots without calling them selected. -/

open Zig Zig.Full Zig.Full.FAssn Zig.Witness

namespace AllocatorImported

def unusedValue : Nat := 37

theorem client (ha : FAdmit ⟪(0 : Nat) = 0⟫) :
    FTotalTriple emp (pure ()) (fun _ => emp) :=
  AllocatorApplications.exact_parameter 0 ha

nonvacuity_witness client := ⟨AllocatorApplications.admit_zero, FAdmit.of_emp⟩

end AllocatorImported
