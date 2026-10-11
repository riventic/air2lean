import ZigLean

/-!
Stand-in for a translated module (architecture audit, area 4). Same shape as a real `Gen.lean`:
it imports only `ZigLean`, which does not provide `Zig.Triple`/`Zig.TotalTriple`/`Zig.Returns`.

`root x` panics (`.overflow`) at `x = 255` and returns `x + 1` otherwise. `spin` never returns.
A sound claim layer must not report `root` as totally correct for all inputs, nor `spin` as
functionally verified.
-/

namespace AuditClaims

def root (x : BitVec 8) : Zig.Result (BitVec 8) := Zig.add false x 1

def spin : Zig.MemM Unit := fun _ => ExceptT.mk none

end AuditClaims
