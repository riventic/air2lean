import ArenaSpec.Retain

/-!
# `ArenaSpec`: `loop66`'s body for the second list

`loop66_c1` of `ArenaSpec.lean` (`reset`'s retaining modes, `ArenaSpec/Retain.lean`), in its own
module so that it builds in parallel with `loop66_c0` (`ArenaSpec/Loop66C0.lean`).
-/

namespace AllocArena.ArenaSpec

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

attribute [local fsym_facts] MemFacts.region_end

include h in
set_option maxHeartbeats 3100000 in
/-- One run of `loop66`'s body for the second list (`limits[1]`, `v1`), as `loop66_c0`. -/
theorem loop66_c1 (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv1 : v1.toNat + 24 ≤ 2 ^ 63) (ok : Bool) (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 1, it⟩)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run ⟨ok, 1, it⟩)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset.loop66
  by_cases hsm : v1.toNat < 2 <;>
    fsym [loop78_ct CI h ctx Ac Sc Kc, CAllocSpec.free' h, CAllocSpec.alloc_upTo h hfit,
      CAllocSpec.resize_upTo h hfit, Child.cown_refund,
      FTotalTriple.region_storePacked_wpts, FTotalTriple.region_store_wpts,
      FTotalTriple.region_storeAll]

end Retain

end AllocArena.ArenaSpec
