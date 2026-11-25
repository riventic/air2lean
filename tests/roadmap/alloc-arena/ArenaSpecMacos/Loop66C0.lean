import ArenaSpecMacos.Retain

/-!
# `ArenaSpecMacos`: `loop66`'s body for the first list

`loop66_c0` of `ArenaSpecMacos.lean`, in its own module so that it builds in parallel with
`loop66_c1` (`ArenaSpecMacos/Loop66C1.lean`).
-/

namespace AllocArena.ArenaSpecMacos

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaMacos

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

attribute [local fsym_facts] MemFacts.region_end

include h in
set_option maxHeartbeats 2650000 in
/-- `loop66`'s body for the first list (`ArenaSpec.loop66_c0`; ledger #undecided-eq-branch-cost). -/
theorem loop66_c0 (hfit : CI.FitsUpTo (2 ^ 63) 3) (pu pf : Ptr) (xu xf : Option Ptr)
    (v0 v1 : BitVec 64) (hv0 : v0.toNat + 24 ≤ 2 ^ 63) (ok : Bool) (it : Option Ptr) :
    CTriple (Tgt := Tgt) (Inv66 CI ctx Ac Sc Kc pu pf xu xf ⟨ok, 0, it⟩)
      ((heap_ArenaAllocator_reset.loop66 ctx #v[pu, pf] #v[v0, v1]).run ⟨ok, 0, it⟩)
      (fun r => if heap_ArenaAllocator_reset.again66 r.1 then Inv66 CI ctx Ac Sc Kc pu pf xu xf r.2
        else Exit66 CI ctx Ac Sc Kc pu pf r) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset.loop66
  by_cases hsm : v0.toNat < 2 <;>
    fsym [loop78_ct CI h ctx Ac Sc Kc, CAllocSpec.free' h, CAllocSpec.alloc_upTo h hfit,
      CAllocSpec.resize_upTo h hfit, Child.cown_refund,
      FTotalTriple.region_storePacked_wpts, FTotalTriple.region_store_wpts,
      FTotalTriple.region_storeAll]

end Retain

end AllocArena.ArenaSpecMacos
