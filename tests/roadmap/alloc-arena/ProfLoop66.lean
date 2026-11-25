import AllocArena.ArenaLinux
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-! SCRATCH (lane fsym-profile, never merged): `ArenaSpec.loop66_c0` alone, for profiling. -/

namespace AllocArena.ProfLoop66

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaLinux

def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

def tables : AllocTables Tgt where
  alloc := [(⟨some 3, 0⟩, fun a => heap_PageAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 8, 0⟩, fun a => heap_ArenaAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 12, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_alloc a.1 a.2.1 (al a.2.2.1) a.2.2.2))]
  resize := [(⟨some 4, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 9, 0⟩, fun a => heap_ArenaAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 13, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_resize a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  remap := [(⟨some 5, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2)),
    (⟨some 10, 0⟩, fun a => heap_ArenaAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2),
    (⟨some 14, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_remap a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2))]
  free := [(⟨some 6, 0⟩, fun a => ConcM.liftMem (heap_PageAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2)),
    (⟨some 11, 0⟩, fun a => heap_ArenaAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2),
    (⟨some 15, 0⟩, fun a => ConcM.liftMem (heap_FixedBufferAllocator_free a.1 a.2.1 (al a.2.2.1) a.2.2.2))]

theorem child_decode (CI : Child) : Enc.decode CI.bytes = pure (⟨CI.cctx, CI.vtp⟩ : mem_Allocator) := by
  simp only [Enc.decode, Child.decodeAt0, Child.decodeAt8]; rfl

section Retain

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
  (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind)

def Exit78 (p : Ptr) (x0 : Option Ptr) :
    heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals → FAssn
  | (.br77 N, _) => aptsE p x0 ⋆ Last CI N ⋆ Cm CI ctx Ac Sc Kc ⋆ plain
  | (.br68, _) => ⟪x0 = none⟫ ⋆ (aptsE p x0 ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)
  | _ => ⟪False⟫

include h in
theorem loop78_ct (p : Ptr) (x : Option Ptr) (ok : Bool) (l : BitVec 64) :
    CTriple (Tgt := Tgt) (aptsE p x ⋆ FreeList CI x ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)
      ((Zig.loop (heap_ArenaAllocator_reset.loop78 ctx) heap_ArenaAllocator_reset.again78).run ⟨ok, l, x⟩)
      (fun r => FAssn.ex fun e => FAssn.ex fun s' => ⟪r = (e, s')⟫ ⋆ Exit78 CI ctx Ac Sc Kc p x (e, s')) := by
  sorry

attribute [local fsym_facts] MemFacts.region_end

def Inv66 (pu pf : Ptr) (xu xf : Option Ptr) (s : heap_ArenaAllocator_resetLocals) : FAssn :=
  ⟪s.local55.toNat ≤ 2⟫ ⋆ (Lst CI (decide (0 < s.local55.toNat)) pu xu ⋆
    Lst CI (decide (1 < s.local55.toNat)) pf xf ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)

def Exit66 (pu pf : Ptr) (r : heap_ArenaAllocator_resetExit × heap_ArenaAllocator_resetLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br65, s')⟫ ⋆ (KeptAt CI pu ⋆ KeptAt CI pf ⋆ Cm CI ctx Ac Sc Kc ⋆ plain)

include h in
set_option maxHeartbeats 2650000 in
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
      CAllocSpec.resize_shrink h hfit, CAllocSpec.resize_grow h hfit, Child.cown_refund,
      FTotalTriple.region_storePacked_wpts, FTotalTriple.region_store_wpts,
      FTotalTriple.region_storeAll]

end Retain

end AllocArena.ProfLoop66
