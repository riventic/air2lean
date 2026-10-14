import AllocArena.ArenaMacos
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-!
# The stock `ArenaAllocator` on aarch64-macos: `free`, `resize` and `remap` against `FAllocSpec`

The statements of `ArenaSpec.lean` for the aarch64-macos translation (`AllocArena/ArenaMacos.lean`),
proved by the same tactics (`AllocArena.Core`), and `deinit` and `reset(.free_all)` walked by
`fsym` as in `ArenaSpec.lean`.
-/

namespace AllocArena.ArenaSpecMacos

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaMacos

arena_spec_statements

/-! ## `deinit` and `reset` (as in `ArenaSpec.lean`) -/

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

/-- The module's allocators: the entries that an indirect call through the child's vtable can
reach. -/
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

set_option maxHeartbeats 2000000 in
/-- `countListCapacity`'s loop, by induction on the list (`ArenaSpec.count_loop`). -/
theorem count_loop (CI : Child) (free : Bool) :
    ∀ (ns : List NodeV) (it : Option Ptr) (c : BitVec 64),
      FTotalTriple (⟪c.toNat + capOf ns < 2 ^ 64⟫ ⋆ Chain CI free ns it)
        ((Zig.loop heap_ArenaAllocator_countListCapacity.loop6
          heap_ArenaAllocator_countListCapacity.again6).run ⟨c, it⟩)
        (fun r => FAssn.ex fun c' : BitVec 64 =>
          ⟪r = (.br5, ⟨c', none⟩) ∧ c'.toNat = c.toNat + capOf ns⟫ ⋆ Chain CI free ns it)
  | [], none, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def]
  | nd :: ns, some N, c => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, toInt_step, count_loop CI free]
  | [], some _, _ | _ :: _, none, _ => by
    rw [Full.loop_run]
    conv in StateT.run heap_ArenaAllocator_countListCapacity.loop6 _ =>
      rw [heap_ArenaAllocator_countListCapacity.loop6]
    fsym

/-- **`countListCapacity`** of a list of whole nodes (`ArenaSpec.count_spec`). -/
theorem count_spec (CI : Child) (ns : List NodeV) (x : Option Ptr) :
    FTotalTriple (Chain CI true ns x) (heap_ArenaAllocator_countListCapacity x)
      (fun c => ⟪c.toNat = capOf ns ∧ capOf ns + 24 ≤ 2 ^ 63⟫ ⋆ Chain CI true ns x) :=
  MemFacts.pre FLogic.total (chain_capOf_le CI ns x) fun _ => by
    unfold heap_ArenaAllocator_countListCapacity
    fsym [count_loop CI true]

section Deinit

variable (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)

def Inv19 (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun ns : List NodeV => ⟪s.local1 = l⟫ ⋆
    (Chain CI true (ns.map NodeV.full) s.it ⋆ FreeCl CI ns ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

def Exit19 (l : BitVec 64) (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) :
    FAssn :=
  ⟪r = (.br18, ⟨l, none⟩)⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
theorem loop19_step (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s) ((heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩).run s)
      (fun r => if heap_ArenaAllocator_deinit.again19 r.1 then Inv19 CI l r.2 else Exit19 CI l r) := by
  refine CTriple.ex fun ns => ?_
  rcases s with ⟨l', it⟩
  unfold heap_ArenaAllocator_deinit.loop19
  cases ns <;> cases it <;> simp only [List.map_cons, List.map_nil] <;>
    fsym [CAllocSpec.free h, toInt_step, Child.cown_refund]

include h in
theorem loop19_ct (st : heap_ArenaAllocator_State) (l : BitVec 64) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv19 CI l s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop19 ⟨⟨CI.cctx, CI.vtp⟩, st⟩)
        heap_ArenaAllocator_deinit.again19).run s)
      (Exit19 CI l) :=
  CTriple.loop (Inv19 CI l) _ (loop19_step CI h st l) s

def Lists9 (used fl : Option Ptr) (k : BitVec 64) : FAssn :=
  if k = 0 then FreeList CI used ⋆ FreeList CI fl else if k = 1 then FreeList CI fl else emp

def Inv9 (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) : FAssn :=
  ⟪s.local1.toNat ≤ 2⟫ ⋆ (Lists9 CI used fl s.local1 ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))

def Exit9 (r : heap_ArenaAllocator_deinitExit × heap_ArenaAllocator_deinitLocals) : FAssn :=
  FAssn.ex fun s' => ⟪r = (.br8, s')⟫ ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList)

include h in
set_option maxHeartbeats 2000000 in
theorem loop9_step (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl]).run s)
      (fun r => if heap_ArenaAllocator_deinit.again9 r.1 then Inv9 CI used fl r.2 else Exit9 CI r) := by
  rcases s with ⟨l, it⟩
  unfold heap_ArenaAllocator_deinit.loop9
  obtain rfl | rfl | hl : l = 0 ∨ l = 1 ∨ 2 ≤ l.toNat := by bv_omega
  all_goals fsym [loop19_ct CI h]

include h in
theorem loop9_ct (used fl : Option Ptr) (s : heap_ArenaAllocator_deinitLocals) :
    CTriple (Tgt := Tgt) (Inv9 CI used fl s)
      ((Zig.loop (heap_ArenaAllocator_deinit.loop9 ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩ #v[used, fl])
        heap_ArenaAllocator_deinit.again9).run s)
      (Exit9 CI) :=
  CTriple.loop (Inv9 CI used fl) _ (loop9_step CI h used fl) s

include h in
set_option maxHeartbeats 2000000 in
/-- **`deinit` gives every node of both lists back to the child.** -/
theorem deinit_ct (used fl : Option Ptr) :
    CTriple (Tgt := Tgt) (FreeList CI used ⋆ FreeList CI fl ⋆ (CI.cown ⋆ vtR CI.vtp CI.fns.toList))
      (heap_ArenaAllocator_deinit ⟨⟨CI.cctx, CI.vtp⟩, ⟨used, fl⟩⟩)
      (fun _ => CI.cown ⋆ vtR CI.vtp CI.fns.toList) := by
  unfold heap_ArenaAllocator_deinit
  fsym [loop9_ct CI h]

end Deinit

section Reset

/-- The arena struct's load in a thread (`ArenaSpec.state_load`). -/
theorem state_load (CI : Child) (ctx : Ptr) (Ac Sc : Nat) (Kc : BlockKind) (first fl : Option Ptr)
    (h0 : 0 ≤ ctx.off) :
    FTTotalTriple (up (regionIn ctx Ac Sc Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) first ⋆ aptsE (ctx.add 24) fl)
      (load heap_ArenaAllocator 8 ctx)
      (fun v => ⟪v = ⟨⟨CI.cctx, CI.vtp⟩, ⟨first, fl⟩⟩⟫ ⋆
        (up (regionIn ctx Ac Sc Kc 8 CI.bytes) ⋆ aptsE (ctx.add 16) first ⋆ aptsE (ctx.add 24) fl)) := by
  have hd := child_decode CI
  refine FTTotalTriple.ofSeq (by fsym) (ThreadLocal.load ?_)
  have hX : OwnsPtr (up (regionIn ctx Ac Sc Kc 8 CI.bytes)) ctx 16 :=
    OwnsPtr.regionIn_in rfl (Int.le_refl _) (by rw [Child.bytes_size]; exact Nat.le_refl _)
  have hZ : OwnsPtr (aptsE (ctx.add 16) first ⋆ aptsE (ctx.add 24) fl)
      ((ctx.add 16).add ((8 : Nat) : Int)) 8 := by
    rw [show (ctx.add 16).add ((8 : Nat) : Int) = ctx.add 24 by
      simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega]
    exact OwnsPtr.aptsE.sepR
  have hYZ := OwnsPtr.join (by simp only [Ptr.add]; omega) OwnsPtr.aptsE.sepL hZ
  have hs : Enc.size heap_ArenaAllocator = 16 + (8 + 8) := rfl
  rw [hs]
  exact OwnsPtr.join h0 hX.sepL hYZ.sepR

/-- The store of the list heads in a thread (`ArenaSpec.heads_store`). -/
theorem heads_store (ctx : Ptr) (u f : Option Ptr) (st : heap_ArenaAllocator_State)
    (h0 : 0 ≤ (ctx.add 16).off) :
    FTTotalTriple (aptsE (ctx.add 16) u ⋆ aptsE (ctx.add 24) f) (store 8 (ctx.add 16) st)
      (fun _ => aptsE (ctx.add 16) st.used_list ⋆ aptsE (ctx.add 24) st.free_list) := by
  refine FTTotalTriple.ofSeq (by fsym) (ThreadLocal.store ?_)
  have hZ : OwnsPtr (aptsE (ctx.add 16) u ⋆ aptsE (ctx.add 24) f) ((ctx.add 16).add ((8 : Nat) : Int)) 8 := by
    rw [show (ctx.add 16).add ((8 : Nat) : Int) = ctx.add 24 by
      simp only [Ptr.add, Ptr.mk.injEq, true_and]; omega]
    exact OwnsPtr.aptsE.sepR
  have hs : (Enc.encode st).size = 8 + 8 :=
    fields_size (by simp only [partSizes, List.map, LawfulEnc.size_encode]; decide)
  rw [hs]
  exact OwnsPtr.join h0 OwnsPtr.aptsE.sepL hZ

set_option maxHeartbeats 2000000 in
theorem reset_free_all_ct (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one)) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [deinit_ct CI h, own_empty, state_load CI, heads_store]

/-- **`reset(.free_all)` meets the reset contract.** -/
theorem reset_free_all_spec (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_free_all_ct CI h γ e ctx)

end Reset

end AllocArena.ArenaSpecMacos

#print axioms AllocArena.ArenaSpecMacos.free_spec
#print axioms AllocArena.ArenaSpecMacos.resize_spec
#print axioms AllocArena.ArenaSpecMacos.remap_spec
#print axioms AllocArena.ArenaSpecMacos.deinit_ct
#print axioms AllocArena.ArenaSpecMacos.reset_free_all_spec
#print axioms AllocArena.ArenaSpecMacos.count_spec
