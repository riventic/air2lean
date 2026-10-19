import AllocArena.ArenaFixedLinux
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-!
# The patched `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

The same statements as `ArenaSpec.lean` for the arena of `upstream/arena-fix.patch`
(`AllocArena/ArenaFixedLinux.lean`), with the same invariant (`AllocArena.Core`). The patched
`free` and `resize` load the node's size after `end_index` and return when `end_index` is past
the buffer (a racing `alloc`'s reservation, `docs/upstream/arena-oob-gep.md`); the invariant keeps
`end_index` within the buffer, so they go on as the stock ones do (`fsym` decides the check from
`OV.FirstFacts`: `24 + ei ≤ sz`). The proofs are those of `ArenaSpec.lean`. `deinit` and
`reset(.free_all)` are the stock ones, walked by `fsym` as in `ArenaSpec.lean`.
-/

namespace AllocArena.ArenaSpecFixed

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaFixedLinux

/-! ## `free`, `resize` and `remap` (as in `ArenaSpec.lean`) -/

set_option maxHeartbeats 2000000 in
/-- `free`'s run, case by case (`ArenaSpec.free_ct`), with the bounds check. -/
theorem free_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra)
      (fun _ => (inv CI γ e ctx).own ⋆ (inv CI γ e ctx).fee φ) := by
  unfold heap_ArenaAllocator_free
  fsym [free_other_upd, free_last_upd]

/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child `CI` (`Child`), and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own ⋆ (inv CI γ e ctx).fee φ) :=
  (free_ct CI γ e ctx s k ra φ bs hlen hpos).toSolo fuel

set_option maxHeartbeats 10000000 in
/-- `resize`'s run, case by case (`ArenaSpec.resize_ct`), with the bounds check. -/
theorem resize_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hpos : 0 < s.len.toNat)
    (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' φ ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  unfold heap_ArenaAllocator_resize
  rcases Nat.lt_trichotomy n.toNat s.len.toNat with hc | hc | hc <;>
  fsym [resize_other_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_shrink_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_grow_upd (S := S) (k := k) (n := n.toNat) (tl := tl),
    resize_false_upd (S := S) (k := k) (n := n.toNat) (tl := tl)]

/-- The whole-region `resize` (`FAllocInv.resize_granted_of`). -/
theorem resize_granted_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k φ bs n.toNat) :=
  (inv CI γ e ctx).resize_granted_gen (T := CTriple) (fun h hp => CTriple.pre h hp)
    (fun h => CTriple.frame h) (fun h => CTriple.ex h) (fun h hu => CTriple.eupd_post h hu)
    (fun A S K q q' tl h1 _ => resize_ct CI γ e ctx s k n ra A S K q q' φ tl (by omega) hn h1) hlen

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k φ bs n.toNat) := by
  unfold heap_ArenaAllocator_remap
  fsym [resize_granted_ct CI γ e ctx s k n ra φ bs hlen hpos hn]

/-- **`resize` meets `FAllocSpec`'s refined `resize` field** for the arena invariant at every
epoch, every child `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte)
    (hpos : 0 < s.len.toNat) (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' φ ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) :=
  (resize_ct CI γ e ctx s k n ra A S K q q' φ tl hpos hn hq).toSolo fuel

/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : Child) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (φ : Frac) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k φ bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k φ bs n.toNat) :=
  (remap_ct CI γ e ctx s k n ra φ bs hlen hpos hn).toSolo fuel

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
    fsym [heap_ArenaAllocator_countListCapacity.again6.eq_def, count_loop CI free]
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
    fsym [CAllocSpec.free' h, Child.cown_refund]

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

set_option maxHeartbeats 2000000 in
theorem reset_free_all_ct (CI : Child) (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv)
    (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) (Released CI γ e ctx) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ (own CI γ (e + 1) ctx ⋆ epTok γ (e + 1) Frac.one)) := by
  have hd := child_decode CI
  unfold heap_ArenaAllocator_reset
  fsym [deinit_ct CI h, own_empty]

/-- **`reset(.free_all)` meets the reset contract.** -/
theorem reset_free_all_spec (CI : Child)
    (h : CAllocSpec (CVTable.dispatch tables CI.fns) CI.cctx CI.toFAllocInv) (γ e : Nat) (ctx : Ptr) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ epTok γ e Frac.one) (heap_ArenaAllocator_reset ctx .free_all)
      (fun r => ⟪r = true⟫ ⋆ ((inv CI γ (e + 1) ctx).own ⋆ epTok γ (e + 1) Frac.one)) :=
  CTriple.eupd (reset_release CI γ e ctx) (reset_free_all_ct CI h γ e ctx)

end Reset

end AllocArena.ArenaSpecFixed

#print axioms AllocArena.ArenaSpecFixed.free_spec
#print axioms AllocArena.ArenaSpecFixed.resize_spec
#print axioms AllocArena.ArenaSpecFixed.remap_spec
#print axioms AllocArena.ArenaSpecFixed.deinit_ct
#print axioms AllocArena.ArenaSpecFixed.reset_free_all_spec
#print axioms AllocArena.ArenaSpecFixed.count_spec
