import AllocArena.ArenaMacos
import AllocArena.Core
import AllocArena.Reset
import ZigLean.Sep.Full.AutoAll

/-!
# `ArenaSpecMacos`: `free`, `resize` and `remap` against `FAllocSpec`

The entries of `ArenaSpecMacos.lean` (the stock arena on aarch64-macos), in their own module so
that they build in parallel with `reset`'s walks (`ArenaSpecMacos/Retain.lean`,
`ArenaSpecMacos/Loop66C0.lean`, `ArenaSpecMacos/Loop66C1.lean`). `ArenaSpecMacos.lean` imports
them.
-/

namespace AllocArena.ArenaSpecMacos

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaMacos

/-! ## `free`, `resize` and `remap` (as in `ArenaSpec.lean`) -/

set_option maxHeartbeats 350000 in
/-- `free`'s run, case by case (`ArenaSpec.free_ct`). -/
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

set_option maxHeartbeats 4250000 in
/-- `resize`'s run, case by case (`ArenaSpec.resize_ct`). -/
theorem resize_ct (CI : Child) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (A S : Nat) (K : BlockKind) (q q' φ : Frac) (tl : Array Byte) (hpos : 0 < s.len.toNat)
    (hn : 0 < n.toNat) (hq : q'.val ≤ q.val) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ ((inv CI γ e ctx).held s.ptr s.len.toNat k A S K q q' φ ⋆
        (inv CI γ e ctx).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  unfold heap_ArenaAllocator_resize
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

end AllocArena.ArenaSpecMacos
