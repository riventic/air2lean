import AllocArena.ArenaFixedLinux
import AllocArena.Core

/-!
# The patched `ArenaAllocator`'s `free`, `resize` and `remap` against `FAllocSpec`

The same statements as `ArenaSpec.lean` for the arena of `upstream/arena-fix.patch`
(`AllocArena/ArenaFixedLinux.lean`), with the same invariant (`AllocArena.Core`). The patched
`free` and `resize` first load the node's size and return when `end_index` is past the buffer
(a racing `alloc`'s reservation, `docs/upstream/arena-oob-gep.md`); the invariant keeps
`end_index` within the buffer, so they go on as the stock ones do (`arena_bounds`).
-/

namespace AllocArena.ArenaSpecFixed

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocArena.Core AllocArena.ArenaFixedLinux

theorem debug_assert_true : debug_assert true = pure () := rfl

/-- `Node.Size.toInt` of the decoded bits of an even size is the size. -/
theorem toInt_ofBits (w : BitVec 64) (h : w.toNat % 2 = 0) :
    heap_ArenaAllocator_Node_Size_toInt (Packed.ofBits w) = pure w := by
  arena_toInt

/-- `Node.loadBuf` of a node whose `size` word holds the even size `sz`: the buffer after the
header, `sz - 24` bytes. -/
theorem loadBuf_ct {N : Ptr} {b : BlockId} {sz : Nat} {R : FAssn} (hb : N.block = some b)
    (h0 : 0 ≤ N.off) (hsz : 24 ≤ sz) (heven : sz % 2 = 0) (hsmall : sz < 2 ^ 63)
    (hmem : ∀ m r rF, Holds m r rF → (apts N (BitVec.ofNat 64 sz) ⋆ R) r → m.FSeq →
      ∃ blk, m.blocks[b]? = some blk ∧ N.off.toNat + sz ≤ blk.bytes.size) :
    CTriple (Tgt := Tgt) (apts N (BitVec.ofNat 64 sz) ⋆ R) (heap_ArenaAllocator_Node_loadBuf N)
      (fun sl => ⟪sl = ⟨N.add 24, BitVec.ofNat 64 (sz - 24)⟩⟫ ⋆ (apts N (BitVec.ofNat 64 sz) ⋆ R)) := by
  arena_loadBuf

/-- `free`'s run, case by case (module doc). -/
theorem free_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra) (fun _ => (inv CI γ e ctx).own) := by
  arena_free_checked

/-- **`free` meets `FAllocSpec`'s `free` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading (`Sched.soloRun`). -/
theorem free_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_free ctx s ⟨BitVec.ofNat 6 k⟩ ra))
      (fun _ => (inv CI γ e ctx).own) :=
  free_ct CI γ e ctx s k ra bs hlen hpos fuel

/-- `resize`'s run, case by case: a slice that is not the first node's last one only shrinks (its
cut bytes become junk); the last one moves `end_index` (shrink, or growth into the tail when it
fits). A successful resize re-points the grant at the new length (`Upd.reassign`). -/
theorem resize_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) := by
  arena_resize_checked

/-- `remap` is `resize`, and returns `memory.ptr` when it succeeds. -/
theorem remap_ct (CI : FAllocInv) (γ e : Nat) (ctx s : _) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat) :
    CTriple (Tgt := Tgt) ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra)
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) := by
  arena_remap

/-- **`resize` meets `FAllocSpec`'s `resize` field** for the arena invariant at every epoch, every
child invariant `CI`, and every depth of the one-thread reading. -/
theorem resize_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).resizePost s.ptr k bs n.toNat) :=
  resize_ct CI γ e ctx s k n ra bs hlen hpos hn fuel

/-- **`remap` meets `FAllocSpec`'s `remap` field.** -/
theorem remap_spec (CI : FAllocInv) (γ e : Nat) (ctx : Ptr) (fuel : Nat) (s : Slice) (k : Nat)
    (n ra : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) :
    FLogic.partial.T ((inv CI γ e ctx).own ⋆ (inv CI γ e ctx).granted s.ptr k bs)
      (Sched.soloRun fuel (heap_ArenaAllocator_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra))
      ((inv CI γ e ctx).remapPost s.ptr k bs n.toNat) :=
  remap_ct CI γ e ctx s k n ra bs hlen hpos hn fuel

end AllocArena.ArenaSpecFixed

#print axioms AllocArena.ArenaSpecFixed.free_spec
#print axioms AllocArena.ArenaSpecFixed.resize_spec
#print axioms AllocArena.ArenaSpecFixed.remap_spec
