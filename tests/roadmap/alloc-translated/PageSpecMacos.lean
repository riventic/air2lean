import AllocTranslated.PageMacos
import PageTok
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Mmap

/-!
# The translated `PageAllocator` on aarch64-macos: `resize`, `remap` and `free` against `FAllocSpec`

The macOS counterpart of `PageSpec.lean` (same token `PageTok.lean`, same statements), for
`AllocTranslated/PageMacos.lean` (Zig 0.16.0, aarch64-macos, 16 KiB pages). macOS has no
`mremap` (`posix.MREMAP` is `void`), so `remap` is `resize` with `may_move`: a page-count shrink
unmaps the cut pages in place, a growth returns `null`/`false`, and every result keeps the grant's
pointer. Proved from the generated code and OSM-01 only, by the invariant and `fsym`.
-/

namespace AllocTranslated.PageSpecMacos

open Zig Zig.Full Zig.Full.FAssn AllocTranslated.PageMacos AllocTranslated.PageTok

abbrev P : Nat := 16384

/-- The page allocator's invariant for an allocator state `own` (the hint word in `PageAlloc.lean`),
which `resize`, `remap` and `free` never touch. -/
def inv (own : FAssn) : FAllocInv := pinv P own

/-- The translated vtable entries, as `RawVTable` fields. `alloc` reaches sync ops (the atomics on
`addr_hint`); a sequential call is the scheduler's run of one thread (`PageObstruction.lean`). -/
def vt : RawVTable where
  alloc c len k ra := fun m =>
    Sched.run Sched.soloEnv dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) m
  resize c s k n ra := heap_PageAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_PageAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_PageAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

variable {own : FAssn}

/-- **`free`** of a granted region: the region and its token go, the allocator state stays. -/
theorem free_spec (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k bs) (vt.free c s k ra) (fun _ => own) := by
  fsym

/-- **`resize`** (the refined field): in place, or `false` and nothing changed. -/
theorem resize_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind)
    (q q' : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k)
    (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val) (hqq : n.toNat < s.len.toNat → q' = q) :
    FTotalTriple (own ⋆ ((inv own).held s.ptr s.len.toNat k A S K q q' ⋆
      FAllocInv.relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (vt.resize c s k n ra) ((inv own).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' tl) := by
  fsym

/-- **`remap`**: in place (macOS has no `mremap`), or `null` and nothing changed. -/
theorem remap_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k bs) (vt.remap c s k n ra)
      ((inv own).remapPost s.ptr k bs n.toNat) := by
  fsym

end AllocTranslated.PageSpecMacos
