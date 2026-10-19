import AllocTranslated.PageLinux
import PageTok
import ZigLean.Sep.Full.AutoClaims
import ZigLean.Sep.Full.Mmap

/-!
# The translated `PageAllocator`'s `resize`, `remap` and `free` against `FAllocSpec` (P4b)

The vtable entries of the translated `std.heap.PageAllocator` (`AllocTranslated/PageLinux.lean`,
Zig 0.16.0, x86_64-linux, `--allocator-model translated`) that do not touch the address hint,
proved from the generated code and the OS mapping model only (premise OSM-01,
`ZigLean/Os/Mmap.lean`). No model of the allocator is used.

`free_spec`, `resize_spec`, `remap_spec` are the `free`, (refined) `resize` and `remap` fields of
`FAllocSpec FLogic.total vt ctx (inv own)` (`ZigLean/Sep/Full/AllocSpec.lean`) for every
allocator state `own : FAssn`. `alloc`, with the hint word as the allocator state, is in
`PageAlloc.lean`.

**The proofs are the invariant (`PageTok.lean`) and the general symbolic executor `fsym`**
(`ZigLean/Sep/Full/Auto.lean`, `docs/proof-automation.md`). It walks the generated code down to
the OS primitives with the library's full-state mapping rules (`ZigLean/Sep/Full/Mmap.lean`):

* `free`: the token's authority and the grant's share make the mapping's full extent, the grant
  and the token's tail its bytes; `munmap` of the whole mapping (`FTotalTriple.munmapWhole'`).
* `resize` (`realloc` without `MAYMOVE`): the same pages keep the mapping (the token's tail gives
  or takes the bytes, the share is raised with the authority or weakened); fewer pages unmap the
  cut pages (`FTotalTriple.munmapTailR`) and lend the share back out of the new extent; more
  pages fail (x86_64-linux never grows in place: the stack grows down).
* `remap` (`realloc` with `MAYMOVE`): `mremap` shrinks in place (`FTotalTriple.mremapShrinkR`) or
  grows in place or moved (`FTotalTriple.mremapMove'`), or fails with the grant unchanged.
-/

namespace AllocTranslated.PageSpec

open Zig Zig.Full Zig.Full.FAssn AllocTranslated.PageLinux AllocTranslated.PageTok

abbrev P : Nat := 4096

/-- The page allocator's invariant for an allocator state `own` (the hint word in `PageAlloc.lean`),
which `resize`, `remap` and `free` never touch. -/
def inv (own : FAssn) : FAllocInv := pinv P own

/-- The translated vtable entries, as `RawVTable` fields. `alloc` reaches sync ops (the atomics on
`addr_hint`); a sequential call is the scheduler's run of one thread (`PageObstruction.lean`), in
an environment that no `alloc` step reads (`PageAlloc.alloc_run`). -/
def vt : RawVTable where
  alloc c len k ra := fun m =>
    Sched.run Sched.soloEnv dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) m
  resize c s k n ra := heap_PageAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_PageAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_PageAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

variable {own : FAssn}

/-- **`free`** of a granted region: the region and its token go, the allocator state stays. -/
theorem free_spec (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (vt.free c s k ra)
      (fun _ => own ⋆ (inv own).fee φ) := by
  fsym

/-- **`free` ends the grant's block** (`FAllocInv.freed`, `PageTok.deadOf`): it unmaps the
whole mapping (`FTotalTriple.munmapWhole_dead`). -/
theorem free_dead_spec (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (vt.free c s k ra)
      (fun _ => (own ⋆ (inv own).fee φ) ⋆ (inv own).freed s.ptr) := by
  show FTotalTriple _ _ (fun _ => (own ⋆ (inv own).fee φ) ⋆ PageTok.deadOf s.ptr)
  unfold PageTok.deadOf
  fsym [FTotalTriple.munmapWhole_dead]

/-- **`resize`** (the refined field): in place, or `false` and nothing changed. -/
theorem resize_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind)
    (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (inv own).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val)
    (hqq : n.toNat < s.len.toNat → q' = q) :
    FTotalTriple (own ⋆ ((inv own).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (inv own).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (vt.resize c s k n ra) ((inv own).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  fsym

/-- **`remap`**: in place, moved (`mremap` may move), or `null` and nothing changed. -/
theorem remap_spec (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (vt.remap c s k n ra)
      ((inv own).remapPost s.ptr k φ bs n.toNat) := by
  fsym

end AllocTranslated.PageSpec
