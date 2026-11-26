import PageAllocMacos
import ZigLean.Sep.Full.AllocBridge
import ZigLean.Sep.Full.AutoThread
import ZigLean.Sep.Full.AutoAll

/-!
# The translated `PageAllocator`'s entries as thread triples on aarch64-macos

The macOS counterpart of `PageThread.lean`: the same statements over
`AllocTranslated/PageMacos.lean` (16 KiB pages), from the generated code and the OS mapping model
only (premise OSM-01: libc's `mmap`/`munmap` are `Os.mmap`/`Os.munmap` at `Os.Target.macos`; there
is no `mremap`). The allocator's only shared state is the hint word, an atomic, so no thread or
lock primitive of the OS is reached and no further premise is used.

* `fthread_alloc`: the in-thread reading of the concurrent `alloc` (`CTriple.toSoloThread` of
  `PageAllocMacos.alloc_ct`).
* `fthread_free`, `fthread_resize`, `fthread_remap`: the invariant and `fsym`'s thread backend.
* `cAllocSpec`: `CAllocSpec (CVTable.ofRaw vt) c ainv`, the page allocator as an environment of
  an open `std.mem.Allocator` (`docs/interfaces.md`), for every program's `Tgt`; alignments up to
  a page, partial correctness, as `PageAllocMacos.fallocSpec`. Its `free` ends the grant's block.
* `cAllocSpec.creation`: the state from the start memory's null hint word.
-/

namespace AllocTranslated.PageThreadMacos

open Zig Zig.Full Zig.Full.FAssn AllocTranslated.PageMacos AllocTranslated.PageSpecMacos
  AllocTranslated.PageAllocMacos Zig.Witness

theorem fthread_alloc (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    FTTriple (ainv.own ⋆ ainv.fee φ) (PageAllocMacos.vt.alloc c len k ra)
      (ainv.allocPost len.toNat k φ) :=
  (alloc_ct c len k ra φ hlen hfit).toSoloThread 16

variable {own : FAssn}

theorem fthread_free (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (PageSpecMacos.vt.free c s k ra)
      (fun _ => (own ⋆ (inv own).fee φ) ⋆ (inv own).freed s.ptr) := by
  show FTTotalTriple _ _ (fun _ => (own ⋆ (inv own).fee φ) ⋆ PageTok.deadOf s.ptr)
  unfold PageTok.deadOf
  fsym [FTotalTriple.munmapWhole_dead]

theorem fthread_resize (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind)
    (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (inv own).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val)
    (hqq : n.toNat < s.len.toNat → q' = q) :
    FTTotalTriple (own ⋆ ((inv own).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (inv own).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (PageSpecMacos.vt.resize c s k n ra)
      ((inv own).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  fsym

theorem fthread_remap (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (PageSpecMacos.vt.remap c s k n ra)
      ((inv own).remapPost s.ptr k φ bs n.toNat) := by
  fsym

/-- **The translated `PageAllocator` meets the concurrent allocator contract on aarch64-macos**
(`CAllocSpec`), its entries read in the caller's thread (`CVTable.ofRaw`), for alignments up to a
page. -/
theorem cAllocSpec (c : Ptr) {Tgt : Type} :
    CAllocSpec (CVTable.ofRaw PageAllocMacos.vt : CVTable Tgt) c ainv :=
  CAllocSpec.ofRaw
    (fun len k ra φ hlen _ hfit => fthread_alloc c len k ra φ hlen hfit)
    (fun s k n ra A S K q q' φ tl hk hn hfit hpos hq hqq =>
      (fthread_resize (own := PageAllocMacos.own) c s k n ra A S K q q' φ tl hk hn hfit.1 hpos hq
        hqq).toPartial)
    (fun s k n ra φ bs hk hn hfit hlen hpos =>
      (fthread_remap (own := PageAllocMacos.own) c s k n ra φ bs hk hn hfit.1 hlen hpos).toPartial)
    (fun s k ra φ bs _ hlen hpos =>
      (fthread_free (own := PageAllocMacos.own) c s k ra φ bs hlen hpos).toPartial)

/-- Both the context pointer and the caller's target type are visible contract arguments. -/
def cAllocSpec.creationParameters : FAllocCreationParameters := ⟨[0, 1], []⟩

/-- The concurrent contract has the same initialized state, for every caller's target type. -/
theorem cAllocSpec.creation (c : Ptr) {Tgt : Type} :
    FTotalTriple (aptsE PageAllocMacos.hint (none : Option Ptr)) (pure ())
      (fun _ => PageAllocMacos.ainv.creationPost) :=
  PageAllocMacos.fallocSpec.creation c

nonvacuity_witness cAllocSpec.creation :=
  ⟨(⟨none, 0⟩ : Ptr), Unit,
    PageAllocMacos.fallocSpec.creation_admission ⟨none, 0⟩ .fresh #[]⟩

end AllocTranslated.PageThreadMacos
