import PageAlloc
import ZigLean.Sep.Full.AllocBridge
import ZigLean.Sep.Full.AutoThread
import ZigLean.Sep.Full.AutoAll

/-!
# The translated `PageAllocator`'s entries as thread triples (L4, fsym-engine ledger #72)

An environment of an open `std.mem.Allocator` (`docs/interfaces.md`) that runs the translated
`PageAllocator` in the caller's thread needs each entry as a **thread triple** (`FTTriple`): a
thread calls it while other threads run (`CAllocSpec.ofRaw`, `ZigLean/Sep/Full/AllocBridge.lean`).
The statements are `PageAlloc.fallocSpec`'s (`PageSpec.lean`, `PageAlloc.lean`):

* `fthread_alloc`: `alloc` is a concurrent function (its hint word is an atomic); the vtable reads
  it in the caller's thread (`Sched.soloRun`), and that reading is a step of the thread
  (`CTriple.toSoloThread` of `PageAlloc.alloc_ct`).
* `fthread_free`, `fthread_resize`: the invariant and `fsym`'s thread backend, which runs each
  sequential mapping rule in the thread with its locality provider (`ZigLean/Sep/Full/Mmap.lean`).
* `remap` is not here yet: the thread backend does not split on the growth-or-shrink side condition
  of `mremap` as the sequential walk does (engine fix in PR #368). With it, the four entries give
  `CAllocSpec (CVTable.ofRaw vt)`, the page allocator as an environment.
-/

namespace AllocTranslated.PageThread

open Zig Zig.Full Zig.Full.FAssn AllocTranslated.PageLinux AllocTranslated.PageSpec
  AllocTranslated.PageAlloc

theorem fthread_alloc (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    FTTriple (ainv.own ⋆ ainv.fee φ) (PageAlloc.vt.alloc c len k ra) (ainv.allocPost len.toNat k φ) :=
  (alloc_ct c len k ra φ hlen hfit).toSoloThread 16

variable {own : FAssn}

theorem fthread_free (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hs : s.len.toNat = bs.size) (hpos : 0 < bs.size) :
    FTTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (PageSpec.vt.free c s k ra)
      (fun _ => own ⋆ (inv own).fee φ) := by
  fsym

theorem fthread_resize (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat) (K : BlockKind)
    (q q' φ : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (inv own).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val)
    (hqq : n.toNat < s.len.toNat → q' = q) :
    FTTotalTriple (own ⋆ ((inv own).held s.ptr s.len.toNat k A S K q q' φ ⋆
      (inv own).relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (PageSpec.vt.resize c s k n ra) ((inv own).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' φ tl) := by
  fsym

theorem fthread_remap (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) (φ : Frac) (bs : Array Byte)
    (hk : k < 64) (hn : 0 < n.toNat) (hfit : (inv own).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTTotalTriple (own ⋆ (inv own).granted s.ptr k φ bs) (PageSpec.vt.remap c s k n ra)
      ((inv own).remapPost s.ptr k φ bs n.toNat) := by
  fsym

/-- **The translated `PageAllocator` meets the concurrent allocator contract** (`CAllocSpec`), its
entries read in the caller's thread (`CVTable.ofRaw`), for alignments up to a page. -/
theorem cAllocSpec (c : Ptr) {Tgt : Type} : CAllocSpec (CVTable.ofRaw PageAlloc.vt : CVTable Tgt) c ainv :=
  CAllocSpec.ofRaw
    (fun len k ra φ hlen _ hfit => fthread_alloc c len k ra φ hlen hfit)
    (fun s k n ra A S K q q' φ tl hk hn hfit hpos hq hqq =>
      (fthread_resize (own := PageAlloc.own) c s k n ra A S K q q' φ tl hk hn hfit.1 hpos hq hqq).toPartial)
    (fun s k n ra φ bs hk hn hfit hlen hpos =>
      (fthread_remap (own := PageAlloc.own) c s k n ra φ bs hk hn hfit.1 hlen hpos).toPartial)
    (fun s k ra φ bs _ hlen hpos => (fthread_free (own := PageAlloc.own) c s k ra φ bs hlen hpos).toPartial)

end AllocTranslated.PageThread
