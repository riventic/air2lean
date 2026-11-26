import PageAlloc
import PageAllocMacos

/-! Scratch experiment of lane m01-page-total (not for merge): every alignment, more heartbeats. -/

namespace AllocTranslated.Scratch

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocTranslated.PageTok

namespace L
open AllocTranslated.PageLinux AllocTranslated.PageSpec

def ainvU : FAllocInv := inv PageAlloc.own

set_option maxHeartbeats 3000000 in
theorem t1 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hk : k < 64) (hfit : ainvU.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvU.own ⋆ ainvU.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvU.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

end L

end AllocTranslated.Scratch
