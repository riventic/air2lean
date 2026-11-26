import PageAlloc
import PageSpecMacos

/-! Scratch experiments of lane m01-page-total (not for merge). -/

namespace AllocTranslated.Scratch

open Zig Zig.Region Zig.Full Zig.Full.FAssn AllocTranslated.PageTok

abbrev hint : Ptr := ⟨some 0, 0⟩

def HintKnN (P : Nat) : Option Ptr → FAssn
  | none => FAssn.emp
  | some h => FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪h.block = some b ∧ 0 ≤ h.off ∧ (A + h.off.toNat) % P = 0⟫ ⋆ known b A

def HintKnI (P : Nat) : Option Ptr → FAssn
  | none => FAssn.emp
  | some h => FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪h.block = some b ∧ 0 ≤ h.off ∧ ((A : Int) + h.off) % (P : Int) = 0⟫ ⋆ known b A

def ownN (P : Nat) : FAssn := FAssn.ex fun h : Option Ptr => aptsE hint h ⋆ HintKnN P h
def ownI (P : Nat) : FAssn := FAssn.ex fun h : Option Ptr => aptsE hint h ⋆ HintKnI P h

namespace L
open AllocTranslated.PageLinux AllocTranslated.PageSpec

def ainvU : FAllocInv := inv PageAlloc.own
def ainvI : FAllocInv := { pinv 4096 (ownI 4096) with fits := fun n k => n + 2 ^ k + 4096 ≤ 2 ^ 64 ∧ k ≤ 12 }
def ainvN : FAllocInv := { pinv 4096 (ownN 4096) with fits := fun n k => n + 2 ^ k + 4096 ≤ 2 ^ 64 ∧ k ≤ 12 }
def ainvNU : FAllocInv := pinv 4096 (ownN 4096)

/-- T1: every alignment, the existing allocator state. -/
theorem t1 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hk : k < 64) (hfit : ainvU.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvU.own ⋆ ainvU.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvU.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-- T2: the generic state, Int form, alignments up to a page. -/
theorem t2 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainvI.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvI.own ⋆ ainvI.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvI.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-- T3: the generic state, Nat form, alignments up to a page. -/
theorem t3 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainvN.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvN.own ⋆ ainvN.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvN.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-- T3u: the generic state, Nat form, every alignment. -/
theorem t3u (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hk : k < 64) (hfit : ainvNU.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvNU.own ⋆ ainvNU.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvNU.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-- T4: total correctness of the in-thread reading. -/
theorem t4 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : PageAlloc.ainv.fits len.toNat k) :
    FTotalTriple (PageAlloc.ainv.own ⋆ PageAlloc.ainv.fee φ) (PageAlloc.vt.alloc c len k ra)
      (PageAlloc.ainv.allocPost len.toNat k φ) := by
  fsym

/-- T5: the same, with the entry unfolded. -/
theorem t5 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : PageAlloc.ainv.fits len.toNat k) :
    FTotalTriple (PageAlloc.ainv.own ⋆ PageAlloc.ainv.fee φ)
      (Sched.soloRun 16 (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra))
      (PageAlloc.ainv.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

end L

namespace M
open AllocTranslated.PageMacos AllocTranslated.PageSpecMacos

def ainvI : FAllocInv := { pinv 16384 (ownI 16384) with fits := fun n k => n + 2 ^ k + 16384 ≤ 2 ^ 64 ∧ k ≤ 14 }
def ainvN : FAllocInv := { pinv 16384 (ownN 16384) with fits := fun n k => n + 2 ^ k + 16384 ≤ 2 ^ 64 ∧ k ≤ 14 }
def ainvNU : FAllocInv := pinv 16384 (ownN 16384)

theorem m2 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainvI.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvI.own ⋆ ainvI.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvI.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

theorem m3 (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainvN.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvN.own ⋆ ainvN.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvN.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

theorem m3u (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hk : k < 64) (hfit : ainvNU.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainvNU.own ⋆ ainvNU.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainvNU.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

end M

end AllocTranslated.Scratch
