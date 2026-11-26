import PageSpecMacos
import ZigLean.Sep.Full.WitnessStart

/-!
# The translated `PageAllocator` on aarch64-macos against `FAllocSpec`, `alloc` included

The macOS counterpart of `PageAlloc.lean`: `fallocSpec`, the translated
`std.heap.PageAllocator` (`AllocTranslated/PageMacos.lean`, aarch64-macos, 16 KiB pages) satisfies
`FAllocSpec FLogic.partial vt c ainv`, from the generated code and the OS mapping model only
(premise OSM-01: on macOS `posix.mmap`/`munmap` are libc's, modelled by the same `Os.mmap`/
`Os.munmap` at `Os.Target.macos`; there is no `mremap`). No model of the allocator is used.

* **The allocator state** is the one of x86_64-linux at this target's page size
  (`PageTok.hown`): the hint word `addr_hint` as a pointer-valued atomic points-to and, for a
  non-null hint, the knowledge of its block's address, page-aligned. **`alloc` is proved by the
  invariant and `fsym`** (`alloc_ct`, the `CTriple` backend), as on x86_64-linux; `resize`,
  `remap` and `free` frame the state (`PageSpecMacos.lean`).
* **The call.** `alloc` is a concurrent function (its hint is an atomic); the vtable entry is its
  call in the caller's thread, each atomic op's oracle choice `0` (`Sched.soloRun`).
* **Alignments up to a page** (`ainv.fits`: `k ≤ 14`); larger ones are open, as on x86_64-linux
  (`PageAlloc.lean`).
* **Partial correctness** of `alloc` (`CTriple`); `free`, `resize` and `remap` are total.
* **Creation** (`fallocSpec.creation`, `docs/claim-strength.md`): the null hint word that the
  translated program initializes (`PageMacos.mem0`, global 0) establishes the state, for every
  placement and arbitrary input stream (`fallocSpec.creation_admission`).
-/

namespace AllocTranslated.PageAllocMacos

open Zig Zig.Region AllocTranslated.PageMacos AllocTranslated.PageSpecMacos Zig.Full Zig.Full.FAssn
  Zig.Witness

/-- `PageAllocator`'s hint word `addr_hint` (`PageTok.hint`: global block 0). -/
abbrev hint : Ptr := PageTok.hint

/-- The allocator state (`PageTok.hown` at 16 KiB pages). -/
def own : FAssn := PageTok.hown P

/-- The page allocator's invariant for every entry: alignments up to a page. -/
def ainv : FAllocInv := { inv own with fits := fun n k => n + 2 ^ k + P ≤ 2 ^ 64 ∧ k ≤ 14 }

/-- **`alloc`** as a concurrent function: the invariant and the general symbolic executor
(`fsym`'s `CTriple` backend), down to the oracle's picks at the owned hint word, the atomic
thread rules and the OS mapping rule (`FTotalTriple.mmapC`, OSM-01). -/
theorem alloc_ct (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainv.own ⋆ ainv.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainv.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-- The translated vtable: `alloc` is called in the caller's thread (`Sched.soloRun`); `resize`,
`remap` and `free` as in `PageSpecMacos.vt`. -/
def vt : RawVTable :=
  { PageSpecMacos.vt with
    alloc := fun c len k ra =>
      Sched.soloRun 16 (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) }

/-- **`alloc`**, for alignments up to a page. -/
theorem alloc_spec (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    FTriple (ainv.own ⋆ ainv.fee φ) (vt.alloc c len k ra) (ainv.allocPost len.toNat k φ) :=
  (alloc_ct c len k ra φ hlen hfit).toSolo 16

/-- **The translated `PageAllocator` satisfies `FAllocSpec` on aarch64-macos** (partial
correctness), for alignments up to a page, from the generated code and OSM-01 only. -/
theorem fallocSpec (c : Ptr) : FAllocSpec FLogic.partial vt c ainv where
  alloc len k ra φ hlen _ hfit := alloc_spec c len k ra φ hlen hfit
  resize s k n ra A S K q q' φ tl hk hn hfit hpos hq hqq :=
    (resize_spec (own := own) c s k n ra A S K q q' φ tl hk hn hfit.1 hpos hq hqq).toPartial
  remap s k n ra φ bs hk hn hfit hs hpos :=
    (remap_spec (own := own) c s k n ra φ bs hk hn hfit.1 hs hpos).toPartial
  free s k ra φ bs _ hs hpos := (free_dead_spec (own := own) c s k ra φ bs hs hpos).toPartial

/-! ## Creation from the initialized hint word -/

/-- The context pointer is a visible contract argument; the state is the global hint word. -/
def fallocSpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩

/-- The null hint initialized by the translated program establishes the allocator state, an
available positive fee and a positive accepted request. -/
theorem fallocSpec.creation (_c : Ptr) :
    FTotalTriple (aptsE hint (none : Option Ptr)) (pure ())
      (fun _ => ainv.creationPost) := by
  fsym [ainv.creationPost_intro Frac.one (by decide)
    (by
      refine ⟨(1 : BitVec 64), 0, by decide, by decide, ?_⟩
      change 1 + 2 ^ 0 + P ≤ 2 ^ 64 ∧ 0 ≤ 14
      decide)]

/-- The exact null hint required by creation, in the actual generated start memory. -/
theorem fallocSpec.creation_input_at (_c : Ptr) (σ : Placement)
    (arbitrary : Array (BitVec 64)) :
    FAdmit.At (PageMacos.mem0 σ arbitrary) (aptsE hint (none : Option Ptr)) := by
  apply FAdmit.At.global_aptsE (σ := σ) (gs := _) (j := 0)
    (bs := Enc.encode (none : Option Ptr)) (a := 8) (K := .global) (v := (none : Option Ptr))
  · rfl
  · rfl
  · exact MemAuth.Keep.of_blocks rfl rfl rfl rfl
  · simp [BlockKind.mappedLo]
  · rfl
  · decide
  · decide
  · decide
  · exact LawfulEnc.size_encode _
  · exact LawfulEnc.decode_encode _

/-- The creation precondition is admissible for every placement and arbitrary input stream. -/
theorem fallocSpec.creation_admission (c : Ptr) (σ : Placement)
    (arbitrary : Array (BitVec 64)) : FAdmit (aptsE hint (none : Option Ptr)) := by
  refine FAdmit.iff_at.mpr ⟨PageMacos.mem0 σ arbitrary, ?_,
    fallocSpec.creation_input_at c σ arbitrary⟩
  refine Mem.FSeq.congrMem (Mem.init_fseq σ _ ?_) rfl rfl ?_
  · decide +kernel
  · exact singleThread_empty rfl (by change 0 < 1; decide)

nonvacuity_witness fallocSpec.creation :=
  ⟨(⟨none, 0⟩ : Ptr), fallocSpec.creation_admission ⟨none, 0⟩ .fresh #[]⟩

end AllocTranslated.PageAllocMacos
