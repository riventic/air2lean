import PageSpec
import ZigLean.Sep.Full.WitnessStart

/-!
# The translated `PageAllocator` against `FAllocSpec`, `alloc` included (P4b)

`fallocSpec`: the translated `std.heap.PageAllocator` (`AllocTranslated/PageLinux.lean`, Zig
0.16.0, x86_64-linux) satisfies `FAllocSpec FLogic.partial vt c ainv`, from the generated code
and the OS mapping model only (premise OSM-01). No model of the allocator is used.

* **The allocator state** `own`: the hint word `addr_hint` as a pointer-valued atomic points-to
  (`aptsE`, O3), and for a non-null hint the knowledge of its block's address, page-aligned
  (`known`, O1). **`alloc` is proved by the invariant and `fsym`** (`alloc_ct`), the general
  symbolic executor's concurrent backend (`CTriple`, `docs/proof-automation.md`): it walks the
  generated code down to the oracle's picks at the owned hint word (`CTriple.pick_unorderedE`,
  `pick_casPtr`), the atomic thread rules (`FTTriple.atomicLoadUnorderedEnc`,
  `FTTriple.cmpxchgPtr`) and the OS mapping rule (`FTotalTriple.mmap'`, OSM-01); `@intFromPtr`
  of the hint reads its knowledge (the block may be unmapped), `@ptrFromInt` never fails since
  the O4 fix, and the new hint's knowledge comes from owning the mapping. `resize`, `remap` and
  `free` frame `own` (`PageSpec.lean`).
* **The call.** `alloc` is a concurrent function (its hint is an atomic). A sequential caller
  runs it in its own thread, each atomic op's oracle choice `0` (`Sched.soloRun`,
  `CTriple`, `ZigLean/Sep/Full/Conc.lean`). `alloc_threadFree` and `alloc_run`: the one-thread
  scheduler run is the same tree read sequentially (`Sched.run_eq_seqRun`). The scheduler's run
  itself (`PageObstruction.vt`) is not a `FAllocSpec` entry: it starts thread `0` from any
  memory and ends it (`checkJoinedByChild`), which an `FSeq` memory with another current thread
  or an unjoined child fails, whatever the allocator does.
* **Alignments up to a page** (`ainv.fits`: `k ≤ 12`, obstruction O5). For a larger alignment,
  `map` asks for extra pages and `std.mem.alignPointer` adds `alignment - 1` to the mapping's
  address with an overflow check. A placement proposal keeps the mapping below `2 ^ 64`
  (`Mem.placeOk`), but the fallback address after every block (`Mem.top`) is unbounded, so the
  check can fail and `map` panics: `alloc_high` (kernel-checked) is such a run from a memory
  whose last block ends high. Natively the kernel never maps that high. The fix is a bound on
  the fallback (a request whose block would end above the address space fails); with it, larger
  alignments need the prefix and tail `munmap`s, which `TotalTriple.munmapPrefix`/`munmapTail`
  already cover.
* **Partial correctness.** The atomic rules are partial (`FTriple`); `free`, `resize` and
  `remap` are total (`PageSpec.lean`).
-/

namespace AllocTranslated.PageAlloc

open Zig Zig.Region AllocTranslated.PageLinux AllocTranslated.PageSpec Zig.Full Zig.Full.FAssn

/-! ## The allocator state: the hint word -/

/-- `PageAllocator`'s hint word `addr_hint` (global block 0). -/
abbrev hint : Ptr := ⟨some 0, 0⟩

/-- What the allocator knows of the hinted mapping: its block's address, page-aligned. -/
def HintKn : Option Ptr → FAssn
  | none => FAssn.emp
  | some h => FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪h.block = some b ∧ 0 ≤ h.off ∧ ((A : Int) + h.off) % 4096 = 0⟫ ⋆ known b A

/-- The allocator state: the hint word with its atomic layout, and the knowledge of its target. -/
def own : FAssn := FAssn.ex fun h : Option Ptr => aptsE hint h ⋆ HintKn h

/-- The page allocator's invariant for every entry: alignments up to a page. -/
def ainv : FAllocInv := { inv own with fits := fun n k => n + 2 ^ k + P ≤ 2 ^ 64 ∧ k ≤ 12 }

/-- **`alloc`** as a concurrent function: the invariant and the general symbolic executor
(`fsym`'s `CTriple` backend). It reads the hint (`FTriple.atomicLoadUnorderedEnc`), checks the
derived address (the facts: both page-aligned), maps the pages (`FTotalTriple.mmap'`, OSM-01),
aligns the mapping's start (a no-op for alignments up to a page), and publishes the mapping with a
`cmpxchg` that succeeds (`FTriple.cmpxchgPtr`); the planner gives the caller the first `len` bytes
with the token and the hint the mapping's address (`known_of_region`). -/
theorem alloc_ct (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    CTriple (Tgt := Tgt) (ainv.own ⋆ ainv.fee φ) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra)
      (ainv.allocPost len.toNat k φ) := by
  unfold heap_PageAllocator_alloc
  fsym

/-! ## The vtable -/

/-- The translated vtable: `alloc` (a concurrent function: its hint is an atomic) is called in the
caller's thread (`Sched.soloRun`); `resize`, `remap` and `free` as in `PageSpec.vt`. -/
def vt : RawVTable :=
  { PageSpec.vt with
    alloc := fun c len k ra =>
      Sched.soloRun 16 (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) }

/-- **`alloc`**, for alignments up to a page. -/
theorem alloc_spec (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) (φ : Frac)
    (hlen : 0 < len.toNat) (hfit : ainv.fits len.toNat k) :
    FTriple (ainv.own ⋆ ainv.fee φ) (vt.alloc c len k ra) (ainv.allocPost len.toNat k φ) :=
  (alloc_ct c len k ra φ hlen hfit).toSolo 16

/-- **The translated `PageAllocator` satisfies `FAllocSpec`** (partial correctness), for
alignments up to a page, from the generated code and OSM-01 only. -/
theorem fallocSpec (c : Ptr) : FAllocSpec FLogic.partial vt c ainv where
  alloc len k ra φ hlen _ hfit := alloc_spec c len k ra φ hlen hfit
  resize s k n ra A S K q q' φ tl hk hn hfit hpos hq hqq :=
    (resize_spec (own := own) c s k n ra A S K q q' φ tl hk hn hfit.1 hpos hq hqq).toPartial
  remap s k n ra φ bs hk hn hfit hs hpos :=
    (remap_spec (own := own) c s k n ra φ bs hk hn hfit.1 hs hpos).toPartial
  free s k ra φ bs _ hs hpos := (free_dead_spec (own := own) c s k ra φ bs hs hpos).toPartial

/-- The OS-backed allocator has no per-instance native context. Its global hint is initialized
to null; creation exposes that word as the invariant and the allocator's (empty) fee. -/
def fallocSpec.creationParameters : FAllocCreationParameters := ⟨[0], []⟩

theorem fallocSpec.creation (_c : Ptr) :
    FTotalTriple (aptsE hint (none : Option Ptr)) (pure ()) (fun _ => ainv.creationPost) := by
  have usable : ∃ len : BitVec 64, ∃ k, 0 < len.toNat ∧ k < 64 ∧ ainv.fits len.toNat k :=
    ⟨1, 0, by decide, by decide, by decide⟩
  fsym [ainv.creationPost_intro Frac.one (by decide) usable]

nonvacuity_witness fallocSpec.creation := ⟨Zig.Witness.p0, Zig.Witness.FAdmit.aptsE (none : Option Ptr) rfl⟩

/-! ## O5 regression: alignments above a page -/

/-- `mem0` with one more (dead, empty) block that ends just below the last page under `2 ^ 64`:
the fallback address of the next mapping (`Mem.top`, the placement proposes nothing) is that
page. -/
def high : Mem :=
  { (mem0 .fresh) with
    blocks := (mem0 .fresh).blocks.push
      { bytes := #[], align := 1, kind := .heap, live := false, addr := 2 ^ 64 - 4097 } }

/-- **O5, fixed.** Before the OS model bounded the address space, `alloc(1, align 8192)` from
`high` mapped two pages at `2 ^ 64 - 4096`, the alignment `@intFromPtr(p) + 8191` of
`std.mem.alignPointer` overflowed and `PageAllocator.map` panicked. Now that `mmap` fails with
`ENOMEM` above `Os.Target.addrLimit` (OSM-01), `alloc` returns `null`, as natively. -/
theorem alloc_high : (((vt.alloc ⟨none, 0⟩ 1 13 0).run high).run.map fun r =>
    match r with | .ok (v, _) => decide (v = none) | _ => false) = some true := by
  decide +kernel

/-- `mem0` under a placement that proposes the address `A` for the first mapping (block 6,
after the six globals). -/
def placedAt (A : Nat) : Mem := mem0 { propose := fun b => if b == 6 then some A else none }

/-- Near the end of the address space, `alloc(1, align 8192)` maps two pages at
`2 ^ 47 - 12288`, unmaps the first one (`TotalTriple.munmapPrefix`) and returns the second. -/
theorem alloc_top : (((vt.alloc ⟨none, 0⟩ 1 13 0).run (placedAt (2 ^ 47 - 12288))).run.map
    fun r =>
    match r with | .ok (some p, _) => decide (p.off = 4096) | _ => false) = some true := by
  decide +kernel

/-- At the end of the address space, `alloc(1, align 8192)` maps two pages ending exactly at
`addrLimit = 2 ^ 47`; the address is already aligned, so it unmaps the second page
(`TotalTriple.munmapTail`; a wrong range would be `.illegal`) and returns the first. -/
theorem alloc_edge : (((vt.alloc ⟨none, 0⟩ 1 13 0).run (placedAt (2 ^ 47 - 8192))).run.map
    fun r =>
    match r with
    | .ok (some p, m) => match m.blocks[6]? with
      | some blk => decide (p.off = 0 ∧ blk.addr = 2 ^ 47 - 8192 ∧ blk.live)
      | none => false
    | _ => false) = some true := by
  decide +kernel

/-! ## The scheduler's reading -/

/-- `alloc` stops only at its two atomic ops' oracle picks, which one thread answers itself. -/
theorem alloc_threadFree (c : Ptr) (len : BitVec 64) (a : mem_Alignment) (ra : BitVec 64) :
    ConcM.ThreadFree (heap_PageAllocator_alloc c len a ra) := by
  unfold heap_PageAllocator_alloc heap_PageAllocator_map
  conc_norm
  set_option maxRecDepth 8192 in repeat' (first
    | apply Sched.ThreadFreeC.bind
    | apply Sched.ThreadFreeC.ite
    | apply Sched.ThreadFreeC.liftMem
    | apply Sched.ThreadFreeC.pure'
    | apply Sched.ThreadFreeC.throw
    | exact Sched.ThreadFreeC.sync rfl
    | split
    | (guard_target = ∀ _, _; intro _))

/-- So a one-thread scheduler run of `alloc` is its sequential reading (`Sched.run_eq_seqRun`). -/
theorem alloc_run (env : Env) (c : Ptr) (len : BitVec 64) (a : mem_Alignment) (ra : BitVec 64)
    (m : Mem) :
    Sched.run env dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len a ra) m =
      (Sched.seqRun 16 (heap_PageAllocator_alloc c len a ra)).run m :=
  Sched.run_eq_seqRun env dispatch 16 (alloc_threadFree c len a ra) m

end AllocTranslated.PageAlloc
