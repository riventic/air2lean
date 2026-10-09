import AllocTranslated.PageLinux
import ZigLean.Sep.AllocSpec

/-!
# Why the translated `PageAllocator` cannot satisfy `AllocSpec` (P4b finding)

`AllocSpec` (`ZigLean/Sep/AllocSpec.lean`) states each vtable entry as a `Triple` in some
`Logic`. A triple quantifies over every sequential memory whose *heap* (`Mem.heap`: the live
bytes) splits into the precondition's part and a frame. Two parts of `Mem` that the translated
`std.heap.PageAllocator.alloc` (Zig 0.16.0, x86_64-linux) reads are not in the heap:

* **O3, atomic locations.** `addr_hint` is read with `@atomicLoad(.unordered)` and written with
  `@cmpxchgStrong`. The model keeps atomic locations in `Mem.atomics`; a location of another size
  at the same bytes makes `locIdx` throw `.unspecified`. `odd` has the heap of `mem0` (the program
  start) and such a location, so no precondition that holds at program start gives a triple for
  `alloc` (`alloc_no_triple_at_start`), and no allocator invariant that holds at program start
  satisfies `AllocSpec` (`not_allocSpec_at_start`), in any logic.
* **O1, dead blocks.** After `free` of the last allocation, `addr_hint` points into an unmapped
  (dead) block; the next `alloc` reads its address (`@intFromPtr`) and checks the alignment of the
  derived hint (`@ptrFromInt` to `[*]align(page_size_min) u8`). Dead blocks are not in the heap.
  `hinted` (the shape a real run reaches: `Eval.lean`) and `hintedLost` (the dead block's metadata
  gone) have the same heap; `alloc` from `hintedLost` is `.illegal`, so no precondition that holds
  after a `free` of the hinted block gives a triple for `alloc` (`alloc_no_triple_after_free`),
  independently of O3 (both memories have no atomic location).

Natively both are fine: the hint is a plain integer and the location has one size. The fix is a
logic whose assertions can constrain these parts of the memory (`docs/alloc-page.md`).
-/

namespace AllocTranslated.PageObstruction

open Zig AllocTranslated.PageLinux

/-- The translated vtable entries, as `RawVTable` fields. `alloc` reaches sync ops (the atomics
on `addr_hint`); a sequential call is the scheduler's run of one thread (every choice `0`, which is
the only option of a single thread). -/
def vt : RawVTable where
  alloc c len k ra := fun m =>
    Sched.run dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra) m
  resize c s k n ra := heap_PageAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_PageAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_PageAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

/-- The error of a run, if it has one. -/
def errOf {α : Type} (r : Result (α × Mem)) : Option Error :=
  match r.run with
  | some (.error e) => some e
  | _ => none

theorem run_of_errOf {α : Type} {r : Result (α × Mem)} {e : Error} (h : errOf r = some e) :
    r.run = some (.error e) := by
  unfold errOf at h
  split at h
  · rename_i heq; cases h; exact heq
  · cases h

/-- A memory whose live blocks end below `nextAddr`, and with an empty footprint, is sequential. -/
theorem seq_of_blocks {m : Mem} (hf : m.footprint = #[]) (hc : m.current < m.clocks.size)
    (hb : m.blocks.all (fun blk => !blk.live || decide (blk.addr + blk.bytes.size < m.nextAddr)) =
      true) : m.Seq := by
  refine ⟨singleThread_empty hf hc, fun l c hl => ?_⟩
  obtain ⟨blk, hblk, hlive, ho, rfl⟩ := Mem.heap_some hl
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.mp hblk
  have := (Array.all_eq_true.mp hb) l.1 hi
  rw [he, hlive] at this
  simpa using this

/-- A triple's precondition, split off a memory, rules out an error from every memory with the same
heap. -/
theorem no_error_of_triple {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} (ht : Triple P c Q)
    {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) (hp : P hP)
    (hs : m.Seq) {e : Error} (herr : errOf (c.run m) = some e) : False := by
  have := ht m hP hF hd hm hp hs
  rw [run_of_errOf herr] at this
  exact this

/-! ## O3: an atomic location of another size at `addr_hint` -/

/-- `mem0` with a 4-byte atomic location at `addr_hint`: the same heap. -/
def odd : Mem := { mem0 with atomics := #[{ block := 0, off := 0, len := 4, msgs := #[] }] }

theorem odd_heap : odd.heap = mem0.heap := rfl

theorem odd_seq : odd.Seq := seq_of_blocks rfl (by decide) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem alloc_odd : errOf ((vt.alloc ⟨none, 0⟩ 1 0 0).run odd) = some .unspecified := by
  decide +kernel

/-- `alloc` ignores the context pointer and the return address. -/
theorem alloc_args (c : Ptr) (len : BitVec 64) (k : Nat) (ra : BitVec 64) :
    vt.alloc c len k ra = vt.alloc ⟨none, 0⟩ len k 0 := by
  have e : heap_PageAllocator_alloc c len ⟨BitVec.ofNat 6 k⟩ ra =
      heap_PageAllocator_alloc ⟨none, 0⟩ len ⟨BitVec.ofNat 6 k⟩ 0 := by
    delta heap_PageAllocator_alloc; rfl
  show (fun m => Sched.run dispatch 16 (fun _ => 0) (heap_PageAllocator_alloc c len _ ra) m) = _
  rw [e]; rfl

set_option maxHeartbeats 0 in
/-- **O3.** No precondition that holds in (a part of) the heap at program start makes
`alloc(1 byte, alignment 1)` a triple of any logic. -/
theorem alloc_no_triple_at_start (L : Logic) (c : Ptr) (ra : BitVec 64) (P : Assn)
    (Q : Option Ptr → Assn) {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : mem0.heap = hP ∪ hF) (hp : P hP) : ¬ L.T P (vt.alloc c 1 0 ra) Q := by
  intro ht
  rw [alloc_args] at ht
  exact no_error_of_triple (L.toPartial ht) hd (by rw [odd_heap]; exact hm) hp odd_seq alloc_odd

/-- So no allocator invariant that holds at program start and admits a 1-byte request satisfies
`AllocSpec`, in any logic. -/
theorem not_allocSpec_at_start (L : Logic) (c : Ptr) (I : AllocInv)
    (hI : ∃ hP hF, Heap.Disjoint hP hF ∧ mem0.heap = hP ∪ hF ∧ I.own hP) (hfit : I.fits 1 0) :
    ¬ AllocSpec L vt c I := by
  intro hs
  obtain ⟨hP, hF, hd, hm, hp⟩ := hI
  exact alloc_no_triple_at_start L c 0 I.own _ hd hm hp
    (hs.alloc 1 0 0 (by decide) (by decide) hfit)

/-! ## O1: the hint points into a dead block -/

/-- `addr_hint` holds a pointer to block 6. -/
def hintBlocks : Array Block :=
  mem0.blocks.modify 0 fun b => { b with bytes := Enc.encode (some (⟨some 6, 0⟩ : Ptr)) }

/-- After a `free` of the last allocation: block 6 is an unmapped mapping at a page address, and
the hint points to it (the shape that `alloc` then `free` from `mem0` reaches). -/
def hinted : Mem :=
  { mem0 with
    blocks := hintBlocks.push
      ({ bytes := #[], align := 4096, kind := .mapped 0, live := false, addr := 8192 } : Block)
    nextAddr := 8192 + 4096 + 1 }

/-- The same heap; the dead block's metadata is not there. -/
def hintedLost : Mem := { hinted with blocks := hintBlocks }

theorem hinted_heap : hintedLost.heap = hinted.heap := by
  funext ⟨x, y⟩
  by_cases hx : x = hintBlocks.size
  · subst hx; simp [Mem.heap, hinted, hintedLost]
  · simp [Mem.heap, hinted, hintedLost, Array.getElem?_push, hx]

set_option maxHeartbeats 0 in
theorem hintedLost_seq : hintedLost.Seq := seq_of_blocks rfl (by decide) (by decide +kernel)

set_option maxHeartbeats 0 in
theorem alloc_hintedLost : errOf ((vt.alloc ⟨none, 0⟩ 1 0 0).run hintedLost) = some .illegal := by
  decide +kernel

/-- `alloc` of one byte then `free` from `mem0`: the shape `hinted` describes. -/
def cycle : Option Mem :=
  match ((vt.alloc ⟨none, 0⟩ 1 0 0).run mem0).run with
  | some (.ok (some p, m)) =>
    match ((vt.free ⟨none, 0⟩ ⟨p, 1⟩ 0 0).run m).run with
    | some (.ok (_, m')) => some m'
    | _ => none
  | _ => none

-- The real run: the hint points to block 6, which is unmapped, at a page address.
#guard (cycle.bind fun m => m.blocks[6]?.map fun b => (b.live, b.addr)) = some (false, 8192)
#guard (cycle.bind fun m => m.blocks[0]?.map fun b =>
  decide (b.bytes = Enc.encode (some (⟨some 6, 0⟩ : Ptr)))) = some true
-- From the real memory the next `alloc` succeeds; from `hinted` too (the model is fine natively).
#guard (cycle.map fun m => (errOf ((vt.alloc ⟨none, 0⟩ 1 0 0).run m)).isNone) = some true
#guard (errOf ((vt.alloc ⟨none, 0⟩ 1 0 0).run hinted)).isNone

set_option maxHeartbeats 0 in
/-- **O1.** No precondition that holds after the hinted block was unmapped makes `alloc` a
triple of any logic. -/
theorem alloc_no_triple_after_free (L : Logic) (c : Ptr) (ra : BitVec 64) (P : Assn)
    (Q : Option Ptr → Assn) {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : hinted.heap = hP ∪ hF) (hp : P hP) : ¬ L.T P (vt.alloc c 1 0 ra) Q := by
  intro ht
  rw [alloc_args] at ht
  exact no_error_of_triple (L.toPartial ht) hd (by rw [hinted_heap]; exact hm) hp hintedLost_seq
    alloc_hintedLost

end AllocTranslated.PageObstruction
