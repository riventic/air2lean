import ZigLean.Sep.Alloc
import ZigLean.Sep.Total
import ZigLean.Mem.Null

/-!
# Address reuse (M05)

Real allocators reuse the address of a freed block. The placement oracle (`Mem.place`,
`docs/address-placement.md`) can give any block any valid address (`Mem.placeOk`), for example the
address of a dead block. Block ids stay unique (`docs/address-reuse.md`).

Lifetime safety does not depend on addresses: `Mem.access` and `free` check the block that a
pointer's provenance names, never an address. This file states that for every placement:

* `afterAlloc_old`: an allocation leaves every existing block, dead or live, unchanged, so it
  never revives a freed block, even one whose address it reuses;
* `access_stale`, `free_stale`: an access or a free through a pointer to a dead block throws
  `.illegal` after any allocations (use after free, double free);
* `Triple.withPlacement`, `TotalTriple.withPlacement`: every separation-logic triple holds under
  every placement and provenance mode (the frame rule included): a triple quantifies over all
  memories, and `alloc_run` (`ZigLean/Sep/Block.lean`) holds for every address `alloc` gives;
* `reuse_witness`: reuse happens: a freed block's address is given to a new block, and a pointer
  to the freed block is still dangling.

The address-sensitive operations are separate: `@ptrFromInt` (`ptrFromAddr`) of an address that
a dead and a reused block both cover gives a pointer with no provenance (`⟨none, n⟩`: its address,
every access `.illegal`) unless the program declares the `ProvenanceMode.liveBlock` contract
(`stale_int_strict`, `stale_int_liveBlock`).
-/

namespace Zig

open Assn

/-- `m` with the placement `σ` and the provenance mode `pm`. -/
def Mem.withPlacement (m : Mem) (σ : Placement) (pm : ProvenanceMode := .strict) : Mem :=
  { m with place := σ, allocPolicy := { m.allocPolicy with provenance := pm } }

@[simp] theorem Mem.heap_withPlacement (m : Mem) (σ : Placement) (pm : ProvenanceMode) :
    (m.withPlacement σ pm).heap = m.heap := rfl

theorem Mem.Seq.withPlacement {m : Mem} (h : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    (m.withPlacement σ pm).Seq := ⟨h.single⟩

/-! ## Lifetimes follow block ids -/

/-- An allocation, at a fresh or a reused address, leaves every existing block as it was. -/
theorem afterAlloc_old (m : Mem) (kind : BlockKind) (size align : Nat) {b : BlockId}
    (hb : b < m.blocks.size) : (m.afterAlloc kind size align).blocks[b]? = m.blocks[b]? := by
  simp [Mem.afterAlloc, Array.getElem?_push, Nat.ne_of_lt hb]

/-- The new block's id is not the id of any existing block, whatever its address. -/
theorem alloc_new_id (m : Mem) (kind : BlockKind) (size align : Nat) {b : BlockId} {blk : Block}
    (hb : m.blocks[b]? = some blk) :
    ∃ p m', (alloc kind size align).run m = pure (p, m') ∧ p.block ≠ some b := by
  refine ⟨⟨some m.blocks.size, 0⟩, _, alloc_run_eq m kind size align, fun h => ?_⟩
  have hlt := (Array.getElem?_eq_some_iff.mp hb).1
  have he : m.blocks.size = b := Option.some.inj h
  omega

/-- A pointer to a dead block cannot access memory. -/
theorem access_dead_block {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (off : Int) (n a : Nat) :
    m.access ⟨some b, off⟩ n a = throw .illegal := by
  simp [Mem.access, hb, hd]

/-- Use after free under every reuse policy: after a free and any number of allocations, at any
addresses (also the freed block's own), an access through the stale pointer throws `.illegal`. -/
theorem access_stale {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (allocs : List (BlockKind × Nat × Nat)) (off : Int) (n a : Nat) :
    (allocs.foldl (fun m (k, s, al) => m.afterAlloc k s al) m).access ⟨some b, off⟩ n a =
      throw .illegal := by
  induction allocs generalizing m with
  | nil => exact access_dead_block hb hd off n a
  | cons x xs ih =>
    obtain ⟨k, s, al⟩ := x
    refine ih ?_
    rw [afterAlloc_old m k s al (Array.getElem?_eq_some_iff.mp hb).1, hb]

/-- Double free under every reuse policy: a free through a pointer to a dead block throws
`.illegal`, also when a live block now has its address. -/
theorem free_stale {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (off : Int) : (free ⟨some b, off⟩).run m = throw .illegal := by
  simp [free, hb, hd, zig_unfold]

/-- `std.mem.Allocator.free`/`destroy`'s `rawFree` of a dead block throws `.illegal`. -/
theorem rawFree_stale {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (off : Int) (n : Nat) :
    (rawFree ⟨some b, off⟩ n).run m = throw .illegal := by
  simp [rawFree, access_dead_block hb hd, zig_unfold]

/-! ## Every triple holds under every placement -/

/-- A triple holds from a memory with any placement and provenance mode: the frame rule, the
allocation and free rules and every client spec built from them are address-independent. -/
theorem Triple.withPlacement {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : Triple P c Q) {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    match (c.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  ht _ hP hF hd hm hp (hs.withPlacement σ pm)

theorem TotalTriple.withPlacement {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : TotalTriple P c Q) {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' hQ, c.run (m.withPlacement σ pm) = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  ht _ hP hF hd hm hp (hs.withPlacement σ pm)

/-! ## Reuse happens, and the stale pointer stays dangling -/

/-- The result of a run of `x` from `m`, without the final memory (for kernel checks). -/
def runValue {α : Type} (x : MemM α) (m : Mem) : Option (Except Error α) :=
  (x.run m).run.map (·.map Prod.fst)

/-- The placement of the witnesses: block 1 at 4096, the address of block 0 under
`Placement.fresh`; every other block fresh. -/
def reuseFirst : Placement := ⟨fun b => if b = 1 then some 4096 else none⟩

/-- Allocate 8 bytes, free them, allocate 8 bytes again; the two addresses and the new block. -/
def reuseRun : MemM (Int × Int × Option BlockId) := do
  let p ← alloc .heap 8 8
  free p
  let q ← alloc .heap 8 8
  pure (← ptrAddr p, ← ptrAddr q, q.block)

/-- Under `reuseFirst`, block 1 gets block 0's address. -/
theorem reuse_witness :
    runValue reuseRun (({} : Mem).withPlacement reuseFirst) =
      some (.ok (4096, 4096, some 1)) := by decide +kernel

/-- Under `Placement.fresh` the second block gets a new address. -/
theorem fresh_witness : runValue reuseRun {} = some (.ok (4096, 4112, some 1)) := by decide +kernel

/-- Allocate, free, allocate again at the same address, store 7 in the new block, then load
through the freed block's pointer. -/
def staleLoadRun : MemM (BitVec 64) := do
  let p ← alloc .heap 8 8
  free p
  let q ← alloc .heap 8 8
  store 8 q (7#64)
  load (BitVec 64) 8 p

/-- The freed block's pointer still names block 0: the load throws `.illegal`, though a live
block now occupies exactly its address. -/
theorem reuse_stale_load :
    runValue staleLoadRun (({} : Mem).withPlacement reuseFirst) = some (.error .illegal) := by
  decide +kernel

/-! ## Stale integer addresses (`@ptrFromInt`) -/

/-- Allocate, keep the integer address, free, reallocate, store 7 in the new block, and load
through `@ptrFromInt` of the kept integer. -/
def staleIntRun : MemM (BitVec 64) := do
  let p ← alloc .heap 8 8
  let n ← ptrAddr p
  free p
  let q ← alloc .heap 8 8
  store 8 q (7#64)
  let r ← ptrFromAddr n.toNat
  load (BitVec 64) 8 r

/-- Strict provenance (the default mode): the stale integer does not silently gain the new
block's provenance. Two blocks cover the address, so the recovery has no provenance and the load
through it is `.illegal`; the naive address reasoning "the integer is the new block's address, so
the load reads 7" is not a theorem of the model. -/
theorem stale_int_strict :
    runValue staleIntRun (({} : Mem).withPlacement reuseFirst) = some (.error .illegal) := by
  decide +kernel

/-- The ambiguous recovery keeps the address: `@intFromPtr` of it is the integer again. -/
def staleIntRoundTrip : MemM Bool := do
  let p ← alloc .heap 8 8
  let n ← ptrAddr p
  free p
  let _ ← alloc .heap 8 8
  let r ← ptrFromAddr n.toNat
  pure (decide ((← ptrAddr r) = n))

theorem stale_int_roundTrip :
    runValue staleIntRoundTrip (({} : Mem).withPlacement reuseFirst) = some (.ok true) := by
  decide +kernel

/-- `==` of the ambiguous recovery and the new block's pointer compares addresses: equal. -/
def staleIntEq : MemM Bool := do
  let p ← alloc .heap 8 8
  let n ← ptrAddr p
  free p
  let q ← alloc .heap 8 8
  let r ← ptrFromAddr n.toNat
  ptrEqAddr r q

theorem stale_int_eq :
    runValue staleIntEq (({} : Mem).withPlacement reuseFirst) = some (.ok true) := by
  decide +kernel

/-- The address-sensitive contract `.liveBlock`: the program declares that the address recovers
the live block's provenance, and the load reads the new block's 7. -/
theorem stale_int_liveBlock :
    runValue staleIntRun (({} : Mem).withPlacement reuseFirst .liveBlock) = some (.ok 7#64) := by
  decide +kernel

/-- Under `Placement.fresh` the integer recovers the dead block, and the load is a use after
free. -/
theorem stale_int_fresh : runValue staleIntRun {} = some (.error .illegal) := by decide +kernel

end Zig
