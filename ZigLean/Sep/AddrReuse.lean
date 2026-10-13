import ZigLean.Sep.Alloc
import ZigLean.Sep.Total
import ZigLean.Mem.Reuse

/-!
# Address reuse in the legacy logic (M05; to be retired)

The facts of the block primitives and the placement are in `ZigLean/Mem/Reuse.lean`; the
full-state triples hold under every placement by `FTriple.withPlacement`/`FTotalTriple.withPlacement`
(`ZigLean/Sep/Full/Strength.lean`). This module keeps what is about the legacy logic and the
hand-written heap, for its remaining users (the legacy `Triple`s of `tutorials/memory-safety`):

* `Triple.withPlacement`, `TotalTriple.withPlacement`: every legacy triple holds under every
  placement and provenance mode (the frame rule included);
* `rawFree_stale`: `rawFree` of a dead block throws `.illegal`.
-/

namespace Zig

open Assn

@[simp] theorem Mem.heap_withPlacement (m : Mem) (σ : Placement) (pm : ProvenanceMode) :
    (m.withPlacement σ pm).heap = m.heap := rfl

theorem Mem.Seq.withPlacement {m : Mem} (h : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    (m.withPlacement σ pm).Seq := ⟨h.single⟩

/-- `std.mem.Allocator.free`/`destroy`'s `rawFree` of a dead block throws `.illegal`. -/
theorem rawFree_stale {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hd : blk.live = false) (off : Int) (n : Nat) :
    (rawFree ⟨some b, off⟩ n).run m = throw .illegal := by
  simp [rawFree, access_dead_block hb hd, zig_unfold]

/-- A triple holds from a memory with any placement and provenance mode: the frame rule, the
allocation and free rules and every client spec built from them are address-independent. -/
theorem Triple.withPlacement {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : Triple P c Q) {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    match (c.run (m.withPlacement σ pm)).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) =>
      ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  ht _ hP hF hd hm hp (hs.withPlacement σ pm)

theorem TotalTriple.withPlacement {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : TotalTriple P c Q) {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF)
    (hm : m.heap = hP ∪ hF) (hp : P hP) (hs : m.Seq) (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' hQ, c.run (m.withPlacement σ pm) = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
      m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  ht _ hP hF hd hm hp (hs.withPlacement σ pm)

end Zig
