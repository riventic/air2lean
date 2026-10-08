import ZigLean.Sep.Total
import ZigLean.Witness

/-!
# Admissible memories for claim witnesses

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) ask for an admissible
input of a triple: a memory `m` with `m.Seq` whose heap splits into the precondition's part and
a disjoint frame. The default memory (no blocks, one thread, empty footprint) with two empty
heaps is one, for any precondition that holds of the empty heap (`emp`, pure assertions).
-/

namespace Zig

theorem Mem.seq_default : ({} : Mem).Seq :=
  ⟨singleThread_empty rfl (by decide), fun l c h => by
    obtain ⟨b, o⟩ := l; simp [Mem.heap] at h⟩

theorem Mem.heap_default : ({} : Mem).heap = Heap.empty := by
  funext l; obtain ⟨b, o⟩ := l; simp [Mem.heap]; rfl

theorem Mem.heap_default_split : ({} : Mem).heap = Heap.empty ∪ Heap.empty := by
  simp [Mem.heap_default]

end Zig
