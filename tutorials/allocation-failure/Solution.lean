import Proofs.Lists.Sep

/-! Exercise solution: a successful `push` adds exactly one new node, disjoint from the old
heap. -/

namespace AllocationFailure

open Lists Zig Assn

theorem push_success_adds_node (a : Allocator) (q : Option Ptr) (v : BitVec 32)
    (m m' : Mem) (hst : m.Seq) (p : Ptr)
    (run : ((push a q v).run m).run = some (.ok (.ok p, m'))) :
    ∃ hN, Heap.Disjoint hN m.heap ∧ m'.heap = hN ∪ m.heap ∧ node p v q hN := by
  have h := push_spec a q v m Heap.empty m.heap (Heap.disjoint_empty m.heap).symm
    (Heap.empty_union m.heap).symm rfl hst
  rw [run] at h
  obtain ⟨hN, disjoint, heap, isNode, -⟩ := h
  exact ⟨hN, disjoint, heap, isNode⟩

end AllocationFailure
