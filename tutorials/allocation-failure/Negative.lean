import Proofs.Lists.Sep

/-! Negative control: Lean must reject this file. `push` can fail, so no proof shows that
every run returns a node; the failure branch of `push_spec` has no pointer to offer. -/
-- expect-error: Type mismatch

namespace AllocationFailure

open Lists Zig Assn

theorem push_never_fails (a : Allocator) (q : Option Ptr) (v : BitVec 32)
    (m m' : Mem) (hst : m.Seq) (e : ErrName)
    (run : ((push a q v).run m).run = some (.ok (.error e, m'))) :
    False := by
  have h := push_spec a q v m Heap.empty m.heap (Heap.disjoint_empty m.heap).symm
    (Heap.empty_union m.heap).symm rfl hst
  rw [run] at h
  obtain ⟨hQ, -, heap, ⟨oom, rfl⟩, -⟩ := h
  exact oom

end AllocationFailure
