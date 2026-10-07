import Proofs.Lists.Sep

/-!
Allocation failure: `push` allocates a list node with `try a.create(Node)`. When the allocator
fails, `push` returns `error.OutOfMemory` and leaves the heap exactly as it was: no leak, no
partial node, no panic.

From the repository root:
  lake build Proofs.Lists.Sep
  lake env lean tutorials/allocation-failure/Main.lean

See tutorials/allocation-failure/README.md for the source, the exercise and the negative control.
-/

namespace AllocationFailure

open Lists Zig Assn

/-- A failed `push` returns `error.OutOfMemory` and the final heap is the initial heap. -/
theorem push_failure_keeps_heap (a : Allocator) (q : Option Ptr) (v : BitVec 32)
    (m m' : Mem) (hst : m.Seq) (e : ErrName)
    (run : ((push a q v).run m).run = some (.ok (.error e, m'))) :
    e = "OutOfMemory" ∧ m'.heap = m.heap := by
  have h := push_spec a q v m Heap.empty m.heap (Heap.disjoint_empty m.heap).symm
    (Heap.empty_union m.heap).symm rfl hst
  rw [run] at h
  obtain ⟨hQ, -, heap, ⟨oom, rfl⟩, -⟩ := h
  exact ⟨oom, by simpa using heap⟩

end AllocationFailure
