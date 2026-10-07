import Proofs.Lists.Append

/-! Exercise solution: a failed `append` reports `error.OutOfMemory` and keeps the old list,
buffer and capacity. -/

namespace GenericContainers

open Lists Zig Assn

theorem append_failure (a : Allocator) (v : BitVec 32) {p ptr : Ptr} {cap : BitVec 64}
    {xs : List (BitVec 32)} {hL hF : Heap} {m m' : Mem} {e : ErrName}
    (list : alist p ptr cap xs hL) (heap : m.heap = hL ∪ hF) (disjoint : Heap.Disjoint hL hF)
    (hst : m.Seq) (items : ptrOk m ptr)
    (run : (array_list_Aligned_u32_null_append p a v).run m = pure (.error e, m')) :
    e = "OutOfMemory" ∧ ∃ hL', m'.heap = hL' ∪ hF ∧ alist p ptr cap xs hL' := by
  obtain ⟨r, m₁, hr, -, hL', -, heap', post⟩ := append_run a v list heap disjoint hst items
  rw [run] at hr
  cases hr
  obtain ⟨oom, list', -⟩ := post
  exact ⟨oom, hL', heap', list'⟩

end GenericContainers
