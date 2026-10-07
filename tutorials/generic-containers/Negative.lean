import Proofs.Lists.Append

/-! Negative control: Lean must reject this file. `append` puts `v` at the end, not at the
front, so the proof of `append_success` cannot establish `v :: xs`. -/
-- expect-error: Application type mismatch

namespace GenericContainers

open Lists Zig Assn

theorem append_prepends (a : Allocator) (v : BitVec 32) {p ptr : Ptr} {cap : BitVec 64}
    {xs : List (BitVec 32)} {hL hF : Heap} {m m' : Mem}
    (list : alist p ptr cap xs hL) (heap : m.heap = hL ∪ hF) (disjoint : Heap.Disjoint hL hF)
    (hst : m.Seq) (items : ptrOk m ptr)
    (run : (array_list_Aligned_u32_null_append p a v).run m = pure (.ok (), m')) :
    ∃ hL' ptr' cap', m'.heap = hL' ∪ hF ∧ alist p ptr' cap' (v :: xs) hL' := by
  obtain ⟨r, m₁, hr, -, hL', -, heap', post⟩ := append_run a v list heap disjoint hst items
  rw [run] at hr
  cases hr
  obtain ⟨ptr', cap', list', -⟩ := post
  exact ⟨hL', ptr', cap', heap', list'⟩

end GenericContainers
