import Proofs.Lists.Append

/-!
Generic containers: `std.ArrayListUnmanaged(u32).append`, the `u32` instance of Zig's generic
array list, translated from the std source. A successful append leaves the list `xs ++ [v]`
in the caller's part of the heap; the rest of the heap is untouched.

From the repository root:
  lake build Proofs.Lists.Append
  lake env lean tutorials/generic-containers/Main.lean

See tutorials/generic-containers/README.md for the source, the exercise and the negative control.
-/

namespace GenericContainers

open Lists Zig Assn

/-- A successful `append` gives the list with `v` at the end (possibly in a new buffer), and
keeps the frame `hF`. -/
theorem append_success (a : Allocator) (v : BitVec 32) {p ptr : Ptr} {cap : BitVec 64}
    {xs : List (BitVec 32)} {hL hF : Heap} {m m' : Mem}
    (list : alist p ptr cap xs hL) (heap : m.heap = hL ∪ hF) (disjoint : Heap.Disjoint hL hF)
    (hst : m.Seq) (items : ptrOk m ptr)
    (run : (array_list_Aligned_u32_null_append p a v).run m = pure (.ok (), m')) :
    ∃ hL' ptr' cap', m'.heap = hL' ∪ hF ∧ alist p ptr' cap' (xs ++ [v]) hL' := by
  obtain ⟨r, m₁, hr, -, hL', -, heap', post⟩ := append_run a v list heap disjoint hst items
  rw [run] at hr
  cases hr
  obtain ⟨ptr', cap', list', -⟩ := post
  exact ⟨hL', ptr', cap', heap', list'⟩

end GenericContainers
