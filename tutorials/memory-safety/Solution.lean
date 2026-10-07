import Proofs.Lists.Sep

/-! Exercise solution: reversing a list and then freeing it leaks nothing. From every
single-threaded memory that holds the list `list hd xs` as part of its heap, the run returns
(so it throws no `.illegal`), and the live heap after it is the rest of the heap: every node of
the list is freed and no other byte changed. -/

namespace MemorySafety.Exercise

open Zig Assn Lists

/-- Reverse the list at `hd` with the generated `reverse`, then free it with the generated
`freeAll`. -/
def reverseThenFree (a : Allocator) (hd : Option Ptr) : MemM Unit :=
  reverse hd >>= fun r => freeAll a r

theorem reverseThenFree_total (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32)) :
    TotalTriple (list hd xs) (reverseThenFree a hd) (fun _ => emp) :=
  TotalTriple.bind (reverse_total hd xs) (fun r => freeAll_total a r xs.reverse)

theorem reverseThenFree_no_leak (a : Allocator) (hd : Option Ptr) (xs : List (BitVec 32))
    (m : Mem) (hL hR : Heap) (hs : m.Seq) (hdj : Heap.Disjoint hL hR) (hm : m.heap = hL ∪ hR)
    (hl : list hd xs hL) :
    ∃ m', (reverseThenFree a hd).run m = pure ((), m') ∧ m'.heap = hR := by
  obtain ⟨_, m', hQ, hr, -, hm', hemp, -⟩ := reverseThenFree_total a hd xs m hL hR hdj hm hl hs
  subst hemp
  exact ⟨m', hr, by simpa using hm'⟩

end MemorySafety.Exercise
