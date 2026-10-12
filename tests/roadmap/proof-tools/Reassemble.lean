import ZigLean.Sep.Full.AutoAll

/-!
Memory-backed array reassembly (`ZigLean/Sep/Full/Arr.lean`). Disjoint parts alone need not agree
on their block's labels, so `arr_append_of_heap` and `arr_reassemble` take the actual memory's
heap; in the full-state logic the joins are updates (`EUpd.arr_join`, `EUpd.arr_unfocus`) that
read the labels from the memory, and `fsym` walks item stores with the array kept whole.
-/

namespace ProofTools.ReassembleTest

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-! ## Assertion lemmas -/

-- Reassembly consumes the actual-memory backing equality.
example (p : Ptr) (xs ys : List (BitVec 32)) (m : Mem) (h hF : Heap)
    (hp : (arr p xs ∗ arr (p.add (4 * xs.length)) ys) h) (hm : m.heap = h ∪ hF) :
    arr p (xs ++ ys) h := by
  exact arr_append_of_heap (by decide) hp hm

-- Empty boundary ranges and the empty array can be joined when backed by memory.
example (p : Ptr) (xs : List (BitVec 32)) (m : Mem) (h hF : Heap)
    (hp : (arr p ([] : List (BitVec 32)) ∗ arr p xs) h) (hm : m.heap = h ∪ hF) :
    arr p xs h := by
  simpa [Ptr.add] using arr_append_of_heap (xs := ([] : List (BitVec 32)))
    (by decide) (by simpa [Ptr.add] using hp) hm

example (p : Ptr) (xs : List (BitVec 32)) (m : Mem) (h hF : Heap)
    (hp : (arr p xs ∗ arr (p.add (4 * xs.length)) ([] : List (BitVec 32))) h)
    (hm : m.heap = h ∪ hF) : arr p xs h := by
  simpa using arr_append_of_heap (by decide) hp hm

example (p : Ptr) (m : Mem) (h hF : Heap)
    (hp : (arr p ([] : List (BitVec 32)) ∗ arr p ([] : List (BitVec 32))) h)
    (hm : m.heap = h ∪ hF) : arr p ([] : List (BitVec 32)) h := by
  simpa [Ptr.add] using arr_append_of_heap (xs := ([] : List (BitVec 32)))
    (ys := ([] : List (BitVec 32))) (by decide) (by simpa [Ptr.add] using hp) hm

-- Reassemble first, last, and singleton focus, with the updated value and original neighbours.
example (p : Ptr) (x y w : BitVec 32) (m : Mem) (h hF : Heap)
    (hp : (arr p ([] : List (BitVec 32)) ∗ (pts p 4 w ∗ arr (p.add 4) [y])) h)
    (hm : m.heap = h ∪ hF) : arr p [w, y] h := by
  simpa [Enc.size, Enc.align, intSize, intAlign, alignUp, Ptr.add] using
    arr_reassemble (xs := [x, y]) (k := 0) (w := w) (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide)
      (by simpa [Enc.size, Enc.align, intSize, intAlign, alignUp, Ptr.add] using hp) hm

example (p : Ptr) (x y w : BitVec 32) (m : Mem) (h hF : Heap)
    (hp : (arr p [x] ∗ (pts (p.add 4) 4 w ∗ arr (p.add 8) ([] : List (BitVec 32)))) h)
    (hm : m.heap = h ∪ hF) : arr p [x, w] h := by
  simpa [Enc.size, Enc.align, intSize, intAlign, alignUp] using
    arr_reassemble (xs := [x, y]) (k := 1) (w := w) (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide)
      (by simpa [Enc.size, Enc.align, intSize, intAlign, alignUp] using hp) hm

example (p : Ptr) (x w : BitVec 32) (m : Mem) (h hF : Heap)
    (hp : (arr p ([] : List (BitVec 32)) ∗ (pts p 4 w ∗ arr (p.add 4) ([] : List (BitVec 32)))) h)
    (hm : m.heap = h ∪ hF) : arr p [w] h := by
  simpa [Enc.size, Enc.align, intSize, intAlign, alignUp, Ptr.add] using
    arr_reassemble (xs := [x]) (k := 0) (w := w) (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide)
      (by simpa [Enc.size, Enc.align, intSize, intAlign, alignUp, Ptr.add] using hp) hm

-- Adjacent disjoint ranges with conflicting addresses cannot be backed by one memory.
example (b : BlockId) (m : Mem) (h₁ h₂ hF : Heap)
    (hp₁ : bytesAt ⟨some b, 0⟩ 0 2 .heap #[.int 1] h₁)
    (hp₂ : bytesAt ⟨some b, 1⟩ 1 2 .heap #[.int 2] h₂)
    (hm : m.heap = (h₁ ∪ h₂) ∪ hF) : False := by
  have hcell₁ : m.heap (b, 0) = some ⟨.int 1, 0, 2, .heap⟩ := by
    rw [hm, Heap.union_apply, Heap.union_apply]
    obtain ⟨b', hb', _, hl⟩ := hp₁
    cases hb'
    rw [hl]
    simp
  have hcell₂ : m.heap (b, 1) = some ⟨.int 2, 1, 2, .heap⟩ := by
    rw [hm, Heap.union_apply, Heap.union_apply]
    obtain ⟨b', hb', _, hl₁⟩ := hp₁
    obtain ⟨b'', hb'', _, hl₂⟩ := hp₂
    cases hb'; cases hb''
    rw [hl₁, hl₂]
    simp
  obtain ⟨blk, hb, _, _, hc⟩ := Mem.heap_some hcell₁
  obtain ⟨blk', hb', _, _, hc'⟩ := Mem.heap_some hcell₂
  rw [hb] at hb'; cases hb'
  simp only [Cell.mk.injEq] at hc hc'
  omega

/-! ## Updates and walks -/

-- Split and join as updates: the join reads the labels from the memory.
example (p : Ptr) (xs ys : List (BitVec 32)) :
    EUpd (up (arr p xs) ⋆ up (arr (p.add (4 * xs.length)) ys)) (up (arr p (xs ++ ys))) :=
  EUpd.arr_join (T := BitVec 32) (by decide)

-- Two independent item stores on whole-array ownership, without unfolding byte internals.
example (p : Ptr) (xs : List (BitVec 32)) (R : FAssn) (i j : BitVec 64)
    (hi : i.toNat < xs.length) (hj : j.toNat < xs.length) (first last : BitVec 32) :
    FTotalTriple (up (arr p xs) ⋆ R)
      (Zig.store 4 (p.elem 4 i) first >>= fun _ => Zig.store 4 (p.elem 4 j) last)
      (fun _ => up (arr p ((xs.set i.toNat first).set j.toNat last)) ⋆ R) := by
  fsym

/-! ## Rejected -/

-- The backing equality is a necessary premise, not invented by framing.
example (p : Ptr) (xs ys : List (BitVec 32)) (h : Heap)
    (hp : (arr p xs ∗ arr (p.add (4 * xs.length)) ys) h) : True := by
  fail_if_success
    have : arr p (xs ++ ys) h := by apply arr_append_of_heap (by decide) hp
  trivial

-- A one-past-end focus cannot be reassembled as a write to an in-bounds item.
example (p : Ptr) (x w : BitVec 32) (m : Mem) (h hF : Heap)
    (hp : (arr p [x] ∗ (pts (p.add 4) 4 w ∗ arr (p.add 8) ([] : List (BitVec 32)))) h)
    (hm : m.heap = h ∪ hF) : True := by
  fail_if_success
    have := arr_reassemble (xs := [x]) (k := 1) (w := w) (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) hp hm
  trivial

-- Duplicated ownership, a lost frame, the old value and a changed neighbour are rejected.
example (p : Ptr) (x y z w : BitVec 32) (R : FAssn) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ R) (Zig.store 4 (p.elem 4 1) w)
        (fun _ => up (arr p [x, w, z])) := by fsym
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ R) (Zig.store 4 (p.elem 4 1) w)
        (fun _ => up (arr p [x, y, z]) ⋆ R) := by fsym
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ R) (Zig.store 4 (p.elem 4 1) w)
        (fun _ => up (arr p [w, w, z]) ⋆ R) := by fsym
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ R) (Zig.store 4 (p.elem 4 1) w)
        (fun _ => up (arr p [x, w, z]) ⋆ (up (arr p [x, w, z]) ⋆ R)) := by fsym
  trivial

end ProofTools.ReassembleTest
