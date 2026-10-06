import ZigLean.Sep.Array.Reassemble

open Zig Assn

-- Reassembly explicitly consumes the actual-memory backing equality.
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

-- Reassemble first, last, and singleton focus, with the updated value and original neighbors.
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

-- Whole-array ownership supports a second independent store without unfolding byte internals.
example (p : Ptr) (xs : List (BitVec 32)) (R : Assn) (i j : BitVec 64)
    (hi : i.toNat < xs.length) (hj : j.toNat < xs.length) (first last : BitVec 32) :
    Triple (arr p xs ∗ R) (store 4 (p.elem 4 i) first >>= fun _ => store 4 (p.elem 4 j) last)
      (fun _ => arr p ((xs.set i.toNat first).set j.toNat last) ∗ R) := by
  exact Triple.bind (Triple.arr_store_reassemble (by decide) (by decide) hi first)
    (fun _ => Triple.arr_store_reassemble (by decide) (by decide)
      (by simpa only [List.length_set] using hj) last)

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

-- The backing equality is a necessary API premise, not invented by framing.
example (p : Ptr) (xs ys : List (BitVec 32)) (h : Heap)
    (hp : (arr p xs ∗ arr (p.add (4 * xs.length)) ys) h) : True := by
  fail_if_success
    have : arr p (xs ++ ys) h := by apply arr_append_of_heap (by decide) hp
  trivial

-- One-past-end focus cannot be reassembled as a write to an in-bounds element.
example (p : Ptr) (x w : BitVec 32) (m : Mem) (h hF : Heap)
    (hp : (arr p [x] ∗ (pts (p.add 4) 4 w ∗ arr (p.add 8) ([] : List (BitVec 32)))) h)
    (hm : m.heap = h ∪ hF) : True := by
  fail_if_success
    have := arr_reassemble (xs := [x]) (k := 1) (w := w) (by decide)
      (by simp only [List.length_cons, List.length_nil]; decide) hp hm
  trivial

-- Duplicated ownership, lost frames, old values, and altered neighbors are rejected.
example (p : Ptr) (x y z w : BitVec 32) (R : Assn) : True := by
  let rule := Triple.arr_store_reassemble (p := p) (xs := [x, y, z]) (i := 1) (R := R)
    (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) w
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ R) (store 4 (p.elem 4 1) w)
        (fun _ => arr p [x, w, z]) := by sep_frame rule
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ R) (store 4 (p.elem 4 1) w)
        (fun _ => arr p [x, y, z] ∗ R) := by sep_frame rule
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ R) (store 4 (p.elem 4 1) w)
        (fun _ => arr p [w, w, z] ∗ R) := by sep_frame rule
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ R) (store 4 (p.elem 4 1) w)
        (fun _ => arr p [x, w, z] ∗ arr p [x, w, z] ∗ R) := by sep_frame rule
  trivial
