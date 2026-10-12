import ZigLean.Sep.Full.AutoAll

/-!
Whole-array ownership in the full-state logic (`ZigLean/Sep/Full/Arr.lean`): the assertion
lemmas `arr_split`/`arr_focus` at their boundaries, and item loads and stores walked by `fsym`
with `FTotalTriple.arr_load`/`arr_store`, keeping the array whole and an independent allocation
in the frame. Bounds are obligations: a one-past-end item is rejected, and a walk never drops
the frame, keeps an old value or changes a neighbour.
-/

namespace ProofTools.ArrayTest

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

-- The proof walks a real store command and keeps an independent heap allocation.
def updateMiddle (p : Ptr) (w : BitVec 32) : MemM Unit := Zig.store 4 (p.elem 4 1) w

theorem updateMiddle_contract (p q : Ptr) (first middle last w : BitVec 32)
    (A S : Nat) (other : Array Byte) :
    FTotalTriple (up (arr p [first, middle, last]) ⋆ up (bytesAt q A S .heap other))
      (updateMiddle p w)
      (fun _ => up (arr p [first, w, last]) ⋆ up (bytesAt q A S .heap other)) := by
  unfold updateMiddle
  fsym

-- An item load returns the item and keeps the array and the frame.
example (p : Ptr) (x y : BitVec 32) (R : FAssn) :
    FTotalTriple (up (arr p [x, y]) ⋆ R) (Zig.load (BitVec 32) 4 (p.elem 4 1))
      (fun v => ⟪v = y⟫ ⋆ (up (arr p [x, y]) ⋆ R)) := by
  fsym

-- A symbolic index with its bound as a premise.
example (p : Ptr) (xs : List (BitVec 32)) (i : BitVec 64) (hi : i.toNat < xs.length) (w : BitVec 32) :
    FTotalTriple (up (arr p xs)) (Zig.store 4 (p.elem 4 i) w) (fun _ => up (arr p (xs.set i.toNat w))) := by
  fsym

/-! ## Assertion lemmas -/

-- The ownership theorem does not require encoding round-trip laws or positive size.
example (T : Type) [Enc T] (p : Ptr) (xs : List T) (h : Heap) (hp : arr p xs h)
    (hs : Enc.align T ∣ Enc.size T) (k : Nat) (hk : k ≤ xs.length) :
    (arr p (xs.take k) ∗ arr (p.add (Enc.size T * k)) (xs.drop k)) h :=
  arr_split hp hk hs

-- Splitting is valid at either endpoint and for an empty array.
example (p : Ptr) (xs : List (BitVec 32)) (h : Heap) (hp : arr p xs h) :
    (arr p ([] : List (BitVec 32)) ∗ arr p xs) h := by
  simpa [Ptr.add] using arr_split hp (k := 0) (by omega) (by decide)

example (p : Ptr) (xs : List (BitVec 32)) (h : Heap) (hp : arr p xs h) :
    (arr p xs ∗ arr (p.add (4 * xs.length)) ([] : List (BitVec 32))) h := by
  simpa [Enc.size, intSize, intAlign, alignUp] using arr_split hp (k := xs.length) (Nat.le_refl _) (by decide)

example (p : Ptr) (h : Heap) (hp : arr p ([] : List (BitVec 32)) h) :
    (arr p ([] : List (BitVec 32)) ∗ arr p ([] : List (BitVec 32))) h := by
  simpa [Ptr.add] using arr_split hp (k := 0) (by simp) (by decide)

-- First and last items keep empty boundary ranges explicitly.
example (p : Ptr) (x y : BitVec 32) (h : Heap) (hp : arr p [x, y] h) :
    (arr p ([] : List (BitVec 32)) ∗ (pts p 4 x ∗ arr (p.add 4) [y])) h := by
  simpa [Ptr.add, Enc.size, intSize, intAlign, alignUp] using arr_focus hp (k := 0) (a := 4) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide)

example (p : Ptr) (x y : BitVec 32) (h : Heap) (hp : arr p [x, y] h) :
    (arr p [x] ∗ (pts (p.add 4) 4 y ∗ arr (p.add 8) ([] : List (BitVec 32)))) h := by
  simpa [Enc.size, intSize, intAlign, alignUp] using arr_focus hp (k := 1) (a := 4) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide)

example (p : Ptr) (x : BitVec 32) (h : Heap) (hp : arr p [x] h) :
    (arr p ([] : List (BitVec 32)) ∗
      (pts p 4 x ∗ arr (p.add 4) ([] : List (BitVec 32)))) h := by
  simpa [Ptr.add, Enc.size, intSize, intAlign, alignUp] using arr_focus hp (k := 0) (a := 4) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide)

-- Nonempty typed ownership cannot overlap itself.
example (p : Ptr) (x : BitVec 32) (h : Heap) : ¬ (pts p 4 x ∗ pts p 4 x) h := by
  rintro ⟨h₁, h₂, hd, _, hp₁, hp₂⟩
  obtain ⟨_, _, _, bs₁, _, hs₁, _, hb₁, _⟩ := hp₁
  obtain ⟨_, _, _, bs₂, _, hs₂, _, hb₂, _⟩ := hp₂
  obtain ⟨b, hpb, _, hl₁⟩ := hb₁
  obtain ⟨b', hpb', _, hl₂⟩ := hb₂
  rw [hpb] at hpb'; cases hpb'
  have hpos₁ : 0 < bs₁.size := by rw [hs₁]; decide
  have hpos₂ : 0 < bs₂.size := by rw [hs₂]; decide
  have hne₁ : h₁ (b, p.off.toNat) ≠ none := by rw [hl₁]; simp [hpos₁]
  have hne₂ : h₂ (b, p.off.toNat) ≠ none := by rw [hl₂]; simp [hpos₂]
  exact (hd (b, p.off.toNat)).elim hne₁ hne₂

/-! ## Rejected -/

-- Bounds are obligations: a one-past-end focus or split, and a focus of the empty array, fail.
example (p : Ptr) (x : BitVec 32) (h : Heap) (hp : arr p [x] h) : True := by
  fail_if_success
    have := arr_focus hp (k := 1) (a := 4) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide)
  fail_if_success
    have := arr_split hp (k := 2) (by simp only [List.length_cons, List.length_nil]; decide) (by decide)
  trivial

example (p : Ptr) (h : Heap) (hp : arr p ([] : List (BitVec 32)) h) : True := by
  fail_if_success
    have := arr_focus hp (k := 0) (a := 4) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide)
  trivial

-- A one-past-end item is not walked.
example (p : Ptr) (x y w : BitVec 32) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [x, y])) (Zig.store 4 (p.elem 4 2) w)
        (fun _ => up (arr p [x, y])) := by fsym
  trivial

-- The frame (the independent allocation) is kept, not dropped.
example (p q : Ptr) (x y z w : BitVec 32) (A S : Nat) (other : Array Byte) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ up (bytesAt q A S .heap other)) (updateMiddle p w)
        (fun _ => up (arr p [x, w, z])) := by
      unfold updateMiddle; fsym
  trivial

-- A store never promises the old item or changed neighbours.
example (p q : Ptr) (x y z w : BitVec 32) (A S : Nat) (other : Array Byte) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ up (bytesAt q A S .heap other)) (updateMiddle p w)
        (fun _ => up (arr p [x, y, z]) ⋆ up (bytesAt q A S .heap other)) := by
      unfold updateMiddle; fsym
  fail_if_success
    have : FTotalTriple (up (arr p [x, y, z]) ⋆ up (bytesAt q A S .heap other)) (updateMiddle p w)
        (fun _ => up (arr p [w, w, z]) ⋆ up (bytesAt q A S .heap other)) := by
      unfold updateMiddle; fsym
  trivial

end ProofTools.ArrayTest

/-- info: 'ProofTools.ArrayTest.updateMiddle_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProofTools.ArrayTest.updateMiddle_contract
