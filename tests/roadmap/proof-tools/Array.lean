import ZigLean.Sep.Array

open Zig Assn

-- The proof exposes a real store command and retains an independent heap allocation.
def updateMiddle (p : Ptr) (w : BitVec 32) : MemM Unit := store 4 (p.elem 4 1) w

theorem updateMiddle_contract (p q : Ptr) (first middle last w : BitVec 32)
    (A S : Nat) (other : Array Byte) :
    Triple (arr p [first, middle, last] ∗ bytesAt q A S .heap other)
      (updateMiddle p w)
      (fun _ => (pts (p.elem 4 1) 4 w ∗
        (arr p [first] ∗ arr (p.add 8) [last])) ∗ bytesAt q A S .heap other) := by
  simpa [updateMiddle, Enc.size, intSize, intAlign, alignUp] using
    (Triple.arr_store_focus (p := p) (vs := [first, middle, last]) (i := 1) (a := 4)
      (R := bytesAt q A S .heap other) (by decide) (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) w)

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

-- First and last elements retain empty boundary ranges explicitly.
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

-- A caller-supplied element load rule uses the same view; command/results are retained.
example (p : Ptr) (x y : BitVec 32) (R : Assn) :
    Triple (arr p [x, y] ∗ R) (load (BitVec 32) 4 (p.add 4))
      (fun v => ((⌜v = y⌝ ∗ pts (p.add 4) 4 y) ∗
        (arr p [x] ∗ arr (p.add 8) ([] : List (BitVec 32)))) ∗ R) := by
  simpa [Enc.size, intSize, intAlign, alignUp] using Triple.arr_focus_frame (p := p) (vs := [x, y]) (k := 1) (a := 4)
    (R := R) (by simp only [List.length_cons, List.length_nil]; decide) (by decide) (by decide) (Triple.load (by decide))

-- Bounds are proof obligations: one-past-end, empty focus, and invalid splits fail.
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

-- Nonempty typed ownership cannot overlap itself, independently of tactic matching.
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

-- After exposing a valid element, it cannot satisfy two overlapping requirements.
example (p : Ptr) (x y : BitVec 32) (c : MemM Unit)
    (rule : Triple (pts (p.add 4) 4 y ∗ pts (p.add 4) 4 y) c (fun _ => emp)) : True := by
  fail_if_success
    have : Triple (arr p [x] ∗ (pts (p.add 4) 4 y ∗ arr (p.add 8) [x])) c
        (fun _ => arr p [x] ∗ arr (p.add 8) [x]) := by sep_frame rule
  trivial

-- Array-aware framing requires neighbors and the independent allocation in the post.
example (p q : Ptr) (x y z w : BitVec 32) (A S : Nat) (other : Array Byte) : True := by
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ bytesAt q A S .heap other) (updateMiddle p w)
        (fun _ => pts (p.elem 4 1) 4 w) := by
      sep_frame (updateMiddle_contract p q x y z w A S other)
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ bytesAt q A S .heap other) (updateMiddle p w)
        (fun _ => (pts (p.elem 4 1) 4 w ∗ (arr p [x] ∗ arr (p.add 8) [z]))) := by
      sep_frame (updateMiddle_contract p q x y z w A S other)
  trivial

-- A store never promises the old selected value (or altered neighboring values).
example (p q : Ptr) (x y z w : BitVec 32) (A S : Nat) (other : Array Byte) : True := by
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ bytesAt q A S .heap other) (updateMiddle p w)
        (fun _ => (pts (p.elem 4 1) 4 y ∗
          (arr p [x] ∗ arr (p.add 8) [z])) ∗ bytesAt q A S .heap other) := by
      sep_frame (updateMiddle_contract p q x y z w A S other)
  fail_if_success
    have : Triple (arr p [x, y, z] ∗ bytesAt q A S .heap other) (updateMiddle p w)
        (fun _ => (pts (p.elem 4 1) 4 w ∗
          (arr p [w] ∗ arr (p.add 8) [z])) ∗ bytesAt q A S .heap other) := by
      sep_frame (updateMiddle_contract p q x y z w A S other)
  trivial
