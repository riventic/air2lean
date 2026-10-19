import ZigLean.Sep.Base.Pts

/-! # Heap vocabulary shared by the full-state and retiring concurrency layers -/

namespace Zig

open Assn

/-- The cells of `h` that `h₁` does not have. -/
def Heap.diff (h h₁ : Heap) : Heap := fun l => if h₁ l = none then h l else none

/-- A part of the memory's heap: the heap is that part with the rest as a frame. -/
theorem heap_eq_union_of_sub {m : Mem} {h : Heap} (hs : h.Sub m.heap) : m.heap = h ∪ m.heap := by
  funext l; simp only [Heap.union_apply]
  cases e : h l with
  | none => rfl
  | some c => rw [hs l c e]; rfl

/-- Owned bytes that are part of the memory put their offsets in bounds (one past the end
included). -/
theorem bytesAt_inBounds_sub {m : Mem} {h : Heap} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hs : h.Sub m.heap) {k : Nat} (hk : k ≤ bs.size)
    (hpos : 0 < bs.size) : m.inBounds (p.add k) = true :=
  bytesAt_inBounds hb (heap_eq_union_of_sub hs) hk hpos

/-- Owned bytes record their block's size `S` (`Cell.size`): any offset up to `S` of a pointer
into the same block is in bounds. -/
theorem bytesAt_inBounds_block {m : Mem} {h : Heap} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hs : h.Sub m.heap) (hpos : 0 < bs.size)
    {q : Ptr} (hq : q.block = p.block) (h0 : 0 ≤ q.off) (hk : q.off ≤ S) :
    m.inBounds q = true := by
  obtain ⟨b, hpb, -, hcells⟩ := hb
  have hc : h (b, p.off.toNat) = some ⟨bs[0]!, A, S, K⟩ := by
    rw [hcells]; simp [hpos]
  obtain ⟨blk, hblk, -, ho, hcell⟩ := Mem.heap_some (hs _ _ hc)
  simp only [Cell.mk.injEq] at hcell
  exact inBounds_of (hq.trans hpb) hblk h0 (by omega)

/-- Owned bytes that are part of the memory put their offsets in bounds: a pointer into them
(one past the end included) is formed (`ptrProject`, MM-3). -/
theorem bytesAt_ptrProject_sub {m : Mem} {h : Heap} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hs : h.Sub m.heap) {k : Nat} (hk : k ≤ bs.size)
    (hpos : 0 < bs.size) : (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  bytesAt_ptrProject_run hb (heap_eq_union_of_sub hs) hk hpos

/-- `bytesAt_ptrProject_sub` up to the end of the block (`S`), not just of `bs`. -/
theorem bytesAt_ptrProject_block {m : Mem} {h : Heap} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hs : h.Sub m.heap) (hpos : 0 < bs.size)
    {k : Nat} (hk : p.off + k ≤ S) :
    (ptrProject p (·.add k)).run m = pure (p.add k, m) :=
  have h0 : 0 ≤ p.off := by obtain ⟨_, _, h0, _⟩ := hb; exact h0
  ptrProject_add_run (bytesAt_inBounds_block hb hs hpos rfl h0 (by omega))
    (bytesAt_inBounds_block hb hs hpos rfl (by rw [Ptr.add_off]; omega) (by rw [Ptr.add_off]; omega))

namespace Heap

variable {h h₁ h₂ : Heap}

theorem Sub.ne {l : Loc} (hs : h₁.Sub h) (hl : h₁ l ≠ none) : h l ≠ none := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hl
  rw [hs l c hc]; simp

theorem sub_union_left : h₁.Sub (h₁ ∪ h₂) := fun l c hc => by simp [hc]

theorem sub_union_right (hd : Disjoint h₁ h₂) : h₂.Sub (h₁ ∪ h₂) := fun l c hc => by
  rcases hd l with e | e
  · simp [e, hc]
  · rw [e] at hc; cases hc

theorem Sub.trans {h₃ : Heap} (h12 : h₁.Sub h₂) (h23 : h₂.Sub h₃) : h₁.Sub h₃ :=
  fun l c hc => h23 l c (h12 l c hc)

theorem union_sub {h₃ : Heap} (h1 : h₁.Sub h₃) (h2 : h₂.Sub h₃) : (h₁ ∪ h₂).Sub h₃ := by
  intro l c hc
  simp only [union_apply] at hc
  cases e : h₁ l with
  | none => rw [e] at hc; exact h2 l c (by simpa using hc)
  | some c' => rw [e] at hc; simp only [Option.some_or, Option.some.injEq] at hc; subst hc; exact h1 l _ e

/-- `h` is `h₁` and the rest. -/
theorem diff_split (hs : h₁.Sub h) : h = h₁ ∪ h.diff h₁ ∧ Disjoint h₁ (h.diff h₁) := by
  refine ⟨funext fun l => ?_, fun l => ?_⟩
  · cases e : h₁ l with
    | none => simp [diff, e]
    | some c => rw [Heap.union_apply, e, hs l c e]; rfl
  · cases e : h₁ l <;> simp [diff, e]

/-- A part disjoint from `h₁` is a part of the rest. -/
theorem sub_diff {h₃ : Heap} (hs : h₃.Sub h) (hd : Disjoint h₃ h₁) : h₃.Sub (h.diff h₁) := by
  intro l c hc
  rcases hd l with e | e
  · rw [e] at hc; cases hc
  · simp [diff, e, hs l c hc]

theorem disjoint_sub {h₃ : Heap} (hd : Disjoint h₁ h₂) (hs : h₃.Sub h₂) : Disjoint h₁ h₃ := by
  intro l
  rcases hd l with e | e
  · exact .inl e
  · right; cases e' : h₃ l with
    | none => rfl
    | some c => rw [hs l c e'] at e; cases e

end Heap

/-- A part of a separating conjunction is part of any heap that contains the whole. -/
theorem sep_sub_left {P Q : Assn} {h h' : Heap} (hpq : (P ∗ Q) h) (hs : h.Sub h') :
    ∃ hp, P hp ∧ hp.Sub h' := by
  obtain ⟨hp, hq, -, rfl, hP, -⟩ := hpq
  exact ⟨hp, hP, Heap.sub_union_left.trans hs⟩

theorem sep_sub_right {P Q : Assn} {h h' : Heap} (hpq : (P ∗ Q) h) (hs : h.Sub h') :
    ∃ hq, Q hq ∧ hq.Sub h' := by
  obtain ⟨hp, hq, hd, rfl, -, hQ⟩ := hpq
  exact ⟨hq, hQ, (Heap.sub_union_right hd).trans hs⟩

end Zig
