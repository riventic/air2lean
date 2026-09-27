import Proofs.Pointers.Gen
import ZigLean.Sep

/-!
# Separation-logic proofs about `examples/pointers/pointers.zig`

`swap` exchanges the values of two `u32` that do not overlap (`pts p 4 x ∗ pts q 4 y`), and
`swap(p, p)` keeps the value. The rest of the memory is unchanged.
-/

open Pointers Zig Assn

theorem swap_sep (p q : Ptr) (x y : BitVec 32) :
    Triple (pts p 4 x ∗ pts q 4 y) (swap p q) (fun _ => pts p 4 y ∗ pts q 4 x) := by
  apply Triple.of_run
  rintro m _ hF hd hm ⟨h₁, h₂, h₁₂, rfl, hp, hq⟩
  obtain ⟨h₁F, h₂F⟩ := Heap.disjoint_union_left.mp hd
  -- `p` with the frame `h₂ ∪ hF`, `q` with the frame `h₁ ∪ hF`.
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  have hm₂ : m.heap = h₂ ∪ (h₁ ∪ hF) := by rw [hm₁, Heap.union_left_comm h₁₂]
  have lx := pts_load_run hp hm₁ (by decide)
  have ly := pts_load_run hq hm₂ (by decide)
  obtain ⟨m₁, s₁, h₁', hd₁, hm₁', hp'⟩ :=
    pts_store_run hp hm₁ (Heap.disjoint_union_right.mpr ⟨h₁₂, h₁F⟩) (by decide) y
  obtain ⟨h₁'₂, h₁'F⟩ := Heap.disjoint_union_right.mp hd₁
  have hm₂' : m₁.heap = h₂ ∪ (h₁' ∪ hF) := by rw [hm₁', Heap.union_left_comm h₁'₂]
  obtain ⟨m₂, s₂, h₂', hd₂, hm₂'', hq'⟩ :=
    pts_store_run hq hm₂' (Heap.disjoint_union_right.mpr ⟨h₁'₂.symm, h₂F⟩) (by decide) x
  obtain ⟨h₂'₁, h₂'F⟩ := Heap.disjoint_union_right.mp hd₂
  refine ⟨(), m₂, h₁' ∪ h₂', ?_, Heap.disjoint_union_left.mpr ⟨h₁'F, h₂'F⟩, ?_,
    h₁', h₂', h₂'₁.symm, rfl, hp', hq'⟩
  · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at lx ly s₁ s₂
    simp [swap, zig_unfold, lx, ly, s₁, s₂]
  · rw [hm₂'', Heap.union_left_comm h₂'₁, ← Heap.union_assoc]

/-- `swap(p, p)` keeps the value. -/
theorem swap_self_sep (p : Ptr) (x : BitVec 32) :
    Triple (pts p 4 x) (swap p p) (fun _ => pts p 4 x) := by
  apply Triple.of_run
  intro m h hF hd hm hp
  have lx := pts_load_run hp hm (by decide)
  obtain ⟨m₁, s₁, h₁, hd₁, hm₁, hp₁⟩ := pts_store_run hp hm hd (by decide) x
  have lx' := pts_load_run hp₁ hm₁ (by decide)
  obtain ⟨m₂, s₂, h₂, hd₂, hm₂, hp₂⟩ := pts_store_run hp₁ hm₁ hd₁ (by decide) x
  refine ⟨(), m₂, h₂, ?_, hd₂, hm₂, hp₂⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at lx s₁ s₂
  simp [swap, zig_unfold, lx, s₁, s₂]
