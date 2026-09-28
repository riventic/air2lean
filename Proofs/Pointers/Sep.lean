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
  rintro m _ hF hd hm ⟨h₁, h₂, h₁₂, rfl, hp, hq⟩ hst
  obtain ⟨h₁F, h₂F⟩ := Heap.disjoint_union_left.mp hd
  -- `p` with the frame `h₂ ∪ hF`, `q` with the frame `h₁ ∪ hF`. `swap` reads `p` then `q` then
  -- writes `p` then `q`: each step mutates memory (`Mem.recordAt`), so it runs on the previous
  -- step's output memory, not on `m` directly.
  have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
  obtain ⟨mA, lx, hmA, hstA⟩ := pts_load_run hp hm₁ (by decide) hst
  have hmA₂ : mA.heap = h₂ ∪ (h₁ ∪ hF) := by rw [hmA, Heap.union_left_comm h₁₂]
  obtain ⟨mB, ly, hmB, hstB⟩ := pts_load_run hq hmA₂ (by decide) hstA
  have hmB₁ : mB.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hmB, Heap.union_left_comm h₁₂.symm]
  obtain ⟨mC, s₁, hstC, h₁', hd₁, hmC, hp'⟩ :=
    pts_store_run hp hmB₁ (Heap.disjoint_union_right.mpr ⟨h₁₂, h₁F⟩) (by decide) hstB y
  obtain ⟨h₁'₂, h₁'F⟩ := Heap.disjoint_union_right.mp hd₁
  have hmC₂ : mC.heap = h₂ ∪ (h₁' ∪ hF) := by rw [hmC, Heap.union_left_comm h₁'₂]
  obtain ⟨mD, s₂, hstD, h₂', hd₂, hmD, hq'⟩ :=
    pts_store_run hq hmC₂ (Heap.disjoint_union_right.mpr ⟨h₁'₂.symm, h₂F⟩) (by decide) hstC x
  obtain ⟨h₂'₁, h₂'F⟩ := Heap.disjoint_union_right.mp hd₂
  refine ⟨(), mD, h₁' ∪ h₂', ?_, Heap.disjoint_union_left.mpr ⟨h₁'F, h₂'F⟩, ?_,
    ⟨h₁', h₂', h₂'₁.symm, rfl, hp', hq'⟩, hstD⟩
  · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at lx ly s₁ s₂
    simp [swap, zig_unfold, lx, ly, s₁, s₂]
  · rw [hmD, Heap.union_left_comm h₂'₁, ← Heap.union_assoc]

/-- `swap(p, p)` keeps the value. -/
theorem swap_self_sep (p : Ptr) (x : BitVec 32) :
    Triple (pts p 4 x) (swap p p) (fun _ => pts p 4 x) := by
  apply Triple.of_run
  intro m h hF hd hm hp hst
  -- Both reads are of `p`; nothing is written in between, so both return `x`. Each read still
  -- mutates memory via `Mem.recordAt`, so the second read and both writes run on the previous
  -- step's output memory.
  obtain ⟨mA, lx1, hmA, hstA⟩ := pts_load_run hp hm (by decide) hst
  obtain ⟨mB, lx2, hmB, hstB⟩ := pts_load_run hp hmA (by decide) hstA
  obtain ⟨mC, s₁, hstC, h₁, hd₁, hmC, hp₁⟩ := pts_store_run hp hmB hd (by decide) hstB x
  obtain ⟨mD, s₂, hstD, h₂, hd₂, hmD, hp₂⟩ := pts_store_run hp₁ hmC hd₁ (by decide) hstC x
  refine ⟨(), mD, h₂, ?_, hd₂, hmD, hp₂, hstD⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at lx1 lx2 s₁ s₂
  simp [swap, zig_unfold, lx1, lx2, s₁, s₂]
