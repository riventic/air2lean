import ZigLean.Sep.Block
import ZigLean.Mem.Alloc

/-!
# The allocator

Rules for the allocator model (`ZigLean/Mem/Alloc.lean`). An allocation gives a new block of kind
`.heap` that nothing else owns, or `error.OutOfMemory` and no bytes: `Mem.failAt` decides, and a
triple holds for every memory, so a spec covers both. A free needs the whole block, of kind `.heap`.
-/

namespace Zig

open Assn

/-- The memory with a new allocation count has the same heap. -/
theorem Mem.heap_allocs (m : Mem) (k : Nat) : ({ m with allocs := k } : Mem).heap = m.heap := rfl

/-- `rawAlloc` gives `none` and changes no byte, or a new heap block, as `alloc_run`. -/
theorem rawAlloc_run {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (n align : Nat) (ha : 0 < align) (hst : m.SingleThread) :
    ∃ r m', (rawAlloc n align).run m = pure (r, m') ∧ m'.SingleThread ∧
      match r with
      | none => m'.heap = h ∪ hF
      | some p => p.off = 0 ∧ ∃ h', Heap.Disjoint (h ∪ h') hF ∧ m'.heap = (h ∪ h') ∪ hF ∧
          Heap.Disjoint h h' ∧ ∃ A, A % align = 0 ∧ bytesAt p A n .heap (Array.replicate n .undef) h' := by
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hm₁ : m₁.heap = h ∪ hF := by rw [Mem.heap_allocs]; exact hm
  by_cases hc : m.failAt = some m.allocs ∨ maxAllocBytes < n
  · refine ⟨none, m₁, ?_, hst, hm₁⟩
    simp [rawAlloc, hc, zig_unfold, m₁, set, StateT.set, MonadStateOf.set]
  · obtain ⟨p, m', h', hr, h0, hd', hm', hdd, hst', A, hA, hb⟩ := alloc_run hd hm₁ .heap n align ha hst
    refine ⟨some p, m', ?_, hst', h0, h', hd', hm', hdd, A, hA, hb⟩
    simp only [StateT.run] at hr
    simp [rawAlloc, hc, zig_unfold, set, StateT.set, MonadStateOf.set, m₁] at hr ⊢
    simp [hr, ExceptT.bindCont]

/-- `rawFree` of a whole heap block (from offset 0, all `S > 0` bytes owned) removes it. -/
theorem rawFree_run {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {bs : Array Byte}
    (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hst : m.SingleThread) :
    ∃ m', (rawFree p S).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.SingleThread := by
  obtain ⟨b, blk, hacc, hblk, -, hsz, -⟩ := bytesAt_access (q := p) (k := 0) (n := S) (a := 1) hb hm
    (by simp [Ptr.add]) hpos (by omega) (Nat.mod_one _)
  have hK : blk.kind = .heap := by
    obtain ⟨b', hpb, -, -⟩ := id hb
    obtain ⟨blk', hblk', -, _, hc⟩ := Mem.heap_some (bytesAt_cell hb hm hpb (j := 0) (by omega))
    obtain ⟨-, -, hl, -, -, -, -⟩ := access_eq hacc
    have : b' = b := by
      obtain ⟨hqb, -⟩ := access_eq hacc; rw [hpb] at hqb; exact Option.some.inj hqb
    subst this
    rw [hblk] at hblk'; cases hblk'
    simp only [Cell.mk.injEq] at hc; exact hc.2.2.2.symm
  obtain ⟨m', hr, hm', hst'⟩ := free_run hb hm hd hS h0 hpos hst
  refine ⟨m', ?_, hm', hst'⟩
  simp only [StateT.run] at hr
  simp [rawFree, zig_unfold, hacc, hK, h0, hsz, hr]

/-- What an allocation of `size` bytes with alignment `align` returns: a new heap block of
undefined bytes, or `error.OutOfMemory` and no bytes. -/
def newBlock (size align : Nat) : Except ErrName Ptr → Assn
  | .ok p => fun h => p.off = 0 ∧ ∃ A, A % align = 0 ∧
      bytesAt p A size .heap (Array.replicate size .undef) h
  | .error e => ⌜e = "OutOfMemory"⌝

/-- `create` gives what `newBlock` says, in a new part `h'` of the heap. -/
theorem create_run {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (a : Allocator) (size align : Nat) (hs : 0 < size) (ha : 0 < align) (hst : m.SingleThread) :
    ∃ r m' h', (a.create size align).run m = pure (r, m') ∧ Heap.Disjoint (h ∪ h') hF ∧
      m'.heap = (h ∪ h') ∪ hF ∧ Heap.Disjoint h h' ∧ m'.SingleThread ∧ newBlock size align r h' := by
  obtain ⟨r, m', hr, hst', hpost⟩ := rawAlloc_run hd hm size align ha hst
  have hns : ¬ size = 0 := by omega
  simp only [StateT.run] at hr
  cases r with
  | none =>
    refine ⟨.error "OutOfMemory", m', Heap.empty, ?_, by simpa using hd, by simpa using hpost,
      Heap.disjoint_empty h, hst', rfl, rfl⟩
    simp [Allocator.create, allocBytes, hns, zig_unfold, hr]
  | some p =>
    obtain ⟨h0, h', hd', hm', hdd, A, hA, hb⟩ := hpost
    refine ⟨.ok p, m', h', ?_, hd', hm', hdd, hst', h0, A, hA, hb⟩
    simp [Allocator.create, allocBytes, hns, zig_unfold, hr]

theorem Triple.create (a : Allocator) (size align : Nat) (hs : 0 < size) (ha : 0 < align) :
    Triple emp (a.create size align) (newBlock size align) :=
  Triple.of_run fun m hP hF hd hm hp hst => by
    have hP0 : hP = Heap.empty := hp
    subst hP0
    obtain ⟨r, m', h', hr, hd', hm', -, hst', hpost⟩ := create_run hd hm a size align hs ha hst
    simp only [Heap.empty_union] at hd' hm'
    exact ⟨r, m', h', hr, hd', hm', hpost, hst'⟩

theorem Triple.destroy (a : Allocator) {p : Ptr} {A S : Nat} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0) (hpos : 0 < S) : Triple (bytesAt p A S .heap bs) (a.destroy S p) (fun _ => emp) :=
  Triple.of_run fun _ _ hF hd hm hb hst => by
    obtain ⟨m', hr, hm', hst'⟩ := rawFree_run hb hm hd hS h0 hpos hst
    refine ⟨(), m', Heap.empty, ?_, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩
    simp [Allocator.destroy, show ¬ S = 0 by omega, hr]

end Zig
