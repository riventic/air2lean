import ZigLean.Sep.Alloc
import ZigLean.Mem.Owned

/-!
# Allocator identity: cross-allocator frees and resets (M01)

Rules for `ZigLean/Mem/Owned.lean`:

* `AllocRef.free_foreign`, `AllocRef.destroy_foreign`, `AllocRef.remap_foreign`: a free,
  destroy or remap through allocator `r` of a block whose kind is not `r.kind` (another
  allocator's block, a stack local, a global) throws `.illegal`.
* `Mem.heap_resetOwned`, `Owned.reset_run`: a reset removes exactly the bytes of the
  allocator's blocks from the heap; every other byte keeps its cell.
-/

namespace Zig

/-! ## Run lemmas of the parts -/

/-- `Mem.access` throws only `.illegal`. -/
theorem access_cases (m : Mem) (p : Ptr) (n al : Nat) :
    m.access p n al = throw .illegal ∨ ∃ b blk o, m.access p n al = pure (b, blk, o) := by
  unfold Mem.access
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inr ⟨_, _, _, rfl⟩
      · exact .inl rfl

/-- An access through a pointer into block `b` finds `b`. -/
theorem access_block {m : Mem} {p : Ptr} {n al : Nat} {b b' : BlockId} {blk blk' : Block} {o : Nat}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk)
    (h : m.access p n al = pure (b', blk', o)) : b' = b ∧ blk' = blk := by
  obtain ⟨hb', hblk', -⟩ := access_eq h
  rw [hpb] at hb'
  cases hb'
  rw [hblk] at hblk'
  exact ⟨rfl, (Option.some.inj hblk').symm⟩

theorem ownedState_run {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) : (ownedState a).run m = pure (st, m) := by
  simp [ownedState, zig_unfold, hs, hl]

theorem ownedState_cases (m : Mem) (a : AllocId) :
    (ownedState a).run m = throw .illegal ∨ ∃ st, (ownedState a).run m = pure (st, m) := by
  cases hs : m.allocators[a]? with
  | none => left; simp [ownedState, zig_unfold, hs]
  | some st =>
    by_cases hl : st.live
    · exact .inr ⟨st, ownedState_run hs hl⟩
    · left; simp [ownedState, zig_unfold, hs, hl]

/-! ## Cross-allocator frees -/

/-- `wholeBlock k` of a block of another kind throws `.illegal`. -/
theorem wholeBlock_foreign {m : Mem} {k : BlockKind} {p : Ptr} {n : Nat} {b : BlockId}
    {blk : Block} (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ k) :
    (wholeBlock k p n).run m = throw .illegal := by
  rcases access_cases m p n 1 with h | ⟨b', blk', o, h⟩
  · simp [wholeBlock, zig_unfold, h]
  · obtain ⟨rfl, rfl⟩ := access_block hpb hblk h
    simp [wholeBlock, zig_unfold, h, hk]

theorem ownedFree_foreign {m : Mem} {a : AllocId} {p : Ptr} {n : Nat} {b : BlockId} {blk : Block}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ .owned a) :
    (ownedFree a p n).run m = throw .illegal := by
  rcases ownedState_cases m a with h | ⟨st, h⟩
  · simp only [ownedFree, StateT.run_bind, h]; rfl
  · have hw := wholeBlock_foreign (n := n) hpb hblk hk
    simp only [ownedFree, StateT.run_bind, h, pure_bind, hw]; rfl

theorem poisonFree_foreign {m : Mem} {p : Ptr} {n : Nat} {b : BlockId} {blk : Block}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ .heap) :
    (poisonFree p n).run m = throw .illegal := by
  rcases access_cases m p n 1 with h | ⟨b', blk', o, h⟩
  · simp [poisonFree, zig_unfold, h]
  · obtain ⟨rfl, rfl⟩ := access_block hpb hblk h
    simp [poisonFree, zig_unfold, h, hk]

theorem rawFree_foreign {m : Mem} {p : Ptr} {n : Nat} {b : BlockId} {blk : Block}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ .heap) :
    (rawFree p n).run m = throw .illegal := by
  rcases access_cases m p n 1 with h | ⟨b', blk', o, h⟩
  · simp [rawFree, zig_unfold, h]
  · obtain ⟨rfl, rfl⟩ := access_block hpb hblk h
    simp [rawFree, zig_unfold, h, hk]

/-- (M01) `free(s)` through allocator `r` of a nonempty slice into a block that `r` did not
make throws `.illegal`: an arena's block through `std.mem.Allocator` or another arena, a
`std.mem.Allocator` block through an arena, a stack or global block through any allocator. -/
theorem AllocRef.free_foreign (r : AllocRef) {m : Mem} {size : Nat} {s : Slice} {b : BlockId}
    {blk : Block} (hn : size * s.len.toNat ≠ 0) (hpb : s.ptr.block = some b)
    (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ r.kind) :
    (r.free size s).run m = throw .illegal := by
  cases r with
  | std => simpa [AllocRef.free, Allocator.free, hn] using poisonFree_foreign hpb hblk hk
  | owned a => simpa [AllocRef.free, hn] using ownedFree_foreign (n := size * s.len.toNat) hpb hblk hk

/-- (M01) `destroy(p)` through `r` of a block that `r` did not make throws `.illegal`. -/
theorem AllocRef.destroy_foreign (r : AllocRef) {m : Mem} {size : Nat} {p : Ptr} {b : BlockId}
    {blk : Block} (hn : size ≠ 0) (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk)
    (hk : blk.kind ≠ r.kind) : (r.destroy size p).run m = throw .illegal := by
  cases r with
  | std => simpa [AllocRef.destroy, Allocator.destroy, hn] using rawFree_foreign hpb hblk hk
  | owned a => simpa [AllocRef.destroy, hn] using ownedFree_foreign (n := size) hpb hblk hk

/-- (M01) `remap(s, n)` through `r` of a nonempty slice into a block that `r` did not make
throws `.illegal`, whatever the new length. -/
theorem AllocRef.remap_foreign (r : AllocRef) {m : Mem} {size : Nat} {s : Slice} {n : BitVec 64}
    {b : BlockId} {blk : Block} (hn : size * s.len.toNat ≠ 0) (hpb : s.ptr.block = some b)
    (hblk : m.blocks[b]? = some blk) (hk : blk.kind ≠ r.kind) :
    (r.remap size s n).run m = throw .illegal := by
  have hw : wholeBlock r.kind s.ptr (size * s.len.toNat) m = throw .illegal :=
    wholeBlock_foreign hpb hblk hk
  simp [AllocRef.remap, hn, discard, Functor.mapConst, StateT.map, zig_unfold, hw]

/-! ## Reset -/

/-- `h` without the cells of the blocks of allocator `a`. -/
def Heap.dropOwned (h : Heap) (a : AllocId) : Heap := fun l =>
  match h l with
  | some c => if c.kind = .owned a then none else some c
  | none => none

/-- (M01) After a reset of `a`, the heap is the old heap without exactly the bytes of `a`'s
blocks. -/
theorem Mem.heap_resetOwned (m : Mem) (a : AllocId) :
    (m.resetOwned a).heap = m.heap.dropOwned a := by
  funext ⟨b, o⟩
  simp only [Mem.heap, Mem.resetOwned, Heap.dropOwned, Array.getElem?_map]
  cases m.blocks[b]? with
  | none => rfl
  | some blk =>
    by_cases hk : blk.kind = .owned a <;>
      by_cases hc : blk.live ∧ o < blk.bytes.size ∧ blk.kind.mappedLo ≤ o <;>
      simp only [hc, dite_true, dite_false] <;> simp [hk] <;>
      first | exact hc | (intro h1 h2; apply Nat.lt_of_not_le; intro h3; exact hc ⟨h1, h2, h3⟩)

/-- A reset of `a` invalidates every byte of `a`'s blocks. -/
theorem Mem.resetOwned_own {m : Mem} {a : AllocId} {l : Loc} {c : Cell} (hc : m.heap l = some c)
    (hk : c.kind = .owned a) : (m.resetOwned a).heap l = none := by
  simp [Mem.heap_resetOwned, Heap.dropOwned, hc, hk]

/-- (M01, frame) A reset of `a` keeps every cell of every other block. -/
theorem Mem.resetOwned_other {m : Mem} {a : AllocId} {l : Loc} {c : Cell}
    (hk : c.kind ≠ .owned a) : (m.resetOwned a).heap l = some c ↔ m.heap l = some c := by
  rw [Mem.heap_resetOwned]
  simp only [Heap.dropOwned]
  cases h : m.heap l with
  | none => simp
  | some c' =>
    by_cases hk' : c'.kind = .owned a
    · simp only [hk', ↓reduceIte, reduceCtorEq, false_iff, Option.some.injEq]
      rintro rfl; exact hk hk'
    · simp [hk']

/-- After a reset of `a`, an access to a block of `a` throws `.illegal`. -/
theorem Mem.resetOwned_access_own {m : Mem} {a : AllocId} {p : Ptr} {n al : Nat} {b : BlockId}
    {blk : Block} (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk)
    (hk : blk.kind = .owned a) : (m.resetOwned a).access p n al = throw .illegal := by
  simp [Mem.access, Mem.resetOwned, hpb, hblk, hk]

/-- (frame) A reset of `a` does not change an access to a block of another kind. -/
theorem Mem.resetOwned_access_other {m : Mem} {a : AllocId} {p : Ptr} {n al : Nat} {b : BlockId}
    {blk : Block} {o : Nat} (h : m.access p n al = pure (b, blk, o)) (hk : blk.kind ≠ .owned a) :
    (m.resetOwned a).access p n al = pure (b, blk, o) := by
  have hlo := access_lo h
  obtain ⟨hpb, hblk, hl, h0, hn, ha, rfl⟩ := access_eq h
  exact access_of hpb (by simp [Mem.resetOwned, hblk, hk]) hl h0 hn ha hlo

theorem Mem.Seq.resetOwned {m : Mem} (hst : m.Seq) (a : AllocId) : (m.resetOwned a).Seq :=
  ⟨hst.single⟩

/-- The memory after `Owned.reset a`. -/
def Mem.afterReset (m : Mem) (a : AllocId) (st : OwnedAlloc) : Mem :=
  { m.resetOwned a with allocators := m.allocators.set! a { st with used := 0, starts := [] } }

theorem Owned.reset_run {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) :
    (Owned.reset a).run m = pure ((), m.afterReset a st) := by
  simp [Owned.reset, setOwned, Mem.afterReset, Mem.resetOwned, zig_unfold, ownedState, hs, hl]

/-- (M01) `Owned.reset a` succeeds on a live allocator; afterwards the heap is the old heap
without exactly `a`'s bytes, `Seq` holds, and `a` is live and empty. -/
theorem Owned.reset_spec {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hst : m.Seq) :
    (Owned.reset a).run m = pure ((), m.afterReset a st) ∧
      (m.afterReset a st).heap = m.heap.dropOwned a ∧ (m.afterReset a st).Seq ∧
      (m.afterReset a st).allocators[a]? = some { st with used := 0, starts := [] } := by
  have hlt : a < m.allocators.size := (Array.getElem?_eq_some_iff.mp hs).1
  refine ⟨Owned.reset_run hs hl, Mem.heap_resetOwned m a, ⟨(hst.resetOwned a).single⟩, ?_⟩
  simp [Mem.afterReset, Mem.resetOwned, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt hlt]

/-- `Arena.deinit a`: the heap without exactly `a`'s bytes, and `a` is dead. -/
theorem Arena.deinit_spec {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hst : m.Seq) :
    ∃ m', (Arena.deinit a).run m = pure ((), m') ∧ m'.heap = m.heap.dropOwned a ∧ m'.Seq ∧
      ∃ st', m'.allocators[a]? = some st' ∧ st'.live = false := by
  obtain ⟨hR, hheap, hstR, hsR⟩ := Owned.reset_spec hs hl hst
  have hlt : a < (m.afterReset a st).allocators.size := (Array.getElem?_eq_some_iff.mp hsR).1
  have hS := ownedState_run hsR hl
  simp only [StateT.run] at hR hS
  let st' : OwnedAlloc := { st with used := 0, starts := [], live := false }
  let m' : Mem := { m.afterReset a st with
    allocators := (m.afterReset a st).allocators.set! a st' }
  refine ⟨m', ?_, hheap, ⟨hstR.single⟩, st',
    by simp [m', Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt], rfl⟩
  simp [Arena.deinit, setOwned, zig_unfold, hR, hS, m', st']

/-- `h` has no cell of allocator `a`'s blocks. -/
theorem Heap.dropOwned_of_none {h : Heap} {a : AllocId}
    (hn : ∀ l c, h l = some c → c.kind ≠ .owned a) : h.dropOwned a = h := by
  funext l
  simp only [Heap.dropOwned]
  cases hl : h l with
  | none => rfl
  | some c => simp [hn l c hl]

theorem Heap.dropOwned_idem (h : Heap) (a : AllocId) : (h.dropOwned a).dropOwned a = h.dropOwned a :=
  Heap.dropOwned_of_none fun l c hc => by
    simp only [Heap.dropOwned] at hc
    split at hc
    · split at hc
      · cases hc
      · cases hc; assumption
    · cases hc

theorem Arena.init_run (m : Mem) :
    Arena.init.run m = pure (m.allocators.size,
      { m with allocators := m.allocators.push { policy := .arena } }) := by
  simp [Arena.init, Owned.init, zig_unfold, set, StateT.set, MonadStateOf.set]

/-! ## Requests -/

/-- An arena request of `n` bytes: `none` and only a policy count, or a new arena block. -/
theorem ownedRawAlloc_arena_run {m : Mem} {a : AllocId} {st : OwnedAlloc}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .arena) (n : Nat) :
    (ownedRawAlloc a n 1).run m =
      if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures
      then pure (none, { m with allocs := m.allocs + 1 })
      else pure (some ⟨some m.blocks.size, 0⟩,
        ({ m with allocs := m.allocs + 1 } : Mem).afterAlloc (.owned a) n 1) := by
  have h := ownedState_run hs hl
  have hA := alloc_run_eq ({ m with allocs := m.allocs + 1 } : Mem) (.owned a) n 1
  simp only [StateT.run] at h hA
  split <;> rename_i hc <;>
    simp [ownedRawAlloc, h, hp, hc, zig_unfold, set, StateT.set, MonadStateOf.set, hA]

/-! ## Fixed buffers -/

/-- A fixed-buffer request: `none` without any change if it does not fit in the buffer, else
a new block of the allocator, `used` past it. -/
theorem ownedRawAlloc_fixedBuffer_run {m : Mem} {a : AllocId} {st : OwnedAlloc} {base cap : Nat}
    (hs : m.allocators[a]? = some st) (hl : st.live) (hp : st.policy = .fixedBuffer base cap)
    (n align : Nat) :
    (ownedRawAlloc a n align).run m =
      if cap < (fixedBufferNext base st.used align n).2 then pure (none, m)
      else pure (some ⟨some m.blocks.size, 0⟩,
        { m.afterAlloc (.owned a) n align with
          allocators := m.allocators.set! a { st with
            used := (fixedBufferNext base st.used align n).2,
            starts := (m.blocks.size, (fixedBufferNext base st.used align n).1) :: st.starts } }) := by
  have h := ownedState_run hs hl
  have hA := alloc_run_eq m (.owned a) n align
  simp only [StateT.run] at h hA
  split <;> rename_i hc <;>
    simp [ownedRawAlloc, h, hp, hc, zig_unfold, hA, setOwned, Mem.afterAlloc]

end Zig
