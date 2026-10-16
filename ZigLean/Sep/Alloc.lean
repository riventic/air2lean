import ZigLean.Sep.Block
import ZigLean.Mem.AllocLemmas

/-!
# The hand-written heap's run lemmas (legacy, to retire)

Run lemmas of the `std` heap model (`rawAlloc`, `rawFree`, `poisonFree`, `Allocator.create`,
`ZigLean/Mem/Alloc.lean`) and its one remaining legacy rule, `Triple.freeSentinel`. An allocation
gives a new block of kind `.heap` that nothing else owns, or `none`/`error.OutOfMemory` and no
bytes, for every memory and therefore every policy (`Mem.allocPolicy`, `Mem.failAt`).

**Legacy-to-retire** (`docs/legacy-retirement.md` §L5, row 5c). The model vocabulary moved out
(the policy as an oracle: `ZigLean/Mem/AllocLemmas.lean`), the policy clients' executable
regression is test-local (`tests/roadmap/allocation-policy`), and the `create`/`destroy` triples
and `releaseAttempts_run` are retired (`docs/alloc-spec.md`, §Retired claims). What is left has
only legacy users: `Sep/Cost` and `Proofs/Lists/Cost` (L8), `Sep/{Sentinel, SentinelRealloc,
RawAlloc, Remap}` (L5a) and `tutorials/memory-safety/Controls.lean` (L4). The module is deleted
with the last of them; nothing new may import it.
-/

namespace Zig

open Assn

/-- The memory with a new allocation count has the same heap. -/
theorem Mem.heap_allocs (m : Mem) (k : Nat) : ({ m with allocs := k } : Mem).heap = m.heap := rfl

/-- `rawAlloc` gives `none` and changes no byte, or a new heap block, as `alloc_run`. -/
theorem rawAlloc_run {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (n align : Nat) (ha : 0 < align) (hst : m.Seq) :
    ∃ r m', (rawAlloc n align).run m = pure (r, m') ∧ m'.Seq ∧ m.blocks.size ≤ m'.blocks.size ∧
      match r with
      | none => m'.heap = h ∪ hF
      | some p => p.off = 0 ∧ ∃ h', Heap.Disjoint (h ∪ h') hF ∧ m'.heap = (h ∪ h') ∪ hF ∧
          Heap.Disjoint h h' ∧ ∃ A, A % align = 0 ∧
            bytesAt p A n .heap (Array.replicate n .undef) h' ∧
            ∀ l c, m.heap l = some c →
              n = 0 ∨ c.addr + c.size ≤ A ∨ A + n ≤ c.addr + c.kind.mappedLo := by
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hm₁ : m₁.heap = h ∪ hF := by rw [Mem.heap_allocs]; exact hm
  have hst₁ : m₁.Seq := ⟨hst.single⟩
  classical
  rw [rawAlloc_eq]
  by_cases hdn : m.allocDenied n
  · exact ⟨none, m₁, by simp only [hdn, ↓reduceIte]; rfl, hst₁, Nat.le_refl _, hm₁⟩
  cases hroom : m.roomFor n align
  · exact ⟨none, m₁, by simp only [hdn, hroom, ↓reduceIte]; rfl, hst₁, Nat.le_refl _, hm₁⟩
  · obtain ⟨p, m', h', hr, h0, hd', hm', hdd, hst', hsz, A, hA, hb, hab⟩ :=
      alloc_run hd hm₁ .heap n align ha hroom hst₁
    refine ⟨some p, m', ?_, hst', by rw [hsz]; exact Nat.le_succ _, h0, h', hd', hm', hdd, A, hA, hb,
      hab⟩
    simp only [hdn, hroom, ↓reduceIte]
    simp only [StateT.run] at hr ⊢
    simp [zig_unfold, hr, m₁]

/-- A nonempty whole heap block has the access, size and kind required by both free paths. -/
theorem heapBlock_access {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat}
    {bs : Array Byte} (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF)
    (hS : bs.size = S) (hpos : 0 < S) :
    ∃ b blk, m.access p S 1 = pure (b, blk, p.off.toNat) ∧
      blk.kind = .heap ∧ blk.bytes.size = S := by
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
  exact ⟨b, blk, by simpa using hacc, hK, hsz⟩

/-- `rawFree` of a whole heap block (from offset 0, all `S > 0` bytes owned) removes it. -/
theorem rawFree_run {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {bs : Array Byte}
    (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hst : m.Seq) :
    ∃ m', (rawFree p S).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size := by
  obtain ⟨b, blk, hacc, hK, hsz⟩ := heapBlock_access hb hm hS hpos
  obtain ⟨m', hr, hm', hst', hsz'⟩ := free_run hb hm hd hS h0 hpos hst
  refine ⟨m', ?_, hm', hst', hsz'⟩
  simp only [StateT.run] at hr
  simp [rawFree, zig_unfold, hacc, hK, h0, hsz, hr]

/-- `poisonFree` of a whole heap block (from offset 0, all `S > 0` bytes owned) removes it. -/
theorem poisonFree_run {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {bs : Array Byte}
    (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hst : m.Seq) :
    ∃ m', (poisonFree p S).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size := by
  obtain ⟨b, blk, hacc, hK, hsz⟩ := heapBlock_access hb hm hS hpos
  let mr := m.recordAt b 0 S .write
  have hmr : mr.heap = h ∪ hF := by
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  obtain ⟨m', hr, hm', hst', hsz'⟩ :=
    rawFree_run hb hmr hd hS h0 hpos (hst.recordAt _ _ _ _)
  refine ⟨m', ?_, hm', hst', hsz'⟩
  have hrac := recordAccess_run (noRace_of_singleThread hst.single b 0 S .write)
  change (recordAccess b 0 S .write).run m = pure ((), mr) at hrac
  simp only [StateT.run] at hr hrac
  simp [poisonFree, zig_unfold, hacc, hK, h0, hsz, hrac, hr, ExceptT.bindCont]

/-- What an allocation of `size` bytes with alignment `align` returns: a new heap block of
undefined bytes, or `error.OutOfMemory` and no bytes. -/
def newBlock (size align : Nat) : Except ErrName Ptr → Assn
  | .ok p => fun h => p.off = 0 ∧ ∃ A, A % align = 0 ∧
      bytesAt p A size .heap (Array.replicate size .undef) h
  | .error e => ⌜e = "OutOfMemory"⌝

/-- `create` gives what `newBlock` says, in a new part `h'` of the heap. -/
theorem create_run {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (a : Allocator) (size align : Nat) (hs : 0 < size) (ha : 0 < align) (hst : m.Seq) :
    ∃ r m' h', (a.create size align).run m = pure (r, m') ∧ Heap.Disjoint (h ∪ h') hF ∧
      m'.heap = (h ∪ h') ∪ hF ∧ Heap.Disjoint h h' ∧ m'.Seq ∧ newBlock size align r h' := by
  obtain ⟨r, m', hr, hst', -, hpost⟩ := rawAlloc_run hd hm size align ha hst
  have hns : ¬ size = 0 := by omega
  simp only [StateT.run] at hr
  cases r with
  | none =>
    refine ⟨.error "OutOfMemory", m', Heap.empty, ?_, by simpa using hd, by simpa using hpost,
      Heap.disjoint_empty h, hst', rfl, rfl⟩
    simp [Allocator.create, allocBytes, hns, zig_unfold, hr]
  | some p =>
    obtain ⟨h0, h', hd', hm', hdd, A, hA, hb, -⟩ := hpost
    refine ⟨.ok p, m', h', ?_, hd', hm', hdd, hst', h0, A, hA, hb⟩
    simp [Allocator.create, allocBytes, hns, zig_unfold, hr]

/-- `free` of a `[:s]T` needs the whole block of `len + 1` items: the sentinel is in it. -/
theorem Triple.freeSentinel (a : Allocator) {s : Slice} {A size : Nat} {bs : Array Byte}
    (hS : bs.size = size * (s.len.toNat + 1)) (h0 : s.ptr.off = 0) (hpos : 0 < size) :
    Triple (bytesAt s.ptr A (size * (s.len.toNat + 1)) .heap bs) (a.freeSentinel size s)
      (fun _ => emp) :=
  Triple.of_run fun _ _ hF hd hm hb hst => by
    obtain ⟨m', hr, hm', hst', -⟩ :=
      poisonFree_run hb hm hd hS h0 (Nat.mul_pos hpos (Nat.succ_pos _)) hst
    refine ⟨(), m', Heap.empty, ?_, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩
    simp [Allocator.freeSentinel, show ¬ size = 0 by omega, hr]

end Zig
