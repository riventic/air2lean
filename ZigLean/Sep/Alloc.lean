import ZigLean.Sep.Block
import ZigLean.Mem.Alloc

/-!
# The allocator

Rules for the allocator model (`ZigLean/Mem/Alloc.lean`). An allocation gives a new block of kind
`.heap` that nothing else owns, or `error.OutOfMemory` and no bytes: `Mem.failAt` and
`Mem.allocPolicy` decide. A triple holds for every memory and therefore every cap and
failure trace, so a spec covers both. A free needs the whole block, of kind `.heap`.
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
            ∀ l c, m.heap l = some c → c.addr + c.size < A := by
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hm₁ : m₁.heap = h ∪ hF := by rw [Mem.heap_allocs]; exact hm
  have hst₁ : m₁.Seq := ⟨hst.single, hst.addr⟩
  by_cases hc : m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures
  · refine ⟨none, m₁, ?_, hst₁, Nat.le_refl _, hm₁⟩
    simp [rawAlloc, hc, zig_unfold, m₁, set, StateT.set, MonadStateOf.set]
  · obtain ⟨p, m', h', hr, h0, hd', hm', hdd, hst', hsz, A, hA, hb, hab⟩ :=
      alloc_run hd hm₁ .heap n align ha hst₁
    refine ⟨some p, m', ?_, hst', by rw [hsz]; exact Nat.le_succ _, h0, h', hd', hm', hdd, A, hA, hb,
      hab⟩
    simp only [StateT.run] at hr
    simp [rawAlloc, hc, zig_unfold, set, StateT.set, MonadStateOf.set, m₁] at hr ⊢
    simp [hr, ExceptT.bindCont]

/-- A nonempty whole heap block has the access, size and kind required by both free paths. -/
private theorem heapBlock_access {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat}
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
    obtain ⟨m', hr, hm', hst', -⟩ := rawFree_run hb hm hd hS h0 hpos hst
    refine ⟨(), m', Heap.empty, ?_, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩
    simp [Allocator.destroy, show ¬ S = 0 by omega, hr]

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

/-- A client that reports allocation success and always releases a nonempty successful
allocation. Failure is a normal result; cleanup is not conditional on a proof of success. -/
def releaseAttempt (size align : Nat) : MemM Bool := do
  match ← rawAlloc size align with
  | none => pure false
  | some p =>
    rawFree p size
    pure true

/-- Total, policy-independent client safety: an actual result exists, with the original
heap restored on either outcome. No success, resource-budget or default-policy premise.
`Seq`/positive size/alignment are the existing sequential memory/access premises. -/
theorem releaseAttempt_run (m : Mem) (size align : Nat) (hs : 0 < size) (ha : 0 < align)
    (hst : m.Seq) :
    ∃ ok m', (releaseAttempt size align).run m = pure (ok, m') ∧
      m'.heap = m.heap ∧ m'.Seq := by
  have hd : Heap.Disjoint Heap.empty m.heap := (Heap.disjoint_empty m.heap).symm
  have hm : m.heap = Heap.empty ∪ m.heap := by simp
  obtain ⟨r, m₁, hr, hst₁, -, hpost⟩ := rawAlloc_run hd hm size align ha hst
  simp only [StateT.run] at hr
  cases r with
  | none =>
    refine ⟨false, m₁, ?_, by simpa using hpost, hst₁⟩
    simp [releaseAttempt, zig_unfold, hr]
  | some p =>
    obtain ⟨h0, h', hd', hm', -, A, -, hb, -⟩ := hpost
    simp only [Heap.empty_union] at hd' hm'
    obtain ⟨m₂, hf, hh, hst₂, -⟩ := rawFree_run hb hm' hd'
      (by simp) h0 hs hst₁
    simp only [StateT.run] at hf
    refine ⟨true, m₂, ?_, by simpa using hh, hst₂⟩
    simp [releaseAttempt, zig_unfold, hr, hf, ExceptT.bindCont]

/-- Repeated attempts can suffer any number of failures; every successful block is freed. -/
def releaseAttempts (sizes : List Nat) (align : Nat) : MemM (List Bool) :=
  match sizes with
  | [] => pure []
  | size :: sizes => do
    let ok ← releaseAttempt size align
    let oks ← releaseAttempts sizes align
    pure (ok :: oks)

/-- A finite repeated-allocation client returns exactly one outcome per request and restores
its original heap under every permitted policy, even if all requests fail. -/
theorem releaseAttempts_run (sizes : List Nat) (align : Nat) (ha : 0 < align)
    (hs : ∀ size ∈ sizes, 0 < size) (m : Mem) (hst : m.Seq) :
    ∃ oks m', (releaseAttempts sizes align).run m = pure (oks, m') ∧
      oks.length = sizes.length ∧ m'.heap = m.heap ∧ m'.Seq := by
  induction sizes generalizing m with
  | nil => exact ⟨[], m, rfl, rfl, rfl, hst⟩
  | cons size sizes ih =>
    obtain ⟨ok, m₁, hr, hh, hst₁⟩ := releaseAttempt_run m size align
      (hs size (by simp)) ha hst
    obtain ⟨oks, m₂, hrr, hlen, hheap, hst₂⟩ := ih (fun n hn => hs n (by simp [hn])) m₁ hst₁
    simp only [StateT.run] at hr hrr
    refine ⟨ok :: oks, m₂, ?_, by simp [hlen], hheap.trans hh, hst₂⟩
    simp [releaseAttempts, zig_unfold, hr, hrr, ExceptT.bindCont]

end Zig
