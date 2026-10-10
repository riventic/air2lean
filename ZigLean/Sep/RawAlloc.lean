import ZigLean.Sep.SentinelRealloc

/-! Contracts of the raw allocator interface (`vtableAlloc`, `vtableResize`, `vtableRemap`,
`vtableFree`, M04). Each call requires a power-of-two alignment at most `2 ^ 63` and a nonzero
length; resize, remap and free also require the whole live heap block that was allocated with
that alignment. A violated precondition is `.illegal`. Under the preconditions, allocation
returns an aligned fresh block or fails without change; resize succeeds in place or changes
nothing; remap succeeds in place, moves to an aligned fresh block, or changes nothing; free
consumes the whole block. Every rule keeps an arbitrary caller frame. -/
namespace Zig
open Assn

theorem rawAlignOk_iff (align : Nat) : rawAlignOk align = true ↔ ∃ k, k < 64 ∧ align = 2 ^ k := by
  simp only [rawAlignOk, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor <;> rintro ⟨k, hk, e⟩ <;> exact ⟨k, hk, e.symm⟩

theorem rawAlignOk_pos {align : Nat} (h : rawAlignOk align = true) : 0 < align := by
  obtain ⟨k, -, rfl⟩ := (rawAlignOk_iff align).mp h
  exact Nat.two_pow_pos k

theorem rawAlignOk_le {align : Nat} (h : rawAlignOk align = true) : align ≤ 2 ^ 63 := by
  obtain ⟨k, hk, rfl⟩ := (rawAlignOk_iff align).mp h
  exact Nat.pow_le_pow_right (by decide) (by omega)

example : rawAlignOk 1 = true ∧ rawAlignOk 16 = true ∧ rawAlignOk (2 ^ 63) = true ∧
    rawAlignOk 0 = false ∧ rawAlignOk 3 = false ∧ rawAlignOk 24 = false ∧
    rawAlignOk (2 ^ 64) = false := by decide

/-! ## Preconditions: violations are illegal -/

theorem vtableAlloc_illegal (a : Allocator) (len : BitVec 64) (align : Nat) (m : Mem)
    (h : rawAlignOk align = false ∨ len.toNat = 0) :
    (vtableAlloc a len align).run m = throw .illegal := by
  simp [vtableAlloc, h, zig_unfold]

theorem vtableResize_illegal (a : Allocator) (s : Slice) (align : Nat) (n : BitVec 64) (m : Mem)
    (h : rawAlignOk align = false ∨ n.toNat = 0) :
    (vtableResize a s align n).run m = throw .illegal := by
  simp [vtableResize, h, zig_unfold]

theorem vtableRemap_illegal (a : Allocator) (s : Slice) (align : Nat) (n : BitVec 64) (m : Mem)
    (h : rawAlignOk align = false ∨ n.toNat = 0) :
    (vtableRemap a s align n).run m = throw .illegal := by
  simp [vtableRemap, h, zig_unfold]

theorem vtableFree_illegal (a : Allocator) (s : Slice) (align : Nat) (m : Mem)
    (h : rawAlignOk align = false) : (vtableFree a s align).run m = throw .illegal := by
  simp [vtableFree, h, zig_unfold]

/-- Memory that is not exactly a whole live heap block allocated with `align` is rejected:
another alignment, an inner or partial slice, a non-heap block or an empty slice. -/
theorem rawBlock_illegal {m : Mem} {s : Slice} {align : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, o))
    (h : blk.kind ≠ .heap ∨ o ≠ 0 ∨ blk.bytes.size ≠ s.len.toNat ∨ blk.align ≠ align ∨
      s.len.toNat = 0) :
    (rawBlock s align).run m = throw .illegal := by
  simp only [rawBlock, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, ExceptT.bind, ExceptT.mk, ExceptT.pure] at hacc ⊢
  simp [hacc, h, zig_unfold, ExceptT.bindCont]

/-- The block and offset of a valid raw request. -/
theorem rawBlock_run {m : Mem} {s : Slice} {align : Nat} {b : BlockId} {blk : Block}
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0)) (hK : blk.kind = .heap)
    (hsz : blk.bytes.size = s.len.toNat) (ha : blk.align = align) (hpos : 0 < s.len.toNat) :
    (rawBlock s align).run m = pure ((b, blk), m) := by
  have hne : s.len.toNat ≠ 0 := by omega
  simp only [rawBlock, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, ExceptT.bind, ExceptT.mk, ExceptT.pure] at hacc ⊢
  simp [hacc, hK, hsz, ha, hne, zig_unfold, ExceptT.bindCont]

/-! ## Allocation -/

/-- What `vtableAlloc` returns: nothing, or a fresh aligned block of undefined bytes. -/
def rawNew (len : BitVec 64) (align : Nat) : Option Ptr → Assn
  | none => emp
  | some p => fun h => p.off = 0 ∧ ∃ A, A % align = 0 ∧
      bytesAt p A len.toNat .heap (Array.replicate len.toNat .undef) h

theorem Triple.vtableAlloc (a : Allocator) (len : BitVec 64) (align : Nat)
    (hal : rawAlignOk align = true) (hlen : 0 < len.toNat) :
    Triple emp (vtableAlloc a len align) (rawNew len align) := by
  apply Triple.of_run
  intro m hP hF hd hm hp hst
  have hP0 : hP = Heap.empty := hp
  subst hP0
  obtain ⟨r, m', hr, hst', -, hpost⟩ := rawAlloc_run hd hm len.toNat align (rawAlignOk_pos hal) hst
  have hc : ¬ (rawAlignOk align = false ∨ len.toNat = 0) := by simp [hal]; omega
  simp only [StateT.run] at hr
  cases r with
  | none =>
    refine ⟨none, m', Heap.empty, ?_, hd, hpost, rfl, hst'⟩
    simp [Zig.vtableAlloc, hc, zig_unfold, hr]
  | some p =>
    obtain ⟨h0, h', hd', hm', -, A, hA, hb, -⟩ := hpost
    simp only [Heap.empty_union] at hd' hm'
    refine ⟨some p, m', h', ?_, hd', hm', ⟨h0, A, hA, hb⟩, hst'⟩
    simp [Zig.vtableAlloc, hc, zig_unfold, hr]

/-! ## Free -/

/-- Freeing the whole block allocated with `align` consumes it; the frame is unchanged. -/
theorem vtableFree_run (a : Allocator) {m : Mem} {s : Slice} {h hF : Heap} {A : Nat}
    {bs : Array Byte} {align : Nat} (hb : bytesAt s.ptr A s.len.toNat .heap bs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hS : bs.size = s.len.toNat)
    (h0 : s.ptr.off = 0) (hpos : 0 < s.len.toNat) (hst : m.Seq) (hal : rawAlignOk align = true)
    (hblkAlign : ∀ b blk, s.ptr.block = some b → m.blocks[b]? = some blk → blk.align = align) :
    ∃ m', (vtableFree a s align).run m = pure ((), m') ∧ m'.heap = hF ∧ m'.Seq := by
  obtain ⟨b, blk, hacc, hblk, hptr, hK, hsz, -⟩ := wholeRequest hb hm hS h0 hpos
  have hrb := rawBlock_run (align := align) hacc hK hsz
    (hblkAlign b blk (by rw [hptr]) hblk) hpos
  obtain ⟨m', hr, hm', hst', -⟩ := rawFree_run hb hm hd hS h0 hpos hst
  refine ⟨m', ?_, by simpa using hm', hst'⟩
  have hc : ¬ rawAlignOk align = false := by simp [hal]
  simp only [StateT.run] at hrb hr
  simp [vtableFree, hc, zig_unfold, hrb, hr, ExceptT.bindCont]

/-! ## Resize and remap -/

/-- The in-place step either changes nothing or owns the resized whole block, at the same
pointer and address. -/
theorem rawInPlace_owned {m : Mem} {b : BlockId} {blk : Block} {hF : Heap} {n : Nat}
    (hblk : m.blocks[b]? = some blk) (hl : blk.live)
    (hd : Heap.Disjoint (blockHeap b blk) hF) (hm : m.heap = blockHeap b blk ∪ hF) (hst : m.Seq)
    (hlo : blk.kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    ∃ r m', (rawInPlace b blk n).run m = pure (r, m') ∧ m'.Seq ∧
      if r then Heap.Disjoint (blockHeap b { blk with bytes := remapBytes blk.bytes n }) hF ∧
          m'.heap = blockHeap b { blk with bytes := remapBytes blk.bytes n } ∪ hF ∧
          bytesAt ⟨some b, 0⟩ blk.addr n blk.kind (remapBytes blk.bytes n)
            (blockHeap b { blk with bytes := remapBytes blk.bytes n })
      else m' = m := by
  by_cases hc : m.allocPolicy.byteRemap ≠ .inPlace ∨ m.allocPolicy.maxBytes < n
  · refine ⟨false, m, ?_, hst, rfl⟩
    simp [rawInPlace, hc, zig_unfold]
  by_cases hg : blk.bytes.size < n ∧ m.growFree b blk n ≠ true
  · refine ⟨false, m, ?_, hst, rfl⟩
    have hc' : ¬ (m.allocPolicy.byteRemap ≠ .inPlace ∨ m.allocPolicy.maxBytes < n) := hc
    simp only [ne_eq, Bool.not_eq_true] at hg hc'
    simp [rawInPlace, hc', hg, zig_unfold]
  let recorded := m.recordAt b 0 blk.bytes.size .write
  have hrec := recordAccess_run (noRace_of_singleThread hst.single b 0 blk.bytes.size .write)
  change (recordAccess b 0 blk.bytes.size .write).run m = pure ((), recorded) at hrec
  simp only [StateT.run] at hrec
  have hbr : recorded.blocks[b]? = some blk := by simpa [recorded, Mem.recordAt] using hblk
  have hmr : recorded.heap = blockHeap b blk ∪ hF := by
    funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
  obtain ⟨hd', hm', hp'⟩ := afterByteRemap_owned_frame hbr hl hd hmr n hlo
  refine ⟨true, recorded.afterByteRemap b blk n, ?_,
    afterByteRemap_seq hbr hl hd hmr (hst.recordAt _ _ _ _) n, hd', hm', hp'⟩
  have hg' : ¬ (blk.bytes.size < n ∧ m.growFree b blk n = false) := by simpa using hg
  have hc' : ¬ (m.allocPolicy.byteRemap ≠ .inPlace ∨ m.allocPolicy.maxBytes < n) := hc
  simp only [ne_eq] at hc'
  simp [rawInPlace, hc', hg', zig_unfold, hrec, ExceptT.bindCont, set, StateT.set,
    MonadStateOf.set]

/-- Raw resize of the whole block allocated with `align`: `false` changes nothing; `true` owns
the retained representation at the same pointer and address (still `align`-aligned). -/
theorem vtableResize_run (a : Allocator) {m : Mem} {s : Slice} {h hF : Heap} {A : Nat}
    {bs : Array Byte} {align : Nat} (n : BitVec 64) (hb : bytesAt s.ptr A s.len.toNat .heap bs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hS : bs.size = s.len.toNat)
    (h0 : s.ptr.off = 0) (hpos : 0 < s.len.toNat) (hst : m.Seq) (hal : rawAlignOk align = true)
    (hn : 0 < n.toNat)
    (hblkAlign : ∀ b blk, s.ptr.block = some b → m.blocks[b]? = some blk → blk.align = align) :
    ∃ r m', (vtableResize a s align n).run m = pure (r, m') ∧ m'.Seq ∧
      if r then ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧
          bytesAt s.ptr A n.toNat .heap (remapBytes bs n.toNat) h'
      else m' = m := by
  obtain ⟨b, blk, hacc, hblk, hptr, hK, hsz, hh, hbytes, haddr, hl⟩ := wholeRequest hb hm hS h0 hpos
  have hrb := rawBlock_run (align := align) hacc hK hsz
    (hblkAlign b blk (by rw [hptr]) hblk) hpos
  obtain ⟨r, m', hr, hst', hpost⟩ := rawInPlace_owned (n := n.toNat) hblk hl (hh ▸ hd) (hh ▸ hm) hst
  have hc : ¬ (rawAlignOk align = false ∨ n.toNat = 0) := by simp [hal]; omega
  simp only [StateT.run] at hrb hr
  refine ⟨r, m', ?_, hst', ?_⟩
  · simp [vtableResize, hc, zig_unfold, hrb, hr, ExceptT.bindCont]
  · cases r with
    | false => exact hpost
    | true =>
      obtain ⟨hd', hm', hp'⟩ := hpost
      refine ⟨_, hd', hm', ?_⟩
      rw [hptr, ← haddr, ← hbytes]
      simpa [hK] using hp'

/-- What `vtableRemap` returns: nothing (no change), or a whole aligned block owning the
retained representation, at the same block or a fresh one. -/
theorem vtableRemap_run (a : Allocator) {m : Mem} {s : Slice} {h hF : Heap} {A : Nat}
    {bs : Array Byte} {align : Nat} (n : BitVec 64) (hb : bytesAt s.ptr A s.len.toNat .heap bs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hS : bs.size = s.len.toNat)
    (h0 : s.ptr.off = 0) (hpos : 0 < s.len.toNat) (hst : m.Seq) (hal : rawAlignOk align = true)
    (hn : 0 < n.toNat) (hA : A % align = 0)
    (hblkAlign : ∀ b blk, s.ptr.block = some b → m.blocks[b]? = some blk → blk.align = align) :
    ∃ r m', (vtableRemap a s align n).run m = pure (r, m') ∧ m'.Seq ∧
      match r with
      | none => m' = m
      | some p => p.off = 0 ∧ ∃ h' A', A' % align = 0 ∧ Heap.Disjoint h' hF ∧
          m'.heap = h' ∪ hF ∧ bytesAt p A' n.toNat .heap (remapBytes bs n.toNat) h' := by
  obtain ⟨b, blk, hacc, hblk, hptr, hK, hsz, hh, hbytes, haddr, hl⟩ := wholeRequest hb hm hS h0 hpos
  have hrb := rawBlock_run (align := align) hacc hK hsz
    (hblkAlign b blk (by rw [hptr]) hblk) hpos
  have hc : ¬ (rawAlignOk align = false ∨ n.toNat = 0) := by simp [hal]; omega
  simp only [StateT.run] at hrb
  by_cases hmv : m.allocPolicy.byteRemap = .move ∧ n.toNat ≤ m.allocPolicy.maxBytes
  · -- Moved: read the retained prefix, allocate aligned, copy, free the old block.
    let recorded := m.recordAt b 0 (Nat.min blk.bytes.size n.toNat) .read
    have hmr : recorded.heap = h ∪ hF := by
      funext l; rw [Mem.heap_recordAt]; exact congrFun hm l
    have hread := recordAccess_run
      (noRace_of_singleThread hst.single b 0 (Nat.min blk.bytes.size n.toNat) .read)
    change (recordAccess b 0 (Nat.min blk.bytes.size n.toNat) .read).run m = pure ((), recorded)
      at hread
    simp only [StateT.run] at hread
    obtain ⟨p, allocated, hNew, ha, hp0, hdf, hma, hdn, hsta, -, A', hA', hnew, -⟩ :=
      alloc_run hd hmr .heap n.toNat align (rawAlignOk_pos hal) (hst.recordAt _ _ _ _)
    simp only [StateT.run] at ha
    have hma' : allocated.heap = hNew ∪ (h ∪ hF) := by
      rw [hma, Heap.union_assoc, Heap.union_left_comm hdn]
    have hdnew : Heap.Disjoint hNew (h ∪ hF) :=
      Heap.disjoint_union_right.mpr ⟨hdn.symm, (Heap.disjoint_union_left.mp hdf).2⟩
    obtain ⟨written, hw, hstw, hW, hdw, hmw, hbw⟩ :=
      bytesAt_store (q := p) (k := 0) (a := 1) (bs' := remapBytes blk.bytes n.toNat) hnew hma'
        hdnew (by simp [Ptr.add]) (by rw [remapBytes_size]; omega)
        (by rw [remapBytes_size]; simp) (Nat.mod_one _) hsta (by simp)
    simp only [StateT.run] at hw
    have hbw' : bytesAt p A' n.toNat .heap (remapBytes bs n.toNat) hW := by
      have hs : (remapBytes blk.bytes n.toNat).size = (Array.replicate n.toNat Byte.undef).size := by
        rw [remapBytes_size, Array.size_replicate]
      rw [writeBytes_all hs, hbytes] at hbw
      exact hbw
    obtain ⟨hdo, hdWF⟩ := Heap.disjoint_union_right.mp hdw
    have hmold : written.heap = h ∪ (hW ∪ hF) := by rw [hmw, Heap.union_left_comm hdo]
    obtain ⟨final, hf, hmf, hstf, -⟩ := rawFree_run hb hmold
      (Heap.disjoint_union_right.mpr ⟨hdo.symm, hd⟩) hS h0 hpos hstw
    simp only [StateT.run] at hf
    refine ⟨some p, final, ?_, hstf, hp0, hW, A', hA', hdWF, by simpa using hmf, hbw'⟩
    simp [vtableRemap, hc, zig_unfold, hrb, hmv, hread, ha, hw, hf, ExceptT.bindCont]
  · obtain ⟨r, m', hr, hst', hpost⟩ :=
      rawInPlace_owned (n := n.toNat) hblk hl (hh ▸ hd) (hh ▸ hm) hst
    simp only [StateT.run] at hr
    cases r with
    | false =>
      refine ⟨none, m', ?_, hst', hpost⟩
      simp [vtableRemap, hc, zig_unfold, hrb, hmv, hr, ExceptT.bindCont]
    | true =>
      obtain ⟨hd', hm', hp'⟩ := hpost
      refine ⟨some s.ptr, m', ?_, hst', h0, _, A, hA, hd', hm', ?_⟩
      · simp [vtableRemap, hc, zig_unfold, hrb, hmv, hr, ExceptT.bindCont]
      · rw [hptr, ← haddr, ← hbytes]
        simpa [hK] using hp'

end Zig
