import ZigLean.Sep.Alloc

/-! Whole-block ownership facts for the byte-remap runtime transition. These source rules
are pending kernel qualification. Success on a byte-buffer retains exact representations,
not a premise that previously undefined bytes become defined. -/
namespace Zig
open Assn

theorem remapBytes_size (bs : Array Byte) (n : Nat) : (remapBytes bs n).size = n := by
  simp only [remapBytes, padTo, Array.size_append, Array.size_extract, Array.size_replicate]
  omega

/-- Each retained byte is unchanged, including any undefined or pointer-fragment byte. -/
theorem remapBytes_prefix (bs : Array Byte) (n i : Nat) (hi : i < bs.size) (hn : i < n) :
    (remapBytes bs n)[i]? = bs[i]? := by
  have hk : i < Nat.min n bs.size := Nat.lt_min.mpr ⟨hn, hi⟩
  unfold remapBytes padTo
  rw [Array.getElem?_append_left (by simpa using hk), Array.getElem?_extract]
  simp [hk]

/-- A newly grown byte is undefined until the client initializes it. -/
theorem remapBytes_suffix (bs : Array Byte) (n i : Nat) (hi : bs.size ≤ i) (hn : i < n) :
    (remapBytes bs n)[i]? = some .undef := by
  have hg : bs.size ≤ n := by omega
  have hs : i - bs.size < n - bs.size := by omega
  unfold remapBytes padTo
  rw [Array.getElem?_append_right (by simpa [Nat.min_eq_right hg] using hi)]
  simp [Nat.min_eq_right hg, hs]

/-- Representation of a whole block, including the block-size metadata on every cell. -/
def blockHeap (b : BlockId) (blk : Block) : Heap := fun l =>
  if l.1 = b ∧ l.2 < blk.bytes.size then
    some ⟨blk.bytes[l.2]!, blk.addr, blk.bytes.size, blk.kind⟩ else none

theorem blockHeap_owned (b : BlockId) (blk : Block) :
    bytesAt ⟨some b, 0⟩ blk.addr blk.bytes.size blk.kind blk.bytes (blockHeap b blk) := by
  refine ⟨b, rfl, Int.le_refl 0, ?_⟩
  intro l
  simp [blockHeap]

/-- A frame disjoint from the complete live block has no cells anywhere in that block,
including beyond the previous end. Such cells are absent from the old whole memory. -/
theorem wholeBlock_frame_none {m : Mem} {b : BlockId} {blk : Block} {hF : Heap}
    (hb : m.blocks[b]? = some blk) (hl : blk.live)
    (hd : Heap.Disjoint (blockHeap b blk) hF) (hm : m.heap = blockHeap b blk ∪ hF) :
    ∀ y, hF (b, y) = none := by
  intro y
  by_cases hy : y < blk.bytes.size
  · have hn : blockHeap b blk (b, y) ≠ none := by simp [blockHeap, hy]
    exact (hd (b, y)).resolve_left hn
  · have e := congrFun hm (b, y)
    simp [Mem.heap, hb, hl, hy, blockHeap] at e
    exact e.symm

/-- Resize consumes the entire old block and produces the entire resized block, with the
same pointer/address and updated size metadata. An arbitrary disjoint caller frame is exact. -/
theorem afterByteRemap_owned_frame {m : Mem} {b : BlockId} {blk : Block} {hF : Heap}
    (hb : m.blocks[b]? = some blk) (hl : blk.live)
    (hd : Heap.Disjoint (blockHeap b blk) hF) (hm : m.heap = blockHeap b blk ∪ hF) (n : Nat)
    (hlo : blk.kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    let next := { blk with bytes := remapBytes blk.bytes n }
    Heap.Disjoint (blockHeap b next) hF ∧
      (m.afterByteRemap b blk n).heap = blockHeap b next ∪ hF ∧
      bytesAt ⟨some b, 0⟩ blk.addr n blk.kind (remapBytes blk.bytes n) (blockHeap b next) := by
  dsimp only
  have hf := wholeBlock_frame_none hb hl hd hm
  have hlt := (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, y⟩
    by_cases e : x = b
    · subst x; right; exact hf y
    · left; simp [blockHeap, e]
  · funext ⟨x, y⟩
    by_cases hx : x = b
    · subst hx
      have e : (m.blocks.set! x { blk with bytes := remapBytes blk.bytes n })[x]? =
          some { blk with bytes := remapBytes blk.bytes n } := by
        rw [Array.set!_eq_setIfInBounds]
        exact Array.getElem?_setIfInBounds_self_of_lt hlt
      simp only [Mem.afterByteRemap, Mem.heap, e]
      by_cases hy : y < (remapBytes blk.bytes n).size
      · simp [blockHeap, hf, hl, hy, hlo, getElem!_pos]
      · simp [blockHeap, hf, hl, hy]
    · have e : (m.blocks.set! b { blk with bytes := remapBytes blk.bytes n })[x]? = m.blocks[x]? := by
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [Ne.symm hx]
      have hmx := congrFun hm (x, y)
      simp [blockHeap, hx] at hmx
      simp only [Mem.afterByteRemap, Mem.heap, e]
      simpa [Mem.heap, blockHeap, hx] using hmx
  · have h := blockHeap_owned b { blk with bytes := remapBytes blk.bytes n }
    simpa [remapBytes_size] using h

/-- The transition does not change thread clocks, histories or scheduler state. -/
theorem afterByteRemap_sameThreads (m : Mem) (b : BlockId) (blk : Block) (n : Nat) :
    m.SameThreads (m.afterByteRemap b blk n) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The resized block ends strictly below the monotonic future-allocation boundary. -/
theorem afterByteRemap_nextAddr (m : Mem) (b : BlockId) (blk : Block) (n : Nat) :
    m.nextAddr ≤ (m.afterByteRemap b blk n).nextAddr ∧
      blk.addr + n < (m.afterByteRemap b blk n).nextAddr := by
  change m.nextAddr ≤ Nat.max m.nextAddr (blk.addr + n + 1) ∧
    blk.addr + n < Nat.max m.nextAddr (blk.addr + n + 1)
  exact ⟨Nat.le_max_left _ _,
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)⟩


/-- Whole-block replacement preserves the sequential-memory invariant. Frame cells
retain their old bounds, and every resized cell lies below the enlarged boundary. -/
theorem afterByteRemap_seq {m : Mem} {b : BlockId} {blk : Block} {hF : Heap}
    (hb : m.blocks[b]? = some blk) (hl : blk.live)
    (hd : Heap.Disjoint (blockHeap b blk) hF) (hm : m.heap = blockHeap b blk ∪ hF)
    (hst : m.Seq) (n : Nat) : (m.afterByteRemap b blk n).Seq := by
  obtain ⟨_, hm', _⟩ := afterByteRemap_owned_frame hb hl hd hm n
  refine ⟨(afterByteRemap_sameThreads m b blk n).singleThread hst.single, ?_⟩
  intro l c hc
  rw [hm', Heap.union_apply] at hc
  cases he : blockHeap b { blk with bytes := remapBytes blk.bytes n } l with
  | some c0 =>
    rw [he] at hc
    cases hc
    simp only [blockHeap] at he
    split at he
    · cases he
      simpa [remapBytes_size] using (afterByteRemap_nextAddr m b blk n).2
    · cases he
  | none =>
    rw [he, Option.none_or] at hc
    have ho : blockHeap b blk l = none := (hd l).resolve_right (by rw [hc]; simp)
    have hcold : m.heap l = some c := by
      rw [hm, Heap.union_apply, ho, Option.none_or]
      exact hc
    have ha := hst.addr l c hcold
    have hn := (afterByteRemap_nextAddr m b blk n).1
    omega

/-- The actual in-place runtime branch, with explicit access/race/resource premises.
No undefined byte is decoded, and no external frame assumption is hidden in the run fact. -/
theorem remapByteBuffer_inPlace_run {m : Mem} {s : Slice} {b : BlockId} {blk : Block} {n : Nat}
    (hmode : m.allocPolicy.byteRemap = .inPlace)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0))
    (hkind : blk.kind = .heap) (hsize : blk.bytes.size = s.len.toNat) (halign : blk.align = 1)
    (hpos : n ≠ 0) (hcap : n ≤ m.allocPolicy.maxBytes)
    (hlatest : blk.bytes.size < n → m.byteRemapLast b blk = true)
    (hrace : NoRace m b 0 blk.bytes.size .write) :
    (remapByteBuffer s n).run m =
      pure (some ⟨s.ptr, BitVec.ofNat 64 n⟩,
        (m.recordAt b 0 blk.bytes.size .write).afterByteRemap b blk n) := by
  have hr := recordAccess_run hrace
  change (recordAccess b 0 blk.bytes.size .write).run m =
    pure ((), m.recordAt b 0 blk.bytes.size .write) at hr
  simp only [StateT.run] at hr
  have hwhole : ¬ (blk.kind ≠ .heap ∨ blk.bytes.size ≠ s.len.toNat) := by
    simp [hkind, hsize]
  have haligned : ¬ (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) := by
    simp [halign, hpos, Nat.not_lt.mpr hcap]
  have hgrowth : ¬ (blk.bytes.size < n ∧ m.byteRemapLast b blk = false) := by
    rintro ⟨hg, hf⟩
    have ht := hlatest hg
    rw [ht] at hf
    cases hf
  simp [remapByteBuffer, hmode, hacc, hwhole, haligned, hgrowth,
    zig_unfold, hr, ExceptT.bindCont, set, StateT.set, MonadStateOf.set]

/-- Complete ownership and exact frame preservation for the actual in-place branch.
Every output cell carries the new size. The old whole-block assertion is consumed. -/
theorem remapByteBuffer_inPlace_owned {m : Mem} {s : Slice} {b : BlockId} {blk : Block}
    {hF : Heap} {n : Nat}
    (hb : m.blocks[b]? = some blk) (hl : blk.live)
    (hd : Heap.Disjoint (blockHeap b blk) hF) (hm : m.heap = blockHeap b blk ∪ hF)
    (hmode : m.allocPolicy.byteRemap = .inPlace)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0))
    (hkind : blk.kind = .heap) (hsize : blk.bytes.size = s.len.toNat) (halign : blk.align = 1)
    (hpos : n ≠ 0) (hcap : n ≤ m.allocPolicy.maxBytes)
    (hlatest : blk.bytes.size < n → m.byteRemapLast b blk = true)
    (hrace : NoRace m b 0 blk.bytes.size .write) :
    ∃ m', (remapByteBuffer s n).run m = pure (some ⟨s.ptr, BitVec.ofNat 64 n⟩, m') ∧
      Heap.Disjoint (blockHeap b { blk with bytes := remapBytes blk.bytes n }) hF ∧
      m'.heap = blockHeap b { blk with bytes := remapBytes blk.bytes n } ∪ hF ∧
      bytesAt ⟨some b, 0⟩ blk.addr n .heap (remapBytes blk.bytes n)
        (blockHeap b { blk with bytes := remapBytes blk.bytes n }) := by
  let recorded := m.recordAt b 0 blk.bytes.size .write
  have hbr : recorded.blocks[b]? = some blk := by simpa [recorded, Mem.recordAt] using hb
  have hmr : recorded.heap = blockHeap b blk ∪ hF := by
    funext l
    rw [Mem.heap_recordAt]
    exact congrFun hm l
  obtain ⟨hd', hm', hp'⟩ := afterByteRemap_owned_frame hbr hl hd hmr n
  refine ⟨recorded.afterByteRemap b blk n,
    remapByteBuffer_inPlace_run hmode hacc hkind hsize halign hpos hcap hlatest hrace,
    hd', hm', ?_⟩
  simpa [hkind] using hp'

/-- Default remap failure is an exact no-op on all memory, even before success validation.
This preserves the old model's failure-only behavior, including its admitted call scope. -/
theorem remapByteBuffer_default_run {m : Mem} (s : Slice) (n : Nat)
    (hmode : m.allocPolicy.byteRemap = .fail) :
    (remapByteBuffer s n).run m = pure (none, m) := by
  simp [remapByteBuffer, hmode, zig_unfold]


/-- Moved success consumes the old whole block, obtains a fresh block, writes the retained
representations and undefined suffix, and reclaims the old allocation. The caller frame is
unchanged. Sequential ownership supplies the existing recorded-access race premises. -/
theorem remapByteBuffer_move_owned {m : Mem} {s : Slice} {b : BlockId} {blk : Block}
    {h hF : Heap} {A n : Nat}
    (hb : bytesAt s.ptr A s.len.toNat .heap blk.bytes h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hst : m.Seq)
    (h0 : s.ptr.off = 0) (hold : 0 < s.len.toNat)
    (hmode : m.allocPolicy.byteRemap = .move)
    (hacc : m.access s.ptr s.len.toNat 1 = pure (b, blk, 0))
    (hkind : blk.kind = .heap) (hsize : blk.bytes.size = s.len.toNat) (halign : blk.align = 1)
    (hpos : 0 < n) (hcap : n ≤ m.allocPolicy.maxBytes) :
    ∃ p m' h' A', (remapByteBuffer s n).run m = pure (some ⟨p, BitVec.ofNat 64 n⟩, m') ∧
      Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ m'.Seq ∧ p.off = 0 ∧
      bytesAt p A' n .heap (remapBytes blk.bytes n) h' := by
  let copied := remapBytes blk.bytes n
  let recorded := m.recordAt b 0 (Nat.min blk.bytes.size n) .read
  have hmr : recorded.heap = h ∪ hF := by
    funext l
    rw [Mem.heap_recordAt]
    exact congrFun hm l
  have hstr : recorded.Seq := hst.recordAt _ _ _ _
  obtain ⟨p, allocated, hNew, ha, hp0, hdf, hma, hdn, hsta, -, A', -, hnew, -⟩ :=
    alloc_run hd hmr .heap n 1 (by omega) hstr
  have hnewSize : (Array.replicate n Byte.undef).size = n := by simp
  have hcopySize : copied.size = n := remapBytes_size _ _
  have hma' : allocated.heap = hNew ∪ (h ∪ hF) := by
    rw [hma, Heap.union_assoc, Heap.union_left_comm hdn]
  have hdnew : Heap.Disjoint hNew (h ∪ hF) :=
    Heap.disjoint_union_right.mpr ⟨hdn.symm, (Heap.disjoint_union_left.mp hdf).2⟩
  obtain ⟨written, hw, hstw, hWritten, hdw, hmw, hbw⟩ :=
    bytesAt_store (q := p) (k := 0) (a := 1) (bs' := copied) hnew hma' hdnew
      (by simp [Ptr.add]) (by omega) (by omega) (Nat.mod_one _) hsta (by simp)
  have hbw' : bytesAt p A' n .heap copied hWritten := by
    have hs : copied.size = (Array.replicate n Byte.undef).size := by
      rw [hcopySize, Array.size_replicate]
    have he := writeBytes_all (a := Array.replicate n Byte.undef) (bs := copied) hs
    rw [he] at hbw
    exact hbw
  have hdo : Heap.Disjoint h hWritten := (Heap.disjoint_union_right.mp hdw).1.symm
  have hmold : written.heap = h ∪ (hWritten ∪ hF) := by
    rw [hmw, Heap.union_left_comm hdo.symm]
  have hdold : Heap.Disjoint h (hWritten ∪ hF) :=
    Heap.disjoint_union_right.mpr ⟨hdo, hd⟩
  obtain ⟨final, hf, hmf, hstf, -⟩ := poisonFree_run hb hmold hdold hsize h0 hold hstw
  have hread := recordAccess_run (noRace_of_singleThread hst.single b 0 (Nat.min blk.bytes.size n) .read)
  change (recordAccess b 0 (Nat.min blk.bytes.size n) .read).run m = pure ((), recorded) at hread
  simp only [StateT.run] at hread ha hw hf
  refine ⟨p, final, hWritten, A', ?_, (Heap.disjoint_union_right.mp hdw).2, ?_, hstf, hp0, hbw'⟩
  · have hc : ¬ m.allocPolicy.maxBytes < n := by omega
    have hn : n ≠ 0 := by omega
    have hwhole : ¬ (blk.kind ≠ .heap ∨ blk.bytes.size ≠ s.len.toNat) := by
      simp [hkind, hsize]
    have haligned : ¬ (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) := by
      simp [halign, hn, hc]
    simp [remapByteBuffer, hmode, hacc, hwhole, haligned,
      zig_unfold, hread, ha, hw, hf, copied, ExceptT.bindCont]
  · simpa using hmf

end Zig
