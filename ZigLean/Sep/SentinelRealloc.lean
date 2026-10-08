import ZigLean.Sep.Sentinel
import ZigLean.Sep.Remap

/-! Byte `realloc` and sentinel reallocation (M04). Under whole-block ownership, every
successful path (in-place remap, moved remap, allocate/copy/free) owns exactly
`remapBytes bs n`; failure leaves the caller's block untouched. Sentinel reallocation
counts the sentinel byte in every request and stores it at the new length. -/
namespace Zig
open Assn

/-- Owning a whole live heap block determines its representation, address and kind. -/
theorem bytesAt_whole {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {bs : Array Byte}
    {b : BlockId} {blk : Block} (hb : bytesAt p A S .heap bs h) (hm : m.heap = h ∪ hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hpb : p.block = some b)
    (hblk : m.blocks[b]? = some blk) (hsz : blk.bytes.size = S) :
    h = blockHeap b blk ∧ blk.bytes = bs ∧ blk.addr = A ∧ blk.kind = .heap ∧ blk.live := by
  have cell : ∀ y, y < S → blk.live ∧ (⟨bs[y]!, A, S, .heap⟩ : Cell) =
      ⟨blk.bytes[y]!, blk.addr, blk.bytes.size, blk.kind⟩ := by
    intro y hy
    have c := bytesAt_cell hb hm hpb (j := y) (by omega)
    simp only [h0, Int.toNat_zero, Nat.zero_add] at c
    obtain ⟨blk', hblk', hl, hy', e⟩ := Mem.heap_some c
    rw [hblk] at hblk'; cases hblk'
    exact ⟨hl, by rw [e, getElem!_pos blk.bytes y hy']⟩
  obtain ⟨hl, c0⟩ := cell 0 hpos
  simp only [Cell.mk.injEq] at c0
  have hbytes : blk.bytes = bs := by
    apply Array.ext (by omega)
    intro i h1 h2
    have := (Cell.mk.inj (cell i (by omega)).2).1
    rw [getElem!_pos bs i h2, getElem!_pos blk.bytes i h1] at this
    exact this.symm
  refine ⟨?_, hbytes, c0.2.1.symm, c0.2.2.2.symm, hl⟩
  obtain ⟨b', hpb', -, hown⟩ := id hb
  rw [hpb] at hpb'; cases hpb'
  funext ⟨x, y⟩
  rw [hown]
  simp only [h0, Int.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, blockHeap,
    hsz, hS]
  by_cases hc : x = b ∧ y < S
  · rw [if_pos hc, if_pos hc, (cell y hc.2).2, hsz]
  · rw [if_neg hc, if_neg hc]

/-- Whole-block ownership of a nonempty slice at offset 0 supplies its access, block and
representation facts. -/
theorem wholeRequest {m : Mem} {s : Slice} {h hF : Heap} {A : Nat} {bs : Array Byte}
    (hb : bytesAt s.ptr A s.len.toNat .heap bs h) (hm : m.heap = h ∪ hF)
    (hS : bs.size = s.len.toNat) (h0 : s.ptr.off = 0) (hpos : 0 < s.len.toNat) :
    ∃ b blk, m.access s.ptr s.len.toNat 1 = pure (b, blk, 0) ∧ m.blocks[b]? = some blk ∧
      s.ptr = ⟨some b, 0⟩ ∧ blk.kind = .heap ∧ blk.bytes.size = s.len.toNat ∧
      h = blockHeap b blk ∧ blk.bytes = bs ∧ blk.addr = A ∧ blk.live := by
  obtain ⟨b, blk, hacc, hK, hsz⟩ := heapBlock_access hb hm hS hpos
  simp only [h0, Int.toNat_zero] at hacc
  obtain ⟨hpb, hblk, -, -, -, -, -⟩ := access_eq hacc
  obtain ⟨hh, hbytes, haddr, -, hl⟩ := bytesAt_whole hb hm hS h0 hpos hpb hblk hsz
  have hptr : s.ptr = ⟨some b, 0⟩ := by cases hp : s.ptr; simp_all
  exact ⟨b, blk, hacc, hblk, hptr, hK, hsz, hh, hbytes, haddr, hl⟩

/-- Selected byte remap under whole-block ownership of a nonempty slice: `none` changes nothing;
success owns exactly the retained representation, at the old or a new block. -/
theorem remapByteBuffer_owned {m : Mem} {s : Slice} {h hF : Heap} {A : Nat} {bs : Array Byte}
    {n : Nat} (hb : bytesAt s.ptr A s.len.toNat .heap bs h) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hS : bs.size = s.len.toNat) (h0 : s.ptr.off = 0)
    (hold : 0 < s.len.toNat) (hn : 0 < n) (hst : m.Seq) :
    ∃ r m', (remapByteBuffer s n).run m = pure (r, m') ∧ m'.Seq ∧
      match r with
      | none => m' = m
      | some g => g.len = BitVec.ofNat 64 n ∧ g.ptr.off = 0 ∧ ∃ h' A', Heap.Disjoint h' hF ∧
          m'.heap = h' ∪ hF ∧ bytesAt g.ptr A' n .heap (remapBytes bs n) h' := by
  obtain ⟨b, blk, hacc, hblk, hptr, hK, hsz, hh, hbytes, -, hl⟩ := wholeRequest hb hm hS h0 hold
  have hwhole : ¬ (blk.kind ≠ .heap ∨ blk.bytes.size ≠ s.len.toNat) := by simp [hK, hsz]
  have hn0 : ¬ n = 0 := by omega
  -- Every `none` result returns the unchanged memory.
  have none_of (hr : (remapByteBuffer s n).run m = pure (none, m)) :
      ∃ r m', (remapByteBuffer s n).run m = pure (r, m') ∧ m'.Seq ∧
        match r with
        | none => m' = m
        | some g => g.len = BitVec.ofNat 64 n ∧ g.ptr.off = 0 ∧ ∃ h' A', Heap.Disjoint h' hF ∧
            m'.heap = h' ∪ hF ∧ bytesAt g.ptr A' n .heap (remapBytes bs n) h' :=
    ⟨none, m, hr, hst, rfl⟩
  by_cases hfail : m.allocPolicy.byteRemap = .fail
  · exact none_of (remapByteBuffer_default_run s n hfail)
  -- Both success policies first return `none` for another alignment or above the cap.
  by_cases hc : blk.align ≠ 1 ∨ m.allocPolicy.maxBytes < n
  · apply none_of
    have hc' : blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n := by
      rcases hc with hc | hc
      · exact .inl hc
      · exact .inr (.inr hc)
    simp [remapByteBuffer, hfail, hacc, hwhole, hc', zig_unfold]
  have halign : blk.align = 1 := by
    simp only [ne_eq, not_or, Decidable.not_not] at hc; exact hc.1
  have hcap : n ≤ m.allocPolicy.maxBytes := by
    simp only [ne_eq, not_or, Nat.not_lt] at hc; exact hc.2
  cases hmode : m.allocPolicy.byteRemap with
  | fail => exact absurd hmode hfail
  | inPlace =>
    by_cases hg : blk.bytes.size < n ∧ m.byteRemapLast b blk ≠ true
    · apply none_of
      have hc' : ¬ (blk.align ≠ 1 ∨ n = 0 ∨ m.allocPolicy.maxBytes < n) := by
        simp [halign, hn0, Nat.not_lt.mpr hcap]
      simp only [ne_eq, Bool.not_eq_true] at hg
      simp [remapByteBuffer, hmode, hacc, hwhole, hc', hg, zig_unfold]
    have hlatest : blk.bytes.size < n → m.byteRemapLast b blk = true := by
      intro hlt
      cases ht : m.byteRemapLast b blk
      · exact absurd ⟨hlt, by simp [ht]⟩ hg
      · rfl
    have hrun := remapByteBuffer_inPlace_run hmode hacc hK hsz halign hn0 hcap hlatest
      (noRace_of_singleThread hst.single b 0 blk.bytes.size .write)
    let recorded := m.recordAt b 0 blk.bytes.size .write
    have hbr : recorded.blocks[b]? = some blk := by simpa [recorded, Mem.recordAt] using hblk
    have hmr : recorded.heap = blockHeap b blk ∪ hF := by
      funext l
      rw [Mem.heap_recordAt, ← hh]
      exact congrFun hm l
    have hdb : Heap.Disjoint (blockHeap b blk) hF := hh ▸ hd
    obtain ⟨hd', hm', hp'⟩ := afterByteRemap_owned_frame hbr hl hdb hmr n
    refine ⟨some ⟨s.ptr, BitVec.ofNat 64 n⟩, recorded.afterByteRemap b blk n, hrun,
      afterByteRemap_seq hbr hl hdb hmr (hst.recordAt _ _ _ _) n, rfl, h0, _, blk.addr, hd',
      hm', ?_⟩
    rw [hptr]
    simpa [hK, hbytes] using hp'
  | move =>
    obtain ⟨p, m', h', A', hr, hd', hm', hst', hp0, hb'⟩ :=
      remapByteBuffer_move_owned (hbytes ▸ hb) hm hd hst h0 hold hmode hacc hK hsz halign hn hcap
    exact ⟨some ⟨p, BitVec.ofNat 64 n⟩, m', hr, hst', rfl, hp0, h', A', hd', hm',
      by simpa [hbytes] using hb'⟩

/-- The copy path writes the `min` prefix into fresh undefined bytes: the same representation
as a remap. -/
theorem writeBytes_copy_eq_remapBytes (bs : Array Byte) (n : Nat) :
    writeBytes (Array.replicate n .undef) 0 (bs.extract 0 (Min.min n bs.size)) =
      remapBytes bs n := by
  apply Array.ext
  · rw [writeBytes_size _ _ _ (by simp; omega), remapBytes_size]; simp
  · intro i h1 h2
    rw [remapBytes_size] at h2
    have e1 := writeBytes_getElem? (Array.replicate n .undef) 0 (bs.extract 0 (Min.min n bs.size))
      (by simp; omega) i
    rw [Array.getElem?_eq_getElem h1] at e1
    by_cases hi : i < bs.size
    · have e2 := remapBytes_prefix bs n i hi h2
      rw [Array.getElem?_eq_getElem (by rw [remapBytes_size]; exact h2)] at e2
      have hin : 0 ≤ i ∧ i < 0 + (bs.extract 0 (Min.min n bs.size)).size := by
        rw [Array.size_extract]; omega
      rw [if_pos hin] at e1
      apply Option.some.inj
      rw [e1, e2, Nat.sub_zero, Array.getElem?_extract]
      simp <;> omega
    · have e2 := remapBytes_suffix bs n i (by omega) h2
      rw [Array.getElem?_eq_getElem (by rw [remapBytes_size]; exact h2)] at e2
      have hin : ¬ (0 ≤ i ∧ i < 0 + (bs.extract 0 (Min.min n bs.size)).size) := by
        rw [Array.size_extract]; omega
      rw [if_neg hin] at e1
      apply Option.some.inj
      rw [e1, e2]
      simp [h2]

/-- Byte `realloc` of a nonempty whole heap block to a nonzero length: every success owns exactly
`remapBytes bs n` (any remap policy, or allocate/copy/free); the only failure is OutOfMemory
with the caller's heap unchanged. The caller frame is exact on both paths. -/
theorem realloc_run {m : Mem} {s : Slice} {h hF : Heap} {A : Nat} {bs : Array Byte}
    (a : Allocator) (n : BitVec 64)
    (hb : bytesAt s.ptr A s.len.toNat .heap bs h) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) (hS : bs.size = s.len.toNat) (h0 : s.ptr.off = 0)
    (hold : 0 < s.len.toNat) (hn : 0 < n.toNat) (hst : m.Seq) :
    ∃ r m', (a.realloc s n).run m = pure (r, m') ∧ m'.Seq ∧
      match r with
      | .ok g => g.len = n ∧ g.ptr.off = 0 ∧ ∃ h' A', Heap.Disjoint h' hF ∧
          m'.heap = h' ∪ hF ∧ bytesAt g.ptr A' n.toNat .heap (remapBytes bs n.toNat) h'
      | .error e => e = "OutOfMemory" ∧ m'.heap = h ∪ hF := by
  have hl0 : ¬ s.len.toNat = 0 := by omega
  have hn0 : ¬ n.toNat = 0 := by omega
  obtain ⟨r, m₁, hr, hst₁, hpost⟩ := remapByteBuffer_owned hb hm hd hS h0 hold hn hst
  simp only [StateT.run] at hr
  cases r with
  | some g =>
    obtain ⟨hg, hg0, h', A', hd', hm', hb'⟩ := hpost
    refine ⟨.ok g, m₁, ?_, hst₁, by rw [hg]; simp, hg0, h', A', hd', hm', hb'⟩
    simp [Allocator.realloc, hl0, hn0, zig_unfold, hr, ExceptT.bindCont]
  | none =>
    subst hpost
    obtain ⟨r, m₂, ha, hst₂, -, hpost⟩ := rawAlloc_run hd hm n.toNat 1 (by omega) hst
    simp only [StateT.run] at ha
    cases r with
    | none =>
      refine ⟨.error "OutOfMemory", m₂, ?_, hst₂, rfl, hpost⟩
      simp [Allocator.realloc, hl0, hn0, zig_unfold, hr, ha, ExceptT.bindCont]
    | some p =>
      obtain ⟨hp0, hN, hdUF, hmN, hdhN, A', -, hbN, -⟩ := hpost
      obtain ⟨k, hk⟩ : ∃ k, k = Nat.min n.toNat s.len.toNat := ⟨_, rfl⟩
      have hk' : k = Min.min n.toNat s.len.toNat := hk
      have hk0 : 0 < k := by omega
      have hkl : k ≤ s.len.toNat := by omega
      have hkn : k ≤ n.toNat := by omega
      have hm₂ : m₂.heap = h ∪ (hN ∪ hF) := by rw [hmN, Heap.union_assoc]
      obtain ⟨b, blk, hacc, -, -, -, hext⟩ := bytesAt_access (q := s.ptr) (k := 0) (n := k)
        (a := 1) hb hm₂ (by simp [Ptr.add]) (by omega) (by omega) (Nat.mod_one _)
      simp only [h0, Int.toNat_zero, Nat.zero_add] at hacc hext
      have hload := loadBytes_run hacc (noRace_of_singleThread hst₂.single b 0 k .read)
      simp only [StateT.run, Nat.zero_add] at hload
      have hdN : Heap.Disjoint hN (h ∪ hF) :=
        Heap.disjoint_union_right.mpr ⟨hdhN.symm, (Heap.disjoint_union_left.mp hdUF).2⟩
      have hm₃ : (m₂.recordAt b 0 k .read).heap = hN ∪ (h ∪ hF) := by
        funext l
        rw [Mem.heap_recordAt, hm₂, Heap.union_left_comm hdhN]
      have hcopy : (blk.bytes.extract 0 k).size = k := by
        rw [hext]; simp; omega
      obtain ⟨m₄, hs, hst₄, hW, hdW, hmW, hbW⟩ := bytesAt_store hbN hm₃ hdN (q := p) (k := 0)
        (a := 1) (bs' := blk.bytes.extract 0 k) (by simp [Ptr.add]) (by omega)
        (by simp only [hcopy, Array.size_replicate]; omega) (Nat.mod_one _)
        (hst₂.recordAt _ _ _ _) (by simp)
      simp only [StateT.run] at hs
      obtain ⟨hdWh, hdWF⟩ := Heap.disjoint_union_right.mp hdW
      have hm₄ : m₄.heap = h ∪ (hW ∪ hF) := by rw [hmW, Heap.union_left_comm hdWh]
      obtain ⟨m₅, hf, hm₅, hst₅, -⟩ := poisonFree_run hb hm₄
        (Heap.disjoint_union_right.mpr ⟨hdWh.symm, hd⟩) hS h0 hold hst₄
      simp only [StateT.run] at hf
      have hbytes : writeBytes (Array.replicate n.toNat .undef) 0 (blk.bytes.extract 0 k) =
          remapBytes bs n.toNat := by
        rw [hext, show k = Min.min n.toNat bs.size by rw [hk', hS]]
        exact writeBytes_copy_eq_remapBytes bs n.toNat
      refine ⟨.ok ⟨p, n⟩, m₅, ?_, hst₅, rfl, hp0, hW, A', hdWF, by simpa using hm₅,
        hbytes ▸ hbW⟩
      simp [Allocator.realloc, hl0, hn0, zig_unfold, hr, ha, ← hk, hload, hs, hf, ExceptT.bindCont]

/-! ## Sentinel reallocation -/

private theorem encode_byte_size (v : BitVec 8) : (Enc.encode v).size = 1 := by
  simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode v

/-- Retained representations below `k ≤ n` are the old ones. -/
theorem remapBytes_extract_prefix (bs : Array Byte) (n k : Nat) (hk : k ≤ n) (hb : k ≤ bs.size) :
    (remapBytes bs n).extract 0 k = bs.extract 0 k := by
  apply Array.ext
  · simp [remapBytes_size]; omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1 h2
    have e := remapBytes_prefix bs n i (by omega) (by omega)
    rw [Array.getElem?_eq_getElem (by rw [remapBytes_size]; omega),
      Array.getElem?_eq_getElem (by omega)] at e
    simpa using Option.some.inj e

/-- A byte sentinel buffer: the whole `len + 1`-byte heap block `bs` at offset 0, whose last
byte is the sentinel. The sentinel byte is owned and counted in the block size. -/
def sentinelBuf (s : Slice) (A : Nat) (bs : Array Byte) (sentinel : BitVec 8) : Assn := fun h =>
  s.ptr.off = 0 ∧ bs.size = s.len.toNat + 1 ∧
    bs.extract s.len.toNat (s.len.toNat + 1) = Enc.encode sentinel ∧
    bytesAt s.ptr A (s.len.toNat + 1) .heap bs h

/-- A successful `allocSentinel` is a sentinel buffer. -/
theorem sentinelBuf_of_newSentinel {n : BitVec 64} {sentinel : BitVec 8} {s : Slice} {h : Heap}
    (hs : newSentinel n sentinel (.ok s) h) :
    ∃ A, sentinelBuf s A (sentinelBytes n.toNat sentinel) sentinel h := by
  obtain ⟨hl, h0, A, hb⟩ := hs
  subst hl
  exact ⟨A, h0, sentinelBytes_size _ _, sentinelBytes_sentinel _ _, hb⟩

/-- A sentinel buffer is released as a whole, including its sentinel byte. -/
theorem Triple.freeSentinelBuf (a : Allocator) {s : Slice} {A : Nat} {bs : Array Byte}
    {sentinel : BitVec 8} :
    Triple (sentinelBuf s A bs sentinel) (a.freeSentinel 1 s) (fun _ => emp) := by
  rintro m hP hF hd hm ⟨h0, hS, -, hb⟩ hst
  exact Triple.freeSentinel a (A := A) (s := s) (bs := bs) (by omega) h0 (by omega) m hP hF hd hm
    (by simpa using hb) hst

/-- Owned bytes after reallocating a sentinel buffer `bs` to length `n`: the retained
representation of all `n + 1` requested bytes, then the sentinel stored at `n`. -/
def sentinelReallocBytes (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) : Array Byte :=
  writeBytes (remapBytes bs (n + 1)) n (Enc.encode sentinel)

private theorem sentinelRealloc_fits (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) :
    n + (Enc.encode sentinel).size ≤ (remapBytes bs (n + 1)).size := by
  rw [encode_byte_size, remapBytes_size]; exact Nat.le_refl _

theorem sentinelReallocBytes_size (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) :
    (sentinelReallocBytes bs n sentinel).size = n + 1 := by
  unfold sentinelReallocBytes
  rw [writeBytes_size _ _ _ (sentinelRealloc_fits bs n sentinel), remapBytes_size]

/-- The sentinel is at the new length. -/
theorem sentinelReallocBytes_sentinel (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) :
    (sentinelReallocBytes bs n sentinel).extract n (n + 1) = Enc.encode sentinel := by
  have e := extract_writeBytes (remapBytes bs (n + 1)) n (Enc.encode sentinel)
    (sentinelRealloc_fits bs n sentinel)
  rwa [encode_byte_size] at e

/-- Every old byte below the new length is retained: the payload prefix and, on growth, the old
sentinel byte at the old length. -/
theorem sentinelReallocBytes_prefix (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) (i : Nat)
    (hi : i < bs.size) (hn : i < n) : (sentinelReallocBytes bs n sentinel)[i]? = bs[i]? := by
  unfold sentinelReallocBytes
  rw [writeBytes_getElem? _ _ _ (sentinelRealloc_fits bs n sentinel) i,
    if_neg (by rw [encode_byte_size]; omega)]
  exact remapBytes_prefix bs (n + 1) i hi (by omega)

/-- Grown bytes between the old block end and the new sentinel are undefined. -/
theorem sentinelReallocBytes_grown (bs : Array Byte) (n : Nat) (sentinel : BitVec 8) (i : Nat)
    (hi : bs.size ≤ i) (hn : i < n) : (sentinelReallocBytes bs n sentinel)[i]? = some .undef := by
  unfold sentinelReallocBytes
  rw [writeBytes_getElem? _ _ _ (sentinelRealloc_fits bs n sentinel) i,
    if_neg (by rw [encode_byte_size]; omega)]
  exact remapBytes_suffix bs (n + 1) i hi (by omega)

/-- Success is a sentinel buffer of length `n` with the reallocated bytes; failure is
OutOfMemory and still the original sentinel buffer. -/
def reallocSentinelPost (s : Slice) (A : Nat) (bs : Array Byte) (n : BitVec 64)
    (sentinel : BitVec 8) : Except ErrName Slice → Assn
  | .ok r => fun h => r.len = n ∧ ∃ A', sentinelBuf r A' (sentinelReallocBytes bs n.toNat sentinel)
      sentinel h
  | .error e => fun h => e = "OutOfMemory" ∧ sentinelBuf s A bs sentinel h

/-- ReleaseSafe `n + 1` overflow panics before any allocator decision. -/
theorem reallocSentinel_overflow (a : Allocator) (s : Slice) (n : BitVec 64)
    (sentinel : BitVec 8) (h : 2 ^ 64 ≤ n.toNat + 1) (m : Mem) :
    (a.reallocSentinel s n sentinel).run m = throw .panic := by
  simp [Allocator.reallocSentinel, h, zig_unfold]

/-- Sentinel reallocation preserves the sentinel invariant on success (at the new length,
with the sentinel byte counted in the request) and on failure (the original block, bytes and
sentinel), for every allocation policy, cap, failure trace and remap mode. -/
theorem Triple.reallocSentinel (a : Allocator) (s : Slice) (n : BitVec 64) (sentinel : BitVec 8)
    {A : Nat} {bs : Array Byte} (hlen : s.len.toNat + 1 < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64) :
    Triple (sentinelBuf s A bs sentinel) (a.reallocSentinel s n sentinel)
      (reallocSentinelPost s A bs n sentinel) := by
  apply Triple.of_run
  intro m hP hF hd hm hpre hst
  obtain ⟨h0, hS, hsent, hb⟩ := hpre
  have ho : ¬ 2 ^ 64 ≤ n.toNat + 1 := by omega
  have hfl : (s.len + 1).toNat = s.len.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  have hn1 : (n + 1).toNat = n.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  obtain ⟨r, m₁, hr, hst₁, hpost⟩ := realloc_run (s := ⟨s.ptr, s.len + 1⟩) a (n + 1)
    (by rw [hfl]; exact hb) hm hd (by rw [hfl]; exact hS) h0 (by rw [hfl]; omega)
    (by rw [hn1]; omega) hst
  simp only [StateT.run] at hr
  -- The generated term spells the BitVec literals as `1#64`.
  replace hr : a.realloc ⟨s.ptr, s.len + 1#64⟩ (n + 1#64) m = pure (r, m₁) := hr
  cases r with
  | error e =>
    obtain ⟨he, hm₁⟩ := hpost
    refine ⟨.error e, m₁, hP, ?_, hd, hm₁, ⟨he, h0, hS, hsent, hb⟩, hst₁⟩
    simp [Allocator.reallocSentinel, ho, zig_unfold, hr, ExceptT.bindCont]
  | ok g =>
    obtain ⟨-, hg0, h', A', hd', hm', hb'⟩ := hpost
    rw [hn1] at hb'
    obtain ⟨m₂, hs, hst₂, h₂, hd₂, hm₂, hb₂⟩ := bytesAt_store hb' hm' hd'
      (q := g.ptr.add n.toNat) (k := n.toNat) (a := 1) (bs' := Enc.encode sentinel) rfl
      (by rw [encode_byte_size]; omega) (sentinelRealloc_fits bs n.toNat sentinel)
      (Nat.mod_one _) hst₁ (by decide)
    simp only [StateT.run] at hs
    refine ⟨.ok ⟨g.ptr, n⟩, m₂, h₂, ?_, hd₂, hm₂, ⟨rfl, A', hg0,
      sentinelReallocBytes_size _ _ _, sentinelReallocBytes_sentinel _ _ _, hb₂⟩, hst₂⟩
    simp [Allocator.reallocSentinel, ho, Zig.store, zig_unfold, hr, hs, ExceptT.bindCont]

/-! ## Client: append to a sentinel-terminated buffer -/

/-- Append `c`: reallocate to `len + 1` (requesting `len + 2` bytes), then write `c` at the old
length. The sentinel moves to the new end. -/
def appendSentinel (a : Allocator) (s : Slice) (c sentinel : BitVec 8) :
    MemM (Except ErrName Slice) := do
  match ← a.reallocSentinel s (s.len + 1) sentinel with
  | .error e => pure (.error e)
  | .ok g =>
    store 1 (g.ptr.add s.len.toNat) c
    pure (.ok g)

/-- After `appendSentinel`: one more byte, the payload unchanged, `c` at the old length and the
sentinel at the new length; on failure the original buffer and sentinel. -/
def appendPost (s : Slice) (A : Nat) (bs : Array Byte) (c sentinel : BitVec 8) :
    Except ErrName Slice → Assn
  | .ok r => fun h => r.len.toNat = s.len.toNat + 1 ∧ ∃ A' bs', sentinelBuf r A' bs' sentinel h ∧
      bs'.extract 0 s.len.toNat = bs.extract 0 s.len.toNat ∧
      bs'.extract s.len.toNat (s.len.toNat + 1) = Enc.encode c
  | .error e => fun h => e = "OutOfMemory" ∧ sentinelBuf s A bs sentinel h

theorem Triple.appendSentinel (a : Allocator) (s : Slice) (c sentinel : BitVec 8) {A : Nat}
    {bs : Array Byte} (hlen : s.len.toNat + 2 < 2 ^ 64) :
    Triple (sentinelBuf s A bs sentinel) (appendSentinel a s c sentinel)
      (appendPost s A bs c sentinel) := by
  have hn : (s.len + 1).toNat = s.len.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  -- The precondition fixes the old block size; keep it for the payload-prefix fact.
  by_cases hbs : bs.size = s.len.toNat + 1
  case neg =>
    intro m hP hF hd hm hpre
    exact absurd hpre.2.1 hbs
  apply Triple.bind (Triple.reallocSentinel a s (s.len + 1) sentinel (by omega) (by omega))
  intro r
  cases r with
  | error e =>
    apply Triple.of_run
    intro m hP hF hd hm hq hst
    exact ⟨.error e, m, hP, rfl, hd, hm, hq, hst⟩
  | ok g =>
    apply Triple.of_run
    intro m hP hF hd hm hq hst
    obtain ⟨hgl, A', h0, hS, hsent, hb⟩ := hq
    rw [hgl, hn] at hS hsent hb
    obtain ⟨old, hold⟩ : ∃ x, x = sentinelReallocBytes bs (s.len.toNat + 1) sentinel := ⟨_, rfl⟩
    rw [← hold] at hS hsent hb
    obtain ⟨m', hs, hst', h', hd', hm', hb'⟩ := bytesAt_store hb hm hd
      (q := g.ptr.add s.len.toNat) (k := s.len.toNat) (a := 1) (bs' := Enc.encode c) rfl
      (by rw [encode_byte_size]; omega) (by rw [encode_byte_size]; omega) (Nat.mod_one _) hst
      (by decide)
    simp only [StateT.run] at hs
    have hfit : s.len.toNat + (Enc.encode c).size ≤ old.size := by
      rw [encode_byte_size]; omega
    refine ⟨.ok g, m', h', ?_, hd', hm', ⟨by rw [hgl, hn], A',
      writeBytes old s.len.toNat (Enc.encode c), ⟨h0, ?_, ?_, ?_⟩, ?_, ?_⟩, hst'⟩
    · simp [Zig.store, zig_unfold, hs, ExceptT.bindCont]
    · rw [writeBytes_size _ _ _ hfit, hgl, hn]; exact hS
    · rw [hgl, hn]
      have e := extract_writeBytes_disjoint old s.len.toNat (Enc.encode c) (s.len.toNat + 1) 1
        hfit (by omega) (by rw [encode_byte_size]; omega)
      rw [e]; exact hsent
    · rw [hgl, hn]; exact hb'
    · have e := extract_writeBytes_disjoint old s.len.toNat (Enc.encode c) 0 s.len.toNat
        hfit (by omega) (by omega)
      rw [Nat.zero_add] at e
      rw [e]
      rw [hold]
      unfold sentinelReallocBytes
      have e2 := extract_writeBytes_disjoint (remapBytes bs (s.len.toNat + 1 + 1))
        (s.len.toNat + 1) (Enc.encode sentinel) 0 s.len.toNat
        (sentinelRealloc_fits bs _ sentinel) (by rw [remapBytes_size]; omega) (by omega)
      rw [Nat.zero_add] at e2
      rw [e2]
      exact remapBytes_extract_prefix bs _ _ (by omega) (by omega)
    · have e := extract_writeBytes old s.len.toNat (Enc.encode c) hfit
      rwa [encode_byte_size] at e

end Zig
