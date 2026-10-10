import ZigLean.Sep.Array

/-!
# Memory-backed array reassembly

Disjoint assertions alone need not agree on a block's address, size, or kind.
`arr_append_of_heap` and `arr_reassemble` therefore require an actual-memory
backing equality. The triple helper obtains that equality from the element rule's
returned memory. Selection stays explicit; this is a scalar array interface,
not a general range search or a source-to-model correspondence theorem.
-/

namespace Zig

open Assn

private theorem bytesAt_heap_empty {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {h : Heap} (hb : bytesAt p A S K bs h) (hz : bs.size = 0) :
    h = Heap.empty := by
  obtain ⟨_, _, _, hl⟩ := hb
  funext l
  rw [hl]
  simp [hz, Heap.empty]

private theorem bytesAt_metadata {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {m : Mem} {h hF : Heap} {b : BlockId} {blk : Block}
    (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF)
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hn : 0 < bs.size) :
    A = blk.addr ∧ S = blk.bytes.size ∧ K = blk.kind := by
  obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (bytesAt_cell hb hm hpb hn)
  rw [hblk] at hblk'; cases hblk'
  simp only [Cell.mk.injEq] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩

private theorem bytesAt_retag_of_heap {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {m : Mem} {h hF : Heap} {b : BlockId} {blk : Block}
    (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF)
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) :
    bytesAt p blk.addr blk.bytes.size blk.kind bs h := by
  by_cases hz : bs.size = 0
  · obtain ⟨b', hp', h0, hl⟩ := hb
    refine ⟨b', hp', h0, fun l => ?_⟩
    rw [hl]
    have hnot : ¬ (l.1 = b' ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size) := by
      rintro ⟨_, hlo, hhi⟩
      omega
    rw [if_neg hnot, if_neg hnot]
  · obtain ⟨rfl, rfl, rfl⟩ := bytesAt_metadata hb hm hpb hblk (by omega)
    exact hb

/-- Concatenate two contiguous byte ownership ranges with shared metadata. -/
theorem bytesAt_append {p : Ptr} {A S : Nat} {K : BlockKind} {xs ys : Array Byte} {h : Heap}
    (hp : (bytesAt p A S K xs ∗ bytesAt (p.add xs.size) A S K ys) h) :
    bytesAt p A S K (xs ++ ys) h := by
  obtain ⟨h₁, h₂, _, rfl, ⟨b, hpb, h0, hl₁⟩, ⟨b', hpb', _, hl₂⟩⟩ := hp
  have he : b = b' := by simpa [Ptr.add, hpb] using hpb'
  subst b'
  have hoff : (p.add xs.size).off.toNat = p.off.toNat + xs.size := by
    simp only [Ptr.add]; omega
  refine ⟨b, hpb, h0, fun l => ?_⟩
  rw [Heap.union_apply, hl₁, hl₂, hoff]
  simp only [Array.size_append]
  by_cases hleft : l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + xs.size
  · have hwhole : l.1 = b ∧ p.off.toNat ≤ l.2 ∧
        l.2 < p.off.toNat + (xs.size + ys.size) := by
      refine ⟨hleft.1, hleft.2.1, ?_⟩
      omega
    rw [if_pos hleft, if_pos hwhole, Option.some_or]
    congr 2
    simp [getElem!_def, Array.getElem?_append, show l.2 - p.off.toNat < xs.size by omega]
  · rw [if_neg hleft, Option.none_or]
    by_cases hright : l.1 = b ∧ p.off.toNat + xs.size ≤ l.2 ∧
        l.2 < p.off.toNat + xs.size + ys.size
    · have hwhole : l.1 = b ∧ p.off.toNat ≤ l.2 ∧
          l.2 < p.off.toNat + (xs.size + ys.size) := by
        refine ⟨hright.1, ?_, ?_⟩ <;> omega
      rw [if_pos hright, if_pos hwhole]
      congr 2
      simp only [getElem!_def, Array.getElem?_append,
        show ¬ l.2 - p.off.toNat < xs.size by omega, ↓reduceIte]
      congr 2; omega
    · have hwhole : ¬ (l.1 = b ∧ p.off.toNat ≤ l.2 ∧
          l.2 < p.off.toNat + (xs.size + ys.size)) := by
        rintro ⟨hblock, hlo, hhi⟩
        by_cases hcut : l.2 < p.off.toNat + xs.size
        · exact hleft ⟨hblock, hlo, hcut⟩
        · exact hright ⟨hblock, by omega, by omega⟩
      rw [if_neg hright, if_neg hwhole]

/-- Concatenate typed ranges backed by one actual memory. Positive element size is explicit. -/
theorem arr_append_of_heap {T : Type} [Enc T] {p : Ptr} {xs ys : List T}
    {m : Mem} {h hF : Heap} (hn : 0 < Enc.size T)
    (hp : (arr p xs ∗ arr (p.add (Enc.size T * xs.length)) ys) h)
    (hm : m.heap = h ∪ hF) : arr p (xs ++ ys) h := by
  obtain ⟨h₁, h₂, hd, rfl, hp₁, hp₂⟩ := hp
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb, hK⟩ := hp₁
  by_cases hx : xs = []
  · subst hx
    have hz : bs.size = 0 := by simpa using hsz
    have he := bytesAt_heap_empty hb hz
    subst he
    simpa [Ptr.add] using hp₂
  · have hnbs : 0 < bs.size := by
      rw [hsz]; exact Nat.mul_pos hn (List.length_pos_iff.mpr hx)
    obtain ⟨b, hpb, _, _⟩ := id hb
    have hm₁ : m.heap = h₁ ∪ (h₂ ∪ hF) := by rw [hm, Heap.union_assoc]
    have hm₂ : m.heap = h₂ ∪ (h₁ ∪ hF) := by
      rw [hm, Heap.union_comm hd, Heap.union_assoc]
    obtain ⟨blk, hblk, _, _, _⟩ := Mem.heap_some (bytesAt_cell hb hm₁ hpb hnbs)
    obtain ⟨haddr, hsize, hkind⟩ := bytesAt_metadata hb hm₁ hpb hblk hnbs
    obtain ⟨A₂, S₂, K₂, bs₂, _, hsz₂, hv₂, hb₂, -, hend₂⟩ := hp₂
    have hb₂' := bytesAt_retag_of_heap hb₂ hm₂
      (by simpa [Ptr.add] using hpb) hblk
    have hb₁' : bytesAt p blk.addr blk.bytes.size blk.kind bs h₁ := by
      simpa only [haddr, hsize, hkind] using hb
    have hptr : p.add (Enc.size T * xs.length) = p.add bs.size := by
      rw [hsz]; simp [Int.natCast_mul]
    have hbytes : bytesAt p blk.addr blk.bytes.size blk.kind (bs ++ bs₂) (h₁ ∪ h₂) :=
      bytesAt_append ⟨h₁, h₂, hd, rfl, hb₁', hptr ▸ hb₂'⟩
    have hoff₂ : (p.add (Enc.size T * xs.length)).off.toNat = p.off.toNat + bs.size := by
      obtain ⟨_, _, h0, _⟩ := id hb
      rw [hsz]; simp only [Ptr.add]; omega
    refine ⟨blk.addr, blk.bytes.size, blk.kind, bs ++ bs₂, haddr ▸ hA, ?_, ?_, hbytes,
      hkind ▸ hK.1, by rw [Array.size_append]; omega⟩
    · simp [hsz, hsz₂, List.length_append, Nat.mul_add]
    · intro j hj
      by_cases hleft : j < xs.length
      · have hend : Enc.size T * j + Enc.size T ≤ bs.size := by
          rw [hsz]; simpa only [Nat.mul_succ] using
            Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hleft)
        have hstart : Enc.size T * j ≤ bs.size := by omega
        rw [Array.extract_append]
        simp only [Nat.sub_eq_zero_of_le hstart, Nat.sub_eq_zero_of_le hend,
          Array.extract_zero, Array.append_empty]
        simpa only [List.getElem_append_left hleft] using hv j hleft
      · have hj₂ : j - xs.length < ys.length := by simp only [List.length_append] at hj; omega
        have hstart : bs.size ≤ Enc.size T * j := by
          rw [hsz]; exact Nat.mul_le_mul_left _ (by omega)
        have hstart' : Enc.size T * j - bs.size = Enc.size T * (j - xs.length) := by
          rw [hsz, Nat.mul_sub_left_distrib]
        have hend' : Enc.size T * j + Enc.size T - bs.size =
            Enc.size T * (j - xs.length) + Enc.size T := by omega
        rw [Array.extract_append]
        have hempty : bs.extract (Enc.size T * j) (Enc.size T * j + Enc.size T) = #[] := by
          apply Array.eq_empty_of_size_eq_zero
          simp only [Array.size_extract]; omega
        rw [hempty, Array.empty_append, hstart', hend']
        rw [List.getElem_append_right (as := xs) (bs := ys) (i := j) (by omega)]
        exact hv₂ _ hj₂

/-- A typed element at full ABI alignment that ends below byte `2 ^ 63` is also a singleton
array. -/
theorem pts_arr_singleton {T : Type} [Enc T] {p : Ptr} {v : T} {h : Heap}
    (hp : pts p (Enc.align T) v h) (hend : p.off.toNat + Enc.size T < 2 ^ 63) : arr p [v] h := by
  obtain ⟨A, S, K, bs, hA, hs, hv, hb, hK⟩ := hp
  refine ⟨A, S, K, bs, hA, by simpa using hs, ?_, hb, hK, by rw [hs]; exact hend⟩
  intro i hi
  have he : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
  subst he
  simpa [← hs] using hv

/-- Reassemble a focused element and its original neighboring values in an actual memory. -/
theorem arr_reassemble {T : Type} [Enc T] {p : Ptr} {xs : List T} {k : Nat} {w : T}
    {m : Mem} {h hF : Heap} (hn : 0 < Enc.size T) (hk : k < xs.length)
    (hp : (arr p (xs.take k) ∗ (pts (p.add (Enc.size T * k)) (Enc.align T) w ∗
      arr (p.add (Enc.size T * (k + 1))) (xs.drop (k + 1)))) h)
    (hm : m.heap = h ∪ hF) : arr p (xs.set k w) h := by
  -- The element ends where the suffix begins, below byte `2 ^ 63`.
  have hsingle := sep_mono (fun _ hpre => hpre)
    (fun h' (htail : (pts (p.add (Enc.size T * k)) (Enc.align T) w ∗
        arr (p.add (Enc.size T * (k + 1))) (xs.drop (k + 1))) h') =>
      (by
        obtain ⟨h₁, h₂, hd, rfl, helem, hsuf⟩ := htail
        have hend : (p.add (Enc.size T * k)).off.toNat + Enc.size T < 2 ^ 63 := by
          obtain ⟨-, -, -, -, -, -, -, ⟨_, _, h0, _⟩, -⟩ := helem
          obtain ⟨-, -, -, bs, -, -, -, -, -, hend⟩ := hsuf
          simp only [Ptr.add] at h0 hend ⊢
          rw [Int.mul_add, Int.mul_one] at hend
          omega
        exact ⟨h₁, h₂, hd, rfl, pts_arr_singleton helem hend, hsuf⟩ :
        (arr (p.add (Enc.size T * k)) [w] ∗
          arr (p.add (Enc.size T * (k + 1))) (xs.drop (k + 1))) h')) hp
  obtain ⟨hpre, htail, hd, rfl, hpre', htail'⟩ := hsingle
  have hptr : (p.add (Enc.size T * k)).add (Enc.size T * ([w] : List T).length) =
      p.add (Enc.size T * (k + 1)) := by simp [Ptr.add, Int.mul_add, Int.add_assoc]
  rw [← hptr] at htail'
  have htailback : m.heap = htail ∪ (hpre ∪ hF) := by
    rw [hm, Heap.union_comm hd, Heap.union_assoc]
  have hjoined := arr_append_of_heap hn htail' htailback
  have hlen : (xs.take k).length = k := by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hwhole := arr_append_of_heap hn
    (show (arr p (xs.take k) ∗ arr (p.add (Enc.size T * (xs.take k).length))
      ([w] ++ xs.drop (k + 1))) (hpre ∪ htail) from
      by rw [hlen]; exact ⟨hpre, htail, hd, rfl, hpre', hjoined⟩) hm
  simpa only [List.set_eq_take_append_cons_drop, hk, ↓reduceIte, List.singleton_append] using hwhole

/-- Apply a full-alignment element update rule and recover whole-array ownership.
The postcondition reassembly uses the actual returned memory, not arbitrary heaps. -/
theorem Triple.arr_update {T : Type} [Enc T] {p : Ptr} {xs : List T} {k : Nat} {w : T}
    {c : MemM Unit} {R : Assn} (hn : 0 < Enc.size T) (hk : k < xs.length)
    (hs : Enc.align T ∣ Enc.size T)
    (rule : Triple (pts (p.add (Enc.size T * k)) (Enc.align T) xs[k]) c
      (fun _ => pts (p.add (Enc.size T * k)) (Enc.align T) w)) :
    Triple (arr p xs ∗ R) c (fun _ => arr p (xs.set k w) ∗ R) := by
  have focused := Triple.arr_focus_frame (R := R) hk (Nat.dvd_refl _) hs rule
  intro m hP hF hd hm hp hseq
  have hr := focused m hP hF hd hm hp hseq
  split at hr
  · trivial
  · exact hr
  · obtain ⟨hQ, hdQ, hmQ, hq, hseq'⟩ := hr
    have hq' : ((arr p (xs.take k) ∗
        (pts (p.add (Enc.size T * k)) (Enc.align T) w ∗
          arr (p.add (Enc.size T * (k + 1))) (xs.drop (k + 1)))) ∗ R) hQ := by
      sep_normalize at hq ⊢; exact hq
    obtain ⟨harray, hR, hdR, rfl, harr, hR'⟩ := hq'
    have hback := hmQ
    rw [Heap.union_assoc] at hback
    exact ⟨harray ∪ hR, hdQ, hmQ,
      ⟨harray, hR, hdR, rfl, arr_reassemble hn hk harr hback, hR'⟩, hseq'⟩

/-- Read an in-bounds scalar element while retaining whole-array ownership. -/
theorem Triple.arr_read {T : Type} [Enc T] {p : Ptr} {xs : List T} {i : BitVec 64}
    (hn : 0 < Enc.size T) (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length) :
    Triple (arr p xs) (Zig.load T (Enc.align T) (p.elem (Enc.size T) i))
      (fun v => ⌜v = xs[i.toNat]⌝ ∗ arr p xs) :=
  Triple.of_run fun _ hP _ hd hm hp hseq => by
    obtain ⟨m', hr, hm', hseq'⟩ := arr_load_run hp hm hn (Nat.dvd_refl _) hs hi hseq
    exact ⟨_, m', hP, hr, hd, hm', sep_lift.mpr ⟨rfl, hp⟩, hseq'⟩

/-- A scalar store through the reusable focus/reassembly interface. -/
theorem Triple.arr_store_reassemble {T : Type} [Enc T] [LawfulEnc T] {p : Ptr}
    {xs : List T} {i : BitVec 64} {R : Assn} (hn : 0 < Enc.size T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < xs.length) (w : T) :
    Triple (arr p xs ∗ R) (Zig.store (Enc.align T) (p.elem (Enc.size T) i) w)
      (fun _ => arr p (xs.set i.toNat w) ∗ R) := by
  intro m hP hF hd hm hp hst
  have hi63 : i.toNat < 2 ^ 63 := by
    obtain ⟨-, -, -, -, ⟨A, S, K, bs, -, hsz, -, -, -, hend⟩, -⟩ := hp
    exact arr_index_lt hend hn (by rw [hsz, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)
  have he : p.elem (Enc.size T) i = p.add (↑(Enc.size T) * ↑i.toNat) := by
    rw [Ptr.elem_eq_of_lt _ _ hi63]; push_cast; rfl
  rw [he]
  exact Triple.arr_update hn hi hs (Triple.store hn w) m hP hF hd hm hp hst

end Zig
