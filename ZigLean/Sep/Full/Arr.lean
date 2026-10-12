import ZigLean.Sep.Full.AutoRules
import ZigLean.Sep.Full.Strength

/-!
# Arrays in the full-state logic (`docs/sep-full-state.md`, Plan A library lane A1)

`arr p vs` (`ZigLean/Sep/Triple.lean`) owns the items `vs` at `p`. Here:

* **Assertion lemmas**: `arr_split` divides an array at a boundary, `arr_focus` exposes one
  item as `pts`, `arr_append_of_heap` and `arr_reassemble` join parts backed by one memory
  (disjoint parts alone need not agree on their block's labels).
* **Updates** (`EUpd`): `EUpd.arr_split`, `EUpd.arr_focus` (an implication), and
  `EUpd.arr_join`, `EUpd.arr_unfocus`, which read the block's labels from the memory (`Res.fix`):
  in the full logic the joined resource is held by the same memory with the same frame.
* **Step rules** (`@[fsym]`): `FTotalTriple.arr_load` and `FTotalTriple.arr_store` of an
  in-bounds item `p.elem (Enc.size T) i` at the type's alignment, keeping the whole array; the
  facts of an array (`facts_arr`) and its extent for pointer formation `&xs[i]` (`Live.arr`).
-/

namespace Zig

open Assn

/-! ## Assertion lemmas -/

section Ownership

variable {T : Type} [Enc T] {p : Ptr} {vs : List T} {h : Heap}

/-- Split an array at an explicit boundary, including the two endpoint boundaries. -/
theorem arr_split (hp : arr p vs h) {k : Nat} (hk : k ≤ vs.length)
    (hs : Enc.align T ∣ Enc.size T) :
    (arr p (vs.take k) ∗ arr (p.add (Enc.size T * k)) (vs.drop k)) h := by
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb, hK⟩ := hp
  have hbnd : Enc.size T * k ≤ bs.size := by
    rw [hsz]; exact Nat.mul_le_mul_left _ hk
  have hoff : (p.add (Enc.size T * k)).off.toNat = p.off.toNat + Enc.size T * k := by
    obtain ⟨_, _, h0, _⟩ := hb
    simp only [Ptr.add]; omega
  apply sep_mono (P := bytesAt p A S K (bs.extract 0 (Enc.size T * k)))
    (Q := bytesAt (p.add (Enc.size T * k)) A S K (bs.extract (Enc.size T * k) bs.size))
    ?_ ?_ (bytesAt_split hb hbnd)
  · intro hpre hbytes
    refine ⟨A, S, K, bs.extract 0 (Enc.size T * k), hA, ?_, ?_, hbytes, hK⟩
    · simp [List.length_take, Nat.min_eq_left hk, Nat.min_eq_left hbnd]
    · intro j hj
      have hjk : j < k := by simpa [List.length_take, Nat.min_eq_left hk] using hj
      have hjv : j < vs.length := by omega
      have hend : Enc.size T * j + Enc.size T ≤ Enc.size T * k := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hjk)
      simpa only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left hend,
        List.getElem_take] using hv j hjv
  · intro hsuf hbytes
    refine ⟨A, S, K, bs.extract (Enc.size T * k) bs.size, ?_, ?_, ?_, hbytes, hK⟩
    · rw [hoff]
      simpa only [Nat.add_assoc] using
        (item_aligned (T := T) (i := k) hA (Nat.dvd_refl _) hs)
    · simp only [Array.size_extract, Nat.min_self, List.length_drop, hsz]
      exact (Nat.mul_sub_left_distrib (Enc.size T) vs.length k).symm
    · intro j hj
      have hjv : k + j < vs.length := by simp only [List.length_drop] at hj; omega
      have hend : Enc.size T * k + (Enc.size T * j + Enc.size T) ≤ bs.size := by
        rw [hsz]
        simpa only [Nat.mul_succ, Nat.mul_add, Nat.add_assoc] using
          Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hjv)
      have hstart : Enc.size T * k + Enc.size T * j = Enc.size T * (k + j) :=
        (Nat.mul_add _ _ _).symm
      have hend' : Enc.size T * k + (Enc.size T * j + Enc.size T) =
          Enc.size T * (k + j) + Enc.size T := by rw [Nat.mul_add, Nat.add_assoc]
      rw [Array.extract_extract, Nat.min_eq_left hend, hstart, hend']
      simpa only [List.getElem_drop] using hv (k + j) hjv

/-- A singleton array provides the typed element assertion at any weaker alignment. -/
theorem arr_singleton_pts {v : T} (hp : arr p [v] h) {a : Nat}
    (ha : a ∣ Enc.align T) : pts p a v h := by
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb, hK⟩ := hp
  have hsize : bs.size = Enc.size T := by simpa using hsz
  refine ⟨A, S, K, bs, ?_, hsize, ?_, hb, hK⟩
  · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans ha (Nat.dvd_of_mod_eq_zero hA))
  · have hdecode := hv 0 (by simp)
    simpa [← hsize] using hdecode

/-- Expose one element; the unchanged prefix and suffix remain separately owned. -/
theorem arr_focus (hp : arr p vs h) {k a : Nat} (hk : k < vs.length)
    (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T) :
    (arr p (vs.take k) ∗
      (pts (p.add (Enc.size T * k)) a vs[k] ∗
        arr (p.add (Enc.size T * (k + 1))) (vs.drop (k + 1)))) h := by
  have hsplit := arr_split hp (Nat.le_of_lt hk) hs
  apply sep_mono (fun _ hpre => hpre) ?_ hsplit
  intro hsuf htail
  have hlen : 1 ≤ (vs.drop k).length := by simp only [List.length_drop]; omega
  have hsplit' := arr_split htail hlen hs
  have htake : (vs.drop k).take 1 = [vs[k]] := by
    calc
      (vs.drop k).take 1 = (vs[k] :: vs.drop (k + 1)).take 1 :=
        congrArg (List.take 1) (List.drop_eq_getElem_cons hk)
      _ = [vs[k]] := rfl
  have hdrop : (vs.drop k).drop 1 = vs.drop (k + 1) := by simp
  have hptr : (p.add (Enc.size T * k)).add (Enc.size T * 1) =
      p.add (Enc.size T * (k + 1)) := by
    simp [Ptr.add, Int.mul_add, Int.add_assoc]
  simp only [Int.natCast_one] at hsplit'
  rw [htake, hdrop, hptr] at hsplit'
  exact sep_mono (fun _ hsingle => arr_singleton_pts hsingle ha)
    (fun _ hrest => hrest) hsplit'

end Ownership

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
    obtain ⟨A₂, S₂, K₂, bs₂, _, hsz₂, hv₂, hb₂, _⟩ := hp₂
    have hb₂' := bytesAt_retag_of_heap hb₂ hm₂
      (by simpa [Ptr.add] using hpb) hblk
    have hb₁' : bytesAt p blk.addr blk.bytes.size blk.kind bs h₁ := by
      simpa only [haddr, hsize, hkind] using hb
    have hptr : p.add (Enc.size T * xs.length) = p.add bs.size := by
      rw [hsz]; simp [Int.natCast_mul]
    have hbytes : bytesAt p blk.addr blk.bytes.size blk.kind (bs ++ bs₂) (h₁ ∪ h₂) :=
      bytesAt_append ⟨h₁, h₂, hd, rfl, hb₁', hptr ▸ hb₂'⟩
    refine ⟨blk.addr, blk.bytes.size, blk.kind, bs ++ bs₂, haddr ▸ hA, ?_, ?_, hbytes,
      hkind ▸ hK⟩
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

/-- A typed element at full ABI alignment is also a singleton array. -/
theorem pts_arr_singleton {T : Type} [Enc T] {p : Ptr} {v : T} {h : Heap}
    (hp : pts p (Enc.align T) v h) : arr p [v] h := by
  obtain ⟨A, S, K, bs, hA, hs, hv, hb, hK⟩ := hp
  refine ⟨A, S, K, bs, hA, by simpa using hs, ?_, hb, hK⟩
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
  have hsingle := sep_mono (fun _ hpre => hpre)
    (fun _ htail => sep_mono (fun _ helem => pts_arr_singleton helem)
      (fun _ hsuf => hsuf) htail) hp
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

namespace Full

open FAssn

section Rules

variable {T : Type} [Enc T] {p : Ptr} {vs xs ys : List T}

theorem SizeFree.arr (p : Ptr) (vs : List T) : SizeFree (fun _ => none) (Zig.arr p vs) := by
  intro h h' hp hn hE hco
  obtain ⟨A, S, K, bs, hal, hsz, hdec, hb, hK⟩ := hp
  obtain ⟨A', S', K', ⟨hal', hK'⟩, hb'⟩ := SizeFree.bytesAt_ex (p := p) (bs := bs)
    (φ := fun A _ K => (A + p.off.toNat) % Enc.align T = 0 ∧ K ≠ .constGlobal)
    (fun A S K S' K' ⟨h1, h2⟩ hk => ⟨h1, fun e => h2 (by subst e; cases K <;> simp_all [BlockKind.norm])⟩)
    h h' ⟨A, S, K, ⟨hal, hK⟩, hb⟩ hn hE hco
  exact ⟨A', S', K', bs, hal', hsz, hdec, hb', hK'⟩

/-- **Reading the labels from the memory**: a resource of a size-free legacy assertion `up P`
is replaced by the same bytes with their block's actual size and kind (`Res.fix`), held by the
same memory with the same frame; `P` holds of them, and their heap with the frame's is the
memory's. -/
theorem up_fix {P : Assn} (hsf : SizeFree (fun _ => none) P) {m : Mem} {r rF : Res}
    (hh : Holds m r rF) (hp : up P r) :
    Holds m (r.fix m) rF ∧ up P (r.fix m) ∧
      m.heap = (r.fix m).heap.erase ∪ (rF.fix m).heap.erase :=
  ⟨(Holds.congrF hh.swap hh.swap.fix_sim rfl rfl).swap,
    ⟨upE_fix hsf (fun _ _ _ _ _ _ _ h => by cases h) hh (upE_none.mpr hp), hp.2.1, hp.2.2⟩,
    hh.fix.heap_exact hh.fix_exact hh.fix_exactF⟩

/-- An update from `up P` to `up P'` that may use the memory's heap. -/
theorem EUpd.up_of_heap {P P' : Assn} (hsf : SizeFree (fun _ => none) P)
    (h : ∀ (m : Mem) hP hF, m.heap = hP ∪ hF → P hP → P' hP) : EUpd (up P) (up P') :=
  fun _ _ _ hh hp _ =>
    have ⟨hh', hp', hm⟩ := up_fix hsf hh hp
    ⟨_, hh', h _ _ _ hm hp'.1, hp'.2⟩

/-- **Split** an array at a boundary. -/
theorem EUpd.arr_split {k : Nat} (hk : k ≤ vs.length) (hs : Enc.align T ∣ Enc.size T) :
    EUpd (up (Zig.arr p vs))
      (up (Zig.arr p (vs.take k)) ⋆ up (Zig.arr (p.add (Enc.size T * k)) (vs.drop k))) :=
  EUpd.of_imp fun _ hp => up_sep ⟨Zig.arr_split hp.1 hk hs, hp.2⟩

/-- **Join** two adjacent arrays (their labels are read from the memory). -/
theorem EUpd.arr_join (hn : 0 < Enc.size T) :
    EUpd (up (Zig.arr p xs) ⋆ up (Zig.arr (p.add (Enc.size T * xs.length)) ys))
      (up (Zig.arr p (xs ++ ys))) :=
  EUpd.trans (EUpd.of_imp fun _ => sep_up)
    (EUpd.up_of_heap (SizeFree.sep (SizeFree.arr _ _) (SizeFree.arr _ _))
      fun _ _ _ hm hp => arr_append_of_heap hn hp hm)

/-- **Focus** on item `k` of an array, as `pts` at the type's alignment. -/
theorem EUpd.arr_focus {k : Nat} (hk : k < vs.length) (hs : Enc.align T ∣ Enc.size T) :
    EUpd (up (Zig.arr p vs))
      (up (pts (p.add (Enc.size T * k)) (Enc.align T) vs[k]) ⋆
        (up (Zig.arr p (vs.take k)) ⋆ up (Zig.arr (p.add (Enc.size T * (k + 1))) (vs.drop (k + 1))))) :=
  EUpd.of_imp fun _ hp => by
    have h := sep_mono_right (fun _ h => up_sep h)
      (up_sep ⟨Zig.arr_focus hp.1 hk (Nat.dvd_refl _) hs, hp.2⟩)
    exact sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h))

/-- **Unfocus**: an item `w` at position `k` goes back into the array. -/
theorem EUpd.arr_unfocus {k : Nat} {w : T} (hn : 0 < Enc.size T) (hk : k < vs.length) :
    EUpd (up (pts (p.add (Enc.size T * k)) (Enc.align T) w) ⋆
        (up (Zig.arr p (vs.take k)) ⋆ up (Zig.arr (p.add (Enc.size T * (k + 1))) (vs.drop (k + 1)))))
      (up (Zig.arr p (vs.set k w))) :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_up (sep_mono_right (fun _ h => sep_up h)
      (sep_assoc (sep_mono_left (fun _ h => sep_comm h) (sep_assoc' h)))))
    (EUpd.up_of_heap (SizeFree.sep (SizeFree.arr _ _) (SizeFree.sep (SizeFree.pts _ _ _)
      (SizeFree.arr _ _))) fun _ _ _ hm hp => arr_reassemble hn hk hp hm)

/-- **Load** of an in-bounds item at the type's alignment; the array stays whole. -/
@[fsym] theorem FTotalTriple.arr_load {i : BitVec 64} (hn : 0 < Enc.size T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) :
    FTotalTriple (up (Zig.arr p vs)) (Zig.load T (Enc.align T) (p.elem (Enc.size T) i))
      (fun v => ⟪v = vs[i.toNat]⟫ ⋆ up (Zig.arr p vs)) :=
  FTotalTriple.eupd (EUpd.arr_focus hi hs) <|
    FTotalTriple.eupd_post (FTotalTriple.frame (FTotalTriple.load
      (q := p.add (Enc.size T * i.toNat)) (a := Enc.align T) (v := vs[i.toNat]) hn))
      fun _ m r rF hh hq hs' => by
        obtain ⟨hv, hq⟩ := sep_lift.mp (sep_assoc hq)
        obtain ⟨r', hh', hp'⟩ := EUpd.arr_unfocus (w := vs[i.toNat]) hn hi m r rF hh hq hs'
        exact ⟨r', hh', sep_lift.mpr ⟨hv, by simpa using hp'⟩⟩

/-- **Store** to an in-bounds item at the type's alignment; the array stays whole. -/
@[fsym] theorem FTotalTriple.arr_store [LawfulEnc T] {i : BitVec 64} (hn : 0 < Enc.size T)
    (hs : Enc.align T ∣ Enc.size T) (hi : i.toNat < vs.length) (w : T) :
    FTotalTriple (up (Zig.arr p vs)) (Zig.store (Enc.align T) (p.elem (Enc.size T) i) w)
      (fun _ => up (Zig.arr p (vs.set i.toNat w))) :=
  FTotalTriple.eupd (EUpd.arr_focus hi hs) <|
    FTotalTriple.eupd_post (FTotalTriple.frame (FTotalTriple.store hn w)) fun _ =>
      EUpd.arr_unfocus hn hi

/-- An array: the block of its pointer, a nonnegative offset. -/
@[fsym_facts] theorem Auto.facts_arr : Auto.AtomFacts (up (Zig.arr p vs)) ((∃ b, p.block = some b) ∧ 0 ≤ p.off) := by
  rintro r ⟨⟨-, -, -, -, -, -, -, ⟨b, hb, h0, -⟩, -⟩, -⟩; exact ⟨⟨b, hb⟩, h0⟩

/-- A nonempty array owns its bytes: its block is live and reaches one past its last item (for
pointer formation `&xs[i]`, `ptrProject_elem_of`, through `Reaches.of_live`). -/
@[fsym_provider] theorem Live.arr {b : BlockId} (hpb : p.block = some b) (hn : 0 < Enc.size T)
    (hl : 0 < vs.length) : Live b (p.off.toNat + Enc.size T * vs.length) (up (Zig.arr p vs)) :=
  Live.bytes hpb fun _ hp => by
    obtain ⟨A, S, K, bs, -, hs, -, hb, -⟩ := hp
    exact ⟨A, S, K, bs, by rw [hs]; exact Nat.mul_pos hn hl, by omega, hb⟩

end Rules

-- The bound of an item of a literal array (`[x, y, z].length`) and of an array after a store
-- (`(xs.set i w).length`) is arithmetic for `omega`.
attribute [fsym_arith] List.length_cons List.length_nil List.length_set

end Full
end Zig
