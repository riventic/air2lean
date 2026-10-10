import ZigLean.Sep.Automation

/-!
# Explicit array ownership framing

`arr_split` divides ownership at a caller-supplied boundary. `arr_focus` exposes one
in-bounds element as `pts`, retaining its prefix and suffix. `Triple.arr_focus_frame`
lifts a supplied element rule through that view and an independent frame. No search
for array indices or arithmetic facts is performed; clients supply the bounds and
ABI divisibility proofs. This optional module is a bounded contribution to P01.
-/

namespace Zig

open Assn

section Ownership

variable {T : Type} [Enc T] {p : Ptr} {vs : List T} {h : Heap}

/-- Split an array at an explicit boundary, including the two endpoint boundaries. -/
theorem arr_split (hp : arr p vs h) {k : Nat} (hk : k ≤ vs.length)
    (hs : Enc.align T ∣ Enc.size T) :
    (arr p (vs.take k) ∗ arr (p.add (Enc.size T * k)) (vs.drop k)) h := by
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb, hK, hend⟩ := hp
  have hbnd : Enc.size T * k ≤ bs.size := by
    rw [hsz]; exact Nat.mul_le_mul_left _ hk
  have hoff : (p.add (Enc.size T * k)).off.toNat = p.off.toNat + Enc.size T * k := by
    obtain ⟨_, _, h0, _⟩ := hb
    simp only [Ptr.add]; omega
  apply sep_mono (P := bytesAt p A S K (bs.extract 0 (Enc.size T * k)))
    (Q := bytesAt (p.add (Enc.size T * k)) A S K (bs.extract (Enc.size T * k) bs.size))
    ?_ ?_ (bytesAt_split hb hbnd)
  · intro hpre hbytes
    refine ⟨A, S, K, bs.extract 0 (Enc.size T * k), hA, ?_, ?_, hbytes, hK,
      by simp only [Array.size_extract]; omega⟩
    · simp [List.length_take, Nat.min_eq_left hk, Nat.min_eq_left hbnd]
    · intro j hj
      have hjk : j < k := by simpa [List.length_take, Nat.min_eq_left hk] using hj
      have hjv : j < vs.length := by omega
      have hend : Enc.size T * j + Enc.size T ≤ Enc.size T * k := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hjk)
      simpa only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left hend,
        List.getElem_take] using hv j hjv
  · intro hsuf hbytes
    refine ⟨A, S, K, bs.extract (Enc.size T * k) bs.size, ?_, ?_, ?_, hbytes, hK,
      by rw [hoff]; simp only [Array.size_extract]; omega⟩
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
  obtain ⟨A, S, K, bs, hA, hsz, hv, hb, hK, -⟩ := hp
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

/-- Lift a caller-supplied element rule through an explicit array view and frame.
The postcondition retains both neighboring ranges and `R`; it cannot drop them. -/
theorem Triple.arr_focus_frame {T α : Type} [Enc T] {p : Ptr} {vs : List T}
    {k a : Nat} {R : Assn} {c : MemM α} {Q : α → Assn}
    (hk : k < vs.length) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (rule : Triple (pts (p.add (Enc.size T * k)) a vs[k]) c Q) :
    Triple (arr p vs ∗ R) c
      (fun v => (Q v ∗ (arr p (vs.take k) ∗
        arr (p.add (Enc.size T * (k + 1))) (vs.drop (k + 1)))) ∗ R) := by
  refine Triple.conseq (Triple.frame (R := R)
    (Triple.frame (R := arr p (vs.take k) ∗
      arr (p.add (Enc.size T * (k + 1))) (vs.drop (k + 1))) rule)) ?_ ?_
  · intro h hp
    have hfocus := sep_mono (fun _ harray => arr_focus harray hk ha hs)
      (fun _ hrest => hrest) hp
    sep_normalize at hfocus ⊢
    exact hfocus
  · intro v h hp; exact hp

/-- A concrete store updates the selected element, retaining its neighbors and frame. -/
theorem Triple.arr_store_focus {T : Type} [Enc T] [LawfulEnc T] {p : Ptr}
    {vs : List T} {i : BitVec 64} {a : Nat} {R : Assn}
    (hn : 0 < Enc.size T) (ha : a ∣ Enc.align T) (hs : Enc.align T ∣ Enc.size T)
    (hi : i.toNat < vs.length) (w : T) :
    Triple (arr p vs ∗ R) (Zig.store a (p.elem (Enc.size T) i) w)
      (fun _ => (pts (p.elem (Enc.size T) i) a w ∗
        (arr p (vs.take i.toNat) ∗
          arr (p.add (Enc.size T * (i.toNat + 1))) (vs.drop (i.toNat + 1)))) ∗ R) := by
  intro m hP hF hd hm hp hst
  rw [arr_sep_elem_eq hp hn hi]
  exact Triple.arr_focus_frame hi ha hs (Triple.store hn w) m hP hF hd hm hp hst

end Zig
