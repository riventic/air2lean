import ZigLean.Sep.Array

/-!
# Memory-backed array reassembly

Disjoint assertions alone need not agree on a block's address, size, or kind.
`arr_append_of_heap` and `arr_reassemble` (`ZigLean/Sep/Full/Arr.lean`) therefore require an
actual-memory backing equality. The triple helper obtains that equality from the element rule's
returned memory. Selection stays explicit; this is a scalar array interface,
not a general range search or a source-to-model correspondence theorem.
-/

namespace Zig

open Assn

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
      (fun _ => arr p (xs.set i.toNat w) ∗ R) :=
  Triple.arr_update hn hi hs (Triple.store hn w)

end Zig
