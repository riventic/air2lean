import ZigLean.Sep.Automation
import ZigLean.Sep.Full.Arr

/-!
# Explicit array ownership framing

`arr_split` divides ownership at a caller-supplied boundary. `arr_focus` exposes one
in-bounds element as `pts`, retaining its prefix and suffix (both assertion lemmas live in
`ZigLean/Sep/Full/Arr.lean`, with the full-state array rules). `Triple.arr_focus_frame`
lifts a supplied element rule through that view and an independent frame. No search
for array indices or arithmetic facts is performed; clients supply the bounds and
ABI divisibility proofs. This optional module is a bounded contribution to P01.
-/

namespace Zig

open Assn

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
  exact Triple.arr_focus_frame hi ha hs (Triple.store hn w)

end Zig
