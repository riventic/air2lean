import ZigLean.Sep.Full.Strength
import Proofs.Lists.Linked

/-!
Strength log of `Proofs/Lists` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back a legacy total triple on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have).

The list is stated over the nodes' fields (`Lists.Linked.node`, with `X := fun _ => emp` here).
Precondition delta to the legacy `Lists.list` (`Proofs/Lists/Sep.lean`): its node owned the whole
16-byte block of the `std` heap model and pinned the block's size and kind (`.heap`) in every
byte. The full-state cells do not pin the block's size (size-free cells, block extents), and the
`std` heap model is retired (`docs/alloc-spec.md`, §Retired claims); the rest of a node's
allocation is the node's `X` (the allocator's grant), so the full-state statement holds for every
owner of the nodes, and the legacy statement below is the one over the fields.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Lists.Open Lists.Linked

namespace StrengthLog.ProofsLists

/-- The list of fields as a legacy assertion. -/
def plist : Option Ptr → List (BitVec 32) → Assn
  | hd, [] => ⌜hd = none⌝ ∗ Assn.emp
  | hd, v :: vs => Assn.ex fun p => Assn.ex fun q =>
      ⌜hd = some p⌝ ∗ ((pts p 8 q ∗ (pts (p.add 8) 4 v ∗ Assn.emp)) ∗ plist q vs)

theorem up_plist : ∀ (hd : Option Ptr) (xs : List (BitVec 32)) (r : Res),
    up (plist hd xs) r ↔ list (fun _ => emp) hd xs r
  | _, [], _ => by simp only [plist, list, lseg]; rw [up_lift, up_emp]; rfl
  | hd, v :: vs, r => by
    simp only [plist, list, lseg, up_ex, FAssn.ex]
    refine exists_congr fun p => exists_congr fun q => ?_
    rw [up_lift, Full.sep_lift]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · refine sep_mono (fun _ h => ?_) (fun r' h => (up_plist q vs r').mp h) (up_sep h)
      exact sep_mono_right (fun _ h => sep_mono_right (fun _ h => up_emp.mp h) (up_sep h)) (up_sep h)
    · refine sep_up (sep_mono (fun _ h => ?_) (fun r' h => (up_plist q vs r').mpr h) h)
      exact sep_up (sep_mono_right (fun _ h => sep_up (sep_mono_right (fun _ h => up_emp.mpr h) h)) h)

theorem plist_sizeFree : ∀ (hd : Option Ptr) (xs : List (BitVec 32)),
    SizeFree (fun _ => none) (plist hd xs)
  | _, [] => SizeFree.sep SizeFree.lift SizeFree.emp
  | _, _ :: vs => SizeFree.ex fun _ => SizeFree.ex fun q => SizeFree.sep SizeFree.lift
      (SizeFree.sep (SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.sep (SizeFree.pts _ _ _) SizeFree.emp))
        (plist_sizeFree q vs))

/-- `Lists.reverse_total` (legacy, over the fields). -/
example (hd : Option Ptr) (xs : List (BitVec 32)) :
    TotalTripleIn Mem.FSeqPlain (plist hd xs) (reverse hd) (fun r => plist r xs.reverse) :=
  FTotalTriple.toTotal_on
    (((reverse_total hd xs).pre fun r h => (up_plist hd xs r).mp h).post fun r _ h =>
      (up_plist r xs.reverse _).mpr h)
    fun r => plist_sizeFree r xs.reverse

/-- `Lists.sum_total` (legacy, `Proofs/Lists/Bounded.lean`, over the fields). -/
example (hd : Option Ptr) (xs : List (BitVec 32)) (htot : (xs.map BitVec.toNat).sum < 2 ^ 64) :
    TotalTripleIn Mem.FSeqPlain (plist hd xs) (sum hd)
      (fun r => ⌜r = BitVec.ofNat 64 (xs.map BitVec.toNat).sum⌝ ∗ plist hd xs) :=
  FTotalTriple.toTotal_on
    (((sum_total hd xs htot).pre fun r h => (up_plist hd xs r).mp h).post fun _ r h => by
      obtain ⟨hv, h⟩ := Full.sep_lift.mp h
      exact up_lift.mpr ⟨hv, (up_plist hd xs r).mpr h⟩)
    fun _ => SizeFree.sep SizeFree.lift (plist_sizeFree hd xs)

end StrengthLog.ProofsLists
