import ZigLean.Sep.Full.Strength
import Proofs.Pointers.Sep

/-!
Strength log of `Proofs/Pointers` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `swap_sep` and `swap_self_sep` were `Triple`s). No precondition delta.

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Pointers

namespace StrengthLog.ProofsPointers

/-- `swap_sep` (legacy: `Triple (pts p 4 x ∗ pts q 4 y) (swap p q) (fun _ => pts p 4 y ∗ pts q 4 x)`). -/
example (p q : Ptr) (x y : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (pts p 4 x ∗ pts q 4 y) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (swap p q).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (pts p 4 y ∗ pts q 4 x) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((swap_sep p q x y).pre fun _ h => up_sep h).post fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)

/-- `swap_self_sep` (legacy: `Triple (pts p 4 x) (swap p p) (fun _ => pts p 4 x)`). -/
example (p : Ptr) (x : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 4 x hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (swap p p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ pts p 4 x hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (swap_self_sep p x) fun _ => SizeFree.pts _ _ _

end StrengthLog.ProofsPointers
