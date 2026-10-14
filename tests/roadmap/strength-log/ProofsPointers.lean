import ZigLean.Sep.Full.Strength
import Proofs.Pointers.Sep

/-!
Strength log of `Proofs/Pointers` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `swap_sep` and `swap_self_sep` were `Triple`s). No precondition delta.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Pointers

namespace StrengthLog.ProofsPointers

/-- `swap_sep` (legacy: `Triple (pts p 4 x ∗ pts q 4 y) (swap p q) (fun _ => pts p 4 y ∗ pts q 4 x)`). -/
example (p q : Ptr) (x y : BitVec 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 4 x ∗ pts q 4 y) (swap p q) (fun _ => pts p 4 y ∗ pts q 4 x) :=
  FTotalTriple.toTotal_on (((swap_sep p q x y).pre fun _ h => up_sep h).post fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)

/-- `swap_self_sep` (legacy: `Triple (pts p 4 x) (swap p p) (fun _ => pts p 4 x)`). -/
example (p : Ptr) (x : BitVec 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 4 x) (swap p p) (fun _ => pts p 4 x) :=
  FTotalTriple.toTotal_on (swap_self_sep p x) fun _ => SizeFree.pts _ _ _

end StrengthLog.ProofsPointers
