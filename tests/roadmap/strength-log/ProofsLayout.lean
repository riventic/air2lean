import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Total
import Proofs.Layout.Mem

/-!
Strength log of `Proofs/Layout` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `numInt_spec`, `setNum_spec` and `bump_ok_spec` were `Triple`s). No
precondition delta.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Layout

namespace StrengthLog.ProofsLayout

/-- `numInt_spec` (legacy: `Triple (pts p 4 (Num.int x)) (numInt p) (fun r => ⌜r = x⌝ ∗ pts p 4 (Num.int x))`). -/
example (p : Ptr) (x : BitVec 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 4 (Num.int x)) (numInt p) (fun r => ⌜r = x⌝ ∗ pts p 4 (Num.int x)) :=
  FTotalTriple.toTotal_on ((numInt_spec p x).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

/-- `setNum_spec` (legacy: `Triple (pts p 4 n) (setNum p true x) (fun _ => pts p 4 (Num.int x))`). -/
example (p : Ptr) (n : Num) (x : BitVec 32) :
    TotalTripleIn Mem.FSeqPlain (pts p 4 n) (setNum p true x) (fun _ => pts p 4 (Num.int x)) :=
  FTotalTriple.toTotal_on (setNum_spec p n x) fun _ => SizeFree.pts _ _ _

/-- `bump_ok_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (p : Ptr) (x : BitVec 8) :
    TotalTripleIn Mem.FSeqPlain (pts p 2 (Except.ok x : Except ErrName (BitVec 8))) (bump p)
      (fun _ => pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8))) :=
  FTotalTriple.toTotal_on (bump_ok_spec p x) fun _ => SizeFree.pts _ _ _

end StrengthLog.ProofsLayout
