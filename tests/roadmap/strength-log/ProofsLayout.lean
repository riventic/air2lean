import ZigLean.Sep.Full.Strength
import Proofs.Layout.Mem

/-!
Strength log of `Proofs/Layout` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `numInt_spec`, `setNum_spec` and `bump_ok_spec` were `Triple`s). No
precondition delta.

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Layout

namespace StrengthLog.ProofsLayout

/-- `numInt_spec` (legacy: `Triple (pts p 4 (Num.int x)) (numInt p) (fun r => ⌜r = x⌝ ∗ pts p 4 (Num.int x))`). -/
example (p : Ptr) (x : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 4 (Num.int x) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (numInt p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = x⌝ ∗ pts p 4 (Num.int x)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((numInt_spec p x).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

/-- `setNum_spec` (legacy: `Triple (pts p 4 n) (setNum p true x) (fun _ => pts p 4 (Num.int x))`). -/
example (p : Ptr) (n : Num) (x : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 4 n hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (setNum p true x).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ pts p 4 (Num.int x) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (setNum_spec p n x) fun _ => SizeFree.pts _ _ _

/-- `bump_ok_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (p : Ptr) (x : BitVec 8) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      pts p 2 (Except.ok x : Except ErrName (BitVec 8)) hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (bump p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        pts p 2 (Except.ok (x + 1) : Except ErrName (BitVec 8)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (bump_ok_spec p x) fun _ => SizeFree.pts _ _ _

end StrengthLog.ProofsLayout
