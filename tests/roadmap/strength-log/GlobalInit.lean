import ZigLean.Sep.Full.Strength
import GlobalInit.Proofs

/-!
Strength log of `tests/roadmap/global-init/GlobalInit/Proofs.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): the migrated triple gives back its legacy statement on every
`Mem.FSeqPlain` memory (no stack budget, which the legacy logic does not have), total instead of
partial. `bump_from_start` keeps its statement word for word.

The statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn GlobalInit GlobalInitClients

namespace StrengthLog.GlobalInit

example (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts counter 4 x hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, bump.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = x + 1⌝ ∗ pts counter 4 (x + 1)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((bump_spec x hx).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

end StrengthLog.GlobalInit
