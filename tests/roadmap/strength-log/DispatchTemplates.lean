import ZigLean.Sep.Full.Strength
import TokenizerProof

/-!
Strength log of `tests/roadmap/dispatch-templates/TokenizerProof.lean`
(`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic): `countTokens_total` gives back
the legacy total triple on every `Mem.FSeqPlain` memory (`FTotalTriple.toTotal_on`).

The statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Tok Tok.Proof

namespace StrengthLog.DispatchTemplates

/-- `countTokens_total` as the legacy total triple on every `Mem.FSeqPlain` memory (no stack
budget, `FTotalTriple.toTotal_on`). -/
example (p : Ptr) (xs : List (BitVec 8)) (hlen : xs.length < 2 ^ 64) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → arr p xs hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (countTokens p (BitVec.ofNat 64 xs.length)).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (⌜v.toNat = tokens .start xs % 2 ^ 32⌝ ∗ arr p xs) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((countTokens_total p xs hlen).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.arr _ _)

end StrengthLog.DispatchTemplates
