import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Total
import TokenizerProof

/-!
Strength log of `tests/roadmap/dispatch-templates/TokenizerProof.lean`
(`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic): `countTokens_total` gives back
the legacy total triple on every `Mem.FSeqPlain` memory (`FTotalTriple.toTotal_on`).
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Tok Tok.Proof

namespace StrengthLog.DispatchTemplates

/-- `countTokens_total` as the legacy total triple on every `Mem.FSeqPlain` memory (no stack
budget, `FTotalTriple.toTotal_on`). -/
example (p : Ptr) (xs : List (BitVec 8)) (hlen : xs.length < 2 ^ 64) :
    TotalTripleIn Mem.FSeqPlain (arr p xs) (countTokens p (BitVec.ofNat 64 xs.length))
      (fun r => ⌜r.toNat = tokens .start xs % 2 ^ 32⌝ ∗ arr p xs) :=
  FTotalTriple.toTotal_on ((countTokens_total p xs hlen).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.arr _ _)

end StrengthLog.DispatchTemplates
