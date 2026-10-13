import ZigLean.Sep.Full.Strength
import GlobalInit.Proofs

/-!
Strength log of `tests/roadmap/global-init/GlobalInit/Proofs.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): the migrated triple gives back its legacy statement on every
`Mem.FSeq` memory, total instead of partial. `bump_from_start` keeps its statement word for word.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn GlobalInit GlobalInitClients

namespace StrengthLog.GlobalInit

example (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    TotalTripleIn Mem.FSeq (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1)) :=
  FTotalTriple.toTotal_on ((bump_spec x hx).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

end StrengthLog.GlobalInit
