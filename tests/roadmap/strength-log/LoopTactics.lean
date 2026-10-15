import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Total
import Proof

/-!
Strength log of `tests/roadmap/loop-tactics/nested/Proof.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): `pairs_total` gives back the legacy total triple on every
`Mem.FSeqPlain` memory (`FTotalTriple.toTotal_on`).
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Nested Nested.Proof

namespace StrengthLog.LoopTactics

/-- The legacy statement (`TotalTriple (pts p 8 v) (pairs p n) (fun _ => pts p 8 …)`) on every
`Mem.FSeqPlain` memory (no stack budget), from `pairs_total`. -/
example (p : Ptr) (n : BitVec 32) (v : BitVec 64)
    (hfit : v.toNat + cnt n.toNat < 2 ^ 64) :
    TotalTripleIn Mem.FSeqPlain (pts p 8 v) (pairs p n)
      (fun _ => pts p 8 (BitVec.ofNat 64 (v.toNat + cnt n.toNat))) :=
  FTotalTriple.toTotal_on (pairs_total p n v hfit) fun _ => SizeFree.pts _ _ _

end StrengthLog.LoopTactics
