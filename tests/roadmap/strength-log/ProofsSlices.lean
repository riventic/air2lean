import ZigLean.Sep.Full.Strength
import ZigLean.Sep.Total
import Proofs.Slices.Sep

/-!
Strength log of `Proofs/Slices` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `bump_spec`, `copyWithin_spec`, `fill_sep` and `reverse_spec` were
`Triple`s). No precondition delta. `counter_init` is unchanged (a statement about `mem0`).
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Slices

namespace StrengthLog.ProofsSlices

/-- `bump_spec` (legacy: `Triple (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1))`). -/
example (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    TotalTripleIn Mem.FSeqPlain (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1)) :=
  FTotalTriple.toTotal_on ((bump_spec x hx).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

/-- `copyWithin_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 32)) (d s n : BitVec 64)
    (hlen : sl.len.toNat = vs.length) (hd : d.toNat + n.toNat ≤ vs.length)
    (hs : s.toNat + n.toNat ≤ vs.length) :
    TotalTripleIn Mem.FSeqPlain (arr sl.ptr vs) (copyWithin sl d s n)
      (fun _ => arr sl.ptr (copyItems vs d.toNat s.toNat n.toNat)) :=
  FTotalTriple.toTotal_on (copyWithin_spec sl vs d s n hlen hd hs) fun _ => SizeFree.arr _ _

/-- `fill_sep` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 8)) (v : BitVec 8) (hlen : sl.len.toNat = vs.length) :
    TotalTripleIn Mem.FSeqPlain (arr sl.ptr vs) (fill sl v) (fun _ => arr sl.ptr (List.replicate vs.length v)) :=
  FTotalTriple.toTotal_on (fill_sep sl vs v hlen) fun _ => SizeFree.arr _ _

/-- `reverse_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    TotalTripleIn Mem.FSeqPlain (arr sl.ptr vs) (reverse sl) (fun _ => arr sl.ptr vs.reverse) :=
  FTotalTriple.toTotal_on (reverse_spec sl vs hlen) fun _ => SizeFree.arr _ _

end StrengthLog.ProofsSlices
