import ZigLean.Sep.Full.Strength
import Proofs.Slices.Sep

/-!
Strength log of `Proofs/Slices` (`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic):
each migrated triple gives back its legacy statement on every `Mem.FSeqPlain` memory (no stack
budget, which the legacy logic does not have), total instead of partial (the legacy `bump_spec`, `copyWithin_spec`, `fill_sep` and `reverse_spec` were
`Triple`s). No precondition delta. `counter_init` is unchanged (a statement about `mem0`).

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn Slices

namespace StrengthLog.ProofsSlices

/-- `bump_spec` (legacy: `Triple (pts counter 4 x) bump (fun r => ⌜r = x + 1⌝ ∗ pts counter 4 (x + 1))`). -/
example (x : BitVec 32) (hx : x.toNat + 1 < 2 ^ 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts counter 4 x hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, bump.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜v = x + 1⌝ ∗ pts counter 4 (x + 1)) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((bump_spec x hx).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)

/-- `copyWithin_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 32)) (d s n : BitVec 64)
    (hlen : sl.len.toNat = vs.length) (hd : d.toNat + n.toNat ≤ vs.length)
    (hs : s.toNat + n.toNat ≤ vs.length) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → arr sl.ptr vs hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (copyWithin sl d s n).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        arr sl.ptr (copyItems vs d.toNat s.toNat n.toNat) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (copyWithin_spec sl vs d s n hlen hd hs) fun _ => SizeFree.arr _ _

/-- `fill_sep` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 8)) (v : BitVec 8) (hlen : sl.len.toNat = vs.length) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → arr sl.ptr vs hP → m.Seq →
      m.FSeqPlain → ∃ r m' hQ, (fill sl v).run m = pure (r, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ arr sl.ptr (List.replicate vs.length v) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (fill_sep sl vs v hlen) fun _ => SizeFree.arr _ _

/-- `reverse_spec` (legacy: the same pre- and postcondition as a `Triple`). -/
example (sl : Slice) (vs : List (BitVec 32)) (hlen : sl.len.toNat = vs.length) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → arr sl.ptr vs hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (reverse sl).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ arr sl.ptr vs.reverse hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (reverse_spec sl vs hlen) fun _ => SizeFree.arr _ _

end StrengthLog.ProofsSlices
