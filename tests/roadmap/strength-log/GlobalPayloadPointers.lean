import ZigLean.Sep.Full.Strength
import Model

/-!
Strength log of `tests/roadmap/global-payload-pointers/Model.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): each migrated theorem gives back its legacy statement on every
`Mem.FSeqPlain` memory (no stack budget, which the legacy logic does not have), for a size-free
frame `R`.

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn GlobalPayloads

namespace StrengthLog.GlobalPayloadPointers

example {T : Type} [Enc T] (root : Ptr) (parent payload leaf a : Nat) (v : T) (R : Assn)
    (hR : SizeFree (fun _ => none) R) (hn : 0 < Enc.size T) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      (pts (resolved root parent payload leaf) a v ∗ R) hP → m.Seq → m.FSeqPlain →
      ∃ r m' hQ, (Zig.load T a (resolved root parent payload leaf)).run m = pure (r, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        ((⌜r = v⌝ ∗ pts (resolved root parent payload leaf) a v) ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((read_frame root parent payload leaf a v (up R) hn).pre
      fun _ h => up_sep h).post fun _ _ h =>
        sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)) hR

example {T : Type} [Enc T] [LawfulEnc T] (root : Ptr) (parent payload leaf a : Nat) (v w : T)
    (R : Assn) (hR : SizeFree (fun _ => none) R) (hn : 0 < Enc.size T) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF →
      (pts (resolved root parent payload leaf) a v ∗ R) hP → m.Seq → m.FSeqPlain →
      ∃ r m' hQ, (Zig.store a (resolved root parent payload leaf) w).run m = pure (r, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (pts (resolved root parent payload leaf) a w ∗ R) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((write_frame root parent payload leaf a v w (up R) hn).pre
      fun _ h => up_sep h).post fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (SizeFree.pts _ _ _) hR

end StrengthLog.GlobalPayloadPointers
