import ZigLean.Sep.Full.Strength
import Model

/-!
Strength log of `tests/roadmap/global-payload-pointers/Model.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): each migrated theorem gives back its legacy statement on every
`Mem.FSeqPlain` memory (no stack budget, which the legacy logic does not have), for a size-free
frame `R`.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn GlobalPayloads

namespace StrengthLog.GlobalPayloadPointers

example {T : Type} [Enc T] (root : Ptr) (parent payload leaf a : Nat) (v : T) (R : Assn)
    (hR : SizeFree (fun _ => none) R) (hn : 0 < Enc.size T) :
    TotalTripleIn Mem.FSeqPlain (pts (resolved root parent payload leaf) a v ∗ R)
      (Zig.load T a (resolved root parent payload leaf))
      (fun r => (⌜r = v⌝ ∗ pts (resolved root parent payload leaf) a v) ∗ R) :=
  FTotalTriple.toTotal_on (((read_frame root parent payload leaf a v (up R) hn).pre
      fun _ h => up_sep h).post fun _ _ h =>
        sep_up (sep_mono_left (fun _ h => up_lift.mpr (sep_lift.mp h)) h))
    fun _ => SizeFree.sep (SizeFree.sep SizeFree.lift (SizeFree.pts _ _ _)) hR

example {T : Type} [Enc T] [LawfulEnc T] (root : Ptr) (parent payload leaf a : Nat) (v w : T)
    (R : Assn) (hR : SizeFree (fun _ => none) R) (hn : 0 < Enc.size T) :
    TotalTripleIn Mem.FSeqPlain (pts (resolved root parent payload leaf) a v ∗ R)
      (Zig.store a (resolved root parent payload leaf) w)
      (fun _ => pts (resolved root parent payload leaf) a w ∗ R) :=
  FTotalTriple.toTotal_on (((write_frame root parent payload leaf a v w (up R) hn).pre
      fun _ h => up_sep h).post fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (SizeFree.pts _ _ _) hR

end StrengthLog.GlobalPayloadPointers
