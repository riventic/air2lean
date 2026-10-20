import ZigLean.Sep.Full.Strength
import Extract

/-!
Strength log of the memory contracts of `tests/roadmap/vcs/Extract.lean`
(`ZigLean/Sep/Full/Strength.lean`; deleted with the legacy logic): each contract gives back the
legacy statement that it replaces, on every `Mem.FSeqPlain` memory (the memories a run reaches,
`Mem.init_fseq`, without a stack budget, which the legacy logic does not have), and total
instead of partial.

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) with
its definition unfolded, word for word, so the log does not use the legacy layer.
-/

namespace StrengthLog.Vcs

open Zig Assn VC VCExtract
open Zig.Full FAssn

example (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 8 old hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (Pointers.addTo p delta).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ pts p 8 (old + delta.setWidth 64) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (addTo_contract p delta old fits) fun _ => SizeFree.pts _ _ _

example (p q : Ptr) (x y : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → (pts p 4 x ∗ pts q 4 y) hP → m.Seq →
      m.FSeqPlain → ∃ v m' hQ, (Pointers.swap p q).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ (pts p 4 y ∗ pts q 4 x) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (((swap_contract p q x y).pre fun _ h => up_sep h).post
      fun _ _ h => sep_up h)
    fun _ => SizeFree.sep (SizeFree.pts _ _ _) (SizeFree.pts _ _ _)

example (p : Ptr) (old : BitVec 32) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts p 4 old hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, (Pointers.swap p p).run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ pts p 4 old hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (swapSelf_contract p old) fun _ => SizeFree.pts _ _ _

-- The legacy `ensures result heap` was `fun v h => result v ∧ heap v h`.
example (p q : Ptr) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → ⌜p.block = none ∧ q.block = none⌝ hP →
      m.Seq → m.FSeqPlain → ∃ v m' hQ, (Pointers.same p q).run m = pure (v, m') ∧
        Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ (v = decide (p.off = q.off) ∧ Assn.emp hQ) ∧
        m'.Seq :=
  FTotalTriple.toTotal_on (((same_contract p q).pre fun _ h =>
      ⟨h.1.1, up_emp.mp ⟨h.1.2, h.2⟩⟩).post fun _ _ h =>
        have e := up_emp.mpr (sep_lift.mp h).2
        ⟨⟨(sep_lift.mp h).1, e.1⟩, e.2⟩)
    fun _ => SizeFree.lift

end StrengthLog.Vcs
