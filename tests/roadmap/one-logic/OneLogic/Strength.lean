import ZigLean.Sep.Full.Strength

/-!
# Strength harness (Plan A, D1a)

Every theorem migrated from the legacy logic to the full-state logic gets an entry here: its
full-state statement, through `FTriple.toTriple_on` / `FTotalTriple.toTotal_on`, gives the legacy
statement on every `Mem.FSeqPlain` memory (the memories a run reaches, `Mem.init_fseq`, without
a stack budget, which the legacy logic does not have). A legacy
statement is deleted only after its entry checks. The log is the `#print axioms` output of
`check.sh`.
-/

namespace OneLogic.Strength

open Zig Zig.Full Zig.Full.FAssn Zig.Assn

/-- The library's typed load: the legacy total triple's statement on every `Mem.FSeqPlain` memory. -/
theorem load {T : Type} [Enc T] {a : Nat} {q : Ptr} {v : T} (hn : 0 < Enc.size T) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts q a v hP → m.Seq → m.FSeqPlain →
      ∃ x m' hQ, (Zig.load T a q).run m = pure (x, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ (⌜x = v⌝ ∗ pts q a v) hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((FTotalTriple.load hn).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts q a v)

/-- The library's typed store: the legacy total triple's statement on every `Mem.FSeqPlain` memory. -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {q : Ptr} {v : T} (hn : 0 < Enc.size T)
    (w : T) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → pts q a v hP → m.Seq → m.FSeqPlain →
      ∃ x m' hQ, (Zig.store a q w).run m = pure (x, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ pts q a w hQ ∧ m'.Seq :=
  FTotalTriple.toTotal_on (FTotalTriple.store hn w) fun _ => SizeFree.pts q a w

end OneLogic.Strength
