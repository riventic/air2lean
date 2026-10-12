import ZigLean.Sep.Full.Strength

/-!
# Strength harness (Plan A, D1a)

Every theorem migrated from the legacy logic to the full-state logic gets an entry here: its
full-state statement, through `FTriple.toTriple_on` / `FTotalTriple.toTotal_on`, gives the legacy
statement on every `Mem.FSeq` memory (the memories a run reaches: `Mem.init_fseq`). A legacy
statement is deleted only after its entry checks. The log is the `#print axioms` output of
`check.sh`.
-/

namespace OneLogic.Strength

open Zig Zig.Full Zig.Full.FAssn Zig.Assn

/-- The library's typed load. -/
theorem load {T : Type} [Enc T] {a : Nat} {q : Ptr} {v : T} (hn : 0 < Enc.size T) :
    TotalTripleIn Mem.FSeq (pts q a v) (Zig.load T a q) (fun x => ⌜x = v⌝ ∗ pts q a v) :=
  FTotalTriple.toTotal_on ((FTotalTriple.load hn).post fun _ _ h => up_lift.mpr (sep_lift.mp h))
    fun _ => SizeFree.sep SizeFree.lift (SizeFree.pts q a v)

/-- The library's typed store. -/
theorem store {T : Type} [Enc T] [LawfulEnc T] {a : Nat} {q : Ptr} {v : T} (hn : 0 < Enc.size T)
    (w : T) :
    TotalTripleIn Mem.FSeq (pts q a v) (Zig.store a q w) (fun _ => pts q a w) :=
  FTotalTriple.toTotal_on (FTotalTriple.store hn w) fun _ => SizeFree.pts q a w

end OneLogic.Strength
