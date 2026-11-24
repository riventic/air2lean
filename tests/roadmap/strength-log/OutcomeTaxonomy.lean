import ZigLean.Sep.Full.Strength
import Outcomes.Taxonomy

/-!
Strength log of `tests/roadmap/outcome-taxonomy/Outcomes/Taxonomy.lean` (`ZigLean/Sep/Full/Strength.lean`;
deleted with the legacy logic): each migrated theorem gives back its legacy statement on every
`Mem.FSeqPlain` memory (no stack budget, which the legacy logic does not have), for a size-free
precondition. The legacy failure statements did not elaborate once a partial triple admits
`.stackOverflow` (STK-01); they carry `e ≠ .stackOverflow` here.

Each statement is the legacy `TotalTripleIn Mem.FSeqPlain P c Q` (`ZigLean/Sep/Total.lean`) or
`Triple P c Q` (`ZigLean/Sep/Triple.lean`) with its definition unfolded, word for word, so the log
does not use the legacy layer.
-/

open Zig Zig.Full Zig.Full.FAssn Zig.Assn OutcomeTaxonomy

namespace StrengthLog.OutcomeTaxonomy

example (P : Assn) (hP : SizeFree (fun _ => none) P) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → m.FSeqPlain →
      ∃ v m' hQ, errorReturn.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧
        (v = (.error "Timeout" : Except ErrName Nat) ∧ P hQ) ∧ m'.Seq :=
  FTotalTriple.toTotal_on ((errorReturn_triple (up P)).post fun _ _ h =>
      have ⟨hr, hp, hk⟩ := sep_lift.mp h; ⟨⟨hr, hp⟩, hk⟩)
    fun _ _ _ hq hn hpin hsz => ⟨hq.1, hP _ _ hq.2 hn hpin hsz⟩

-- No legacy triple lifts to a full-state one any more (the bridge is deleted), so the legacy
-- failure statement (`¬ Triple P (fail e) Q`, unfolded) is read off the legacy definition at the
-- same admissible memory. Its full-state counterpart is `fail_not_triple`.
example (P : Assn) (e : Error) (he : e ≠ .stackOverflow) (_hP : SizeFree (fun _ => none) P)
    (Q : Nat → Assn) (m : Mem) (hP' hF : Heap) (hd : Heap.Disjoint hP' hF)
    (hm : m.heap = hP' ∪ hF) (hp : P hP') (hs : m.FSeq) :
    ¬ ∀ (m : Mem) hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq →
      match ((fail e).run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq :=
  fun ht => he (ht m hP' hF hd hm hp hs.1)

example (P : Assn) :
    ∀ (m : Mem) hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → m.FSeqPlain →
      match (diverge.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (_, m')) => ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ False ∧ m'.Seq :=
  FTriple.toTriple_on (Q := fun _ _ => False) ((diverge_triple (up P)).post fun _ _ h => h.elim)
    fun _ _ _ h => h.elim

end StrengthLog.OutcomeTaxonomy
