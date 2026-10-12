import ZigLean.Sep.Total
import ZigLean.Sep.Full.Witness

/-!
# Admissible memories for claim witnesses

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) ask for an admissible
input of a triple: a memory `m` with `m.Seq` whose heap splits into the precondition's part and
a disjoint frame. The default memory (no blocks, one thread, empty footprint) with two empty
heaps is one, for any precondition that holds of the empty heap (`emp`, pure assertions).
`Witness.mem1 bs` (`ZigLean/Mem/Witness.lean`) is one for a precondition that owns one block of
bytes (`mem1_bytesAt`, `mem1_pts`, `ZigLean/Sep/Full/Witness.lean`), with the whole heap as the
precondition's part and an empty frame.

`Witness.Admit P` is the premise telescope of a triple with precondition `P` after its
arguments, and `Witness.Live P c` that telescope followed by a successful run of `c`: the
statements `T.nonvacuous` and `T.returns` of a triple `T` end in them definitionally.
-/

namespace Zig

theorem Mem.seq_default : ({} : Mem).Seq :=
  ⟨singleThread_empty rfl (by decide)⟩

theorem Mem.heap_default : ({} : Mem).heap = Heap.empty := by
  funext l; obtain ⟨b, o⟩ := l; simp [Mem.heap]; rfl

theorem Mem.heap_default_split : ({} : Mem).heap = Heap.empty ∪ Heap.empty := by
  simp [Mem.heap_default]

namespace Witness

open Assn

/-! ## Admissible inputs and returning runs -/

/-- An admissible input of a triple with precondition `P`. -/
def Admit (P : Assn) : Prop :=
  ∃ (m : Mem) (hP hF : Heap) (_ : Heap.Disjoint hP hF) (_ : m.heap = hP ∪ hF) (_ : P hP) (_ : m.Seq),
    True

/-- An admissible input of a triple with precondition `P` on which `c` returns. -/
def Live {α : Type} (P : Assn) (c : MemM α) : Prop :=
  ∃ (m : Mem) (hP hF : Heap) (_ : Heap.Disjoint hP hF) (_ : m.heap = hP ∪ hF) (_ : P hP) (_ : m.Seq),
    ∃ r, (c.run m).run = some (.ok r)

theorem Admit.of_heap {P : Assn} {m : Mem} (hp : P m.heap) (hs : m.Seq) : Admit P :=
  ⟨m, m.heap, Heap.empty, Heap.disjoint_empty _, (Heap.union_empty _).symm, hp, hs, trivial⟩

theorem Admit.of_empty {P : Assn} (hp : P Heap.empty) : Admit P :=
  ⟨{}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, hp, Mem.seq_default,
    trivial⟩

theorem Admit.emp : Admit Assn.emp := Admit.of_empty rfl

theorem Live.of_heap {α : Type} {P : Assn} {c : MemM α} {m : Mem} (hp : P m.heap) (hs : m.Seq)
    (hr : ∃ r, (c.run m).run = some (.ok r)) : Live P c :=
  ⟨m, m.heap, Heap.empty, Heap.disjoint_empty _, (Heap.union_empty _).symm, hp, hs, hr⟩

theorem Live.of_empty {α : Type} {P : Assn} {c : MemM α} (hp : P Heap.empty)
    (hr : ∃ r, (c.run {}).run = some (.ok r)) : Live P c :=
  ⟨{}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, hp, Mem.seq_default,
    hr⟩

/-- A total triple returns on every admissible input. -/
theorem Live.of_total {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} (ht : TotalTriple P c Q)
    (h : Admit P) : Live P c := by
  obtain ⟨m, hP, hF, hd, hm, hp, hs, -⟩ := h
  obtain ⟨v, m', -, hr, -⟩ := ht m hP hF hd hm hp hs
  exact ⟨m, hP, hF, hd, hm, hp, hs, (v, m'), by rw [hr]; rfl⟩

end Witness

end Zig
