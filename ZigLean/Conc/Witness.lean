import ZigLean.Conc.Own
import ZigLean.Sep.Witness

/-!
# Admissible inputs of thread triples

The premise telescope of a thread triple `TTriple P c Q` (`ZigLean/Conc/Own.lean`) after its
arguments is `Witness.TAdmit P`: a memory whose heap splits into the precondition's part and a
frame, a current thread with a clock, and that thread owning the precondition's part.
`Witness.TLive P c` adds a successful run of `c`. A memory with an empty footprint, such as
`Witness.mem1 bs`, owns every heap.
-/

namespace Zig.Witness

/-- An admissible input of a thread triple with precondition `P`. -/
def TAdmit (P : Assn) : Prop :=
  ∃ (m : Mem) (hP hF : Heap) (_ : Heap.Disjoint hP hF) (_ : m.heap = hP ∪ hF) (_ : P hP)
    (_ : m.current < m.clocks.size) (_ : m.Owns m.current hP), True

/-- An admissible input of a thread triple with precondition `P` on which `c` returns. -/
def TLive {α : Type} (P : Assn) (c : MemM α) : Prop :=
  ∃ (m : Mem) (hP hF : Heap) (_ : Heap.Disjoint hP hF) (_ : m.heap = hP ∪ hF) (_ : P hP)
    (_ : m.current < m.clocks.size) (_ : m.Owns m.current hP), ∃ r, (c.run m).run = some (.ok r)

theorem owns_of_footprint {m : Mem} (hf : m.footprint = #[]) (t : ThreadId) (h : Heap) :
    m.Owns t h := fun e he => by rw [hf] at he; cases he; contradiction

theorem TAdmit.of_heap {P : Assn} {m : Mem} (hp : P m.heap) (hc : m.current < m.clocks.size)
    (hf : m.footprint = #[]) : TAdmit P :=
  ⟨m, m.heap, Heap.empty, Heap.disjoint_empty _, (Heap.union_empty _).symm, hp, hc,
    owns_of_footprint hf _ _, trivial⟩

theorem TAdmit.of_empty {P : Assn} (hp : P Heap.empty) : TAdmit P :=
  ⟨{}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, hp, Nat.zero_lt_one,
    owns_of_footprint rfl _ _, trivial⟩

theorem TLive.of_heap {α : Type} {P : Assn} {c : MemM α} {m : Mem} (hp : P m.heap)
    (hc : m.current < m.clocks.size) (hf : m.footprint = #[])
    (hr : ∃ r, (c.run m).run = some (.ok r)) : TLive P c :=
  ⟨m, m.heap, Heap.empty, Heap.disjoint_empty _, (Heap.union_empty _).symm, hp, hc,
    owns_of_footprint hf _ _, hr⟩

theorem TLive.of_empty {α : Type} {P : Assn} {c : MemM α} (hp : P Heap.empty)
    (hr : ∃ r, (c.run {}).run = some (.ok r)) : TLive P c :=
  ⟨{}, Heap.empty, Heap.empty, Heap.disjoint_empty _, Mem.heap_default_split, hp, Nat.zero_lt_one,
    owns_of_footprint rfl _ _, hr⟩

/-- `mem1 bs` as a thread-triple input. -/
theorem TAdmit.mem1 {P : Assn} {bs : Array Byte} {kind : BlockKind} (hp : P (mem1 bs kind).heap) :
    TAdmit P :=
  TAdmit.of_heap hp Nat.zero_lt_one rfl

theorem TLive.mem1 {α : Type} {P : Assn} {c : MemM α} {bs : Array Byte} {kind : BlockKind}
    (hp : P (mem1 bs kind).heap) (hr : ∃ r, (c.run (mem1 bs kind)).run = some (.ok r)) : TLive P c :=
  TLive.of_heap hp Nat.zero_lt_one rfl hr

/-- The `u32` of a run of a function `!u32`: a completed run of a concurrent program, for a
statement about one schedule. -/
def okVal (r : Result (Except ErrName (BitVec 32) × Mem)) : Option Nat :=
  match r.run with
  | some (.ok (.ok v, _)) => some v.toNat
  | _ => none

end Zig.Witness
