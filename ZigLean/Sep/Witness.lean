import ZigLean.Sep.Total
import ZigLean.Mem.Witness

/-!
# Admissible memories for claim witnesses

`nonvacuity_witness` and `liveness_witness` (`ZigLean/Witness.lean`) ask for an admissible
input of a triple: a memory `m` with `m.Seq` whose heap splits into the precondition's part and
a disjoint frame. The default memory (no blocks, one thread, empty footprint) with two empty
heaps is one, for any precondition that holds of the empty heap (`emp`, pure assertions).
`Witness.mem1 bs` (`ZigLean/Mem/Witness.lean`) is one for a precondition that owns one block of
bytes (`mem1_bytesAt`, `mem1_pts`), with the whole heap as the precondition's part and an empty
frame.

`Witness.Admit P` is the premise telescope of a triple with precondition `P` after its
arguments, and `Witness.Live P c` that telescope followed by a successful run of `c`: the
statements `T.nonvacuous` and `T.returns` of a triple `T` end in them definitionally.
-/

namespace Zig

theorem Mem.seq_default : ({} : Mem).Seq :=
  ⟨singleThread_empty rfl (by decide), fun l c h => by
    obtain ⟨b, o⟩ := l; simp [Mem.heap] at h⟩

theorem Mem.heap_default : ({} : Mem).heap = Heap.empty := by
  funext l; obtain ⟨b, o⟩ := l; simp [Mem.heap]; rfl

theorem Mem.heap_default_split : ({} : Mem).heap = Heap.empty ∪ Heap.empty := by
  simp [Mem.heap_default]

namespace Witness

open Assn

/-! ## One block of bytes -/

theorem mem1_heap (bs : Array Byte) (kind : BlockKind) (l : Loc) :
    (mem1 bs kind).heap l =
      if l.1 = 0 ∧ l.2 < bs.size then some ⟨bs[l.2]!, 4096, bs.size, kind⟩ else none := by
  obtain ⟨b, o⟩ := l
  rcases b with _ | b
  · by_cases h : o < bs.size
    · simp [Mem.heap, mem1, blk, h]
    · simp [Mem.heap, mem1, blk, h]
  · simp [Mem.heap, mem1]

theorem mem1_seq (bs : Array Byte) (kind : BlockKind) : (mem1 bs kind).Seq := by
  refine ⟨singleThread_empty rfl Nat.zero_lt_one, fun l c hc => ?_⟩
  rw [mem1_heap] at hc
  split at hc
  · cases hc; simp [mem1]
  · cases hc

theorem mem1_bytesAt (bs : Array Byte) (kind : BlockKind) :
    bytesAt p0 4096 bs.size kind bs (mem1 bs kind).heap :=
  ⟨0, rfl, by decide, fun l => by simp [mem1_heap, p0]⟩

/-- `p0` points to the value that the block holds. -/
theorem mem1_pts {T : Type} [Enc T] {bs : Array Byte} {kind : BlockKind} {a : Nat} {v : T}
    (hs : bs.size = Enc.size T) (hv : Enc.decode bs = pure v) (ha : 4096 % a = 0)
    (hk : kind ≠ .constGlobal) : pts p0 a v (mem1 bs kind).heap :=
  ⟨4096, bs.size, kind, bs, by simpa [p0] using ha, hs, hv, mem1_bytesAt bs kind, hk⟩

theorem mem1_pts' {T : Type} [Enc T] [LawfulEnc T] (v : T) {a : Nat} (ha : 4096 % a = 0) :
    pts p0 a v (mem1 (Enc.encode v)).heap :=
  mem1_pts (LawfulEnc.size_encode v) (LawfulEnc.decode_encode v) ha (by decide)

/-- Two values one after the other: `p0` points to `v` and `p0.add (Enc.size T)` to `w`. -/
theorem mem1_pts₂ {T U : Type} [Enc T] [LawfulEnc T] [Enc U] [LawfulEnc U] (v : T) (w : U)
    {a b : Nat} (ha : 4096 % a = 0) (hb : (4096 + Enc.size T) % b = 0) :
    (pts p0 a v ∗ pts (p0.add (Enc.size T)) b w)
      (mem1 (Enc.encode v ++ Enc.encode w)).heap := by
  have hv := LawfulEnc.size_encode v
  have hw := LawfulEnc.size_encode w
  obtain ⟨h₁, h₂, hd, he, hb₁, hb₂⟩ :=
    bytesAt_split (mem1_bytesAt (Enc.encode v ++ Enc.encode w) .heap) (k := Enc.size T)
      (by simp [hv])
  have e₁ : (Enc.encode v ++ Enc.encode w).extract 0 (Enc.size T) = Enc.encode v := by
    simp [Array.extract_append, ← hv]
  have e₂ : (Enc.encode v ++ Enc.encode w).extract (Enc.size T)
      (Enc.encode v ++ Enc.encode w).size = Enc.encode w := by
    simp [Array.extract_append, ← hv]
  rw [e₁] at hb₁
  rw [e₂] at hb₂
  refine ⟨h₁, h₂, hd, he, ⟨_, _, _, _, by simpa [p0] using ha, hv, LawfulEnc.decode_encode v, hb₁,
    by decide⟩, ⟨_, _, _, _, ?_, hw, LawfulEnc.decode_encode w, hb₂, by decide⟩⟩
  simpa [p0, Ptr.add] using hb

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

/-- A successful result as an `Option`: `okb d` exactly when `d = some (.ok r)`. -/
def okb {ε β : Type} : Option (Except ε β) → Bool
  | some (.ok _) => true
  | _ => false

theorem ok_of_okb {ε β : Type} {d : Option (Except ε β)} (h : okb d = true) :
    ∃ r, d = some (.ok r) := by
  match d, h with
  | some (.ok r), _ => exact ⟨r, rfl⟩

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
