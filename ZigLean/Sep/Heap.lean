import ZigLean.Mem.Lemmas

/-!
# Heaps

A separation-logic assertion is a predicate on a `Heap`: a partial map from a location (a block
and a byte offset) to a `Cell`. `Mem.heap m` is the heap of all live bytes of `m`. A cell also
holds the address, the size and the kind of its block, so an assertion can state the alignment
of a pointer, that it owns a whole block (for `free`), and that the allocator made the block (for
`Allocator.free`).
-/

namespace Zig

/-- A byte, with the address, the size and the kind of its block. -/
structure Cell where
  byte : Byte
  addr : Nat
  size : Nat
  kind : BlockKind
  deriving DecidableEq

abbrev Loc := BlockId × Nat

/-- A partial map from locations to cells. -/
abbrev Heap := Loc → Option Cell

namespace Heap

def empty : Heap := fun _ => none

/-- No location is in both heaps. -/
def Disjoint (h₁ h₂ : Heap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

/-- The cells of both heaps (`h₁` first; the two are disjoint where this is used). -/
def union (h₁ h₂ : Heap) : Heap := fun l => (h₁ l).or (h₂ l)

instance : Union Heap := ⟨union⟩

@[simp] theorem union_apply (h₁ h₂ : Heap) (l : Loc) : (h₁ ∪ h₂) l = (h₁ l).or (h₂ l) := rfl

theorem Disjoint.symm {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) : Disjoint h₂ h₁ :=
  fun l => (h l).symm

theorem union_comm {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) : h₁ ∪ h₂ = h₂ ∪ h₁ := by
  funext l; rcases h l with e | e <;> simp [e]

theorem union_assoc (h₁ h₂ h₃ : Heap) : h₁ ∪ h₂ ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  funext l; simp [Option.or_assoc]

theorem union_left_comm {h₁ h₂ h₃ : Heap} (h : Disjoint h₁ h₂) :
    h₁ ∪ (h₂ ∪ h₃) = h₂ ∪ (h₁ ∪ h₃) := by
  rw [← union_assoc, union_comm h, union_assoc]

@[simp] theorem empty_union (h : Heap) : empty ∪ h = h := by funext l; simp [empty]

@[simp] theorem union_empty (h : Heap) : h ∪ empty = h := by funext l; simp [empty]

theorem disjoint_empty (h : Heap) : Disjoint h empty := fun _ => Or.inr rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Disjoint (h₁ ∪ h₂) h₃ ↔ Disjoint h₁ h₃ ∧ Disjoint h₂ h₃ := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases h l with e | e <;> simp_all [Option.or_eq_none_iff]
  · rintro ⟨a, b⟩ l
    rcases a l with e | e
    · rcases b l with e' | e'
      · left; simp [e, e']
      · right; exact e'
    · right; exact e

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Disjoint h₁ (h₂ ∪ h₃) ↔ Disjoint h₁ h₂ ∧ Disjoint h₁ h₃ := by
  constructor
  · intro h; have := disjoint_union_left.mp h.symm; exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨a, b⟩; exact (disjoint_union_left.mpr ⟨a.symm, b.symm⟩).symm

/-- A cell of `h₁` is the cell of `h₁ ∪ h₂` there. -/
theorem union_of_left {h₁ h₂ : Heap} {l : Loc} {c : Cell} (h : h₁ l = some c) :
    (h₁ ∪ h₂) l = some c := by simp [h]

theorem union_of_right {h₁ h₂ : Heap} {l : Loc} (h : h₁ l = none) : (h₁ ∪ h₂) l = h₂ l := by
  simp [h]

end Heap

/-- The live bytes of `m`. -/
def Mem.heap (m : Mem) : Heap := fun (b, o) =>
  match m.blocks[b]? with
  | some blk =>
    if h : blk.live ∧ o < blk.bytes.size then some ⟨blk.bytes[o], blk.addr, blk.bytes.size, blk.kind⟩
    else none
  | none => none

theorem Mem.heap_some {m : Mem} {b : BlockId} {o : Nat} {c : Cell} (h : m.heap (b, o) = some c) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live ∧ ∃ ho : o < blk.bytes.size,
      c = ⟨blk.bytes[o], blk.addr, blk.bytes.size, blk.kind⟩ := by
  unfold Mem.heap at h
  cases hb : m.blocks[b]? with
  | none => simp [hb] at h
  | some blk =>
    simp only [hb] at h
    by_cases hc : blk.live ∧ o < blk.bytes.size
    · rw [dite_eq_left_of_eq_true (eq_true hc)] at h; cases h; exact ⟨blk, rfl, hc.1, hc.2, rfl⟩
    · rw [dite_eq_right_of_eq_false (eq_false hc)] at h; cases h

theorem writeBytes_getElem? (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size)
    (i : Nat) : (writeBytes a o bs)[i]? = if o ≤ i ∧ i < o + bs.size then bs[i - o]? else a[i]? := by
  unfold writeBytes
  have ho : Min.min o a.size = o := Nat.min_eq_left (by omega)
  by_cases h1 : i < o
  · have : ¬ o ≤ i := by omega
    simp [Array.getElem?_append, h1, ho, this]
  · by_cases h2 : i < o + bs.size
    · simp [Array.getElem?_append, h1, h2, ho, show i - o < bs.size by omega, show o ≤ i by omega]
    · simp [Array.getElem?_append, h1, h2, ho, show ¬ i - o < bs.size by omega, Array.getElem?_extract]
      rw [show o + bs.size + (i - o - bs.size) = i by omega]
      split
      · rfl
      · rw [Array.getElem?_eq_none]; omega

theorem writeBytes_getElem (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size)
    (i : Nat) (hi : i < (writeBytes a o bs).size) :
    (writeBytes a o bs)[i] = if o ≤ i ∧ i < o + bs.size then bs[i - o]! else a[i]! := by
  have hs := writeBytes_size a o bs h
  apply Option.some.inj
  rw [← Array.getElem?_eq_getElem hi, writeBytes_getElem? a o bs h i]
  by_cases hc : o ≤ i ∧ i < o + bs.size
  · simp only [hc, and_self, ↓reduceIte]
    rw [getElem!_pos bs (i - o) (by omega), Array.getElem?_eq_getElem (by omega)]
  · simp only [hc, ↓reduceIte]
    rw [getElem!_pos a i (by omega), Array.getElem?_eq_getElem (by omega)]

/-- `Mem.recordAt` only changes `clocks`/`footprint`, never `blocks`, so it never changes the
heap (bridges `storeBytes_run`/`loadBytes_run`'s extra `.recordAt` layer for `Assert.lean`). -/
theorem Mem.heap_recordAt {m : Mem} {block off len : Nat} {kind : AccessKind} (l : Loc) :
    (m.recordAt block off len kind).heap l = m.heap l := by simp [Mem.heap, Mem.recordAt]

theorem Mem.heap_write {m : Mem} {b : BlockId} {blk : Block} {o : Nat} {bs : Array Byte}
    (hblk : m.blocks[b]? = some blk) (hl : blk.live) (hn : o + bs.size ≤ blk.bytes.size) (l : Loc) :
    (m.write b blk o bs).heap l =
      if l.1 = b ∧ o ≤ l.2 ∧ l.2 < o + bs.size then some ⟨bs[l.2 - o]!, blk.addr, blk.bytes.size, blk.kind⟩
      else m.heap l := by
  obtain ⟨b', x⟩ := l
  have hb : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hs := writeBytes_size blk.bytes o bs hn
  by_cases hbb : b' = b
  · subst hbb
    have e : (m.blocks.set! b' { blk with bytes := writeBytes blk.bytes o bs })[b']? =
        some { blk with bytes := writeBytes blk.bytes o bs } := by
      rw [Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hb
    unfold Mem.heap Mem.write
    simp only [e, hblk, true_and]
    by_cases hx : x < blk.bytes.size
    · have hx' : x < (writeBytes blk.bytes o bs).size := by omega
      rw [dite_eq_left_of_eq_true (eq_true ⟨hl, hx'⟩), dite_eq_left_of_eq_true (eq_true ⟨hl, hx⟩),
        writeBytes_getElem _ _ _ hn _ hx', hs]
      by_cases hc : o ≤ x ∧ x < o + bs.size
      · simp only [hc, and_self, ↓reduceIte]
      · simp only [hc, ↓reduceIte, getElem!_pos blk.bytes x hx]
    · have hx' : ¬ x < (writeBytes blk.bytes o bs).size := by omega
      have hc : ¬ (o ≤ x ∧ x < o + bs.size) := by omega
      simp [hx, hx', hc]
  · have e : (m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs })[b']? = m.blocks[b']? := by
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [Ne.symm hbb]
    unfold Mem.heap Mem.write
    simp only [e, hbb, false_and, ↓reduceIte]

theorem writeBytes_getElem! (a : Array Byte) (o : Nat) (bs : Array Byte) (h : o + bs.size ≤ a.size)
    (i : Nat) : (writeBytes a o bs)[i]! = if o ≤ i ∧ i < o + bs.size then bs[i - o]! else a[i]! := by
  by_cases hc : o ≤ i ∧ i < o + bs.size
  · simp only [getElem!_def, writeBytes_getElem? a o bs h i, hc, and_self, ↓reduceIte]
  · simp only [getElem!_def, writeBytes_getElem? a o bs h i, hc, ↓reduceIte]

/-- The memory invariant of `Triple`: one thread. It says nothing about addresses: the rules
hold for every placement (`Mem.place`), and the only address facts they give are the ones Zig
guarantees (`alloc_run`: aligned, clear of every live block). -/
structure Mem.Seq (m : Mem) : Prop where
  single : m.SingleThread

theorem Mem.Seq.recordAt {m : Mem} (h : m.Seq) (block off len : Nat) (kind : AccessKind) :
    (m.recordAt block off len kind).Seq :=
  ⟨singleThread_recordAt h.single block off len kind⟩

end Zig
