import ZigLean.Sep.Heap

/-!
# Assertions

An assertion is a predicate on a heap. `P ∗ Q` holds of a heap that splits into two disjoint
parts, one for `P` and one for `Q`. `bytesAt p A S K bs` owns exactly the bytes `bs` at `p`, in a
block with address `A`, size `S` and kind `K`. The typed forms (`pts`, `arr`, `ZigLean/Sep/Triple.lean`)
build on it.

The two lemmas at the end are the base of every rule: an access to a part of owned bytes succeeds
and reads them (`bytesAt_access`), and a store to that part changes only the owned heap
(`bytesAt_store`).
-/

namespace Zig

abbrev Assn := Heap → Prop

namespace Assn

def emp : Assn := fun h => h = Heap.empty

/-- A fact that owns no bytes. -/
def lift (φ : Prop) : Assn := fun h => φ ∧ h = Heap.empty

def sep (P Q : Assn) : Assn := fun h =>
  ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = h₁ ∪ h₂ ∧ P h₁ ∧ Q h₂

def ex {α : Type} (P : α → Assn) : Assn := fun h => ∃ a, P a h

end Assn

scoped infixr:35 " ∗ " => Assn.sep
scoped notation "⌜" φ "⌝" => Assn.lift φ

open Assn

/-- `h` owns exactly the bytes `bs` at `p`, in a block with address `A`, size `S` and kind `K`. -/
def bytesAt (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) : Assn := fun h =>
  ∃ b, p.block = some b ∧ 0 ≤ p.off ∧ ∀ l : Loc, h l =
    if l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size
    then some ⟨bs[l.2 - p.off.toNat]!, A, S, K⟩ else none

section Sep

theorem sep_comm {P Q : Assn} {h : Heap} : (P ∗ Q) h → (Q ∗ P) h := by
  rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₂, h₁, hd.symm, Heap.union_comm hd, hq, hp⟩

theorem sep_assoc {P Q R : Assn} {h : Heap} : ((P ∗ Q) ∗ R) h → (P ∗ (Q ∗ R)) h := by
  rintro ⟨h₁₂, h₃, hd, rfl, ⟨h₁, h₂, hd', rfl, hp, hq⟩, hr⟩
  obtain ⟨hd₁₃, hd₂₃⟩ := Heap.disjoint_union_left.mp hd
  exact ⟨h₁, h₂ ∪ h₃, Heap.disjoint_union_right.mpr ⟨hd', hd₁₃⟩, Heap.union_assoc _ _ _, hp,
    h₂, h₃, hd₂₃, rfl, hq, hr⟩

theorem sep_assoc' {P Q R : Assn} {h : Heap} : (P ∗ (Q ∗ R)) h → ((P ∗ Q) ∗ R) h := by
  rintro ⟨h₁, h₂₃, hd, rfl, hp, ⟨h₂, h₃, hd', rfl, hq, hr⟩⟩
  obtain ⟨hd₁₂, hd₁₃⟩ := Heap.disjoint_union_right.mp hd
  exact ⟨h₁ ∪ h₂, h₃, Heap.disjoint_union_left.mpr ⟨hd₁₃, hd'⟩, (Heap.union_assoc _ _ _).symm,
    ⟨h₁, h₂, hd₁₂, rfl, hp, hq⟩, hr⟩

theorem sep_mono {P P' Q Q' : Assn} {h : Heap} (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) :
    (P ∗ Q) h → (P' ∗ Q') h := by
  rintro ⟨h₁, h₂, hd, rfl, a, b⟩
  exact ⟨h₁, h₂, hd, rfl, hp _ a, hq _ b⟩

theorem sep_emp {P : Assn} {h : Heap} : (P ∗ emp) h ↔ P h := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, hp, rfl⟩; simpa using hp
  · intro hp; exact ⟨h, Heap.empty, Heap.disjoint_empty h, by simp, hp, rfl⟩

theorem sep_lift {φ : Prop} {P : Assn} {h : Heap} : (⌜φ⌝ ∗ P) h ↔ φ ∧ P h := by
  constructor
  · rintro ⟨h₁, h₂, -, rfl, ⟨hφ, rfl⟩, hp⟩; simpa using And.intro hφ hp
  · rintro ⟨hφ, hp⟩; exact ⟨Heap.empty, h, (Heap.disjoint_empty h).symm, by simp, ⟨hφ, rfl⟩, hp⟩

end Sep

section Bytes

variable {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}

/-- The cell of an owned byte in the memory. -/
theorem bytesAt_cell (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) {b : BlockId}
    (hpb : p.block = some b) {j : Nat} (hj : j < bs.size) :
    m.heap (b, p.off.toNat + j) = some ⟨bs[j]!, A, S, K⟩ := by
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  rw [hm]
  apply Heap.union_of_left
  rw [hl]
  simp [hj]

/-- An access to the `n > 0` bytes at `q`, a part of the bytes that `h` owns (`q` is `k` bytes
after `p`), succeeds if its address is aligned, and reads the owned bytes. -/
theorem bytesAt_access (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) {q : Ptr} {k n a : Nat}
    (hq : q = p.add k) (hn : 0 < n) (hk : k + n ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) :
    ∃ b blk, m.access q n a = pure (b, blk, p.off.toNat + k) ∧ m.blocks[b]? = some blk ∧
      blk.addr = A ∧ blk.bytes.size = S ∧
      blk.bytes.extract (p.off.toNat + k) (p.off.toNat + k + n) = bs.extract k (k + n) := by
  obtain ⟨b, hpb, h0, -⟩ := id hb
  -- The first and the last byte fix the block and its bounds.
  have c0 := bytesAt_cell hb hm hpb (j := k) (by omega)
  obtain ⟨blk, hblk, hlive, _, hc0⟩ := Mem.heap_some c0
  have cl := bytesAt_cell hb hm hpb (j := k + n - 1) (by omega)
  obtain ⟨blk', hblk', -, hlt, -⟩ := Mem.heap_some cl
  rw [hblk] at hblk'; cases hblk'
  simp only [Cell.mk.injEq] at hc0
  obtain ⟨-, hA, hS, -⟩ := hc0
  refine ⟨b, blk, ?_, hblk, hA.symm, hS.symm, ?_⟩
  · have hoff : q.off.toNat = p.off.toNat + k := by subst hq; simp [Ptr.add]; omega
    have := access_of (m := m) (p := q) (n := n) (a := a) (by subst hq; simpa [Ptr.add] using hpb)
      hblk hlive (by subst hq; simp [Ptr.add]; omega) (by subst hq; simp [Ptr.add]; omega)
      (by rw [hoff, ← hA]; simpa [Nat.add_assoc] using ha)
    rw [hoff] at this; exact this
  · apply Array.ext
    · simp; omega
    · intro i hi _
      simp only [Array.size_extract] at hi
      have ci := bytesAt_cell hb hm hpb (j := k + i) (by omega)
      obtain ⟨blk', hblk', -, hlt', hc⟩ := Mem.heap_some ci
      rw [hblk] at hblk'; cases hblk'
      simp only [Cell.mk.injEq] at hc
      simp only [Array.getElem_extract]
      have e : blk.bytes[p.off.toNat + k + i] = blk.bytes[p.off.toNat + (k + i)] := by
        simp [Nat.add_assoc]
      rw [e, ← hc.1]
      simp [getElem!_pos, show k + i < bs.size by omega]

/-- A store of `bs'` (`0 < bs'.size`) at `q`, a part of the bytes that `h` owns, succeeds if its
address is aligned, the access does not race (`hnr`) and the block is not a `const` global (`hw`).
The result memory is the recorded access and the write; the owned bytes are `writeBytes bs k bs'`,
and the frame `hF` is unchanged. -/
theorem bytesAt_store_core (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF)
    (hd : Heap.Disjoint h hF) {q : Ptr} {k a : Nat} {bs' : Array Byte} (hq : q = p.add k)
    (hn : 0 < bs'.size) (hk : k + bs'.size ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0)
    (hnr : ∀ b, p.block = some b → NoRace m b (p.off.toNat + k) bs'.size .write)
    (hw : K ≠ .constGlobal) :
    ∃ b blk, p.block = some b ∧ (storeBytes q a bs').run m =
      pure ((), (m.recordAt b (p.off.toNat + k) bs'.size .write).write b blk (p.off.toNat + k) bs') ∧
      ∃ h', Heap.Disjoint h' hF ∧
        ((m.recordAt b (p.off.toNat + k) bs'.size .write).write b blk (p.off.toNat + k) bs').heap =
          h' ∪ hF ∧ bytesAt p A S K (writeBytes bs k bs') h' := by
  obtain ⟨b, blk, hacc, hblk, hA, hS, -⟩ := bytesAt_access hb hm hq hn hk ha
  obtain ⟨hqb, -, hl, hq0, hbound, -, -⟩ := access_eq hacc
  obtain ⟨b', hpb, h0, hown⟩ := id hb
  have hbb : b' = b := by
    have : q.block = p.block := by subst hq; rfl
    rw [this, hpb] at hqb; exact Option.some.inj hqb
  subst hbb
  have hnr' := hnr b' hpb
  have hK : blk.kind = K := by
    obtain ⟨blk', hblk', -, _, hc⟩ := Mem.heap_some (bytesAt_cell hb hm hpb (j := k) (by omega))
    rw [hblk] at hblk'; cases hblk'
    simp only [Cell.mk.injEq] at hc; exact hc.2.2.2.symm
  have hws := writeBytes_size bs k bs' hk
  have hqo : q.off.toNat = p.off.toNat + k := by subst hq; simp [Ptr.add]; omega
  have hpbq := hpb
  generalize ho : p.off.toNat = o at hown hqo ha hacc hnr' ⊢
  let h' : Heap := fun l =>
    if l.1 = b' ∧ o ≤ l.2 ∧ l.2 < o + (writeBytes bs k bs').size
    then some ⟨(writeBytes bs k bs')[l.2 - o]!, A, S, K⟩ else none
  refine ⟨b', blk, hpb, storeBytes_run hacc (hK ▸ hw) hnr',
    h', ?_, ?_, ⟨b', hpb, h0, fun l => by simp only [h', ho]⟩⟩
  · intro l
    by_cases hc : l.1 = b' ∧ o ≤ l.2 ∧ l.2 < o + (writeBytes bs k bs').size
    · right
      have hl' : h l ≠ none := by rw [hown l]; simp only [hc.1, true_and]; rw [hws] at hc; simp [hc.2]
      exact (hd l).resolve_left hl'
    · left; simp [h', hc]
  · funext ⟨x, y⟩
    have hbsz : o + k + bs'.size ≤ blk.bytes.size := by rw [← hqo]; omega
    have hblk_r : (m.recordAt b' (o + k) bs'.size AccessKind.write).blocks[b']? = some blk := hblk
    rw [Mem.heap_write hblk_r hl hbsz, Mem.heap_recordAt]
    have hmx := congrFun hm (x, y)
    simp only [Heap.union_apply] at hmx ⊢
    rw [hown (x, y)] at hmx
    simp only [h', hws]
    by_cases hx : x = b'
    · subst hx
      by_cases hw : o + k ≤ y ∧ y < o + k + bs'.size
      · have hin : o ≤ y ∧ y < o + bs.size := by omega
        simp only [hw, hin, and_self, ↓reduceIte, Option.some_or, writeBytes_getElem! bs k bs' hk,
          show k ≤ y - o ∧ y - o < k + bs'.size by omega]
        rw [← hA, ← hS, ← hK, show y - (o + k) = y - o - k by omega]
      · simp only [hw, true_and, ↓reduceIte]
        by_cases hin : o ≤ y ∧ y < o + bs.size
        · simp only [hin, and_self, ↓reduceIte, Option.some_or] at hmx ⊢
          rw [hmx, writeBytes_getElem! bs k bs' hk]
          simp [show ¬ (k ≤ y - o ∧ y - o < k + bs'.size) by omega]
        · simp only [hin, ↓reduceIte, Option.none_or] at hmx ⊢
          exact hmx
    · simp only [hx, false_and, ↓reduceIte, Option.none_or] at hmx ⊢
      exact hmx

/-- `bytesAt_store_core` in a single-threaded memory (`hst`, so the access cannot race:
`noRace_of_singleThread`); the result is itself single-threaded. -/
theorem bytesAt_store (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    {q : Ptr} {k a : Nat} {bs' : Array Byte} (hq : q = p.add k) (hn : 0 < bs'.size)
    (hk : k + bs'.size ≤ bs.size) (ha : (A + p.off.toNat + k) % a = 0) (hst : m.SingleThread)
    (hw : K ≠ .constGlobal) :
    ∃ m', (storeBytes q a bs').run m = pure ((), m') ∧ m'.SingleThread ∧
      ∃ h', Heap.Disjoint h' hF ∧ m'.heap = h' ∪ hF ∧ bytesAt p A S K (writeBytes bs k bs') h' := by
  obtain ⟨b, blk, -, hr, hh⟩ := bytesAt_store_core hb hm hd hq hn hk ha
    (fun b _ => noRace_of_singleThread hst b _ _ _) hw
  exact ⟨_, hr, singleThread_write (singleThread_recordAt hst _ _ _ _) _ _ _ _, hh⟩

/-- The live block `b` as owned bytes, and the rest of the memory. -/
theorem Mem.heap_split {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (hl : blk.live) :
    ∃ h hF, Heap.Disjoint h hF ∧ m.heap = h ∪ hF ∧
      bytesAt ⟨some b, 0⟩ blk.addr blk.bytes.size blk.kind blk.bytes h := by
  refine ⟨fun l => if l.1 = b then m.heap l else none, fun l => if l.1 = b then none else m.heap l,
    ?_, ?_, b, rfl, Int.le_refl 0, ?_⟩
  · intro l; by_cases e : l.1 = b <;> simp [e]
  · funext l; by_cases e : l.1 = b <;> simp [e]
  · rintro ⟨x, y⟩
    by_cases e : x = b
    · subst e
      simp only [↓reduceIte, Mem.heap, hb, hl, true_and, Int.toNat_zero, Nat.zero_le, Nat.zero_add,
        Nat.sub_zero]
      by_cases hy : y < blk.bytes.size
      · simp [hy, getElem!_pos]
      · simp [hy]
    · simp [e]

end Bytes

end Zig
