import ZigLean.Mem.Lemmas

/-!
# Live blocks have disjoint address ranges (migration stage 3, `docs/sep-full-state.md`)

`Mem.LiveDisjoint m`: no two live blocks of `m` share an address, in the sense of
`Block.clearOf` (the relation that the placement check `Mem.addrFree` applies to a new block, so
a block of size 0 constrains nothing). Every new block is placed clear of the live ones
(`Mem.newAddr_addrFree`), so every memory reachable from one without blocks has it. It is part of
the full-state memory invariant `Mem.FSeq` (`ZigLean/Sep/Full/Triple.lean`), and `LDMono m m'`
(a step keeps it) is part of `Tame`.

The lemmas here are the cases of the memory model's block updates: the blocks unchanged
(`LDMono.of_blocks`), a block that keeps its address and does not grow or come to life
(`LDMono.set`, `free`, a store, `munmap`), and a pushed block clear of the live ones
(`LDMono.push`, `alloc`, `mmap`).
-/

namespace Zig

/-- Live blocks occupy disjoint address ranges (module doc). -/
def Mem.LiveDisjoint (m : Mem) : Prop :=
  ∀ (b b' : BlockId) (blk blk' : Block), b ≠ b' → m.blocks[b]? = some blk →
    m.blocks[b']? = some blk' → blk'.live → blk.clearOf blk'.addr blk'.bytes.size = true

namespace Full

/-- The step from `m` to `m'` keeps `Mem.LiveDisjoint`. -/
def LDMono (m m' : Mem) : Prop := m.LiveDisjoint → m'.LiveDisjoint

theorem LDMono.refl (m : Mem) : LDMono m m := id

theorem LDMono.trans {m₁ m₂ m₃ : Mem} (h₁ : LDMono m₁ m₂) (h₂ : LDMono m₂ m₃) : LDMono m₁ m₃ :=
  fun h => h₂ (h₁ h)

theorem LDMono.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : LDMono m m' := by
  intro hd b b' blk blk' hbb h1 h2 hl
  rw [h] at h1 h2; exact hd b b' blk blk' hbb h1 h2 hl

theorem clearOf_iff {blk : Block} {A n : Nat} :
    blk.clearOf A n = true ↔
      (blk.live = false ∨ n = 0 ∨ blk.bytes.size = 0 ∨ A + n ≤ blk.addr ∨
        blk.addr + blk.bytes.size ≤ A) := by
  simp [Block.clearOf, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, or_assoc]

/-- A block that keeps its address, does not grow and does not come to life stays clear of a
range inside the old one. -/
theorem clearOf_shrink {blk blk' : Block} {A n A' n' : Nat} (h : blk.clearOf A n = true)
    (hl : blk'.live = true → blk.live = true) (ha : blk'.addr = blk.addr)
    (hs : blk'.bytes.size ≤ blk.bytes.size) (hA : A ≤ A') (hn : A' + n' ≤ A + n) :
    blk'.clearOf A' n' = true := by
  rw [clearOf_iff] at h ⊢
  by_cases hl' : blk'.live = true
  · have := hl hl'
    rcases h with h | h | h | h | h
    · simp_all
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · right; right; right; right; omega
  · left; simpa using hl'

/-- Clearance between two live blocks is symmetric. -/
theorem clearOf_symm {blk blk' : Block} (hl : blk.live = true) (hl' : blk'.live = true)
    (h : blk.clearOf blk'.addr blk'.bytes.size = true) :
    blk'.clearOf blk.addr blk.bytes.size = true := by
  rw [clearOf_iff] at h ⊢
  rcases h with h | h | h | h | h
  · simp_all
  · right; right; left; exact h
  · right; left; exact h
  · right; right; right; right; exact h
  · right; right; right; left; exact h

/-- Each block of `m'` is the block of `m` with the same id, at the same address, no larger, and
not newly live. -/
theorem LDMono.shrink {m m' : Mem}
    (h : ∀ (b : BlockId) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk : Block, m.blocks[b]? = some blk ∧
      (blk'.live = true → blk.live = true) ∧ blk'.addr = blk.addr ∧
      blk'.bytes.size ≤ blk.bytes.size) : LDMono m m' := by
  intro hd b b' blk₁' blk₂' hbb h1 h2 hl
  obtain ⟨blk₁, e1, l1, a1, s1⟩ := h b blk₁' h1
  obtain ⟨blk₂, e2, l2, a2, s2⟩ := h b' blk₂' h2
  have := hd b b' blk₁ blk₂ hbb e1 e2 (l2 hl)
  exact clearOf_shrink this l1 a1 s1 (by omega) (by omega)

/-- Replacing block `b` by one at the same address, no larger and not newly live. -/
theorem LDMono.set {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : nb.live = true → blk.live = true) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size ≤ blk.bytes.size) (h : m'.blocks = m.blocks.set! b nb) :
    LDMono m m' := by
  refine LDMono.shrink fun b' blk' h' => ?_
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h'
  by_cases e : b = b'
  · subst e
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [hlt, if_true, Option.some.injEq] at h'
    subst h'
    exact ⟨blk, hb, hl, ha, hs⟩
  · simp only [e, if_false] at h'
    exact ⟨blk', h', id, rfl, Nat.le_refl _⟩

/-- Growing the live block `b` in place to at most `lo + len` bytes, where the added range
`[addr + lo, addr + lo + len)` is clear of every other block (`Mem.mappingRoom`). -/
theorem LDMono.grow {m m' : Mem} {b : BlockId} {blk nb : Block} {lo len : Nat}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (ha : nb.addr = blk.addr)
    (hlo : lo ≤ blk.bytes.size) (hsz : nb.bytes.size ≤ lo + len)
    (hroom : ∀ (j : BlockId) (o : Block), j ≠ b → m.blocks[j]? = some o →
      o.clearOf (blk.addr + lo) len = true)
    (h : m'.blocks = m.blocks.set! b nb) : LDMono m m' := by
  intro hd
  -- every other block is clear of the grown range
  have hclear : ∀ (j : BlockId) (o : Block), j ≠ b → m.blocks[j]? = some o →
      o.clearOf nb.addr nb.bytes.size = true := by
    intro j o hj ho
    have h1 := clearOf_iff.mp (hd j b o blk hj ho hb hl)
    have h2 := clearOf_iff.mp (hroom j o hj ho)
    rw [clearOf_iff, ha]
    by_cases hol : o.live = false
    · left; exact hol
    right
    rcases h1 with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hol
    all_goals rcases h2 with h2 | h2 | h2 | h2 | h2
    all_goals first | exact absurd h2 hol | omega
  have hget : ∀ j, m'.blocks[j]? = if j = b then some nb else m.blocks[j]? := by
    intro j
    rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    by_cases e : j = b
    · subst e; simp [hlt]
    · simp [e, Ne.symm e]
  intro x y bx by' hxy h1 h2 hly
  rw [hget] at h1 h2
  by_cases ex : x = b <;> by_cases ey : y = b
  · exact absurd (ex.trans ey.symm) hxy
  · simp only [ex, if_true, if_neg ey, Option.some.injEq] at h1 h2
    subst h1
    by_cases hn : nb.live = true
    · exact clearOf_symm hly hn (hclear y by' ey h2)
    · rw [clearOf_iff]; left; simpa using hn
  · simp only [ey, if_true, if_neg ex, Option.some.injEq] at h1 h2
    subst h2
    exact hclear x bx ex h1
  · simp only [if_neg ex, if_neg ey] at h1 h2
    exact hd x y bx by' hxy h1 h2 hly

/-- Pushing a block that is dead or clear of every live block (`Mem.addrFree`). -/
theorem LDMono.push {m m' : Mem} {nb : Block}
    (hf : nb.live = true → m.addrFree nb.addr nb.bytes.size = true)
    (h : m'.blocks = m.blocks.push nb) : LDMono m m' := by
  intro hd b b' blk blk' hbb h1 h2 hl
  rw [h, Array.getElem?_push] at h1 h2
  have hall : ∀ (j : Nat) (x : Block), m.blocks[j]? = some x → nb.live = true →
      x.clearOf nb.addr nb.bytes.size = true := by
    intro j x hx hn
    have := hf hn
    unfold Mem.addrFree at this
    rw [Array.all_eq_true] at this
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
    exact this j hi
  by_cases e1 : b = m.blocks.size <;> by_cases e2 : b' = m.blocks.size
  · exact absurd (e1.trans e2.symm) hbb
  · simp only [e1, if_true, if_neg e2, Option.some.injEq] at h1 h2
    subst h1
    by_cases hn : nb.live = true
    · exact clearOf_symm hl hn (hall b' blk' h2 hn)
    · rw [clearOf_iff]; left; simpa using hn
  · simp only [e2, if_true, if_neg e1, Option.some.injEq] at h1 h2
    subst h2
    exact hall b blk h1 hl
  · simp only [if_neg e1, if_neg e2] at h1 h2
    exact hd b b' blk blk' hbb h1 h2 hl

/-- A new block's address is clear of every live block. -/
theorem _root_.Zig.Mem.newAddr_addrFree (m : Mem) (size align : Nat) :
    m.addrFree (m.newAddr size align) size = true := by
  unfold Mem.newAddr
  split
  · exact (Mem.placed?_ok ‹_›).2.2.2
  · unfold Mem.addrFree
    rw [Array.all_eq_true]
    intro i hi
    have := Mem.lt_top (m := m) (b := i) (Array.getElem?_eq_getElem hi)
    have := le_alignUp m.top align
    rw [clearOf_iff]; right; right; right; right; omega

/-- A global's block is placed like any new block. -/
theorem LDMono.addGlobal (m : Mem) (bs : Array Byte) (a : Nat) (k : BlockKind) :
    LDMono m (m.addGlobal bs a k) :=
  LDMono.push (fun _ => m.newAddr_addrFree _ _) rfl

/-- The memory at program start keeps live blocks apart, so `Mem.FSeq`'s `LiveDisjoint` holds of
every memory reachable from it. -/
theorem _root_.Zig.Mem.ofGlobals_liveDisjoint (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) : (Mem.ofGlobals σ gs).LiveDisjoint := by
  unfold Mem.ofGlobals
  suffices h : ∀ (gs : List (Array Byte × Nat × BlockKind)) (m : Mem), m.LiveDisjoint →
      (gs.foldl (fun m (bs, a, k) => m.addGlobal bs a k) m).LiveDisjoint from
    h gs _ fun _ _ _ _ _ h => by simp at h
  intro gs
  induction gs with
  | nil => exact fun _ h => h
  | cons g gs ih =>
    obtain ⟨bs, a, k⟩ := g
    exact fun m h => ih _ (LDMono.addGlobal m bs a k h)

/-- A range inside a clear one is clear. -/
theorem _root_.Zig.Mem.addrFree_mono {m : Mem} {A n A' n' : Nat} (h : m.addrFree A n = true)
    (hA : A ≤ A') (hn : A' + n' ≤ A + n) : m.addrFree A' n' = true := by
  unfold Mem.addrFree at h ⊢
  rw [Array.all_eq_true] at h ⊢
  exact fun i hi => clearOf_shrink (h i hi) id rfl (Nat.le_refl _) hA hn

end Full
end Zig
