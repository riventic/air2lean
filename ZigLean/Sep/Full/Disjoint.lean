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

/-- Live blocks occupy disjoint address ranges (module doc). A block occupies its live bytes
`[addr + lo, addr + size)` (`Block.clearOf`, `BlockKind.mappedLo`): a thread's stack blocks may
lie below an OS mapping's first live offset (MM-19). -/
def Mem.LiveDisjoint (m : Mem) : Prop :=
  ∀ (b b' : BlockId) (blk blk' : Block), b ≠ b' → m.blocks[b]? = some blk →
    m.blocks[b']? = some blk' → blk'.live →
      blk.clearOf (blk'.addr + blk'.kind.mappedLo) (blk'.bytes.size - blk'.kind.mappedLo) = true

namespace Full

/-- Every live block ends inside the address space, below `2 ^ 63` (O-H: every placement's
`Placement.addrLimit` is at most `2 ^ 63`, and `alloc`, `mmap` and `mremap` never place a block
above it). -/
def _root_.Zig.Mem.LiveBounded (m : Mem) : Prop :=
  ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → blk.live = true →
    blk.addr + blk.bytes.size ≤ 2 ^ 63

/-- The address layout of the live blocks: apart (`Mem.LiveDisjoint`) and inside the address
space (`Mem.LiveBounded`). The third part of `Mem.FSeq`. -/
def _root_.Zig.Mem.LiveLayout (m : Mem) : Prop := m.LiveDisjoint ∧ m.LiveBounded

/-- The step from `m` to `m'` keeps `Mem.LiveDisjoint` (the pairwise part of `LDMono`). -/
def PDMono (m m' : Mem) : Prop := m.LiveDisjoint → m'.LiveDisjoint

/-- The step from `m` to `m'` keeps the live layout (`Mem.LiveLayout`). -/
def LDMono (m m' : Mem) : Prop := m.LiveLayout → m'.LiveLayout

theorem PDMono.refl (m : Mem) : PDMono m m := id

theorem PDMono.trans {m₁ m₂ m₃ : Mem} (h₁ : PDMono m₁ m₂) (h₂ : PDMono m₂ m₃) : PDMono m₁ m₃ :=
  fun h => h₂ (h₁ h)

theorem PDMono.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : PDMono m m' := by
  intro hd b b' blk blk' hbb h1 h2 hl
  rw [h] at h1 h2; exact hd b b' blk blk' hbb h1 h2 hl

theorem clearOf_iff {blk : Block} {A n : Nat} :
    blk.clearOf A n = true ↔
      (blk.live = false ∨ n = 0 ∨ blk.bytes.size ≤ blk.kind.mappedLo ∨
        A + n ≤ blk.addr + blk.kind.mappedLo ∨ blk.addr + blk.bytes.size ≤ A) := by
  simp [Block.clearOf, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, or_assoc]

/-- **Two live blocks share no byte address**: live byte `x` of a live block `b` (at or above its
first live offset) and live byte `x'` of a live block `b' ≠ b` lie at different addresses
(`Mem.LiveDisjoint`). -/
theorem _root_.Zig.Mem.LiveDisjoint.addr_ne {m : Mem} (h : m.LiveDisjoint) {b b' : BlockId}
    {blk blk' : Block} (hbb : b ≠ b') (hb : m.blocks[b]? = some blk) (hb' : m.blocks[b']? = some blk')
    (hl : blk.live = true) (hl' : blk'.live = true) {x x' : Nat} (hx : x < blk.bytes.size)
    (hx' : x' < blk'.bytes.size) (hlo : blk.kind.mappedLo ≤ x := by simp)
    (hlo' : blk'.kind.mappedLo ≤ x' := by simp) : blk.addr + x ≠ blk'.addr + x' := by
  have := clearOf_iff.mp (h b b' blk blk' hbb hb hb' hl')
  rcases this with h | h | h | h | h <;> simp_all <;> omega

/-- A block that keeps its address, does not grow (at either end) and does not come to life stays
clear of a range inside the old one. -/
theorem clearOf_shrink {blk blk' : Block} {A n A' n' : Nat} (h : blk.clearOf A n = true)
    (hl : blk'.live = true → blk.live = true) (ha : blk'.addr = blk.addr)
    (hs : blk'.bytes.size ≤ blk.bytes.size) (hA : A ≤ A') (hn : A' + n' ≤ A + n)
    (hlo : blk.kind.mappedLo ≤ blk'.kind.mappedLo := by simp) :
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

/-- Clearance between the live bytes of two live blocks is symmetric. -/
theorem clearOf_symm {blk blk' : Block} (hl : blk.live = true) (hl' : blk'.live = true)
    (h : blk.clearOf (blk'.addr + blk'.kind.mappedLo) (blk'.bytes.size - blk'.kind.mappedLo) = true) :
    blk'.clearOf (blk.addr + blk.kind.mappedLo) (blk.bytes.size - blk.kind.mappedLo) = true := by
  rw [clearOf_iff] at h ⊢
  rcases h with h | h | h | h | h
  · simp_all
  all_goals right; omega

/-- A block clear of a range is clear of the live bytes of a block in that range. -/
theorem clearOf_live {o nb : Block} {A n : Nat} (h : o.clearOf A n = true) (hA : A ≤ nb.addr + nb.kind.mappedLo)
    (hn : nb.addr + nb.bytes.size ≤ A + n) :
    o.clearOf (nb.addr + nb.kind.mappedLo) (nb.bytes.size - nb.kind.mappedLo) = true := by
  rw [clearOf_iff] at h ⊢
  by_cases hs : nb.bytes.size ≤ nb.kind.mappedLo
  · right; left; omega
  rcases h with h | h | h | h | h
  · left; exact h
  all_goals right; omega

/-- Each block of `m'` is the block of `m` with the same id, at the same address, no larger (at
either end), and not newly live. -/
theorem PDMono.shrink {m m' : Mem}
    (h : ∀ (b : BlockId) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk : Block, m.blocks[b]? = some blk ∧
      (blk'.live = true → blk.live = true) ∧ blk'.addr = blk.addr ∧
      blk'.bytes.size ≤ blk.bytes.size ∧ blk.kind.mappedLo ≤ blk'.kind.mappedLo) : PDMono m m' := by
  intro hd b b' blk₁' blk₂' hbb h1 h2 hl
  obtain ⟨blk₁, e1, l1, a1, s1, o1⟩ := h b blk₁' h1
  obtain ⟨blk₂, e2, l2, a2, s2, o2⟩ := h b' blk₂' h2
  have := hd b b' blk₁ blk₂ hbb e1 e2 (l2 hl)
  by_cases hz : blk₂'.bytes.size ≤ blk₂'.kind.mappedLo
  · rw [clearOf_iff]; right; left; omega
  exact clearOf_shrink this l1 a1 s1 (by omega) (by omega) o1

/-- Replacing block `b` by one at the same address, no larger (at either end) and not newly
live. -/
theorem PDMono.set {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : nb.live = true → blk.live = true) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size ≤ blk.bytes.size) (h : m'.blocks = m.blocks.set! b nb)
    (hlo : blk.kind.mappedLo ≤ nb.kind.mappedLo := by simp) :
    PDMono m m' := by
  refine PDMono.shrink fun b' blk' h' => ?_
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h'
  by_cases e : b = b'
  · subst e
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [hlt, if_true, Option.some.injEq] at h'
    subst h'
    exact ⟨blk, hb, hl, ha, hs, hlo⟩
  · simp only [e, if_false] at h'
    exact ⟨blk', h', id, rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Growing the live block `b` in place to at most `lo + len` bytes, live from `lo` or above,
where `[addr + lo, addr + lo + len)` is clear of every other block (`Mem.mappingRoom`). -/
theorem PDMono.grow {m m' : Mem} {b : BlockId} {blk nb : Block} {lo len : Nat}
    (hb : m.blocks[b]? = some blk) (_hl : blk.live = true) (ha : nb.addr = blk.addr)
    (_hlo : lo ≤ blk.bytes.size) (hsz : nb.bytes.size ≤ lo + len)
    (hroom : ∀ (j : BlockId) (o : Block), j ≠ b → m.blocks[j]? = some o →
      o.clearOf (blk.addr + lo) len = true)
    (h : m'.blocks = m.blocks.set! b nb) (hnlo : lo ≤ nb.kind.mappedLo) :
    PDMono m m' := by
  intro hd
  -- every other block is clear of the grown block's live bytes
  have hclear : ∀ (j : BlockId) (o : Block), j ≠ b → m.blocks[j]? = some o →
      o.clearOf (nb.addr + nb.kind.mappedLo) (nb.bytes.size - nb.kind.mappedLo) = true :=
    fun j o hj ho => clearOf_live (hroom j o hj ho) (by omega) (by omega)
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
theorem PDMono.push {m m' : Mem} {nb : Block}
    (hf : nb.live = true → m.addrFree nb.addr nb.bytes.size = true)
    (h : m'.blocks = m.blocks.push nb) : PDMono m m' := by
  intro hd b b' blk blk' hbb h1 h2 hl
  rw [h, Array.getElem?_push] at h1 h2
  have hall : ∀ (j : Nat) (x : Block), m.blocks[j]? = some x → nb.live = true →
      x.clearOf (nb.addr + nb.kind.mappedLo) (nb.bytes.size - nb.kind.mappedLo) = true := by
    intro j x hx hn
    have := hf hn
    unfold Mem.addrFree at this
    rw [Array.all_eq_true] at this
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
    exact clearOf_live (this j hi) (by omega) (by omega)
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
theorem PDMono.addGlobal (m : Mem) (bs : Array Byte) (a : Nat) (k : BlockKind) :
    PDMono m (m.addGlobal bs a k) :=
  PDMono.push (fun _ => m.globalPlace_addrFree _ _) rfl

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
    exact fun m h => ih _ (PDMono.addGlobal m bs a k h)

private theorem sum_cost (l : List Block) (s a : Nat) :
    (l.map fun b => s + b.bytes.size + a).sum = l.length * (s + a) + (l.map (·.bytes.size)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, ih]; omega

private theorem liveBounded_addGlobal (m : Mem) (bs : Array Byte) (a : Nat) (k : BlockKind)
    (T : Nat) (n : Nat) (hm : m.LiveBounded)
    (hfit : 4096 + (m.blocks.size + n + 2) * ((m.blocks.toList.map (·.bytes.size)).sum + (bs.size + a + T))
      ≤ 2 ^ 63) :
    (m.addGlobal bs a k).LiveBounded := by
  intro j blk hj hl
  rw [Mem.addGlobal_blocks, Array.getElem?_push] at hj
  split at hj
  · cases hj
    show m.globalPlace bs.size a + bs.size ≤ 2 ^ 63
    unfold Mem.globalPlace
    split
    · exact Mem.roomFor_le ‹_›
    · have hb := (m.firstFit_spec bs.size a).2.2.2
      rw [sum_cost, Array.length_toList] at hb
      generalize (m.blocks.toList.map (·.bytes.size)).sum = L at hb hfit
      generalize m.blocks.size = K at hb hfit
      have h1 : (K + 1) * (bs.size + a) ≤ (K + 1) * (L + (bs.size + a + T)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (K + 2) * (L + (bs.size + a + T)) ≤ (K + n + 2) * (L + (bs.size + a + T)) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h1 h2
      omega
  · exact hm j blk hj hl

private theorem liveBounded_fold : ∀ (gs : List (Array Byte × Nat × BlockKind)) (m : Mem),
    m.LiveBounded →
    4096 + (m.blocks.size + gs.length + 1) *
      ((m.blocks.toList.map (·.bytes.size)).sum + (gs.map fun g => g.1.size + g.2.1).sum) ≤ 2 ^ 63 →
    (gs.foldl (fun m (bs, a, k) => m.addGlobal bs a k) m).LiveBounded
  | [], _, hm, _ => hm
  | (bs, a, k) :: gs, m, hm, hfit => by
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.sum_cons] at hfit ⊢
    have hfit' : 4096 + (m.blocks.size + gs.length + 2) *
        ((m.blocks.toList.map (·.bytes.size)).sum + (bs.size + a + (gs.map fun g => g.1.size + g.2.1).sum))
        ≤ 2 ^ 63 := by
      rwa [show m.blocks.size + (gs.length + 1) + 1 = m.blocks.size + gs.length + 2 by omega] at hfit
    refine liveBounded_fold gs _ (liveBounded_addGlobal m bs a k _ _ hm hfit') ?_
    rw [Mem.addGlobal_blocks, Array.size_push, Array.toList_push, List.map_append, List.sum_append,
      show m.blocks.size + 1 + gs.length + 1 = m.blocks.size + gs.length + 2 by omega]
    refine Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _) hfit'
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- **Every global ends inside the address space** at program start, under every placement, if
the globals fit (`Mem.GlobalsFit`): a placed global ends below `Placement.addrLimit`, any other
one is packed by the first fit (`Mem.globalPlace`). With `Mem.ofGlobals_liveDisjoint`, the
memory at program start has the layout of `Mem.FSeq` (`Mem.LiveLayout`). -/
theorem _root_.Zig.Mem.ofGlobals_liveBounded (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) (h : Mem.GlobalsFit gs) :
    (Mem.ofGlobals σ gs).LiveBounded :=
  liveBounded_fold gs _ (fun _ _ hb _ => by simp at hb) (by simpa [Mem.GlobalsFit] using h)

theorem _root_.Zig.Mem.ofGlobals_liveLayout (σ : Placement)
    (gs : List (Array Byte × Nat × BlockKind)) (h : Mem.GlobalsFit gs) :
    (Mem.ofGlobals σ gs).LiveLayout :=
  ⟨Mem.ofGlobals_liveDisjoint σ gs, Mem.ofGlobals_liveBounded σ gs h⟩

/-- A range inside a clear one is clear. -/
theorem _root_.Zig.Mem.addrFree_mono {m : Mem} {A n A' n' : Nat} (h : m.addrFree A n = true)
    (hA : A ≤ A') (hn : A' + n' ≤ A + n) : m.addrFree A' n' = true := by
  unfold Mem.addrFree at h ⊢
  rw [Array.all_eq_true] at h ⊢
  exact fun i hi => clearOf_shrink (h i hi) id rfl (Nat.le_refl _) hA hn


/-! ### The live layout: the pairwise part and the bound together -/

theorem LDMono.refl (m : Mem) : LDMono m m := id

theorem LDMono.trans {m₁ m₂ m₃ : Mem} (h₁ : LDMono m₁ m₂) (h₂ : LDMono m₂ m₃) : LDMono m₁ m₃ :=
  fun h => h₂ (h₁ h)

theorem LDMono.of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) : LDMono m m' :=
  fun hd => ⟨PDMono.of_blocks h hd.1, fun b blk hb hl => hd.2 b blk (by rw [← h]; exact hb) hl⟩

theorem LDMono.shrink {m m' : Mem}
    (h : ∀ (b : BlockId) (blk' : Block), m'.blocks[b]? = some blk' → ∃ blk : Block, m.blocks[b]? = some blk ∧
      (blk'.live = true → blk.live = true) ∧ blk'.addr = blk.addr ∧
      blk'.bytes.size ≤ blk.bytes.size ∧ blk.kind.mappedLo ≤ blk'.kind.mappedLo) :
    LDMono m m' := fun hd => by
  refine ⟨PDMono.shrink h hd.1, fun b blk' hb hl => ?_⟩
  obtain ⟨blk, e, l, a, sz, -⟩ := h b blk' hb
  have := hd.2 b blk e (l hl)
  omega

theorem LDMono.set {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (hl : nb.live = true → blk.live = true) (ha : nb.addr = blk.addr)
    (hs : nb.bytes.size ≤ blk.bytes.size) (h : m'.blocks = m.blocks.set! b nb)
    (hlo : blk.kind.mappedLo ≤ nb.kind.mappedLo := by simp) :
    LDMono m m' := by
  refine LDMono.shrink fun b' blk' h' => ?_
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h'
  by_cases e : b = b'
  · subst e
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [hlt, if_true, Option.some.injEq] at h'
    subst h'
    exact ⟨blk, hb, hl, ha, hs, hlo⟩
  · simp only [e, if_false] at h'
    exact ⟨blk', h', id, rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Growing the live block `b` in place, inside the address space (`hbnd`). -/
theorem LDMono.grow {m m' : Mem} {b : BlockId} {blk nb : Block} {lo len : Nat}
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (ha : nb.addr = blk.addr)
    (hlo : lo ≤ blk.bytes.size) (hsz : nb.bytes.size ≤ lo + len)
    (hroom : ∀ (j : BlockId) (o : Block), j ≠ b → m.blocks[j]? = some o →
      o.clearOf (blk.addr + lo) len = true)
    (hbnd : blk.addr + lo + len ≤ 2 ^ 63)
    (h : m'.blocks = m.blocks.set! b nb) (hnlo : lo ≤ nb.kind.mappedLo) : LDMono m m' := fun hd => by
  refine ⟨PDMono.grow hb hl ha hlo hsz hroom h hnlo hd.1, fun j o hj hlj => ?_⟩
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hj
  by_cases e : b = j
  · subst e
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    simp only [hlt, if_true, Option.some.injEq] at hj
    subst hj; omega
  · simp only [e, if_false] at hj
    exact hd.2 j o hj hlj

/-- Pushing a block that is dead, or clear of every live block (`Mem.addrFree`) and inside the
address space. -/
theorem LDMono.push {m m' : Mem} {nb : Block}
    (hf : nb.live = true → m.addrFree nb.addr nb.bytes.size = true)
    (hbnd : nb.live = true → nb.addr + nb.bytes.size ≤ 2 ^ 63)
    (h : m'.blocks = m.blocks.push nb) : LDMono m m' := fun hd => by
  refine ⟨PDMono.push hf h hd.1, fun j o hj hlj => ?_⟩
  rw [h, Array.getElem?_push] at hj
  split at hj
  · cases hj; exact hbnd hlj
  · exact hd.2 j o hj hlj

/-- A block that `alloc` makes with room (`Mem.allocOk`) keeps the live layout. -/
theorem LDMono.alloc {m m' : Mem} {kind : BlockKind} {size align : Nat} {nb : Block}
    (hroom : m.allocOk kind size align = true) (ha : nb.addr = m.allocAddr kind size align)
    (hs : nb.bytes.size = size) (h : m'.blocks = m.blocks.push nb) : LDMono m m' :=
  LDMono.push (fun _ => by rw [ha, hs]; exact (Mem.allocOk_fit hroom).2)
    (fun _ => by rw [ha, hs]; exact Mem.allocOk_le hroom) h


end Full
end Zig
