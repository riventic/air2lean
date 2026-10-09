import ZigLean.Sep.Triple

/-!
# Blocks: `alloc` and `free`

`alloc` gives a new block that nothing else owns: its bytes are undefined. `free` needs the
whole block (every byte, from offset 0) and takes it away. A stack local whose address escapes
(`Zig.allocStack` at function entry, `Zig.free` at the return) uses both.
-/

namespace Zig

open Assn

/-- The heap after a new block `nb` at index `m.blocks.size`. -/
theorem Mem.heap_push (m : Mem) (nb : Block) (a : Nat) (l : Loc) :
    ({ m with blocks := m.blocks.push nb, nextAddr := a } : Mem).heap l =
      if l.1 = m.blocks.size then
        (if h : nb.live ∧ l.2 < nb.bytes.size then some ⟨nb.bytes[l.2], nb.addr, nb.bytes.size, nb.kind⟩
         else none)
      else m.heap l := by
  obtain ⟨x, y⟩ := l
  by_cases hx : x = m.blocks.size
  · subst hx; simp [Mem.heap]
  · simp only [Mem.heap, Array.getElem?_push, hx, ↓reduceIte]

theorem Mem.heap_none_size (m : Mem) (y : Nat) : m.heap (m.blocks.size, y) = none := by
  simp [Mem.heap]

/-- `m'` is `m` with other blocks: the threads' part of the memory is the same. -/
structure Mem.SameThreads (m m' : Mem) : Prop where
  current : m'.current = m.current
  clocks : m'.clocks = m.clocks
  threads : m'.threads = m.threads
  footprint : m'.footprint = m.footprint
  atomics : m'.atomics = m.atomics
  seen : m'.seen = m.seen
  nextMsg : m'.nextMsg = m.nextMsg
  waiters : m'.waiters = m.waiters
  woken : m'.woken = m.woken
  groups : m'.groups = m.groups

theorem Mem.SameThreads.singleThread {m m' : Mem} (h : m.SameThreads m') (hs : m.SingleThread) :
    m'.SingleThread := by
  unfold Mem.SingleThread; rw [h.current, h.clocks, h.footprint]; exact hs

/-- `alloc` adds the block `m.blocks.size`, of `size` undefined bytes, that nothing owned. -/
theorem alloc_run_core {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (kind : BlockKind) (size align : Nat) (ha : 0 < align) :
    ∃ p m' h', (alloc kind size align).run m = pure (p, m') ∧ p.off = 0 ∧
      p.block = some m.blocks.size ∧ m'.blocks.size = m.blocks.size + 1 ∧
      Heap.Disjoint (h ∪ h') hF ∧ m'.heap = (h ∪ h') ∪ hF ∧ Heap.Disjoint h h' ∧ m.SameThreads m' ∧
      ∃ A, A = alignUp m.nextAddr align ∧ A % align = 0 ∧
        bytesAt p A size kind (Array.replicate size .undef) h' := by
  let A := alignUp m.nextAddr align
  let nb : Block := { bytes := Array.replicate size .undef, align, kind, live := true, addr := A }
  let h' : Heap := fun l =>
    if l.1 = m.blocks.size ∧ 0 ≤ l.2 ∧ l.2 < 0 + size then some ⟨.undef, A, size, kind⟩ else none
  -- Every location of the new block is free in the old memory.
  have hfree : ∀ y, h (m.blocks.size, y) = none ∧ hF (m.blocks.size, y) = none := by
    intro y
    have := congrFun hm (m.blocks.size, y)
    rw [Mem.heap_none_size] at this
    exact Option.or_eq_none_iff.mp this.symm
  have hh' : ∀ x y, x ≠ m.blocks.size → h' (x, y) = none := by
    intro x y hx; simp [h', hx]
  refine ⟨⟨some m.blocks.size, 0⟩, _, h', rfl, rfl, rfl, by simp, ?_, ?_, ?_, ?_, A, rfl, ?_, ?_⟩
  · refine Heap.disjoint_union_left.mpr ⟨hd, fun ⟨x, y⟩ => ?_⟩
    by_cases hx : x = m.blocks.size
    · subst hx; right; exact (hfree y).2
    · left; exact hh' x y hx
  · funext ⟨x, y⟩
    rw [Mem.heap_push]
    by_cases hx : x = m.blocks.size
    · subst hx
      obtain ⟨e₁, e₂⟩ := hfree y
      by_cases hy : y < size
      · simp [h', A, e₁, hy]
      · simp [h', e₁, e₂, hy]
    · simp [hh' x y hx, hx, hm]
  · intro ⟨x, y⟩
    by_cases hx : x = m.blocks.size
    · subst hx; left; exact (hfree y).1
    · right; exact hh' x y hx
  · -- `alloc` only changes `blocks` and `nextAddr`.
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [A, alignUp, Nat.ne_of_gt ha, ↓reduceIte, Nat.mul_mod_left]
  · refine ⟨m.blocks.size, rfl, Int.le_refl 0, fun l => ?_⟩
    simp only [h', Int.toNat_zero, Array.size_replicate]
    split <;> simp_all

/-- The memory after `alloc`: the new block at `alignUp m.nextAddr align`. -/
def Mem.afterAlloc (m : Mem) (kind : BlockKind) (size align : Nat) : Mem :=
  { m with
    blocks := m.blocks.push
      { bytes := Array.replicate size .undef, align, kind, live := true,
        addr := alignUp m.nextAddr align }
    nextAddr := alignUp m.nextAddr align + size + 1 }

theorem alloc_run_eq (m : Mem) (kind : BlockKind) (size align : Nat) :
    (alloc kind size align).run m = pure (⟨some m.blocks.size, 0⟩, m.afterAlloc kind size align) :=
  rfl

theorem Mem.Seq.alloc {m : Mem} (hst : m.Seq) (kind : BlockKind) (size align : Nat) :
    (m.afterAlloc kind size align).Seq := by
  refine ⟨hst.single, fun l c hc => ?_⟩
  have hle := le_alignUp m.nextAddr align
  unfold Mem.afterAlloc at hc ⊢
  rw [Mem.heap_push] at hc
  split at hc
  · split at hc
    · cases hc; simp
    · cases hc
  · have := hst.addr l c hc
    simp only; omega

theorem alloc_run {m : Mem} {h hF : Heap} (hd : Heap.Disjoint h hF) (hm : m.heap = h ∪ hF)
    (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hst : m.Seq) :
    ∃ p m' h', (alloc kind size align).run m = pure (p, m') ∧ p.off = 0 ∧
      Heap.Disjoint (h ∪ h') hF ∧ m'.heap = (h ∪ h') ∪ hF ∧ Heap.Disjoint h h' ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size + 1 ∧
      ∃ A, A % align = 0 ∧ bytesAt p A size kind (Array.replicate size .undef) h' ∧
        ∀ l c, m.heap l = some c → c.addr + c.size < A := by
  obtain ⟨p, m', h', hr, h0, -, -, hd', hm', hdd, -, A, hAe, hA, hb⟩ :=
    alloc_run_core hd hm kind size align ha
  have e := hr.symm.trans (alloc_run_eq m kind size align)
  simp only [pure, ExceptT.pure, ExceptT.mk] at e
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj (Option.some.inj e))
  refine ⟨p, _, h', hr, h0, hd', hm', hdd, hst.alloc kind size align, by simp [Mem.afterAlloc], A,
    hA, hb, fun l c hc => ?_⟩
  have := hst.addr l c hc
  have := le_alignUp m.nextAddr align
  omega

/-- `free` of a whole block (from offset 0, all `S > 0` bytes owned, its end races with no
access: `Mem.freeRaces`) removes it from the heap. -/
theorem free_run_core {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hnr : ∀ b, p.block = some b → m.freeRaces b S = false) :
    ∃ m', (free p).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧
      m'.blocks.size = m.blocks.size ∧ m.SameThreads m' ∧ m'.nextAddr = m.nextAddr := by
  obtain ⟨b, hpb, -, hown⟩ := id hb
  have c0 := bytesAt_cell hb hm hpb (j := 0) (by omega)
  obtain ⟨blk, hblk, hl, _, hc⟩ := Mem.heap_some c0
  simp only [Cell.mk.injEq] at hc
  have hsz : blk.bytes.size = S := hc.2.2.1.symm
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  refine ⟨{ m with blocks := m.blocks.set! b { blk with live := false } }, ?_, ?_, by simp,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp [free, hpb, hblk, hl, h0, hsz, hnr b hpb, zig_unfold, set, StateT.set, MonadStateOf.set]
  · funext ⟨x, y⟩
    have hmx := congrFun hm (x, y)
    simp only [Heap.union_apply, Heap.empty, Option.none_or] at hmx ⊢
    rw [hown] at hmx
    by_cases hx : x = b
    · subst hx
      have e : (m.blocks.set! x { blk with live := false })[x]? = some { blk with live := false } := by
        rw [Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hlt
      simp only [Mem.heap, e]
      simp only [Bool.false_eq_true, false_and, dite_false]
      -- The owner has every byte of the block, so the frame has none.
      by_cases hy : y < S
      · have : h (x, y) ≠ none := by rw [hown]; simp [h0, hS, hy]
        exact ((hd (x, y)).resolve_left this).symm
      · have hn : m.heap (x, y) = none := by simp [Mem.heap, hblk, hsz, hy]
        rw [hn, h0] at hmx
        simp [hS, hy] at hmx
        exact hmx
    · have e : (m.blocks.set! b { blk with live := false })[x]? = m.blocks[x]? := by
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [Ne.symm hx]
      simp only [hx, false_and, ↓reduceIte, Option.none_or] at hmx
      simp only [Mem.heap, e] at hmx ⊢
      exact hmx

theorem free_run {m : Mem} {h hF : Heap} {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    (hb : bytesAt p A S K bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) (hst : m.Seq) :
    ∃ m', (free p).run m = pure ((), m') ∧ m'.heap = Heap.empty ∪ hF ∧ m'.Seq ∧
      m'.blocks.size = m.blocks.size := by
  obtain ⟨m', hr, hm', hsz, hs, hn⟩ := free_run_core hb hm hd hS h0 hpos
    fun b _ => freeRaces_of_singleThread hst.single b S
  refine ⟨m', hr, hm', ⟨hs.singleThread hst.single, hst.addr.of_heap hn fun l c hc => ?_⟩, hsz⟩
  refine ⟨l, c, ?_, rfl, rfl⟩
  rw [hm', Heap.union_apply, Heap.empty, Option.none_or] at hc
  rw [hm, Heap.union_apply]
  rcases hd l with h1 | h1
  · rw [h1, Option.none_or]; exact hc
  · rw [h1] at hc; cases hc

theorem Triple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align) :
    Triple emp (alloc kind size align) (fun p => Assn.ex fun A =>
      ⌜p.off = 0 ∧ A % align = 0⌝ ∗ bytesAt p A size kind (Array.replicate size .undef)) :=
  Triple.of_run fun _ hP _ hd hm hp hst => by
    obtain ⟨p, m', h', hr, h0, hd', hm', -, hst', -, A, hA, hb, -⟩ := alloc_run hd hm kind size align ha hst
    have hP0 : hP = Heap.empty := hp
    subst hP0
    simp only [Heap.empty_union] at hd' hm'
    refine ⟨p, m', h', hr, hd', hm', ?_, hst'⟩
    exact ⟨A, sep_lift.mpr ⟨⟨h0, hA⟩, hb⟩⟩

theorem Triple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hS : bs.size = S)
    (h0 : p.off = 0)
    (hpos : 0 < S) : Triple (bytesAt p A S K bs) (free p) (fun _ => emp) :=
  Triple.of_run fun _ _ hF hd hm hb hst => by
    obtain ⟨m', hr, hm', hst', -⟩ := free_run hb hm hd hS h0 hpos hst
    exact ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty hF).symm, hm', rfl, hst'⟩

end Zig
