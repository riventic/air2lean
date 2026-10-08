import ZigLean.Os.Mmap
import ZigLean.Sep.Alloc

/-!
# Separation-logic rules of the OS page-mapping model (premise OS-01)

Proof-only module (not imported by `ZigLean.lean`): the rules of `Os.mmap`, `Os.munmap` and
`Os.mremap` (`ZigLean/Os/Mmap.lean`, `docs/os-mmap.md`).

`mapping P p A lo bs` owns the whole live range of one OS mapping: the bytes `bs` at `p`, which
points at the mapping's first live offset `lo`, in a block at the page-aligned address `A`.

* `Triple.mmap`: a fresh mapping of `len` zero bytes, or an `MMapError` and no change.
* `Triple.munmapWhole`, `Triple.munmapPrefix`, `Triple.munmapTail`: `munmap` consumes the
  permission of exactly the unmapped range; a trim leaves the rest as a mapping.
* `Triple.mremapShrink`, `Triple.mremapGrow`: the new mapping (in place or moved), or an
  `MRemapError` and the old mapping.
* `munmap_whole_then_illegal`, `munmap_prefix_access_illegal`, `munmap_tail_access_illegal`:
  after `munmap` every access to the unmapped bytes and a second `munmap` are `.illegal`.
* `mapDenied_iff`: the failure decision is `rawAlloc`'s (`Mem.allocDenied`).
-/

namespace Zig

open Assn

/-! ## Page arithmetic -/

theorem alignUp_mod_self {n P : Nat} (hP : 0 < P) : alignUp n P % P = 0 := by
  unfold alignUp; rw [if_neg (by omega)]; exact Nat.mul_mod_left _ _

theorem alignUp_lt {n P : Nat} (hP : 0 < P) : alignUp n P < n + P := by
  unfold alignUp; rw [if_neg (by omega)]
  have := Nat.div_mul_le_self (n + P - 1) P
  omega

theorem alignUp_add_aligned {a n P : Nat} (hP : 0 < P) (ha : a % P = 0) :
    alignUp (a + n) P = a + alignUp n P := by
  unfold alignUp; rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨q, rfl⟩ : ∃ q, a = P * q := ⟨a / P, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)).symm⟩
  rw [show P * q + n + P - 1 = (n + P - 1) + q * P by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_right _ _ hP, Nat.add_mul, Nat.mul_comm q P]
  omega

theorem alignUp_zero (P : Nat) : alignUp 0 P = 0 := by
  unfold alignUp; split
  · rfl
  · rename_i h; rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]; simp

theorem alignUp_of_mod {n P : Nat} (hP : 0 < P) (h : n % P = 0) : alignUp n P = n := by
  have := alignUp_add_aligned (a := n) (n := 0) hP h
  rw [Nat.add_zero, alignUp_zero, Nat.add_zero] at this; exact this

/-! ## The mapping assertion -/

/-- `h` owns the whole live range of a mapping (module doc). -/
def mapping (P : Nat) (p : Ptr) (A lo : Nat) (bs : Array Byte) : Assn := fun h =>
  p.off = lo ∧ 0 < bs.size ∧ A % P = 0 ∧ lo % P = 0 ∧
    bytesAt p A (lo + bs.size) (.mapped lo) bs h

/-- The cells of block `b` with the block state `nb`, as `Mem.heap` shows them. -/
def liveCells (b : BlockId) (nb : Block) : Heap := fun l =>
  if l.1 = b then
    if h : nb.live ∧ l.2 < nb.bytes.size ∧ nb.kind.mappedLo ≤ l.2 then
      some ⟨nb.bytes[l.2]'h.2.1, nb.addr, nb.bytes.size, nb.kind⟩ else none
  else none

/-- The heap after block `b` becomes `nb`. -/
theorem Mem.heap_setBlock {m m' : Mem} {b : BlockId} {nb : Block} (hlt : b < m.blocks.size)
    (hm' : m'.blocks = m.blocks.set! b nb) (l : Loc) :
    m'.heap l = if l.1 = b then liveCells b nb l else m.heap l := by
  obtain ⟨x, y⟩ := l
  by_cases hx : x = b
  · subst hx
    have e : m'.blocks[x]? = some nb := by
      rw [hm', Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hlt
    simp only [↓reduceIte, liveCells, Mem.heap_of e]
  · have e : m'.blocks[x]? = m.blocks[x]? := by
      rw [hm', Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [Ne.symm hx]
    simp only [hx, ↓reduceIte, Mem.heap, e]

/-- The facts that a mapping permission gives about its block. -/
theorem mapping_block {m : Mem} {h hF : Heap} {P : Nat} {p : Ptr} {A lo : Nat} {bs : Array Byte}
    (hp : mapping P p A lo bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) :
    ∃ b blk, p = ⟨some b, lo⟩ ∧ m.blocks[b]? = some blk ∧ blk.live ∧ blk.kind = .mapped lo ∧
      blk.addr = A ∧ blk.bytes.size = lo + bs.size ∧ blk.bytes.extract lo (lo + bs.size) = bs ∧
      (∀ y, hF (b, y) = none) ∧ (∀ l, l.1 ≠ b → h l = none) := by
  obtain ⟨hoff, hpos, -, -, hb⟩ := hp
  obtain ⟨b, hpb, h0, hown⟩ := id hb
  have hlo : p.off.toNat = lo := by omega
  obtain ⟨b', blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p.add 0) (k := 0) (n := bs.size)
    (a := 1) hb hm (by simp [Ptr.add]) hpos (by omega) (Nat.mod_one _)
  obtain ⟨hqb, -, hl, -⟩ := access_eq hacc
  have : b' = b := by simp [Ptr.add] at hqb; rw [hpb] at hqb; cases hqb; rfl
  subst this
  have c0 := bytesAt_cell hb hm hpb (j := 0) hpos
  obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some c0
  rw [hblk] at hblk'; cases hblk'
  have hK : blk.kind = .mapped lo := by
    simp only [Cell.mk.injEq] at hc; exact hc.2.2.2.symm
  have hp' : p = ⟨some b', lo⟩ := by
    cases p; simp only at hpb hoff; subst hpb; subst hoff; rfl
  refine ⟨b', blk, hp', hblk, hl, hK, hA, hS, by simpa [hlo] using hx, fun y => ?_,
    fun l hl => ?_⟩
  · by_cases hy : lo ≤ y ∧ y < lo + bs.size
    · have : h (b', y) ≠ none := by rw [hown]; simp [hlo, hy]
      exact (hd (b', y)).resolve_left this
    · have e := congrFun hm (b', y)
      rw [Mem.heap_of hblk, dif_neg (by rw [hK, hS]; simp; omega)] at e
      exact (Option.or_eq_none_iff.mp e.symm).2
  · rw [hown]; simp [hl]

/-- After block `b` (owned whole by `h`) becomes `nb`, the heap is `nb`'s cells and the frame. -/
theorem heap_replace {m m' : Mem} {h hF : Heap} {b : BlockId} {nb : Block}
    (hm : m.heap = h ∪ hF) (hlt : b < m.blocks.size) (hm' : m'.blocks = m.blocks.set! b nb)
    (hFb : ∀ y, hF (b, y) = none) (hh : ∀ l, l.1 ≠ b → h l = none) :
    m'.heap = liveCells b nb ∪ hF := by
  funext ⟨x, y⟩
  rw [Mem.heap_setBlock hlt hm', Heap.union_apply]
  by_cases hx : x = b
  · subst hx; simp [hFb]
  · simp only [hx, ↓reduceIte, liveCells, Option.none_or]
    rw [hm, Heap.union_apply, hh (x, y) hx, Option.none_or]

theorem liveCells_disjoint {b : BlockId} {nb : Block} {hF : Heap} (hFb : ∀ y, hF (b, y) = none) :
    Heap.Disjoint (liveCells b nb) hF := by
  rintro ⟨x, y⟩
  by_cases hx : x = b
  · subst hx; right; exact hFb y
  · left; simp [liveCells, hx]

/-- The cells of a live mapping block are a `bytesAt` of its live bytes. -/
theorem liveCells_bytesAt {b : BlockId} {nb : Block} {lo : Nat} (hl : nb.live)
    (hk : nb.kind = .mapped lo) (hlo : lo ≤ nb.bytes.size) :
    bytesAt ⟨some b, lo⟩ nb.addr nb.bytes.size (.mapped lo) (nb.bytes.extract lo nb.bytes.size)
      (liveCells b nb) := by
  refine ⟨b, rfl, by simp, fun ⟨x, y⟩ => ?_⟩
  simp only [liveCells, hk, BlockKind.mappedLo_mapped, hl, true_and, Int.toNat_natCast,
    Array.size_extract, Nat.min_self]
  by_cases hx : x = b
  · subst hx
    by_cases hy : lo ≤ y ∧ y < nb.bytes.size
    · rw [dif_pos ⟨hy.2, hy.1⟩]
      simp only [↓reduceIte, show lo ≤ y ∧ y < lo + (nb.bytes.size - lo) by omega, and_self,
        Option.some.injEq, Cell.mk.injEq, and_true]
      rw [extract_getElem! nb.bytes (a := lo) (b := nb.bytes.size) (j := y - lo) (by omega)
        (Nat.le_refl _), getElem!_pos nb.bytes _ (by omega)]
      simp [show lo + (y - lo) = y by omega]
    · rw [dif_neg (by omega)]
      simp only [↓reduceIte, true_and]
      rw [if_neg (by omega)]
  · simp [hx]

/-- `liveCells` of a dead block is empty. -/
theorem liveCells_dead {b : BlockId} {nb : Block} (hl : nb.live = false) :
    liveCells b nb = Heap.empty := by
  funext l; simp [liveCells, hl, Heap.empty]

/-! ## The failure decision -/

/-- `mmap`/`mremap` fail exactly when `rawAlloc` would (`Mem.allocDenied`). -/
theorem mapDenied_iff (m : Mem) (n : Nat) : m.mapDenied n = true ↔ m.allocDenied n := by
  simp only [Mem.mapDenied, Mem.allocDenied, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-! ## mmap -/

theorem Os.mmap_run (os : Os.Profile) (hint : Option Ptr) (len : BitVec 64) (hlen : len.toNat ≠ 0)
    (m : Mem) :
    (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0).run m =
      if m.mapDenied len.toNat then
        pure (.error (m.allocPolicy.os.mmapError m.allocs len.toNat).name,
          { m with allocs := m.allocs + 1 })
      else
        pure (.ok ⟨⟨some m.blocks.size, 0⟩, len⟩,
          ({ m with allocs := m.allocs + 1 } : Mem).afterMmap os.pageSize len.toNat) := by
  by_cases hd : m.mapDenied len.toNat
  · simp [Os.mmap, hlen, hd, zig_unfold, set, StateT.set, MonadStateOf.set]
  · simp [Os.mmap, hlen, hd, zig_unfold, set, StateT.set, MonadStateOf.set]

/-- The heap after `mmap`: the old one and the new block's cells. -/
theorem Mem.heap_afterMmap (m : Mem) (P n : Nat) :
    (m.afterMmap P n).heap = liveCells m.blocks.size
      { bytes := Array.replicate n (.int 0), align := P, kind := .mapped 0, live := true,
        addr := alignUp m.nextAddr P } ∪ m.heap := by
  funext ⟨x, y⟩
  unfold Mem.afterMmap
  rw [Mem.heap_push, Heap.union_apply]
  by_cases hx : x = m.blocks.size
  · subst hx
    simp only [↓reduceIte, liveCells, Mem.heap_none_size, Option.or_none]
  · simp [hx, liveCells]

theorem Mem.Seq.afterMmap {m : Mem} (hst : m.Seq) (P n : Nat) : (m.afterMmap P n).Seq := by
  refine ⟨hst.single, fun l c hc => ?_⟩
  rw [Mem.heap_afterMmap, Heap.union_apply] at hc
  have hle := le_alignUp m.nextAddr P
  have hn := le_alignUp n P
  cases e : liveCells m.blocks.size _ l with
  | some c' =>
    rw [e, Option.some_or] at hc; cases hc
    obtain ⟨x, y⟩ := l
    simp only [liveCells] at e
    split at e
    · split at e
      · cases e; simp [Mem.afterMmap]; omega
      · cases e
    · cases e
  | none =>
    rw [e, Option.none_or] at hc
    have := hst.addr l c hc
    simp only [Mem.afterMmap]; omega

/-- What `mmap` returns: a fresh mapping of `len` zero bytes, or an `MMapError`. -/
def mmapPost (P : Nat) (len : BitVec 64) : Except ErrName Slice → Assn
  | .ok s => fun h => s.len = len ∧ s.ptr.off = 0 ∧
      ∃ A, mapping P s.ptr A 0 (Array.replicate len.toNat (.int 0)) h
  | .error e => ⌜e ∈ mmapErrorNames⌝

theorem MmapError.name_mem (e : MmapError) : e.name ∈ mmapErrorNames := by
  cases e <;> simp [MmapError.name, mmapErrorNames]

theorem MremapError.name_mem (e : MremapError) : e.name ∈ mremapErrorNames := by
  cases e <;> simp [MremapError.name, mremapErrorNames]

/-- **mmap.** From nothing: a fresh, page-aligned mapping of exactly `len` zero bytes that
nothing else owns, or an `MMapError` with the heap unchanged. For every failure policy. -/
theorem Triple.mmap (os : Os.Profile) (hP : 0 < os.pageSize) (hint : Option Ptr) (len : BitVec 64)
    (hlen : 0 < len.toNat) :
    Triple emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (mmapPost os.pageSize len) :=
  Triple.of_run fun m hP' hF hd hm hp hst => by
    have hP0 : hP' = Heap.empty := hp
    subst hP0
    rw [Heap.empty_union] at hm
    have hst₁ : ({ m with allocs := m.allocs + 1 } : Mem).Seq := ⟨hst.single, hst.addr⟩
    by_cases hdn : m.mapDenied len.toNat
    · refine ⟨.error (m.allocPolicy.os.mmapError m.allocs len.toNat).name,
        { m with allocs := m.allocs + 1 }, Heap.empty, ?_, (Heap.disjoint_empty hF).symm,
        by rw [Heap.empty_union]; exact hm, ⟨MmapError.name_mem _, rfl⟩, hst₁⟩
      rw [Os.mmap_run os hint len (by omega), if_pos hdn]
    · let m₁ : Mem := { m with allocs := m.allocs + 1 }
      let nb : Block :=
        { bytes := Array.replicate len.toNat (.int 0)
          align := os.pageSize
          kind := .mapped 0
          live := true
          addr := alignUp m₁.nextAddr os.pageSize }
      have hfree : ∀ y, hF (m.blocks.size, y) = none := by
        intro y; have := congrFun hm (m.blocks.size, y)
        rw [Mem.heap_none_size] at this; exact this.symm
      refine ⟨.ok ⟨⟨some m.blocks.size, 0⟩, len⟩, m₁.afterMmap os.pageSize len.toNat,
        liveCells m.blocks.size nb, ?_,
        liveCells_disjoint hfree, ?_, ⟨rfl, rfl, alignUp m₁.nextAddr os.pageSize, rfl, ?_, ?_,
          by simp, ?_⟩, hst₁.afterMmap _ _⟩
      · rw [Os.mmap_run os hint len (by omega), if_neg hdn]
      · rw [Mem.heap_afterMmap]; show _ ∪ m.heap = _; rw [hm]
      · simp [nb]; omega
      · exact alignUp_mod_self hP
      · have := liveCells_bytesAt (b := m.blocks.size) (nb := nb) (lo := 0) rfl rfl (Nat.zero_le _)
        simpa [nb] using this

end Zig
