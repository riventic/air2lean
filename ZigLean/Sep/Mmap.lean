import ZigLean.Os.Mmap
import ZigLean.Sep.Alloc
import ZigLean.Sep.Total

/-!
# Separation-logic rules of the OS page-mapping model (premise OSM-01)

Proof-only module (not imported by `ZigLean.lean`): the rules of `Os.mmap`, `Os.munmap` and
`Os.mremap` (`ZigLean/Os/Mmap.lean`, `docs/os-mmap.md`).

`mapping P p A lo bs` owns the whole live range of one OS mapping: the bytes `bs` at `p`, which
points at the mapping's first live offset `lo`, in a block at the page-aligned address `A`.

Every rule is a total triple (the OS calls return).

* `TotalTriple.mmap`: a fresh mapping of `len` zero bytes, or `error.OutOfMemory` and no change.
* `TotalTriple.munmapWhole`, `TotalTriple.munmapPrefix`, `TotalTriple.munmapTail`: `munmap`
  consumes the permission of exactly the unmapped range; a trim leaves the rest as a mapping.
* `TotalTriple.mremapShrink`, `TotalTriple.mremapGrow`: the new mapping (in place or moved), or
  an `error.OutOfMemory` and the old mapping.
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

theorem Os.mmap_run (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (hlen : len.toNat ≠ 0)
    (m : Mem) :
    (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0).run m =
      if m.mapDenied len.toNat then
        pure (.error "OutOfMemory", { m with allocs := m.allocs + 1 })
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
        addr := m.mapAddr P n } ∪ m.heap := by
  funext ⟨x, y⟩
  unfold Mem.afterMmap
  rw [Mem.heap_push, Heap.union_apply]
  by_cases hx : x = m.blocks.size
  · subst hx
    simp only [↓reduceIte, liveCells, Mem.heap_none_size, Option.or_none]
  · simp [hx, liveCells]

theorem Mem.Seq.afterMmap {m : Mem} (hst : m.Seq) (P n : Nat) : (m.afterMmap P n).Seq :=
  ⟨hst.single⟩

/-- What `mmap` returns: a fresh mapping of `len` zero bytes, or an `MMapError`. -/
def mmapPost (P : Nat) (len : BitVec 64) : Except ErrName Slice → Assn
  | .ok s => fun h => s.len = len ∧ s.ptr.off = 0 ∧
      ∃ A, mapping P s.ptr A 0 (Array.replicate len.toNat (.int 0)) h
  | .error e => ⌜e = "OutOfMemory"⌝

/-- **mmap.** From nothing: a fresh, page-aligned mapping of exactly `len` zero bytes that
nothing else owns, or an `MMapError` with the heap unchanged. For every failure policy. -/
theorem TotalTriple.mmap (os : Os.Target) (hint : Option Ptr) (len : BitVec 64)
    (hlen : 0 < len.toNat) :
    TotalTriple emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (mmapPost os.pageSize len) :=
  TotalTriple.of_run fun m hP' hF hd hm hp hst => by
    have hP := os.pageSize_pos
    have hP0 : hP' = Heap.empty := hp
    subst hP0
    rw [Heap.empty_union] at hm
    have hst₁ : ({ m with allocs := m.allocs + 1 } : Mem).Seq := ⟨hst.single⟩
    by_cases hdn : m.mapDenied len.toNat
    · refine ⟨.error "OutOfMemory",
        { m with allocs := m.allocs + 1 }, Heap.empty, ?_, (Heap.disjoint_empty hF).symm,
        by rw [Heap.empty_union]; exact hm, ⟨rfl, rfl⟩, hst₁⟩
      rw [Os.mmap_run os hint len (by omega), if_pos hdn]
    · let m₁ : Mem := { m with allocs := m.allocs + 1 }
      let nb : Block :=
        { bytes := Array.replicate len.toNat (.int 0)
          align := os.pageSize
          kind := .mapped 0
          live := true
          addr := m₁.mapAddr os.pageSize len.toNat }
      have hfree : ∀ y, hF (m.blocks.size, y) = none := by
        intro y; have := congrFun hm (m.blocks.size, y)
        rw [Mem.heap_none_size] at this; exact this.symm
      refine ⟨.ok ⟨⟨some m.blocks.size, 0⟩, len⟩, m₁.afterMmap os.pageSize len.toNat,
        liveCells m.blocks.size nb, ?_,
        liveCells_disjoint hfree, ?_, ⟨rfl, rfl, m₁.mapAddr os.pageSize len.toNat, rfl, ?_, ?_,
          by simp, ?_⟩, hst₁.afterMmap _ _⟩
      · rw [Os.mmap_run os hint len (by omega), if_neg hdn]
      · rw [Mem.heap_afterMmap]; show _ ∪ m.heap = _; rw [hm]
      · simp [nb]; omega
      · exact Mem.newAddr_mod m₁ _ _ hP
      · have := liveCells_bytesAt (b := m.blocks.size) (nb := nb) (lo := 0) rfl rfl (Nat.zero_le _)
        simpa [nb] using this

/-! ## Replacing a whole owned block -/

/-- A memory whose block `b` became `nb` is again `Seq` (one thread). -/
theorem Mem.Seq.replace {m' : Mem} (hsingle : m'.SingleThread) : m'.Seq := ⟨hsingle⟩

/-- The frame's cells are cells of the memory. -/
theorem frame_sub {m : Mem} {h hF : Heap} (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) :
    ∀ l c, hF l = some c → m.heap l = some c := by
  intro l c hc
  rw [hm, Heap.union_apply]
  rcases hd l with e | e
  · rw [e, Option.none_or]; exact hc
  · rw [e] at hc; cases hc

theorem extract_mid {a bs : Array Byte} {lo n k : Nat} (h : a.extract lo (lo + n) = bs)
    (hn : lo + n ≤ a.size) (hk : k ≤ n) : a.extract (lo + k) (lo + n) = bs.extract k n := by
  subst h; apply Array.ext
  · simp; try omega
  · intro i h1 h2; simp only [Array.getElem_extract]; congr 1; omega

theorem extract_pre {a bs : Array Byte} {lo n k : Nat} (h : a.extract lo (lo + n) = bs)
    (hn : lo + n ≤ a.size) (hk : k ≤ n) :
    (a.extract 0 (lo + k)).extract lo (lo + k) = bs.extract 0 k := by
  subst h; apply Array.ext
  · simp; try omega
  · intro i h1 h2; simp only [Array.getElem_extract, Nat.zero_add]

theorem mod_add3 {a b c P : Nat} (ha : a % P = 0) (hb : b % P = 0) (hc : c % P = 0) :
    (a + (b + c)) % P = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero ha)
    (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hb) (Nat.dvd_of_mod_eq_zero hc)))

/-! ## munmap -/

/-- `munmap` of a range of a live mapping that `unmapCase` admits: record the removed bytes as a
write, then apply the case to the block. -/
theorem Os.munmap_run {m : Mem} (os : Os.Target) (s : Slice) {b : BlockId} {blk : Block}
    {lo : Nat} {u : Os.Unmap} (hb : s.ptr.block = some b) (hblk : m.blocks[b]? = some blk)
    (hl : blk.live) (hk : blk.kind = .mapped lo) (h0 : 0 ≤ s.ptr.off)
    (hal : (blk.addr + s.ptr.off.toNat) % os.pageSize = 0)
    (hu : Os.unmapCase os.pageSize lo blk.bytes.size s.ptr.off.toNat s.len.toNat = some u)
    (hst : m.SingleThread) :
    (Os.munmap os s).run m =
      pure ((), { m.recordAt b s.ptr.off.toNat
        (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size -
          s.ptr.off.toNat) .write with blocks := m.blocks.set! b (u.apply blk) }) := by
  have hrec := recordAccess_run (noRace_of_singleThread hst b s.ptr.off.toNat
    (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size - s.ptr.off.toNat)
    .write)
  simp only [StateT.run] at hrec
  simp [Os.munmap, Os.mappingAt, hb, hblk, hl, hk, h0, hal, hu, zig_unfold, hrec,
    ExceptT.bindCont, set, StateT.set, MonadStateOf.set, Mem.recordAt]

/-- The common part of the `munmap` rules: the memory after a case `u` on a whole owned mapping,
for the range from byte `k` of it. -/
theorem munmap_owned {m : Mem} {h hF : Heap} (os : Os.Target)
    {p : Ptr} {A lo : Nat} {bs : Array Byte} {k : Nat} {len : BitVec 64} {u : Os.Unmap}
    (hp : mapping os.pageSize p A lo bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) (hk : k % os.pageSize = 0)
    (hu : Os.unmapCase os.pageSize lo (lo + bs.size) (lo + k) len.toNat = some u) :
    ∃ b blk, p = ⟨some b, lo⟩ ∧ m.blocks[b]? = some blk ∧ blk.live ∧ blk.kind = .mapped lo ∧
      blk.addr = A ∧ blk.bytes.size = lo + bs.size ∧ blk.bytes.extract lo (lo + bs.size) = bs ∧
      (∀ y, hF (b, y) = none) ∧
      ∃ m', (Os.munmap os ⟨p.add k, len⟩).run m = pure ((), m') ∧
        m'.heap = liveCells b (u.apply blk) ∪ hF ∧ m'.SingleThread ∧
        m'.blocks = m.blocks.set! b (u.apply blk) := by
  obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, hh⟩ := mapping_block hp hm hd
  obtain ⟨-, -, hA0, hlo0, -⟩ := hp
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hoff : (((⟨some b, lo⟩ : Ptr).add k).off).toNat = lo + k := by simp [Ptr.add]; omega
  have hr := Os.munmap_run os ⟨(⟨some b, lo⟩ : Ptr).add k, len⟩ (b := b) (blk := blk) (lo := lo)
    (u := u) rfl hblk hl hK (by simp [Ptr.add]; omega)
    (by rw [hoff, hA]; exact mod_add3 hA0 hlo0 hk) (by rw [hoff, hS]; exact hu) hst.single
  refine ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, _, hr,
    heap_replace (h := h) hm hlt rfl hFb hh, singleThread_recordAt hst.single _ _ _ _, rfl⟩

theorem Ptr.add_zero' (p : Ptr) : p.add 0 = p := by cases p; simp [Ptr.add]

theorem unmapCase_whole {P lo S n : Nat} (hS : 0 < S) (hn : 0 < n)
    (heq : alignUp n P = alignUp S P) : Os.unmapCase P lo (lo + S) lo n = some .whole := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_pos ⟨rfl, by rw [heq]⟩]

theorem unmapCase_prefix {P lo S n : Nat} (hS : 0 < S) (hn : 0 < n)
    (hlt : alignUp n P < alignUp S P) :
    Os.unmapCase P lo (lo + S) lo n = some (.prefix (lo + alignUp n P)) := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem unmapCase_tail {P lo S k n : Nat} (hk : 0 < k) (hkS : k < S) (hn : 0 < n)
    (heq : k + alignUp n P = alignUp S P) :
    Os.unmapCase P lo (lo + S) (lo + k) n = some (.tail (lo + k)) := by
  unfold Os.unmapCase; dsimp only
  rw [Nat.add_sub_cancel_left, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

theorem add_le_of_mod {a b P : Nat} (ha : a % P = 0) (hb : b % P = 0) (h : a < b) :
    a + P ≤ b := by
  obtain ⟨q₁, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨q₂, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  have : q₁ < q₂ := Nat.lt_of_mul_lt_mul_left h
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this

/-- **munmap, whole mapping.** Consumes the mapping's permission; nothing is left. -/
theorem TotalTriple.munmapWhole (os : Os.Target) {p : Ptr} {A lo : Nat} {bs : Array Byte}
    {len : BitVec 64} (hlen : 0 < len.toNat) (heq : alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    TotalTriple (mapping os.pageSize p A lo bs) (Os.munmap os ⟨p, len⟩) (fun _ => emp) :=
  TotalTriple.of_run fun m h hF hd hm hp hst => by
    have hpos := hp.2.1
    obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, -, hFb, m', hr, hm', hs', hb'⟩ :=
      munmap_owned os (k := 0) (len := len) hp hm hd hst (Nat.zero_mod _)
        (by rw [Nat.add_zero]; exact unmapCase_whole hpos hlen heq)
    rw [show (((0 : Nat) : Int)) = 0 from rfl, Ptr.add_zero'] at hr
    have hdead : liveCells b (Os.Unmap.apply blk .whole) = Heap.empty :=
      liveCells_dead (by simp [Os.Unmap.apply])
    rw [hdead] at hm'
    exact ⟨(), m', Heap.empty, hr, (Heap.disjoint_empty hF).symm, hm', rfl, Mem.Seq.replace hs'⟩

/-- **munmap, page prefix.** `len` (rounded up to pages, `k`) is less than the mapping: the
permission of its first `k` bytes is consumed; the rest is a mapping that starts `k` bytes later. -/
theorem TotalTriple.munmapPrefix (os : Os.Target) {p : Ptr} {A lo : Nat}
    {bs : Array Byte} {len : BitVec 64} (hlen : 0 < len.toNat)
    (hlt : alignUp len.toNat os.pageSize < alignUp bs.size os.pageSize) :
    TotalTriple (mapping os.pageSize p A lo bs) (Os.munmap os ⟨p, len⟩)
      (fun _ => mapping os.pageSize (p.add (alignUp len.toNat os.pageSize)) A
        (lo + alignUp len.toNat os.pageSize)
        (bs.extract (alignUp len.toNat os.pageSize) bs.size)) :=
  TotalTriple.of_run fun m h hF hd hm hp hst => by
    have hP := os.pageSize_pos
    have hpos := hp.2.1
    have hA0 := hp.2.2.1
    have hlo0 := hp.2.2.2.1
    let k := alignUp len.toNat os.pageSize
    have hkS : k < bs.size := by
      have := alignUp_lt (n := bs.size) hP
      have := add_le_of_mod (alignUp_mod_self (n := len.toNat) hP)
        (alignUp_mod_self (n := bs.size) hP) hlt
      omega
    obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, m', hr, hm', hs', hb'⟩ :=
      munmap_owned os (k := 0) (len := len) hp hm hd hst (Nat.zero_mod _)
        (by rw [Nat.add_zero]; exact unmapCase_prefix hpos hlen hlt)
    rw [show (((0 : Nat) : Int)) = 0 from rfl, Ptr.add_zero'] at hr
    let nb := Os.Unmap.apply blk (.prefix (lo + k))
    have hnbl : nb.live := hl
    have hnbk : nb.kind = .mapped (lo + k) := rfl
    have hnbs : nb.bytes.size = lo + bs.size := hS
    refine ⟨(), m', liveCells b nb, hr, liveCells_disjoint hFb, hm', ⟨?_, by simp; omega, hA0,
      ?_, ?_⟩, Mem.Seq.replace hs'⟩
    · simp [Ptr.add]
    · show (lo + k) % os.pageSize = 0
      have := mod_add3 (a := 0) (Nat.zero_mod _) hlo0 (alignUp_mod_self (n := len.toNat) hP)
      simpa using this
    · have hc := liveCells_bytesAt (b := b) hnbl hnbk (by rw [hnbs]; omega)
      have hp' : (⟨some b, (lo : Int)⟩ : Ptr).add k = ⟨some b, ((lo + k : Nat) : Int)⟩ := by
        simp [Ptr.add]
      rw [hp', show lo + k + (bs.extract k bs.size).size = nb.bytes.size by simp [hnbs]; omega]
      have e1 : nb.addr = A := hA
      have e2 : nb.bytes.extract (lo + k) nb.bytes.size = bs.extract k bs.size := by
        rw [show nb.bytes = blk.bytes from rfl, hS]; exact extract_mid hx (by omega) (by omega)
      rw [e1, e2] at hc; exact hc

/-- **munmap, page tail.** From byte `k` (a page multiple, inside the mapping) to the mapping's
page end: the permission of those bytes is consumed; the first `k` bytes stay a mapping. -/
theorem TotalTriple.munmapTail (os : Os.Target) {p : Ptr} {A lo k : Nat} {bs : Array Byte}
    {len : BitVec 64} (hk : k % os.pageSize = 0) (hk0 : 0 < k) (hkS : k < bs.size)
    (hlen : 0 < len.toNat)
    (heq : k + alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    TotalTriple (mapping os.pageSize p A lo bs) (Os.munmap os ⟨p.add k, len⟩)
      (fun _ => mapping os.pageSize p A lo (bs.extract 0 k)) :=
  TotalTriple.of_run fun m h hF hd hm hp hst => by
    have hA0 := hp.2.2.1
    have hlo0 := hp.2.2.2.1
    obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, m', hr, hm', hs', hb'⟩ :=
      munmap_owned os (k := k) (len := len) hp hm hd hst hk (unmapCase_tail hk0 hkS hlen heq)
    let nb := Os.Unmap.apply blk (.tail (lo + k))
    have hnbl : nb.live := hl
    have hnbk : nb.kind = .mapped lo := hK
    have hnbs : nb.bytes.size = lo + k := by
      show (blk.bytes.extract 0 (lo + k)).size = lo + k; simp [hS]; omega
    refine ⟨(), m', liveCells b nb, hr, liveCells_disjoint hFb, hm', ⟨rfl, by simp; omega, hA0,
      hlo0, ?_⟩, Mem.Seq.replace hs'⟩
    · have hc := liveCells_bytesAt (b := b) hnbl hnbk (by rw [hnbs]; omega)
      rw [hnbs, show nb.addr = A from hA ▸ rfl] at hc
      rw [show nb.bytes = blk.bytes.extract 0 (lo + k) from rfl,
        extract_pre hx (by omega) (by omega)] at hc
      rw [show lo + (bs.extract 0 k).size = lo + k by simp; omega]
      exact hc

/-! ## Unmapped bytes are illegal -/

/-- An access to a block that is dead, or below its first live offset, or past its bytes,
throws `.illegal`. -/
theorem access_illegal {m : Mem} {q : Ptr} {n a : Nat} {b : BlockId} {nb : Block}
    (hq : q.block = some b) (hb : m.blocks[b]? = some nb)
    (h : nb.live = false ∨ q.off.toNat < nb.kind.mappedLo ∨ nb.bytes.size < q.off + n) :
    m.access q n a = throw .illegal := by
  unfold Mem.access
  simp only [hq, hb]
  rw [if_neg]
  rintro ⟨hl, h0, hn, -, hlo⟩
  rcases h with h | h | h
  · rw [hl] at h; cases h
  · omega
  · omega

theorem Os.mappingAt_dead {m : Mem} {p : Ptr} {b : BlockId} {blk : Block}
    (hb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hl : blk.live = false) :
    (Os.mappingAt p).run m = throw .illegal := by
  cases hk : blk.kind <;>
    simp [Os.mappingAt, hb, hblk, hk, hl, zig_unfold, throw, throwThe, MonadExceptOf.throw,
      ExceptT.mk, StateT.lift, StateT.bind, ExceptT.bind, ExceptT.bindCont, get, getThe,
      MonadStateOf.get, StateT.get, pure, ExceptT.pure, StateT.run]

/-- `munmap` of a block that is not live (a double `munmap`) throws `.illegal`. -/
theorem Os.munmap_dead {m : Mem} (os : Os.Target) (s : Slice) {b : BlockId} {blk : Block}
    (hb : s.ptr.block = some b) (hblk : m.blocks[b]? = some blk) (hl : blk.live = false) :
    (Os.munmap os s).run m = throw .illegal := by
  have h := Os.mappingAt_dead (m := m) hb hblk hl
  simp only [StateT.run] at h
  simp only [Os.munmap, StateT.run, bind, StateT.bind, h]
  rfl

/-- **No use after munmap, no double munmap.** After `munmap` of a whole mapping, every access to
its block and a second `munmap` of the same range throw `.illegal`. -/
theorem munmap_whole_then_illegal {m : Mem} {h hF : Heap} (os : Os.Target) {p : Ptr}
    {A lo : Nat} {bs : Array Byte} {len : BitVec 64} (hp : mapping os.pageSize p A lo bs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hst : m.Seq) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    ∃ m', (Os.munmap os ⟨p, len⟩).run m = pure ((), m') ∧
      (Os.munmap os ⟨p, len⟩).run m' = throw .illegal ∧
      ∀ q n a, q.block = p.block → m'.access q n a = throw .illegal := by
  obtain ⟨b, blk, rfl, hblk, -, -, -, -, -, -, m', hr, -, -, hb'⟩ :=
    munmap_owned os (k := 0) (len := len) hp hm hd hst (Nat.zero_mod _)
      (by rw [Nat.add_zero]; exact unmapCase_whole hp.2.1 hlen heq)
  rw [show (((0 : Nat) : Int)) = 0 from rfl, Ptr.add_zero'] at hr
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hb₂ : m'.blocks[b]? = some (Os.Unmap.apply blk .whole) := by
    rw [hb', Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hlt
  refine ⟨m', hr, Os.munmap_dead os _ rfl hb₂ rfl, fun q n a hq => access_illegal hq hb₂ (.inl rfl)⟩

/-- After `munmap` of a page prefix, every access below the new first live offset throws
`.illegal`. -/
theorem munmap_prefix_access_illegal {m : Mem} {h hF : Heap} (os : Os.Target)
    {p : Ptr} {A lo : Nat} {bs : Array Byte} {len : BitVec 64}
    (hp : mapping os.pageSize p A lo bs h) (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF)
    (hst : m.Seq) (hlen : 0 < len.toNat)
    (hlt : alignUp len.toNat os.pageSize < alignUp bs.size os.pageSize) :
    ∃ m', (Os.munmap os ⟨p, len⟩).run m = pure ((), m') ∧
      ∀ q n a, q.block = p.block → q.off.toNat < lo + alignUp len.toNat os.pageSize →
        m'.access q n a = throw .illegal := by
  have hP := os.pageSize_pos
  obtain ⟨b, blk, rfl, hblk, -, -, -, -, -, -, m', hr, -, -, hb'⟩ :=
    munmap_owned os (k := 0) (len := len) hp hm hd hst (Nat.zero_mod _)
      (by rw [Nat.add_zero]; exact unmapCase_prefix hp.2.1 hlen hlt)
  rw [show (((0 : Nat) : Int)) = 0 from rfl, Ptr.add_zero'] at hr
  have hlt' : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hb₂ : m'.blocks[b]? = some (Os.Unmap.apply blk (.prefix (lo + alignUp len.toNat os.pageSize))) := by
    rw [hb', Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hlt'
  exact ⟨m', hr, fun q n a hq ho => access_illegal hq hb₂ (.inr (.inl (by simpa [Os.Unmap.apply])))⟩

/-- After `munmap` of a page tail from byte `k`, every access that reaches byte `k` or beyond
throws `.illegal`. -/
theorem munmap_tail_access_illegal {m : Mem} {h hF : Heap} (os : Os.Target) {p : Ptr}
    {A lo k : Nat} {bs : Array Byte} {len : BitVec 64} (hp : mapping os.pageSize p A lo bs h)
    (hm : m.heap = h ∪ hF) (hd : Heap.Disjoint h hF) (hst : m.Seq)
    (hk : k % os.pageSize = 0) (hk0 : 0 < k) (hkS : k < bs.size) (hlen : 0 < len.toNat)
    (heq : k + alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    ∃ m', (Os.munmap os ⟨p.add k, len⟩).run m = pure ((), m') ∧
      ∀ (q : Ptr) (n a : Nat), q.block = p.block → ((lo + k : Nat) : Int) < q.off + n →
        m'.access q n a = throw .illegal := by
  obtain ⟨b, blk, rfl, hblk, -, -, -, hS, -, -, m', hr, -, -, hb'⟩ :=
    munmap_owned os (k := k) (len := len) hp hm hd hst hk (unmapCase_tail hk0 hkS hlen heq)
  have hlt' : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  have hb₂ : m'.blocks[b]? = some (Os.Unmap.apply blk (.tail (lo + k))) := by
    rw [hb', Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hlt'
  refine ⟨m', hr, fun q n a hq ho => access_illegal hq hb₂ (.inr (.inr ?_))⟩
  simp only [Os.Unmap.apply, Array.size_extract, hS]; omega

/-! ## mremap -/

/-- The argument checks of `mremap` pass for the whole live mapping at `p`. -/
theorem Os.mremap_eq {m : Mem} (os : Os.Target) {b : BlockId} {blk : Block} {lo : Nat}
    {oldLen newLen : BitVec 64} {flags : BitVec 32} (hhas : os.hasMremap = true)
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) (hblk : m.blocks[b]? = some blk) (hl : blk.live)
    (hK : blk.kind = .mapped lo) (hold0 : oldLen.toNat ≠ 0)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (blk.bytes.size - lo) os.pageSize) :
    (Os.mremap os (some ⟨some b, lo⟩) oldLen newLen flags none).run m =
      (Os.mremapLive os ⟨some b, lo⟩ b blk lo newLen flags).run m := by
  rcases hfl with rfl | rfl <;>
  simp [Os.mremap, Os.mappingAt, Os.mremapMayMove, hhas, hblk, hl, hK, hold0, hold, zig_unfold,
    ExceptT.bindCont]

theorem mremapFill_size (P cur n : Nat) : (mremapFill P cur n).size = n - cur := by
  simp [mremapFill]

theorem Os.mremapLive_zero {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32) (hn : newLen.toNat = 0) :
    (Os.mremapLive os p b blk lo newLen flags).run m = throw .unspecified := by
  simp [Os.mremapLive, hn, zig_unfold]

theorem Os.mremapLive_shrink {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32) (hn0 : newLen.toNat ≠ 0)
    (hn : newLen.toNat ≤ blk.bytes.size - lo) (hst : m.SingleThread) :
    (Os.mremapLive os p b blk lo newLen flags).run m =
      pure (.ok ⟨p, newLen⟩, (m.recordAt b (lo + newLen.toNat)
        (blk.bytes.size - (lo + newLen.toNat)) .write).mremapShrunk b blk lo newLen.toNat) := by
  have hrec := recordAccess_run (noRace_of_singleThread hst b (lo + newLen.toNat)
    (blk.bytes.size - (lo + newLen.toNat)) .write)
  simp only [StateT.run] at hrec
  simp [Os.mremapLive, hn0, hn, zig_unfold, hrec, ExceptT.bindCont, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Mem.recordAt]

theorem Os.mremapLive_grow {m : Mem} (os : Os.Target) (p : Ptr) (b : BlockId) (blk : Block)
    (lo : Nat) (newLen : BitVec 64) (flags : BitVec 32)
    (hn : blk.bytes.size - lo < newLen.toNat) (hst : m.SingleThread) :
    let n := newLen.toNat
    let m₁ : Mem := { m with allocs := m.allocs + 1 }
    (Os.mremapLive os p b blk lo newLen flags).run m =
      if m.mapDenied n then pure (.error "OutOfMemory", m₁)
      else if flags = Os.mremapMayMove ∧
          (m.allocPolicy.os.mremapMoves m.allocs n = true ∨ m.mappingRoom b blk lo (alignUp n os.pageSize) = false) then
        pure (.ok ⟨⟨some m.blocks.size, 0⟩, newLen⟩,
          (m₁.recordAt b lo (blk.bytes.size - lo) .write).mremapMoved os.pageSize b blk lo n)
      else if m.mappingRoom b blk lo (alignUp n os.pageSize) = false then pure (.error "OutOfMemory", m₁)
      else pure (.ok ⟨p, newLen⟩, m₁.mremapGrown os.pageSize b blk lo n) := by
  intro n m₁
  have hn0 : newLen.toNat ≠ 0 := by omega
  have hn' : ¬ newLen.toNat ≤ blk.bytes.size - lo := by omega
  have hnr := noRace_of_singleThread (m := m₁) hst b lo (blk.bytes.size - lo) .write
  unfold NoRace at hnr
  by_cases hd : m.mapDenied n
  · simp [Os.mremapLive, hn0, hn', hd, zig_unfold, n, m₁, set, StateT.set, MonadStateOf.set]
  by_cases hmv : flags = Os.mremapMayMove ∧
      (m.allocPolicy.os.mremapMoves m.allocs n = true ∨ m.mappingRoom b blk lo (alignUp n os.pageSize) = false)
  · simp only [hd, hmv, if_true, if_false, Bool.false_eq_true]
    simp only [m₁] at hnr
    simp [hnr, Os.mremapLive, hn0, hn', hd, hmv, zig_unfold, n, set, StateT.set, MonadStateOf.set,
      recordAccess, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.run,
      ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind_some,
      Mem.recordAt, liftM, monadLift, MonadLift.monadLift, StateT.lift]
    rfl
  · simp only [hd, hmv, if_false, Bool.false_eq_true]
    by_cases ht : m.mappingRoom b blk lo (alignUp n os.pageSize) = false
    · have hf : ¬ flags = Os.mremapMayMove := fun h => hmv ⟨h, .inr ht⟩
      simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
        MonadStateOf.set, ExceptT.bindCont]
    · have hf : ¬ (flags = Os.mremapMayMove ∧ m.allocPolicy.os.mremapMoves m.allocs n = true) :=
        fun h => hmv ⟨h.1, .inl h.2⟩
      simp [Os.mremapLive, hn0, hn', hd, hf, ht, zig_unfold, n, m₁, set, StateT.set,
        MonadStateOf.set, ExceptT.bindCont, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet]

/-- The heap after a new block `nb` at index `X.blocks.size`. -/
theorem Mem.heap_pushBlock (X : Mem) (nb : Block) :
    ({ X with blocks := X.blocks.push nb } : Mem).heap =
      liveCells X.blocks.size nb ∪ X.heap := by
  funext ⟨x, y⟩
  rw [Mem.heap_push, Heap.union_apply]
  by_cases hx : x = X.blocks.size
  · subst hx; simp only [↓reduceIte, liveCells, Mem.heap_none_size, Option.or_none]
  · simp [hx, liveCells]

theorem extract_clamp {a : Array Byte} {i j : Nat} (h : a.size ≤ j) :
    a.extract i j = a.extract i a.size := by
  apply Array.ext
  · simp; omega
  · intro k h1 h2; simp only [Array.getElem_extract]

/-- The live bytes after an append: the old live bytes, then the appended ones. -/
theorem extract_append_live {a f bs : Array Byte} {lo : Nat} (hlo : lo ≤ a.size)
    (hx : a.extract lo a.size = bs) : (a ++ f).extract lo (a ++ f).size = bs ++ f := by
  rw [Array.extract_append, extract_clamp (a := a) (by simp), hx,
    show lo - a.size = 0 by omega, show (a ++ f).size - a.size = f.size by simp,
    Array.extract_size]

/-- What `mremap` returns for a growth: the grown mapping, in place or moved, or an
`error.OutOfMemory` and the old mapping. -/
def mremapPost (P : Nat) (p : Ptr) (A lo : Nat) (bs : Array Byte) (n : Nat) (newLen : BitVec 64) :
    Except ErrName Slice → Assn
  | .ok s => fun h => s.len = newLen ∧ ∃ A' lo', mapping P s.ptr A' lo' (bs ++ mremapFill P bs.size n) h
  | .error e => fun h => e = "OutOfMemory" ∧ mapping P p A lo bs h

/-- **mremap, shrink.** In place: the permission of the cut bytes is consumed, the first
`newLen` bytes stay a mapping at the same pointer. -/
theorem TotalTriple.mremapShrink (os : Os.Target) (hhas : os.hasMremap = true)
    {flags : BitVec 32} (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {A lo : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp bs.size os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : newLen.toNat ≤ bs.size) :
    TotalTriple (mapping os.pageSize p A lo bs) (Os.mremap os (some p) oldLen newLen flags none)
      (fun r => ⌜r = .ok ⟨p, newLen⟩⌝ ∗ mapping os.pageSize p A lo (bs.extract 0 newLen.toNat)) :=
  TotalTriple.of_run fun m h hF hd hm hp hst => by
    have hA0 := hp.2.2.1
    have hlo0 := hp.2.2.2.1
    obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, hh⟩ := mapping_block hp hm hd
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    have hcur : blk.bytes.size - lo = bs.size := by omega
    rw [Os.mremap_eq os hhas hfl hblk hl hK (by omega) (by rw [hcur]; exact hold),
      Os.mremapLive_shrink os _ b blk lo newLen flags (by omega) (by omega) hst.single]
    let nb : Block := { blk with bytes := blk.bytes.extract 0 (lo + newLen.toNat) }
    have hnbs : nb.bytes.size = lo + newLen.toNat := by simp [nb, hS]; omega
    have hm' : ((m.recordAt b (lo + newLen.toNat) (blk.bytes.size - (lo + newLen.toNat)) .write).mremapShrunk
        b blk lo newLen.toNat).heap = liveCells b nb ∪ hF := heap_replace hm hlt rfl hFb hh
    refine ⟨_, _, liveCells b nb, rfl, liveCells_disjoint hFb, hm', sep_lift.mpr ⟨rfl, rfl,
      by simp; omega, hA0, hlo0, ?_⟩, Mem.Seq.replace (singleThread_recordAt hst.single _ _ _ _)⟩
    · have hc := liveCells_bytesAt (b := b) (nb := nb) hl hK (by rw [hnbs]; omega)
      rw [hnbs, show nb.addr = A from hA] at hc
      rw [show nb.bytes = blk.bytes.extract 0 (lo + newLen.toNat) from rfl,
        extract_pre hx (by omega) (by omega)] at hc
      rw [show lo + (bs.extract 0 newLen.toNat).size = lo + newLen.toNat by simp; omega]
      exact hc

/-- **mremap, growth.** For every failure, move and placement decision: the grown mapping (the
old bytes, then `mremapFill`), in place at the same pointer or moved to a fresh page-aligned
block (the old block ends), or `error.OutOfMemory` with the old mapping unchanged. -/
theorem TotalTriple.mremapGrow (os : Os.Target) (hhas : os.hasMremap = true)
    {flags : BitVec 32} (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {A lo : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp bs.size os.pageSize)
    (hn : bs.size < newLen.toNat) :
    TotalTriple (mapping os.pageSize p A lo bs) (Os.mremap os (some p) oldLen newLen flags none)
      (mremapPost os.pageSize p A lo bs newLen.toNat newLen) :=
  TotalTriple.of_run fun m h hF hd hm hp hst => by
    have hP := os.pageSize_pos
    have hpos := hp.2.1
    have hA0 := hp.2.2.1
    have hlo0 := hp.2.2.2.1
    obtain ⟨b, blk, rfl, hblk, hl, hK, hA, hS, hx, hFb, hh⟩ := mapping_block hp hm hd
    have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
    have hcur : blk.bytes.size - lo = bs.size := by omega
    have hx' : blk.bytes.extract lo blk.bytes.size = bs := by rw [hS]; exact hx
    rw [Os.mremap_eq os hhas hfl hblk hl hK (by omega) (by rw [hcur]; exact hold),
      Os.mremapLive_grow os _ b blk lo newLen flags (by omega) hst.single]
    have hst₁ : ({ m with allocs := m.allocs + 1 } : Mem).Seq := ⟨hst.single⟩
    let n := newLen.toNat
    let fill := mremapFill os.pageSize (blk.bytes.size - lo) n
    have hfill : fill = mremapFill os.pageSize bs.size n := by simp only [fill, hcur]
    have hfs : fill.size = n - bs.size := by rw [hfill, mremapFill_size]
    by_cases hd₁ : m.mapDenied n
    · rw [if_pos hd₁]
      exact ⟨_, _, h, rfl, hd, hm, ⟨rfl, hp⟩, hst₁⟩
    rw [if_neg hd₁]
    by_cases hmv : flags = Os.mremapMayMove ∧
        (m.allocPolicy.os.mremapMoves m.allocs n = true ∨ m.mappingRoom b blk lo (alignUp n os.pageSize) = false)
    · rw [if_pos hmv]
      -- The move: the old block ends, the new one is pushed.
      let m₁ : Mem := { m with allocs := m.allocs + 1 }
      let mr := m₁.recordAt b lo (blk.bytes.size - lo) .write
      let mid : Mem := { mr with blocks := mr.blocks.set! b { blk with live := false } }
      let nnb : Block :=
        { bytes := blk.bytes.extract lo blk.bytes.size ++ fill, align := os.pageSize,
          kind := .mapped 0, live := true, addr := m.mapAddr os.pageSize n }
      have hmid : mid.heap = hF := by
        rw [heap_replace (m := m) hm hlt rfl hFb hh, liveCells_dead rfl, Heap.empty_union]
      have hN : mid.blocks.size = m.blocks.size := by simp [mid, mr, m₁, Mem.recordAt]
      have hfree : ∀ y, hF (m.blocks.size, y) = none := by
        intro y; have := congrFun hm (m.blocks.size, y)
        rw [Mem.heap_none_size] at this
        exact (Option.or_eq_none_iff.mp this.symm).2
      have hm' : (mr.mremapMoved os.pageSize b blk lo n).heap = liveCells m.blocks.size nnb ∪ hF := by
        have := Mem.heap_pushBlock mid nnb
        rw [hmid, hN] at this; exact this
      have hnbs : nnb.bytes.size = n := by
        simp [nnb, hfs, hS]; omega
      refine ⟨_, _, liveCells m.blocks.size nnb, rfl, liveCells_disjoint hfree, hm', ⟨rfl,
        m.mapAddr os.pageSize n, 0, rfl, by simp; omega, Mem.newAddr_mod m _ _ hP, Nat.zero_mod _,
        ?_⟩, Mem.Seq.replace (singleThread_recordAt hst.single _ _ _ _)⟩
      · have hc := liveCells_bytesAt (b := m.blocks.size) (nb := nnb) rfl rfl (Nat.zero_le _)
        rw [Array.extract_size] at hc
        rw [show nnb.bytes = bs ++ mremapFill os.pageSize bs.size n by
          simp only [nnb, hx', hfill]] at hc
        rw [Nat.zero_add]
        exact hc
    rw [if_neg hmv]
    by_cases ht : m.mappingRoom b blk lo (alignUp n os.pageSize) = false
    · rw [if_pos ht]
      exact ⟨_, _, h, rfl, hd, hm, ⟨rfl, hp⟩, hst₁⟩
    rw [if_neg ht]
    -- In place.
    let nb : Block := { blk with bytes := blk.bytes ++ fill }
    have hnbs : nb.bytes.size = lo + n := by simp [nb, hfs, hS]; omega
    have hm' : (({ m with allocs := m.allocs + 1 } : Mem).mremapGrown os.pageSize b blk lo n).heap =
        liveCells b nb ∪ hF := heap_replace hm hlt rfl hFb hh
    refine ⟨_, _, liveCells b nb, rfl, liveCells_disjoint hFb, hm', ⟨rfl, A, lo, rfl, by simp; omega,
      hA0, hlo0, ?_⟩, Mem.Seq.replace hst.single⟩
    · have hc := liveCells_bytesAt (b := b) (nb := nb) hl hK (by rw [hnbs]; omega)
      rw [show nb.bytes.extract lo nb.bytes.size = bs ++ mremapFill os.pageSize bs.size n by
          rw [show nb.bytes = blk.bytes ++ fill from rfl, extract_append_live (by omega) hx', hfill],
        show nb.addr = A from hA] at hc
      rw [show lo + (bs ++ mremapFill os.pageSize bs.size n).size = nb.bytes.size by
        rw [hnbs]; simp [mremapFill_size]; omega]
      exact hc

/-! ## Kernel-checked examples (`x86_64-linux` profile) -/

namespace MmapExamples

open Os

/-- The outcome of a run: `true` iff it throws `.illegal`. -/
def isIllegal {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.error .illegal) => true
  | _ => false

/-- The outcome of a run: `true` iff it returns. -/
def returns {α : Type} (c : MemM α) : Bool :=
  match (c.run {}).run with
  | some (.ok _) => true
  | _ => false

def lx : Target := .linux

def map8 : MemM Slice := do
  match ← Os.mmap lx none 8 lx.protReadWrite lx.mapPrivateAnonymous noFd 0 with
  | .ok s => pure s
  | .error _ => throw .panic

/-- A store into a fresh mapping returns. -/
example : returns (do let s ← map8; store 1 (s.ptr.add 7) (1 : BitVec 8)) = true := by
  decide +kernel

/-- Use after `munmap` is illegal. -/
example : isIllegal (do let s ← map8; Os.munmap lx s; load (BitVec 8) 1 s.ptr) = true := by
  decide +kernel

/-- A double `munmap` is illegal. -/
example : isIllegal (do let s ← map8; Os.munmap lx s; Os.munmap lx s) = true := by
  decide +kernel

/-- `munmap` of a range in the middle of a mapping is illegal. -/
example : isIllegal (do
    let s ← match ← Os.mmap lx none 12288 lx.protReadWrite lx.mapPrivateAnonymous noFd 0 with
      | .ok s => pure s
      | .error _ => throw .panic
    Os.munmap lx ⟨s.ptr.add 4096, 4096⟩) = true := by decide +kernel

end MmapExamples

end Zig
