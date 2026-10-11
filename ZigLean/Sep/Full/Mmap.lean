import ZigLean.Sep.Full.Pinned
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Mmap

/-!
# Native full-state rules of the OS page-mapping primitives (premise OSM-01)

The rules of `Os.munmap` and `Os.mremap` (`ZigLean/Os/Mmap.lean`, `docs/os-mmap.md`) over
full-state resources, with **block extents** (`docs/sep-full-state.md` §Block extents): a step
that changes a mapping's size or live start needs the mapping's full extent `bext` and only the
bytes it releases. The bytes a caller keeps may be anyone's (a frame's): their cells do not
record the block's size or live start (`Cell.norm`), so they stay true.

* `Holds.reblock`: the general step. Block `b` of `m` becomes `nb` (same address, kind of the
  same normal form, live); the resource holds `b`'s full extent and exactly the bytes that stop
  being live; it gets the full extent of `nb` and the bytes that become live (`reblockRes`).
* `Holds.trim`: a mapping cut to its first `hi` bytes, from the extent and the cut bytes.
* `FTotalTriple.munmapTail'`: `bext` and the unmapped pages' bytes; the rest of the mapping stays
  with whoever owns it.
* `FTotalTriple.mremapShrink'`: `bext` and the cut bytes.
* `FTotalTriple.munmapPrefix'`: `bext` and the unmapped first pages; the mapping's live start
  moves (a kind of the same normal form, so the kept cells stay true).
* `FTotalTriple.mremapGrow'`: growth in place (no `MAYMOVE`) from `bext` alone; the new bytes go
  to the caller (`mremapGrowPost`), `LDMono.grow` from `Mem.mappingRoom`.

A whole mapping (`mmap`, `munmap` of the whole mapping, a growth that may move) needs every byte
of it; those steps lift from `ZigLean/Sep/Mmap.lean` with the pinned bridge (`FTriple.ofTriple`),
as the page allocator does (`tests/roadmap/alloc-translated/PageAlloc.lean`, `PageSpec.pinned`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Changing a resource's full extents -/

/-- **The full extents of a resource can change** to any blocks on which the frame has only
dormant claims: ledgers, balances and finiteness only see the frame there. -/
theorem Ghost.ok_exts_change {E E' : BlockId → Option (Nat × BlockKind)} {gF : Ghost}
    (hok : Ghost.Ok (Ghost.exts E) gF)
    (hd : ∀ b, (E' b).isSome → (gF.extent b).Dormant gF.ls) : Ghost.Ok (Ghost.exts E') gF := by
  have hep : ((Ghost.exts E).add gF).ls = gF.ls := Ghost.ls_exts_add
  have hvF : ∀ b, (gF.extent b).Valid ∧ (gF.extent b).TagOk gF.ls := fun b => by
    have hv := hok.1.2 b
    have hle : (gF.extent b).Le (((Ghost.exts E).add gF).extent b) := ECell.le_add' _ _
    refine ⟨ECell.Valid.of_add (b := (Ghost.exts E).extent b) ?_,
      ECell.TagOk.of_le (ls' := ((Ghost.exts E).add gF).ls)
        (fun _ _ _ h => by rw [hep]; exact h) hok.1.uniq hle hv.2⟩
    rw [ECell.add_comm]; exact hv.1
  refine ⟨⟨fun γ => ?_, fun b => ?_⟩, ?_⟩
  · have := hok.1.1 γ; simpa [Ghost.add, Ghost.exts] using this
  · rw [Ghost.ls_exts_add]
    by_cases hb : (E' b).isSome
    · obtain ⟨⟨S, K⟩, hS⟩ := Option.isSome_iff_exists.mp hb
      rw [show (Ghost.add (Ghost.exts E') gF).extent b = (ECell.auth1 S K Frac.one).add (gF.extent b) by
        simp [Ghost.add, Ghost.exts, hS]]
      exact (hd b hb).auth1_ok
    · have hn : E' b = none := by simpa using hb
      rw [show (Ghost.add (Ghost.exts E') gF).extent b = gF.extent b by
        simp [Ghost.add, Ghost.exts, hn]]
      exact hvF b
  · obtain ⟨N, hN⟩ := hok.2
    refine ⟨N, fun γ hγ => ⟨by have := (hN γ hγ).1; simpa [Ghost.add, Ghost.exts] using this,
      fun b e k => ?_, fun γ' e' M e => by
        have := (hN γ hγ).2.2 γ' e' M e; simpa [Ghost.add, Ghost.exts] using this⟩⟩
    have h1 := (hN γ hγ).2.1 b e k
    rw [((Ghost.exts_add_tags E' gF b).2 γ e k).1, ((Ghost.exts_add_tags E' gF b).2 γ e k).2]
    rwa [((Ghost.exts_add_tags E gF b).2 γ e k).1, ((Ghost.exts_add_tags E gF b).2 γ e k).2] at h1

/-- The extent map of one block. -/
def extOne (b : BlockId) (S : Nat) (K : BlockKind) : BlockId → Option (Nat × BlockKind) :=
  fun x => if x = b then some (S, K) else none

/-! ## One block's extent changes -/

/-- The blocks after `set!` at an existing index. -/
theorem blocks_set_get {m m' : Mem} {b : BlockId} {blk nb : Block} (hb : m.blocks[b]? = some blk)
    (h : m'.blocks = m.blocks.set! b nb) (x : BlockId) :
    m'.blocks[x]? = if x = b then some nb else m.blocks[x]? := by
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rw [h, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : x = b
  · subst e; simp [hlt]
  · simp [e, Ne.symm e]

/-- The resource after `Holds.reblock`: the bytes of `b` that became live, and `nb`'s extent. -/
def reblockRes (m m' : Mem) (b : BlockId) (nb : Block) : Res :=
  ⟨fun l => if l.1 = b ∧ m.heap l = none then (m'.heap l).map (⟨·, none⟩) else none, Know.none,
    Ghost.exts (extOne b nb.bytes.size nb.kind)⟩

/-- **One block's extent changes under its full extent** (module doc): block `b` becomes `nb` at
the same address with a kind of the same normal form, its live bytes keep their values, and the
resource owns `b`'s full extent and exactly the bytes that stop being live (`X`'s cells). Then
the new memory holds `reblockRes` (the bytes that became live and `nb`'s full extent) with the
same frame. -/
theorem Holds.reblock {m m' : Mem} {r rF : Res} {b : BlockId} {blk nb : Block} {S : Nat}
    {K : BlockKind} {X : Assn} (hh : Holds m r rF) (hp : (up X ⋆ bext b S K) r)
    (hb : m.blocks[b]? = some blk) (hbs : m'.blocks = m.blocks.set! b nb)
    (hsh : shapes m' = shapes m) (hl : nb.live = true) (ha : nb.addr = blk.addr)
    (hk : nb.kind.norm = blk.kind.norm) (hlo : nb.kind.mappedLo < nb.bytes.size)
    (hkeep : ∀ o c c', m.heap (b, o) = some c → m'.heap (b, o) = some c' → c'.byte = c.byte)
    (hX : ∀ h, X h → ∀ l, h l ≠ none ↔ (l.1 = b ∧ m.heap l ≠ none ∧ m'.heap l = none)) :
    Holds m' (reblockRes m m' b nb) rF := by
  obtain ⟨hXr, -, hrg⟩ := up_sep_bext hp
  replace hrg : r.gh = Ghost.exts (extOne b S K) := hrg
  have hdom : ∀ l, r.heap l ≠ none ↔ (l.1 = b ∧ m.heap l ≠ none ∧ m'.heap l = none) := fun l => by
    have := hX _ hXr l
    simp only [FHeap.erase, ne_eq, Option.map_eq_none_iff] at this
    exact this
  have hget := blocks_set_get hb hbs
  have hb' : m'.blocks[b]? = some nb := by rw [hget]; simp
  have hoth : ∀ l : Loc, l.1 ≠ b → m'.heap l = m.heap l := fun ⟨x, o⟩ hx => by
    simp only [Mem.heap]; rw [hget x, if_neg hx]
  have hFlive : ∀ l fc, rF.heap l = some fc → m.heap l ≠ none := fun l fc h => by
    obtain ⟨c, hc, -⟩ := hh.swap.cellN h; rw [hc]; simp
  have hold := hh.heap.1
  -- the frame's claims on `b` are dormant
  have hok : Ghost.Ok (Ghost.exts (extOne b S K)) rF.gh := by
    have := hh.ghost.1; rwa [hrg] at this
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have := full_excl hok (b := b) (S := S) (K := K) (by simp [Ghost.exts, extOne])
    rwa [Ghost.ls_exts_add] at this
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _,
    hh.knowF.trans (KMono.set hb ha hbs), ⟨Ghost.ok_exts_change hok fun x hx => ?_, fun x => ?_⟩⟩
  · -- disjoint
    by_cases hc : l.1 = b ∧ m.heap l = none
    · right
      cases e : rF.heap l with
      | none => rfl
      | some fc => exact absurd hc.2 (hFlive _ _ e)
    · left; simp [reblockRes, hc]
  · -- the cells up to `Cell.norm`
    simp only [FHeap.union_apply, reblockRes]
    by_cases hx : l.1 = b
    · by_cases hm : m.heap l = none
      · have hFn : rF.heap l = none := by
          cases e : rF.heap l with
          | none => rfl
          | some fc => exact absurd hm (hFlive _ _ e)
        rw [if_pos ⟨hx, hm⟩, hFn]
        cases m'.heap l <;> rfl
      · rw [if_neg (fun h => hm h.2), Option.none_or]
        by_cases hm' : m'.heap l = none
        · have hr : r.heap l ≠ none := (hdom l).mpr ⟨hx, hm, hm'⟩
          have hFn : rF.heap l = none := by
            rcases hh.disj l with e | e
            · exact absurd e hr
            · exact e
          rw [hm', hFn]; rfl
        · have hrn : r.heap l = none := Classical.byContradiction fun hc => hm' ((hdom l).mp hc).2.2
          have h1 := hold l
          rw [FHeap.union_apply, hrn, Option.none_or] at h1
          rw [← h1]
          obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hm
          obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hm'
          rw [hc, hc']
          obtain ⟨x, o⟩ := l
          simp only at hx; subst hx
          have hby := hkeep o c c' hc hc'
          obtain ⟨blk1, e1, -, ho1, e1'⟩ := Mem.heap_some hc
          obtain ⟨blk2, e2, -, ho2, e2'⟩ := Mem.heap_some hc'
          rw [hb] at e1; cases e1
          rw [hb'] at e2; cases e2
          rw [e1', e2'] at hby ⊢
          simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq, true_and, and_true]
          exact ⟨hby, ha, hk⟩
    · rw [if_neg (fun h => hx h.1), Option.none_or, hoth l hx]
      have hrn : r.heap l = none := Classical.byContradiction fun hc => hx ((hdom l).mp hc).1
      have h1 := hold l
      rw [FHeap.union_apply, hrn, Option.none_or] at h1
      exact h1
  · -- tags
    simp only [FHeap.union_apply, reblockRes] at hfc
    split at hfc
    · cases e : m'.heap l with
      | none => rw [e, Option.map_none, Option.none_or] at hfc; rw [hsh]; exact hh.tagF hfc
      | some c => rw [e, Option.map_some, Option.some_or] at hfc; cases hfc; trivial
    · rw [Option.none_or] at hfc; rw [hsh]; exact hh.tagF hfc
  · -- no frame claim on `b` (the only block of the new extents)
    have : x = b := Classical.byContradiction fun hne => by simp [extOne, hne] at hx
    subst this; exact hdorm
  · -- the extent claims hold in `m'`
    show ECell.TrueIn _ _ _ _
    simp only [reblockRes]
    rw [Ghost.ls_exts_add]
    by_cases hx : x = b
    · subst hx
      rw [show (Ghost.add (Ghost.exts (extOne x nb.bytes.size nb.kind)) rF.gh).extent x =
        (ECell.auth1 nb.bytes.size nb.kind Frac.one).add (rF.gh.extent x) by
          simp [Ghost.add, Ghost.exts, extOne]]
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · simp only [ECell.add, hdorm.1, Nat.add_zero, ECell.auth1] at hp'
        split at hp'
        · rename_i he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          exact ⟨nb, hb', hl, rfl, rfl, hlo⟩
        · cases hp'
      · rw [hdorm.req_auth1 hk']; exact ⟨nb, hb', hl, Nat.zero_le _, hlo⟩
    · have ht := hh.ghost.2 x
      rw [hrg] at ht
      have e1 : (Ghost.add (Ghost.exts (extOne b nb.bytes.size nb.kind)) rF.gh).extent x = rF.gh.extent x := by
        simp [Ghost.add, Ghost.exts, extOne, hx]
      have e2 : (Ghost.add (Ghost.exts (extOne b S K)) rF.gh).extent x = rF.gh.extent x := by
        simp [Ghost.add, Ghost.exts, extOne, hx]
      rw [e1]
      rw [e2, Ghost.ls_exts_add] at ht
      obtain ⟨h1, h2⟩ := ht
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · obtain ⟨blk0, hb0, rest⟩ := h1 S' K' hp'
        exact ⟨blk0, by rw [hget, if_neg hx]; exact hb0, rest⟩
      · obtain ⟨blk0, hb0, rest⟩ := h2 k hk'
        exact ⟨blk0, by rw [hget, if_neg hx]; exact hb0, rest⟩

theorem exts_extOne (b : BlockId) (S : Nat) (K : BlockKind) :
    Ghost.exts (extOne b S K) = Ghost.atExt b (ECell.auth1 S K Frac.one) := by
  ext1
  · funext γ; simp [Ghost.atExt, Ghost.exts]
  · funext x; simp only [Ghost.atExt, Ghost.exts, extOne]; split <;> simp_all

/-- After a step that makes no byte of `b` live, `reblockRes` is `nb`'s full extent. -/
theorem reblockRes_bext {m m' : Mem} {b : BlockId} {nb : Block}
    (h : ∀ o, m'.heap (b, o) ≠ none → m.heap (b, o) ≠ none) :
    bext b nb.bytes.size nb.kind (reblockRes m m' b nb) := by
  refine ⟨?_, rfl, exts_extOne b _ _⟩
  funext ⟨x, o⟩
  simp only [reblockRes, FHeap.empty]
  split
  · rename_i hc
    obtain ⟨rfl, hm⟩ := hc
    cases e : m'.heap (x, o) with
    | none => rfl
    | some c => exact absurd hm (h o (by rw [e]; simp))
  · rfl

/-- The cells of `bytesAt`. -/
theorem bytesAt_dom {p : Ptr} {b : BlockId} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    (hb : p.block = some b) (hp : bytesAt p A S K bs h) (l : Loc) :
    h l ≠ none ↔ (l.1 = b ∧ p.off.toNat ≤ l.2 ∧ l.2 < p.off.toNat + bs.size) := by
  obtain ⟨b', hb', -, hl⟩ := hp
  rw [hb] at hb'; cases hb'
  rw [hl l]; split <;> simp_all

/-- The live bytes of block `b` with state `blk` (live, kind `.mapped lo`). -/
theorem heap_mapped {m : Mem} {b : BlockId} {blk : Block} {lo : Nat} (hb : m.blocks[b]? = some blk)
    (hl : blk.live = true) (hk : blk.kind = .mapped lo) (o : Nat) :
    m.heap (b, o) ≠ none ↔ (lo ≤ o ∧ o < blk.bytes.size) := by
  rw [Mem.heap_of hb]; simp only [hl, hk, BlockKind.mappedLo, true_and]
  split <;> simp_all <;> omega

/-! ## Trimming a mapping's tail -/

/-- **A mapping loses its tail `[hi, S)` under its extent**: the extent and exactly the trimmed
bytes (any labels) give, in a memory whose block `b` is cut to `hi` bytes, the extent of the first
`hi` bytes; the kept bytes stay with whoever owns them. -/
theorem Holds.trim {m m' : Mem} {r rF : Res} {b : BlockId} {blk : Block} {q : Ptr}
    {A S S' lo hi : Nat} {K' : BlockKind} {cut : Array Byte} (hh : Holds m r rF)
    (hpre : (up (bytesAt q A S' K' cut) ⋆ bext b S (.mapped lo)) r)
    (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (hsz : blk.bytes.size = S)
    (hK : blk.kind = .mapped lo) (hqb : q.block = some b) (hq : q.off.toNat = hi) (hlo : lo < hi)
    (hhi : hi ≤ S) (hcut : cut.size = S - hi)
    (hbs : m'.blocks = m.blocks.set! b { blk with bytes := blk.bytes.extract 0 hi })
    (hsh : shapes m' = shapes m) :
    Holds m' (reblockRes m m' b { blk with bytes := blk.bytes.extract 0 hi }) rF ∧
      bext b hi (.mapped lo) (reblockRes m m' b { blk with bytes := blk.bytes.extract 0 hi }) ∧
      LDMono m m' := by
  let nb : Block := { blk with bytes := blk.bytes.extract 0 hi }
  have hnbs : nb.bytes.size = hi := by simp [nb]; omega
  have hnbk : nb.kind = .mapped lo := hK
  have hb' : m'.blocks[b]? = some nb := by rw [blocks_set_get hb hbs]; simp [nb]
  have hheap := heap_mapped hb hl hK
  have hheap' := heap_mapped hb' hl hnbk
  refine ⟨Holds.reblock (nb := nb) hh hpre hb hbs hsh hl rfl (by simp [nb])
    (by rw [hnbk, hnbs]; simp [BlockKind.mappedLo]; omega)
    (fun o c c' hc hc' => by
      obtain ⟨_, e1, -, ho1, rfl⟩ := Mem.heap_some hc
      obtain ⟨_, e2, -, ho2, rfl⟩ := Mem.heap_some hc'
      rw [hb] at e1; cases e1; rw [hb'] at e2; cases e2
      simp [nb])
    (fun h hX l => by
      rw [bytesAt_dom hqb hX l, hq]
      obtain ⟨x, o⟩ := l
      by_cases hx : x = b
      · subst hx
        have h1 := hheap o
        have h2 := hheap' o
        rw [hsz] at h1; rw [hnbs] at h2
        simp only [true_and]
        constructor
        · rintro ⟨ha1, ha2⟩
          exact ⟨h1.mpr ⟨by omega, by omega⟩,
            Classical.byContradiction fun hc => by have := h2.mp hc; omega⟩
        · rintro ⟨hb1, hb2⟩
          obtain ⟨hlo1, hlt1⟩ := h1.mp hb1
          have hn : ¬ (lo ≤ o ∧ o < hi) := fun hc => (h2.mpr hc) hb2
          exact ⟨by omega, by omega⟩
      · simp [hx]), ?_, LDMono.set (nb := nb) hb (fun _ => hl) rfl (by rw [hnbs, hsz]; omega) hbs⟩
  have := reblockRes_bext (m := m) (m' := m') (b := b) (nb := nb) fun o h' => by
    have := (hheap' o).mp h'; exact (hheap o).mpr ⟨this.1, by omega⟩
  rwa [hnbs, hnbk] at this

/-! ## `munmap` of a page tail -/

/-- **munmap, page tail, from the extent.** The mapping's full extent and the bytes of its last
pages `[lo + k, S)` (any labels; the cells' address is the block's): `munmap` from byte `lo + k`
leaves the extent of the first `lo + k` bytes. The kept bytes `[lo, lo + k)` stay with whoever
owns them. -/
theorem FTotalTriple.munmapTail' (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo k : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = ((lo + k : Nat) : Int)) (hk : 0 < k) (hS : S = lo + k + tail.size)
    (htl : 0 < tail.size) (hal : (A + (lo + k)) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : k + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTotalTriple (up (bytesAt p A S' K' tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b (lo + k) (.mapped lo)) := by
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_comm hpre)
  obtain ⟨hXr, -, -⟩ := up_sep_bext hpre
  have hoff : p.off.toNat = lo + k := by rw [hp0]; omega
  -- the first unmapped byte gives the block's address
  have hA : A = blk.addr := by
    obtain ⟨b', hb', -, hcells⟩ := hXr
    rw [hpb] at hb'; cases hb'
    have := hcells (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at this
    simp only [FHeap.erase, Option.map_eq_some_iff] at this
    obtain ⟨fc, hfc, he⟩ := this
    obtain ⟨blk', hb'', -, -, -, ha, -⟩ := hh.block hfc
    rw [hb] at hb''; cases hb''
    rw [← ha, he]
  have hu : Os.unmapCase os.pageSize lo blk.bytes.size p.off.toNat len.toNat = some (.tail (lo + k)) := by
    rw [hsz, hoff]
    have := unmapCase_tail (P := os.pageSize) (lo := lo) (S := S - lo) (k := k) (n := len.toNat) hk
      (by omega) hlen heq
    rwa [show lo + (S - lo) = S by omega] at this
  have hrun := Os.munmap_run os ⟨p, len⟩ (b := b) (blk := blk) (lo := lo) hpb hb hl hK (by rw [hp0]; omega)
    (by rw [hoff, ← hA]; exact hal) hu hs.1.single
  obtain ⟨hh', hpost, hld⟩ := Holds.trim (m' := { m.recordAt b p.off.toNat
    (Nat.min (p.off.toNat + alignUp len.toNat os.pageSize) blk.bytes.size - p.off.toNat) .write with
      blocks := m.blocks.set! b (Os.Unmap.apply blk (.tail (lo + k))) })
    (hi := lo + k) hh hpre hb hl hsz hK hpb hoff (by omega) (by omega) (by omega) rfl rfl
  exact ⟨(), _, _, hrun, hh', hpost, ⟨Mem.Seq.replace (singleThread_recordAt hs.1.single _ _ _ _),
    hs.2.1, hld hs.2.2⟩⟩

/-! ## `munmap` of a page prefix -/

/-- **munmap, page prefix, from the extent.** The mapping's full extent and the bytes of its first
pages `[lo, lo + k)` (`k = alignUp len P`, short of the mapping's end; any labels): `munmap` from
the live start leaves the extent of the mapping live from `lo + k`, at the same address and size.
The kept bytes `[lo + k, S)` stay with whoever owns them. -/
theorem FTotalTriple.munmapPrefix' (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo : Nat}
    {K' : BlockKind} {pre : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hlen : 0 < len.toNat)
    (hk : pre.size = alignUp len.toNat os.pageSize) (hlt : lo + pre.size < S)
    (hal : (A + lo) % os.pageSize = 0) :
    FTotalTriple (up (bytesAt p A S' K' pre) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b S (.mapped (lo + pre.size))) := by
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_comm hpre)
  obtain ⟨hXr, -, -⟩ := up_sep_bext hpre
  have hoff : p.off.toNat = lo := by rw [hp0]; omega
  have hpos : 0 < pre.size := by have := le_alignUp len.toNat os.pageSize; omega
  -- the first unmapped byte gives the block's address
  have hA : A = blk.addr := by
    obtain ⟨b', hb', -, hcells⟩ := hXr
    rw [hpb] at hb'; cases hb'
    have := hcells (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at this
    simp only [FHeap.erase, Option.map_eq_some_iff] at this
    obtain ⟨fc, hfc, he⟩ := this
    obtain ⟨blk', hb'', -, -, -, ha, -⟩ := hh.block hfc
    rw [hb] at hb''; cases hb''
    rw [← ha, he]
  have hu : Os.unmapCase os.pageSize lo blk.bytes.size p.off.toNat len.toNat =
      some (.prefix (lo + pre.size)) := by
    rw [hsz, hoff, hk]
    have h1 := le_alignUp (S - lo) os.pageSize
    have := unmapCase_prefix (P := os.pageSize) (lo := lo) (S := S - lo) (n := len.toNat)
      (by omega) hlen (by omega)
    rwa [show lo + (S - lo) = S by omega] at this
  have hrun := Os.munmap_run os ⟨p, len⟩ (b := b) (blk := blk) (lo := lo) hpb hb hl hK (by rw [hp0]; omega)
    (by rw [hoff, ← hA]; exact hal) hu hs.1.single
  let nb : Block := { blk with kind := .mapped (lo + pre.size) }
  let m' : Mem := { m.recordAt b p.off.toNat
    (Nat.min (p.off.toNat + alignUp len.toNat os.pageSize) blk.bytes.size - p.off.toNat) .write with
      blocks := m.blocks.set! b nb }
  have hb' : m'.blocks[b]? = some nb := by rw [blocks_set_get hb rfl]; simp
  have hheap := heap_mapped hb hl hK
  have hheap' := heap_mapped (blk := nb) hb' hl rfl
  have hh' := Holds.reblock (m' := m') (nb := nb) hh hpre hb rfl rfl hl rfl (by simp [nb, hK, BlockKind.norm])
    (by simp [nb, BlockKind.mappedLo]; omega)
    (fun o c c' hc hc' => by
      obtain ⟨_, e1, -, ho1, rfl⟩ := Mem.heap_some hc
      obtain ⟨_, e2, -, ho2, rfl⟩ := Mem.heap_some hc'
      rw [hb] at e1; cases e1; rw [hb'] at e2; cases e2
      simp [nb])
    (fun h hX l => by
      rw [bytesAt_dom hpb hX l, hoff]
      obtain ⟨x, o⟩ := l
      by_cases hx : x = b
      · subst hx
        have h1 := hheap o
        have h2 := hheap' o
        rw [hsz] at h1; simp only [nb] at h2; rw [hsz] at h2
        simp only [true_and]
        constructor
        · rintro ⟨ha1, ha2⟩
          exact ⟨h1.mpr ⟨by omega, by omega⟩,
            Classical.byContradiction fun hc => by have := h2.mp hc; omega⟩
        · rintro ⟨hb1, hb2⟩
          obtain ⟨hlo1, hlt1⟩ := h1.mp hb1
          have hn : ¬ (lo + pre.size ≤ o ∧ o < S) := fun hc => (h2.mpr hc) hb2
          exact ⟨by omega, by omega⟩
      · simp [hx])
  have hpost := reblockRes_bext (m := m) (m' := m') (b := b) (nb := nb) fun o h' => by
    have := (hheap' o).mp h'; exact (hheap o).mpr ⟨by omega, this.2⟩
  rw [show nb.bytes.size = S from hsz] at hpost
  exact ⟨(), m', _, hrun, hh', hpost, ⟨Mem.Seq.replace (singleThread_recordAt hs.1.single _ _ _ _),
    hs.2.1, LDMono.set (nb := nb) hb (fun _ => hl) rfl (Nat.le_refl _) rfl hs.2.2⟩⟩

/-! ## `mremap` growth in place -/

/-- `Holds` reads a memory only through its blocks and its atomic layout. -/
theorem Holds.congrMem {m m' : Mem} {r rF : Res} (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hh : Holds m r rF) : Holds m' r rF := by
  have e1 : m'.heap = m.heap := by funext ⟨x, o⟩; simp only [Mem.heap, hb]
  have e2 : shapes m' = shapes m := by simp only [shapes, ha]
  have e3 : m'.kn = m.kn := by funext x A; simp only [Mem.kn, hb]
  obtain ⟨hd, hm, hk, hkF, hg, ht⟩ := hh
  refine ⟨hd, ?_, e3 ▸ hk, e3 ▸ hkF, hg, fun x => ?_⟩
  · unfold FMatch; rw [e1, e2]; exact hm
  · have := ht x; unfold ECell.TrueIn at this ⊢; simpa only [hb] using this

/-- A resource after `Holds.reblock` that owns the bytes that became live as `P`. -/
theorem reblockRes_up {m m' : Mem} {b : BlockId} {nb : Block} {P : Assn}
    (hP : P (reblockRes m m' b nb).heap.erase) :
    (up P ⋆ bext b nb.bytes.size nb.kind) (reblockRes m m' b nb) :=
  ⟨⟨(reblockRes m m' b nb).heap, Know.none, Ghost.unit⟩,
    ⟨FHeap.empty, Know.none, Ghost.exts (extOne b nb.bytes.size nb.kind)⟩,
    fun _ => .inr rfl, by simp [reblockRes, FHeap.union_empty, Know.union_none, Ghost.unit_add],
    ⟨hP, rfl, rfl⟩, rfl, rfl, exts_extOne b _ _⟩

/-- What `mremap` without `MAYMOVE` returns for a growth from the full extent: the extent of the
grown mapping and its new bytes `[S, lo + n)` (`mremapFill`), or `error.OutOfMemory` and the
extent unchanged. -/
def mremapGrowPost (P : Nat) (b : BlockId) (S lo n : Nat) (newLen : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok s => ⟪s = ⟨⟨some b, (lo : Int)⟩, newLen⟩⟫ ⋆ FAssn.ex fun A : Nat =>
      up (bytesAt ⟨some b, (S : Int)⟩ A (lo + n) (.mapped lo) (mremapFill P (S - lo) n)) ⋆
        bext b (lo + n) (.mapped lo)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ bext b S (.mapped lo)

/-- **mremap, growth in place, from the extent alone.** Without `MAYMOVE` the mapping grows in
place where the pages after it are free (`Mem.mappingRoom`) and fails with `error.OutOfMemory`
otherwise. The existing bytes stay with whoever owns them; the new ones go to the caller. -/
theorem FTotalTriple.mremapGrow' (os : Os.Target) (hhas : os.hasMremap = true) {b : BlockId}
    {S lo : Nat} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTotalTriple (bext b S (.mapped lo)) (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none)
      (mremapGrowPost os.pageSize b S lo newLen.toNat newLen) := by
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, hlo⟩ := hh.bauth (sep_emp.mpr hpre)
  simp only [BlockKind.mappedLo] at hlo
  subst hsz
  let n := newLen.toNat
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hh₁ : Holds m₁ r rF := Holds.congrMem (m := m) rfl rfl hh
  have hs₁ : m₁.FSeq := ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩
  have hrun := (Os.mremap_eq (m := m) (oldLen := oldLen) (newLen := newLen) os hhas (.inl rfl) hb hl
    hK (by omega) hold).trans (Os.mremapLive_grow os _ b blk lo newLen 0 hn hs.1.single)
  have hmv : ¬ ((0 : BitVec 32) = Os.mremapMayMove ∧ (m.allocPolicy.os.mremapMoves m.allocs n = true ∨
      m.mappingRoom b blk lo (alignUp n os.pageSize) = false)) := fun h => by
    have := h.1; simp [Os.mremapMayMove] at this
  rw [if_neg hmv] at hrun
  by_cases hd : m.mapDenied n
  · rw [if_pos hd] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg hd] at hrun
  by_cases ht : m.mappingRoom b blk lo (alignUp n os.pageSize) = false
  · rw [if_pos ht] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg ht] at hrun
  have hroom : m.mappingRoom b blk lo (alignUp n os.pageSize) = true := by simpa using ht
  -- in place
  let fill := mremapFill os.pageSize (blk.bytes.size - lo) n
  have hfs : fill.size = n - (blk.bytes.size - lo) := mremapFill_size _ _ _
  let nb : Block := { blk with bytes := blk.bytes ++ fill }
  have hnbs : nb.bytes.size = lo + n := by simp only [nb, Array.size_append, hfs]; omega
  let m₂ := m₁.mremapGrown os.pageSize b blk lo n
  have hb₁ : m₁.blocks[b]? = some blk := hb
  have hb₂ : m₂.blocks[b]? = some nb := by rw [blocks_set_get hb₁ rfl]; simp [nb, fill]
  have hheap := heap_mapped hb₁ hl hK
  have hheap' := heap_mapped (blk := nb) hb₂ hl hK
  have hh₂ := Holds.reblock (m' := m₂) (nb := nb) (X := Assn.emp) hh₁
    (sep_comm (sep_emp.mpr hpre) |> sep_mono_left fun _ h => up_emp.mpr h) hb₁ rfl rfl hl rfl rfl
    (by rw [hK, hnbs]; simp only [BlockKind.mappedLo]; omega)
    (fun o c c' hc hc' => by
      obtain ⟨_, e1, -, ho1, rfl⟩ := Mem.heap_some hc
      obtain ⟨_, e2, -, ho2, rfl⟩ := Mem.heap_some hc'
      rw [hb₁] at e1; cases e1; rw [hb₂] at e2; cases e2
      simp [nb, Array.getElem_append_left ho1])
    (fun h hX l => by
      rw [show h = Heap.empty from hX]
      simp only [Heap.empty, ne_eq, not_true_eq_false, false_iff, not_and, Decidable.not_not]
      rintro rfl hm
      have := (hheap l.2).mp hm
      exact Classical.byContradiction fun hc => hc ((hheap' l.2).mpr ⟨this.1, by omega⟩) |>.elim)
  refine ⟨_, m₂, _, hrun, hh₂, sep_lift.mpr ⟨rfl, ⟨blk.addr, ?_⟩⟩, ⟨Mem.Seq.replace hs.1.single,
    hs.2.1, LDMono.grow (nb := nb) (lo := lo) (len := alignUp n os.pageSize) hb₁ hl rfl (by omega)
      (by rw [hnbs]; have := le_alignUp n os.pageSize; omega)
      (fun j o hj ho => Mem.mappingRoom_clear hroom j o hj ho) rfl hs₁.2.2⟩⟩
  have hup := reblockRes_up (m := m₁) (m' := m₂) (b := b) (nb := nb)
    (P := bytesAt ⟨some b, (blk.bytes.size : Int)⟩ blk.addr (lo + n) (.mapped lo) fill) ?_
  · rw [hnbs, show nb.kind = .mapped lo from hK] at hup; exact hup
  refine ⟨b, rfl, Int.natCast_nonneg _, fun ⟨x, o⟩ => ?_⟩
  simp only [reblockRes, FHeap.erase, Int.toNat_natCast]
  by_cases hx : x = b
  · subst hx
    simp only [true_and]
    have h1 := hheap o
    have h2 := hheap' o
    rw [hnbs] at h2
    by_cases hin : blk.bytes.size ≤ o ∧ o < blk.bytes.size + fill.size
    · have hm1 : m₁.heap (x, o) = none := Classical.byContradiction fun hc => by
        have := h1.mp hc; omega
      rw [if_pos hm1, if_pos hin, Mem.heap_of hb₂, dif_pos ⟨hl, by rw [hnbs]; omega, by
        rw [hK]; simp only [BlockKind.mappedLo]; omega⟩]
      simp only [Option.map_some, nb, hK, Array.size_append, hfs]
      rw [Array.getElem_append_right (by omega), getElem!_pos fill (o - blk.bytes.size) (by omega)]
      congr 2; omega
    · rw [if_neg hin]
      by_cases hm1 : m₁.heap (x, o) = none
      · rw [if_pos hm1]
        cases e : m₂.heap (x, o) with
        | none => rfl
        | some c =>
          have h2' := h2.mp (by rw [e]; simp)
          by_cases ho : o < blk.bytes.size
          · exact absurd hm1 (h1.mpr ⟨h2'.1, ho⟩)
          · exfalso; have := hfs; omega
      · rw [if_neg hm1]; rfl
  · simp [hx]

/-! ## `mremap` shrink -/

/-- **mremap, shrink, from the extent.** The mapping's full extent and the cut bytes
`[lo + n, S)` (any labels): `mremap` to `n` bytes stays in place and leaves the extent of the
first `lo + n` bytes; the kept bytes stay with whoever owns them. -/
theorem FTotalTriple.mremapShrink' (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTotalTriple (up (bytesAt ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩ A S' K' cut) ⋆
        bext b S (.mapped lo))
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨⟨some b, (lo : Int)⟩, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_comm hpre)
  rw [← hsz] at hold
  have hrun := (Os.mremap_eq (m := m) (oldLen := oldLen) (newLen := newLen) os hhas hfl hb hl hK
    (by omega) hold).trans
      (Os.mremapLive_shrink os _ b blk lo newLen flags (by omega) (by omega) hs.1.single)
  obtain ⟨hh', hpost, hld⟩ := Holds.trim
    (m' := (m.recordAt b (lo + newLen.toNat) (blk.bytes.size - (lo + newLen.toNat)) .write).mremapShrunk
      b blk lo newLen.toNat)
    (hi := lo + newLen.toNat) hh hpre hb hl hsz hK rfl (by show ((lo + newLen.toNat : Nat) : Int).toNat = _; omega)
    (by omega) hn hcut rfl rfl
  exact ⟨_, _, _, hrun, hh', sep_lift.mpr ⟨rfl, hpost⟩,
    ⟨Mem.Seq.replace (singleThread_recordAt hs.1.single _ _ _ _), hs.2.1, hld hs.2.2⟩⟩

end Full
end Zig
