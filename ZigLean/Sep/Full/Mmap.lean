import ZigLean.Sep.Full.Pinned
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Mmap
import ZigLean.Sep.Full.AutoAttr

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
    have hv := hok.1.2.1 b
    have hle : (gF.extent b).Le (((Ghost.exts E).add gF).extent b) := ECell.le_add' _ _
    refine ⟨ECell.Valid.of_add (b := (Ghost.exts E).extent b) ?_,
      ECell.TagOk.of_le (ls' := ((Ghost.exts E).add gF).ls)
        (fun _ _ _ h => by rw [hep]; exact h) hok.1.uniq hle hv.2⟩
    rw [ECell.add_comm]; exact hv.1
  refine ⟨⟨fun γ => ?_, fun b => ?_, hok.1.2.2.congr (by rw [Ghost.exts_add_cl, Ghost.exts_add_cl])
    (by rw [Ghost.ls_exts_add, Ghost.ls_exts_add])⟩, ?_⟩
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

/-- The heap part of `Holds.reblock`: block `b` becomes `nb` (same address, kind of the same
normal form, live bytes keep their values), and the resource's bytes are exactly those that stop
being live. Then `reblockRes`'s new bytes and the frame match the new memory. -/
theorem Holds.reblock_heap {m m' : Mem} {r rF : Res} {b : BlockId} {blk nb : Block}
    (hh : Holds m r rF) (hb : m.blocks[b]? = some blk) (hbs : m'.blocks = m.blocks.set! b nb)
    (hsh : shapes m' = shapes m) (ha : nb.addr = blk.addr) (hk : nb.kind.norm = blk.kind.norm)
    (hkeep : ∀ o c c', m.heap (b, o) = some c → m'.heap (b, o) = some c' → c'.byte = c.byte)
    (hdom : ∀ l, r.heap l ≠ none ↔ (l.1 = b ∧ m.heap l ≠ none ∧ m'.heap l = none)) :
    FHeap.Disjoint (reblockRes m m' b nb).heap rF.heap ∧
      FMatch m' ((reblockRes m m' b nb).heap ∪ rF.heap) := by
  have hget := blocks_set_get hb hbs
  have hb' : m'.blocks[b]? = some nb := by rw [hget]; simp
  have hoth : ∀ l : Loc, l.1 ≠ b → m'.heap l = m.heap l := fun ⟨x, o⟩ hx => by
    simp only [Mem.heap]; rw [hget x, if_neg hx]
  have hFlive : ∀ l fc, rF.heap l = some fc → m.heap l ≠ none := fun l fc h => by
    obtain ⟨c, hc, -⟩ := hh.swap.cellN h; rw [hc]; simp
  have hold := hh.heap.1
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩⟩
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
  -- the frame's claims on `b` are dormant
  have hok : Ghost.Ok (Ghost.exts (extOne b S K)) rF.gh := by
    have := hh.ghost.1; rwa [hrg] at this
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have := full_excl hok (b := b) (S := S) (K := K) (by simp [Ghost.exts, extOne])
    rwa [Ghost.ls_exts_add] at this
  obtain ⟨hdisj, hmatch⟩ := hh.reblock_heap hb hbs hsh ha hk hkeep hdom
  refine ⟨hdisj, hmatch, Know.sub_none _,
    hh.knowF.trans (KMono.set hb ha hbs), ⟨Ghost.ok_exts_change hok fun x hx => ?_, fun x => ?_,
      (hh.ghost.2.2.mono (by rw [hbs]; simp)).congr (by simp only [reblockRes]; rw [hrg, Ghost.exts_add_cl, Ghost.exts_add_cl])⟩⟩
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
    · have ht := hh.ghost.2.1 x
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

/-- The resource after `Holds.grow`: the bytes that became live and the authority over `nb`'s
extent with the fraction `q`. -/
def growRes (m m' : Mem) (b : BlockId) (nb : Block) (q : Frac) : Res :=
  ⟨(reblockRes m m' b nb).heap, Know.none, Ghost.atExt b (ECell.auth1 nb.bytes.size nb.kind q)⟩

/-- A cell whose authority claim moves: the shares stay. -/
theorem ECell.auth1_move {S S' : Nat} {K K' : BlockKind} {q : Frac} {d : ECell}
    (hv : ((ECell.auth1 S K q).add d).Valid) :
    (∀ x, d.auth x = 0) ∧ ((ECell.auth1 S' K' q).add d).Valid ∧
      (ECell.auth1 S' K' q).add d =
        { ((ECell.auth1 S K q).add d) with auth := (ECell.auth1 S' K' q).auth } := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hz : ∀ x, d.auth x = 0 := fun x => by
    have := h1 x
    by_cases hx : x = (S, K)
    · subst hx; simp [ECell.add, ECell.auth1] at this; omega
    · rcases Nat.eq_zero_or_pos (d.auth x) with h | h
      · exact h
      · exact absurd (h2 (S, K) x (by simp [ECell.add, ECell.auth1]; omega)
          (by simp only [ECell.add]; omega)).symm hx
  have he : (ECell.auth1 S' K' q).add d =
      { ((ECell.auth1 S K q).add d) with auth := (ECell.auth1 S' K' q).auth } := by
    ext <;> simp [ECell.add, ECell.auth1, hz]
  refine ⟨hz, ⟨fun x => ?_, fun x y hx hy => ?_, fun n => ?_⟩, he⟩
  · simp only [ECell.add, hz, Nat.add_zero, ECell.auth1]; split <;> omega
  · simp only [ECell.add, hz, Nat.add_zero, ECell.auth1] at hx hy
    split at hx <;> split at hy <;> simp_all
  · rw [he, ECell.total_eq]; have := h3 n; rw [ECell.total_eq] at this; exact this

/-- **A block grows under a partial authority**: the resource holds the authority over `b`'s
extent with any fraction `q` (the shares of `1 - q` are out); `b` grows in place (same address and
kind, at least as many bytes, the live bytes keep their values). Every share stays true (the block
only grows), so the new memory holds the new bytes and the authority over the grown extent with
the same fraction. -/
theorem Holds.grow {m m' : Mem} {r rF : Res} {b : BlockId} {blk nb : Block} {S : Nat}
    {K : BlockKind} {q : Frac} (hh : Holds m r rF) (hp : Zig.Full.bauth b S K q r)
    (hb : m.blocks[b]? = some blk) (hbs : m'.blocks = m.blocks.set! b nb)
    (hsh : shapes m' = shapes m) (hl : nb.live = true) (ha : nb.addr = blk.addr)
    (hk : nb.kind = blk.kind) (hsz : blk.bytes.size ≤ nb.bytes.size)
    (hkeep : ∀ o c c', m.heap (b, o) = some c → m'.heap (b, o) = some c' → c'.byte = c.byte) :
    Holds m' (growRes m m' b nb q) rF := by
  obtain ⟨blk0, hb0, hl0, hS, hK, hlo⟩ := hh.bauth (sep_emp.mpr hp)
  rw [hb] at hb0; cases hb0
  obtain ⟨hr0, -, hrg⟩ := hp
  have hget := blocks_set_get hb hbs
  have hb' : m'.blocks[b]? = some nb := by rw [hget]; simp
  have hdom : ∀ l, r.heap l ≠ none ↔ (l.1 = b ∧ m.heap l ≠ none ∧ m'.heap l = none) := by
    rintro ⟨x, o⟩
    rw [hr0]
    simp only [FHeap.empty, ne_eq, not_true_eq_false, false_iff, not_and, Decidable.not_not]
    rintro rfl hm
    rw [Mem.heap_of hb'] at ⊢
    rw [Mem.heap_of hb] at hm
    split at hm
    · rename_i hc
      rw [dif_pos ⟨hl, by omega, by rw [hk]; exact hc.2.2⟩]; simp
    · exact absurd rfl hm
  obtain ⟨hdisj, hmatch⟩ := hh.reblock_heap hb hbs hsh ha (by rw [hk]) hkeep hdom
  have hok := hh.ghost.1
  rw [hrg] at hok
  -- the cell of `b` before and after
  have hvb := hok.1.2.1 b
  have ecb : ∀ c : ECell, ((Ghost.atExt b c).add rF.gh).extent b = c.add (rF.gh.extent b) := by
    intro c; simp [Ghost.add, Ghost.atExt]
  have ecx : ∀ (c : ECell) x, x ≠ b → ((Ghost.atExt b c).add rF.gh).extent x = rF.gh.extent x := by
    intro c x hx; simp [Ghost.add, Ghost.atExt, hx]
  have els : ∀ c, ((Ghost.atExt b c).add rF.gh).ls = rF.gh.ls := by
    intro c; funext γ e p; simp [Ghost.ls, Ghost.add, Ghost.atExt]
  rw [ecb, els] at hvb
  obtain ⟨hz, hv', he⟩ := ECell.auth1_move (S' := nb.bytes.size) (K' := nb.kind) hvb.1
  refine ⟨hdisj, hmatch, Know.sub_none _, hh.knowF.trans (KMono.set hb ha hbs), ?_⟩
  show GOk m' (Ghost.atExt b (ECell.auth1 nb.bytes.size nb.kind q)) rF.gh
  refine ⟨⟨⟨fun γ => ?_, fun x => ?_, hok.1.2.2.congr (by funext x y; simp) (by rw [els, els])⟩, ?_⟩,
    fun x => ?_, (hh.ghost.2.2.mono (by rw [hbs]; simp)).congr (by rw [hrg]; funext x y; simp)⟩
  · have := hok.1.1 γ; simpa [Ghost.add, Ghost.atExt] using this
  · show ((((Ghost.atExt b _).add rF.gh).extent x).Valid ∧ _)
    rw [els]
    by_cases hx : x = b
    · subst hx; rw [ecb, he]; exact ⟨he ▸ hv', hvb.2⟩
    · have := hok.1.2.1 x; rw [ecx _ _ hx, els] at this; rw [ecx _ _ hx]; exact this
  · obtain ⟨N, hN⟩ := hok.2
    refine ⟨N, fun γ hγ => ⟨?_, fun x e k => ?_, fun γ' e' M e => ?_⟩⟩
    · have := (hN γ hγ).1; simpa [Ghost.add, Ghost.atExt] using this
    · have := (hN γ hγ).2.1 x e k
      by_cases hx : x = b
      · subst hx; rw [ecb] at this ⊢; rw [he]; exact this
      · rw [ecx _ _ hx] at this ⊢; exact this
    · have := (hN γ hγ).2.2 γ' e' M e; simpa [Ghost.add, Ghost.atExt] using this
  · show ECell.TrueIn _ _ _ _
    have ht := hh.ghost.2.1 x
    rw [hrg] at ht
    change ECell.TrueIn _ m _ _ at ht
    rw [els] at ht ⊢
    by_cases hx : x = b
    · subst hx
      rw [ecb] at ht ⊢
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · simp only [ECell.add, hz, Nat.add_zero, ECell.auth1] at hp'
        split at hp'
        · rename_i e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨nb, hb', hl, rfl, rfl, by rw [hk, hK]; omega⟩
        · cases hp'
      · rw [he] at hk'
        obtain ⟨blk1, hb1, -, hk1, -⟩ := ht.2 k hk'
        rw [hb] at hb1; cases hb1
        exact ⟨nb, hb', hl, by omega, by rw [hk, hK]; omega⟩
    · rw [ecx _ _ hx] at ht ⊢
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
  · funext x y; simp [Ghost.atExt, Ghost.exts]

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
  exact ⟨(), _, _, hrun, hh', hpost, ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩,
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
  exact ⟨(), m', _, hrun, hh', hpost, ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩,
    hs.2.1, LDMono.set (nb := nb) hb (fun _ => hl) rfl (Nat.le_refl _) rfl hs.2.2⟩⟩

/-! ## `mremap` growth in place -/

/-- `Holds` reads a memory only through its blocks and its atomic layout. -/
theorem Holds.congrMem {m m' : Mem} {r rF : Res} (hb : m'.blocks = m.blocks)
    (ha : m'.atomics = m.atomics) (hh : Holds m r rF) : Holds m' r rF := by
  have e1 : m'.heap = m.heap := by funext ⟨x, o⟩; simp only [Mem.heap, hb]
  have e2 : shapes m' = shapes m := by simp only [shapes, ha]
  have e3 : m'.kn = m.kn := by funext x A; simp only [Mem.kn, hb]
  obtain ⟨hd, hm, hk, hkF, hg, ht, hcf⟩ := hh
  refine ⟨hd, ?_, e3 ▸ hk, e3 ▸ hkF, hg, fun x => ?_, fun x hx => hcf x (by rw [← hb]; exact hx)⟩
  · unfold FMatch; rw [e1, e2]; exact hm
  · have := ht x; unfold ECell.TrueIn at this ⊢; simpa only [hb] using this

/-- A resource after `Holds.grow` that owns the bytes that became live as `P`. -/
theorem growRes_up {m m' : Mem} {b : BlockId} {nb : Block} {q : Frac} {P : Assn}
    (hP : P (growRes m m' b nb q).heap.erase) :
    (up P ⋆ bauth b nb.bytes.size nb.kind q) (growRes m m' b nb q) :=
  ⟨⟨(growRes m m' b nb q).heap, Know.none, Ghost.unit⟩,
    ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 nb.bytes.size nb.kind q)⟩,
    fun _ => .inr rfl, by simp [growRes, FHeap.union_empty, Know.union_none, Ghost.unit_add],
    ⟨hP, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- What `mremap` without `MAYMOVE` returns for a growth under the authority `q` over the
mapping's extent: the authority over the grown extent and the new bytes `[S, lo + n)`
(`mremapFill`), or `error.OutOfMemory` and the authority unchanged. -/
def mremapGrowPost (P : Nat) (b : BlockId) (S lo n : Nat) (q : Frac) (newLen : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok s => ⟪s = ⟨⟨some b, (lo : Int)⟩, newLen⟩⟫ ⋆ FAssn.ex fun A : Nat =>
      up (bytesAt ⟨some b, (S : Int)⟩ A (lo + n) (.mapped lo) (mremapFill P (S - lo) n)) ⋆
        bauth b (lo + n) (.mapped lo) q
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ bauth b S (.mapped lo) q

/-- **mremap, growth in place, from the authority alone.** Without `MAYMOVE` the mapping grows in
place where the pages after it are free (`Mem.mappingRoom`) and fails with `error.OutOfMemory`
otherwise. The authority may hold any fraction `q` of the extent (`bext` is `q = 1`): growth keeps
every share true. The existing bytes stay with whoever owns them; the new ones go to the caller. -/
theorem FTotalTriple.mremapGrow' (os : Os.Target) (hhas : os.hasMremap = true) {b : BlockId}
    {S lo : Nat} {q : Frac} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTotalTriple (bauth b S (.mapped lo) q)
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none)
      (mremapGrowPost os.pageSize b S lo newLen.toNat q newLen) := by
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
      m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false)) := fun h => by
    have := h.1; simp [Os.mremapMayMove] at this
  rw [if_neg hmv] at hrun
  by_cases hd : m.mapDenied n
  · rw [if_pos hd] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg hd] at hrun
  by_cases ht : m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false
  · rw [if_pos ht] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg ht] at hrun
  have hroom : m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = true := by simpa using ht
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
  have hh₂ := Holds.grow (m' := m₂) (nb := nb) hh₁ hpre hb₁ rfl rfl hl rfl rfl
    (by simp only [nb, Array.size_append]; omega)
    (fun o c c' hc hc' => by
      obtain ⟨_, e1, -, ho1, rfl⟩ := Mem.heap_some hc
      obtain ⟨_, e2, -, ho2, rfl⟩ := Mem.heap_some hc'
      rw [hb₁] at e1; cases e1; rw [hb₂] at e2; cases e2
      simp [nb, Array.getElem_append_left ho1])
  refine ⟨_, m₂, _, hrun, hh₂, sep_lift.mpr ⟨rfl, ⟨blk.addr, ?_⟩⟩, ⟨⟨hs.1.single⟩,
    hs.2.1, LDMono.grow (nb := nb) (lo := lo) (len := alignUp n os.pageSize) hb₁ hl rfl (by omega)
      (by rw [hnbs]; have := le_alignUp n os.pageSize; omega)
      (fun j o hj ho => Mem.mappingRoom_clear hroom j o hj ho)
      (Nat.le_trans (Mem.mappingRoom_le hroom) os.addrLimit_le) rfl hs₁.2.2⟩⟩
  have hup := growRes_up (m := m₁) (m' := m₂) (b := b) (nb := nb) (q := q)
    (P := bytesAt ⟨some b, (blk.bytes.size : Int)⟩ blk.addr (lo + n) (.mapped lo) fill) ?_
  · rw [hnbs, show nb.kind = .mapped lo from hK] at hup; exact hup
  refine ⟨b, rfl, Int.natCast_nonneg _, fun ⟨x, o⟩ => ?_⟩
  simp only [growRes, reblockRes, FHeap.erase, Int.toNat_natCast]
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
    ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1, hld hs.2.2⟩⟩

/-! ## Whole mappings: `mmap` of a fresh block, `munmap` of a whole block

A step that creates or ends a block needs every byte of it, so these two rules lift the legacy
rules of `ZigLean/Sep/Mmap.lean` with the pinned bridge (`FTotalTriple.ofTotal`): the new
mapping's full extent is read back from its cells (`upPost_bext`), and a whole mapping is pinned
by its full extent (`up_sep_bext`). Clients see only full-state assertions. -/

/-- What `mmap` returns over full-state resources: a fresh mapping of `len` zero bytes, live
from offset 0 at a page-aligned address whose pages end at or below the address limit `L`, with
its full extent; or `error.OutOfMemory`. -/
def fmmapPost (P L : Nat) (len : BitVec 64) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = len ∧ s.ptr.off = 0⟫ ⋆ FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪s.ptr.block = some b ∧ A % P = 0 ∧ A + alignUp len.toNat P ≤ L⟫ ⋆
        (up (regionIn s.ptr A len.toNat (.mapped 0) P (Array.replicate len.toNat (.int 0))) ⋆
          bext b len.toNat (.mapped 0))
  | .error e => ⟪e = "OutOfMemory"⟫

/-- **mmap, from nothing**: a fresh mapping of `len` zero bytes with its full extent, or
`error.OutOfMemory` and nothing. For every failure policy. -/
theorem FTotalTriple.mmap' (os : Os.Target) (hint : Option Ptr) (len : BitVec 64)
    (hlen : 0 < len.toNat) :
    FTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPost os.pageSize os.addrLimit len) := by
  refine ((FTotalTriple.ofTotal (E := fun _ => none) (B := fun _ => False)
    (TotalTriple.mmap os hint len hlen) (Tame.mmap _ _ _ _ _ _ _)
    (fun _ he _ _ hl => by rw [he] at hl; cases hl) (fun _ _ _ _ _ _ _ h => by cases h)
    (SizeFree.of_pinned fun _ he _ _ hl => by rw [he] at hl; cases hl)
    (.inl fun _ h => h.elim)).pre fun r hr => upE_none.mpr (up_emp.mpr hr)).eupd_post fun v => ?_
  rcases v with e | s
  · refine EUpd.upPost_up.trans (EUpd.of_imp fun r h => ?_)
    exact ⟨h.1.1, up_emp.mp ⟨h.1.2, h.2⟩⟩
  · intro m r rF hh hp hs
    obtain ⟨hsl, ho, A, hAL, hm⟩ : mmapPost os.pageSize os.addrLimit len (.ok s) r.heap.erase := by
      obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq
    obtain ⟨-, hpos, hA, -, hb⟩ := hm
    obtain ⟨b, hpb, h0, hl⟩ := hb
    have hc : r.heap.erase (b, s.ptr.off.toNat) =
        some ⟨(Array.replicate len.toNat (Byte.int 0))[0]!, A, 0 + len.toNat, .mapped 0⟩ := by
      rw [hl, if_pos ⟨rfl, Nat.le_refl _, by simp at hpos ⊢; omega⟩]; simp
    simp only [FHeap.erase, Option.map_eq_some_iff] at hc
    obtain ⟨fc, hfc, hfe⟩ := hc
    obtain ⟨r', hh', hr'⟩ := EUpd.drop (fun _ h => h) m r rF hh
      (upPost_bext (b := b) (S := len.toNat) (K := .mapped 0) hp
        ⟨_, fc, hfc, by rw [hfe]; simp, by rw [hfe], fun h => h.elim⟩) hs
    obtain ⟨r₁, r₂, hd, he, ⟨hq, hk, hg⟩, h2⟩ := hr'
    obtain ⟨-, -, A', hAL', -, -, hA', -, hb'⟩ := hq
    refine ⟨r', hh', sep_lift.mpr ⟨⟨hsl, ho⟩, b, A', sep_lift.mpr ⟨⟨hpb, hA', hAL'⟩,
      r₁, r₂, hd, he, ⟨⟨?_, by simp, ?_⟩, hk, hg⟩, h2⟩⟩⟩
    · rw [ho]; simpa using hA'
    · simpa using hb'

theorem FTotalTriple.munmapWholeCore (os : Os.Target) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {len : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hS : S = lo + bs.size) (hpos : 0 < bs.size) (hA : A % os.pageSize = 0)
    (hlo : lo % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    FTotalTriple (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo))
      (Os.munmap os ⟨p, len⟩) (fun _ => FAssn.emp) := by
  subst hS
  have hcell : ∀ h, mapping os.pageSize p A lo bs h → ∀ l c, h l = some c →
      l.1 = b ∧ c.size = lo + bs.size ∧ c.kind = .mapped lo := fun h hm l c hl => by
    obtain ⟨e, h1, h2⟩ := bytesAt_of_cell hm.2.2.2.2 hl
    rw [hpb] at e; cases e; exact ⟨rfl, h1, h2⟩
  refine ((FTotalTriple.ofTotal (E := ext1 b (lo + bs.size) (.mapped lo)) (B := fun x => x = b)
    (TotalTriple.munmapWhole os hlen heq) (Tame.munmap _ _)
    (fun h hm l c hl => (hcell h hm l c hl).1)
    (fun h hm l c S' K' hl he => by
      obtain ⟨e1, e2, e3⟩ := hcell h hm l c hl
      simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨e2.trans he.1, e3.trans he.2⟩)
    (SizeFree.of_pinned fun h hm l c hl => ext1_isSome (hcell h hm l c hl).1)
    (.inl fun _ h => ext1_isSome h)).pre fun r hr => ?_).eupd_post
      fun _ => EUpd.upPost_up.trans (EUpd.of_imp fun _ h => up_emp.mp h)
  obtain ⟨hq, hk, hg⟩ := up_sep_bext hr
  exact ⟨⟨hp0, hpos, hA, hlo, hq.2.2⟩, hk, hg⟩

/-- **munmap of a whole mapping** from its bytes (one region `[lo, S)`, any alignment, the
mapping's labels) and its full extent: the block ends; nothing is left. -/
theorem FTotalTriple.munmapWhole' (os : Os.Target) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {len : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.munmap os ⟨p, len⟩) (fun _ => FAssn.emp) :=
  FTotalTriple.lift fun h => FTotalTriple.munmapWholeCore os hpb hp0 (by omega) (by omega) hA hlo hlen
    (by rw [h]; exact heq)

/-- What `mremap` returns for a growth of a whole mapping (`bs`, live from `lo`, at `p` in block
`b`) to `n` bytes: the grown mapping (the old bytes, then `mremapFill`) with its full extent, in
place or moved (a fresh page-aligned block; the old one ends); or `error.OutOfMemory` and the
old mapping. -/
def fmremapPost (P : Nat) (p : Ptr) (b : BlockId) (A S lo a : Nat) (bs : Array Byte)
    (newLen : BitVec 64) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = newLen⟫ ⋆ FAssn.ex fun b' => FAssn.ex fun A' : Nat => FAssn.ex fun lo' : Nat =>
      ⟪s.ptr.block = some b' ∧ s.ptr.off = (lo' : Int) ∧ A' % P = 0 ∧ lo' % P = 0⟫ ⋆
        (up (regionIn s.ptr A' (lo' + newLen.toNat) (.mapped lo') P
          (bs ++ mremapFill P bs.size newLen.toNat)) ⋆ bext b' (lo' + newLen.toNat) (.mapped lo'))
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo))

/-- A legacy post with a cell of a mapping's block whose full extent it may get back. -/
theorem upPost_mapping {Q : Assn} {E : BlockId → Option (Nat × BlockKind)} {r : Res} {b : BlockId}
    (hp : upPost Q (fun x => x = b) E r) (hE : (E b).isSome) {P : Nat} {q : Ptr} {A lo : Nat}
    {bs : Array Byte} (hm : mapping P q A lo bs r.heap.erase) :
    ∃ b', q.block = some b' ∧ ((up Q ⋆ bext b' (lo + bs.size) (.mapped lo)) ⋆
      fun r => r.heap = FHeap.empty ∧ r.know = Know.none) r := by
  obtain ⟨-, hpos, -, -, b', hqb, h0, hl⟩ := hm
  have hc : r.heap.erase (b', q.off.toNat) = some ⟨bs[0]!, A, lo + bs.size, .mapped lo⟩ := by
    rw [hl, if_pos ⟨rfl, Nat.le_refl _, by omega⟩]; simp [hpos]
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, hfe⟩ := hc
  exact ⟨b', hqb, upPost_bext hp ⟨_, fc, hfc, by rw [hfe], by rw [hfe], fun h => h ▸ hE⟩⟩

theorem FTotalTriple.mremapMoveCore (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hS : S = lo + bs.size) (hpos : 0 < bs.size) (hA : A % os.pageSize = 0)
    (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp bs.size os.pageSize)
    (hn : bs.size < newLen.toNat) :
    FTotalTriple (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPost os.pageSize p b A S lo a bs newLen) := by
  subst hS
  refine FTotalTriple.pre (P := ⟪(A + p.off.toNat) % a = 0⟫ ⋆
      (up (regionIn p A (lo + bs.size) (.mapped lo) a bs) ⋆ bext b (lo + bs.size) (.mapped lo)))
    (FTotalTriple.lift fun hal => ?_) fun r hr => by
      refine sep_lift.mpr ⟨?_, hr⟩
      obtain ⟨_, _, _, _, hu, _⟩ := hr; exact hu.1.1
  have hcell : ∀ h, mapping os.pageSize p A lo bs h → ∀ l c, h l = some c →
      l.1 = b ∧ c.size = lo + bs.size ∧ c.kind = .mapped lo := fun h hm l c hl => by
    obtain ⟨e, h1, h2⟩ := bytesAt_of_cell hm.2.2.2.2 hl
    rw [hpb] at e; cases e; exact ⟨rfl, h1, h2⟩
  have hE : (ext1 b (lo + bs.size) (.mapped lo) b).isSome := ext1_isSome rfl
  refine ((FTotalTriple.ofTotal (E := ext1 b (lo + bs.size) (.mapped lo)) (B := fun x => x = b)
    (TotalTriple.mremapGrow os hhas hfl hold0 hold hn) (Tame.mremap _ _ _ _ _ _)
    (fun h hm l c hl => (hcell h hm l c hl).1)
    (fun h hm l c S' K' hl he => by
      obtain ⟨e1, e2, e3⟩ := hcell h hm l c hl
      simp only [ext1, e1, if_pos, Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨e2.trans he.1, e3.trans he.2⟩)
    (SizeFree.of_pinned fun h hm l c hl => ext1_isSome (hcell h hm l c hl).1)
    (.inl fun _ h => ext1_isSome h)).pre fun r hr => ?_).eupd_post fun v => ?_
  · obtain ⟨hq, hk, hg⟩ := up_sep_bext hr
    exact ⟨⟨hp0, hpos, hA, hlo, hq.2.2⟩, hk, hg⟩
  intro m r rF hh hp hs
  rcases v with e | s
  · obtain ⟨he, hm⟩ : e = "OutOfMemory" ∧ mapping os.pageSize p A lo bs r.heap.erase := by
      obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq
    obtain ⟨b', hb', hx⟩ := upPost_mapping hp hE hm
    rw [hpb] at hb'; cases hb'
    obtain ⟨r', hh', r₁, r₂, hd, hr, ⟨hq, hk, hg⟩, h2⟩ := EUpd.drop (fun _ h => h) m r rF hh hx hs
    exact ⟨r', hh', sep_lift.mpr ⟨he, r₁, r₂, hd, hr, ⟨⟨hal, by simp, hq.2.2.2.2.2⟩, hk, hg⟩, h2⟩⟩
  · obtain ⟨hsl, A', lo', hm⟩ : s.len = newLen ∧ ∃ A' lo',
        mapping os.pageSize s.ptr A' lo' (bs ++ mremapFill os.pageSize bs.size newLen.toNat)
          r.heap.erase := by
      obtain ⟨E', ⟨hq, -⟩, -⟩ := hp; exact hq
    have hsz : (bs ++ mremapFill os.pageSize bs.size newLen.toNat).size = newLen.toNat := by
      simp only [Array.size_append, mremapFill_size]; omega
    obtain ⟨b', hb', hx⟩ := upPost_mapping hp hE hm
    have ho := hm.1
    rw [hsz] at hx
    obtain ⟨r', hh', r₁, r₂, hd, hr, ⟨hq, hk, hg⟩, h2⟩ := EUpd.drop (fun _ h => h) m r rF hh hx hs
    obtain ⟨-, A'', lo'', ho', -, hA'', hlo'', hb''⟩ := hq
    rw [ho] at ho'
    have e : lo' = lo'' := by exact_mod_cast ho'
    subst e
    refine ⟨r', hh', sep_lift.mpr ⟨hsl, b', A'', lo', sep_lift.mpr ⟨⟨hb', ho, hA'', hlo''⟩,
      r₁, r₂, hd, hr, ⟨⟨?_, by simp, ?_⟩, hk, hg⟩, h2⟩⟩⟩
    · rw [ho]; simp only [Int.toNat_natCast]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hA'')
        (Nat.dvd_of_mod_eq_zero hlo''))
    · rwa [hsz] at hb''

/-- **mremap, growth of a whole mapping**, from its bytes (one region `[lo, S)`, the mapping's
labels) and its full extent: for every failure, move and placement decision (`fmremapPost`). -/
theorem FTotalTriple.mremapMove' (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPost os.pageSize p b A S lo a bs newLen) :=
  FTotalTriple.lift fun h => FTotalTriple.mremapMoveCore os hhas hfl hpb hp0 (by omega) (by omega) hA
    hlo hold0 (by rw [h]; exact hold) (by omega)

/-! ## Claims of mappings (`docs/sep-full-state.md` §Byte-range claims)

A new mapping's creator claims its bytes (`FTriple.mintClaimOpt`): `mmap` yields the claim on
`[0, 2^64)` of the new block, past the mapping's end as well, so that an in-place `mremap` growth
(which mints nothing: the block is not new) finds the new bytes already claimed. `mremap` passes the
mapping's claim on: in place it stays, a moved mapping's new block gets a fresh one (the old block's
claim is dropped with the old block). -/

/-- The end of a mapping's claim: past every offset. -/
abbrev claimEnd : Nat := 2 ^ 64

/-- A run of `mmap` that returns a mapping creates its block. -/
theorem Os.mmap_fresh {os : Os.Target} {hint : Option Ptr} {len : BitVec 64} {prot flags fd : BitVec 32}
    {off : BitVec 64} {m m' : Mem} {s : Slice} {b : BlockId}
    (h : ((Os.mmap os hint len prot flags fd off).run m).run = some (.ok (.ok s, m')))
    (hb : s.ptr.block = some b) : m.blocks.size ≤ b ∧ b < m'.blocks.size := by
  unfold Os.mmap at h
  simp only at h
  split at h
  · exact (Tame.throw_bind_ok h).elim
  split at h
  · exact (Tame.throw_bind_ok h).elim
  obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h3
  obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
  have e := Conc.Proto.MemM.set_ok h5
  subst e
  split at h6
  · obtain ⟨h7, -⟩ := Conc.Proto.MemM.pure_ok h6; cases h7
  · obtain ⟨_, m₄, h7, h8⟩ := Conc.Proto.MemM.bind_ok h6
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h7
    obtain ⟨_, m₅, h9, h10⟩ := Conc.Proto.MemM.bind_ok h8
    obtain ⟨h11, rfl⟩ := Conc.Proto.MemM.pure_ok h10
    have e := Conc.Proto.MemM.set_ok h9
    subst e
    cases h11; cases hb
    simp [Mem.afterMmap]

/-- A run of `mremap` that returns a mapping other than the old one creates its block. -/
theorem Os.mremap_fresh {os : Os.Target} {p : Ptr} {oldLen newLen : BitVec 64} {flags : BitVec 32}
    {m m' : Mem} {s : Slice} {b : BlockId}
    (h : ((Os.mremap os (some p) oldLen newLen flags none).run m).run = some (.ok (.ok s, m')))
    (hp : s.ptr ≠ p) (hb : s.ptr.block = some b) : m.blocks.size ≤ b ∧ b < m'.blocks.size := by
  unfold Os.mremap at h
  simp only at h
  split at h
  · exact (Tame.throw_bind_ok h).elim
  obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h1
  obtain ⟨⟨b₀, blk, lo⟩, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
  obtain ⟨rfl, -, -, -⟩ := Tame.mappingAt_ok h3
  split at h4
  · exact (Tame.throw_bind_ok h4).elim
  unfold Os.mremapLive at h4
  simp only at h4
  split at h4
  · exact (Tame.throw_bind_ok h4).elim
  split at h4
  · obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
    obtain ⟨_, m₄, h7, h8⟩ := Conc.Proto.MemM.bind_ok h6
    obtain ⟨h9, -⟩ := Conc.Proto.MemM.pure_ok h8
    cases h9; exact absurd rfl hp
  · obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h5
    obtain ⟨_, m₄, h7, h8⟩ := Conc.Proto.MemM.bind_ok h6
    have e := Conc.Proto.MemM.set_ok h7
    subst e
    split at h8
    · obtain ⟨h9, -⟩ := Conc.Proto.MemM.pure_ok h8; cases h9
    split at h8
    · split at h8
      · obtain ⟨h9, -⟩ := Conc.Proto.MemM.pure_ok h8; cases h9
      obtain ⟨_, m₅, h9, h10⟩ := Conc.Proto.MemM.bind_ok h8
      obtain ⟨-, rfl⟩ := Conc.Proto.recordAccess_ok h9
      obtain ⟨_, m₆, h11, h12⟩ := Conc.Proto.MemM.bind_ok h10
      obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h11
      obtain ⟨_, m₇, h13, h14⟩ := Conc.Proto.MemM.bind_ok h12
      obtain ⟨h15, rfl⟩ := Conc.Proto.MemM.pure_ok h14
      have e := Conc.Proto.MemM.set_ok h13
      subst e
      cases h15; cases hb
      simp [Mem.mremapMoved, Mem.recordAt]
    split at h8
    · obtain ⟨h9, -⟩ := Conc.Proto.MemM.pure_ok h8; cases h9
    · obtain ⟨_, m₅, h9, h10⟩ := Conc.Proto.MemM.bind_ok h8
      obtain ⟨h11, -⟩ := Conc.Proto.MemM.pure_ok h10
      cases h11; exact absurd rfl hp

/-- What `mmap` returns, with the new mapping's claim (`fmmapPost`). -/
def fmmapPostC (P L : Nat) (len : BitVec 64) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = len ∧ s.ptr.off = 0⟫ ⋆ FAssn.ex fun b => FAssn.ex fun A : Nat =>
      ⟪s.ptr.block = some b ∧ A % P = 0 ∧ A + alignUp len.toNat P ≤ L⟫ ⋆
        (up (regionIn s.ptr A len.toNat (.mapped 0) P (Array.replicate len.toNat (.int 0))) ⋆
          (bext b len.toNat (.mapped 0) ⋆ bclaim b 0 claimEnd))
  | .error e => ⟪e = "OutOfMemory"⟫

/-- **mmap with the new mapping's claim** (`FTotalTriple.mmap'`, `FTotalTriple.mintClaimOpt`). -/
theorem FTotalTriple.mmapC (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (hlen : 0 < len.toNat) :
    FTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPostC os.pageSize os.addrLimit len) := by
  refine (FTotalTriple.mintClaimOpt (fun v => match v with | .ok s => s.ptr.block | .error _ => none)
    (fun _ => 0) (fun _ => claimEnd) (FTotalTriple.mmap' os hint len hlen) (fun m v m' b h e => ?_)
    (fun v b r e hq => ?_)).post fun v r h => ?_
  · cases v with
    | error => cases e
    | ok s => exact Os.mmap_fresh h e
  · cases v with
    | error => cases e
    | ok s =>
      exact noCl_sep (noCl_lift _) (noCl_ex fun b => noCl_ex fun A => noCl_sep (noCl_lift _)
        (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _))) r hq b
  · cases v with
    | error => exact sep_emp.mp h
    | ok s =>
      obtain ⟨h1, h⟩ := sep_lift.mp (sep_assoc h)
      obtain ⟨b, h⟩ := sep_ex.mp h
      obtain ⟨A, h⟩ := sep_ex.mp h
      obtain ⟨h2, h⟩ := sep_lift.mp (sep_assoc h)
      have e : (match (Except.ok s : Except ErrName Slice) with | .ok s => s.ptr.block | .error _ => none) =
        some b := h2.1
      rw [e] at h
      exact sep_lift.mpr ⟨h1, b, A, sep_lift.mpr ⟨h2, sep_assoc h⟩⟩

/-- What `mremap` of a whole mapping returns, with the mapping's claim (`fmremapPost`). -/
def fmremapPostC (P : Nat) (p : Ptr) (b : BlockId) (A S lo a : Nat) (bs : Array Byte)
    (newLen : BitVec 64) : Except ErrName Slice → FAssn
  | .ok s => ⟪s.len = newLen⟫ ⋆ FAssn.ex fun b' => FAssn.ex fun A' : Nat => FAssn.ex fun lo' : Nat =>
      ⟪s.ptr.block = some b' ∧ s.ptr.off = (lo' : Int) ∧ A' % P = 0 ∧ lo' % P = 0⟫ ⋆
        (up (regionIn s.ptr A' (lo' + newLen.toNat) (.mapped lo') P
          (bs ++ mremapFill P bs.size newLen.toNat)) ⋆
          (bext b' (lo' + newLen.toNat) (.mapped lo') ⋆ bclaim b' lo' claimEnd))
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
      (bext b S (.mapped lo) ⋆ bclaim b lo claimEnd))

/-- **mremap, growth of a whole mapping, with its claim** (`FTotalTriple.mremapMove'`): in place the
claim stays, a moved mapping gets a fresh one. -/
theorem FTotalTriple.mremapMoveC (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
        (bext b S (.mapped lo) ⋆ bclaim b lo claimEnd)))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPostC os.pageSize p b A S lo a bs newLen) := by
  let nb : Except ErrName Slice → Option BlockId := fun v => match v with
    | .ok s => if s.ptr = p then none else s.ptr.block
    | .error _ => none
  let lo' : Except ErrName Slice → Nat := fun v => match v with
    | .ok s => s.ptr.off.toNat
    | .error _ => 0
  refine (((FTotalTriple.mintClaimOpt nb lo' (fun _ => claimEnd)
    (FTotalTriple.mremapMove' os hhas hfl (A := A) (S := S) (lo := lo) (a := a) (bs := bs) hpb hp0 hlt hA
      hlo hold0 hold hn) ?_ ?_).frame (R := bclaim b lo claimEnd)).pre ?_).eupd_post ?_
  · intro m v m' b' h e
    cases v with
    | error => cases e
    | ok s =>
      by_cases hs : s.ptr = p
      · simp [nb, hs] at e
      · simp only [nb, if_neg hs] at e; exact Os.mremap_fresh h hs e
  · intro v b' r e hq
    cases v with
    | error => cases e
    | ok s =>
      exact noCl_sep (noCl_lift _) (noCl_ex fun b => noCl_ex fun A => noCl_ex fun lo => noCl_sep (noCl_lift _)
        (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _))) r hq b'
  · exact fun r h => sep_assoc' (sep_mono_right (fun _ x => sep_assoc' x) h)
  intro v
  cases v with
  | error e =>
    refine EUpd.of_imp fun r h => ?_
    simp only [nb, lo', optClaim, fmremapPost, fmremapPostC] at h ⊢
    have h := sep_mono_left (fun _ x => sep_emp.mp x) h
    exact sep_mono_right (fun _ x => sep_assoc x) (sep_assoc h)
  | ok s =>
    by_cases hs : s.ptr = p
    · refine EUpd.of_imp fun r h => ?_
      simp only [nb, lo', if_pos hs, optClaim, fmremapPost, fmremapPostC] at h ⊢
      have h := sep_mono_left (fun _ x => sep_emp.mp x) h
      obtain ⟨h1, h⟩ := sep_lift.mp (sep_assoc h)
      obtain ⟨b', h⟩ := sep_ex.mp h
      obtain ⟨A', h⟩ := sep_ex.mp h
      obtain ⟨lo', h⟩ := sep_ex.mp h
      obtain ⟨h2, h⟩ := sep_lift.mp (sep_assoc h)
      have eb : b' = b := by rw [hs, hpb] at h2; exact (Option.some.inj h2.1).symm
      have el : lo' = lo := by have := h2.2.1; rw [hs, hp0] at this; exact_mod_cast this.symm
      subst eb el
      exact sep_lift.mpr ⟨h1, b', A', lo', sep_lift.mpr ⟨h2, sep_assoc h⟩⟩
    · refine (EUpd.drop (fun _ h => ⟨h.1, h.2.1⟩)).trans (EUpd.of_imp fun r h => ?_)
      simp only [nb, lo', if_neg hs, fmremapPost, fmremapPostC] at h ⊢
      obtain ⟨h1, h⟩ := sep_lift.mp (sep_assoc h)
      obtain ⟨b', h⟩ := sep_ex.mp h
      obtain ⟨A', h⟩ := sep_ex.mp h
      obtain ⟨lo', h⟩ := sep_ex.mp h
      obtain ⟨h2, h⟩ := sep_lift.mp (sep_assoc h)
      rw [h2.1, h2.2.1] at h
      simp only [optClaim, Int.toNat_natCast] at h
      exact sep_lift.mpr ⟨h1, b', A', lo', sep_lift.mpr ⟨h2, sep_assoc h⟩⟩

/-! ## Step rules of the symbolic executor

The mapping rules over regions (`regionIn`, the region library's form), tagged `@[fsym]`
(`docs/proof-automation.md`): their side conditions (blocks, offsets, page alignment of lengths
and addresses) are hypotheses. -/

theorem up_regionIn_bytesAt {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte} {X : FAssn}
    {r : Res} (h : (up (regionIn p A S K a bs) ⋆ X) r) : (up (bytesAt p A S K bs) ⋆ X) r :=
  sep_mono_left (fun _ hu => ⟨hu.1.2.2, hu.2⟩) h

/-- `munmap` of a mapping's page tail `[p.off, S)`, from the tail's region and the extent: the
mapping is cut at `p`. -/
theorem FTotalTriple.munmapTailR (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo a : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : 0 ≤ p.off) (hk : lo < p.off.toNat) (hS : S = p.off.toNat + tail.size)
    (htl : 0 < tail.size) (hal : (A + p.off.toNat) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : p.off.toNat - lo + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTotalTriple (up (regionIn p A S' K' a tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b p.off.toNat (.mapped lo)) := by
  have e : lo + (p.off.toNat - lo) = p.off.toNat := by omega
  have t := FTotalTriple.munmapTail' os (k := p.off.toNat - lo) (A := A) (S := S) (S' := S') (K' := K')
    (tail := tail) (len := len) hpb (by rw [e]; omega) (by omega) (by omega) htl (by rw [e]; exact hal)
    hlen heq
  rw [e] at t
  exact t.pre fun _ h => up_regionIn_bytesAt h

/-- `mremap` shrinking a mapping (live from `lo`, at `p`) to `newLen` bytes, from the cut bytes'
region and the extent. -/
theorem FTotalTriple.mremapShrinkR (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo a : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} {p : Ptr} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTotalTriple (up (regionIn (p.add newLen.toNat) A S' K' a cut) ⋆ bext b S (.mapped lo))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨p, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  obtain ⟨pb, po⟩ := p
  simp only at hpb hp0; subst hpb hp0
  have e : (⟨some b, (lo : Int)⟩ : Ptr).add newLen.toNat = ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩ := by
    simp [Ptr.add]
  rw [e]
  exact (FTotalTriple.mremapShrink' os hhas hfl hold0 hold hn0 hn hcut).pre fun _ h => up_regionIn_bytesAt h

/-- `alignUp` by a positive size, for the arithmetic solver (`omega` divides by a literal). -/
theorem alignUp_pos_eq {n a : Nat} (h : 0 < a) : alignUp n a = (n + a - 1) / a * a := by
  unfold alignUp; rw [if_neg (by omega)]

attribute [fsym_arith] alignUp_pos_eq Os.Target.pageSize Os.Target.hasMremap mremapFill_size

attribute [fsym] FTotalTriple.mmapC FTotalTriple.munmapWhole' FTotalTriple.mremapMoveC
  FTotalTriple.munmapTailR FTotalTriple.mremapShrinkR

end Full
end Zig
