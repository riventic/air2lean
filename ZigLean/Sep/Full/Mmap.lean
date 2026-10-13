import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Atomic
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.Ops
import ZigLean.Os.MmapRun
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
of it; those steps are the block steps `Holds.push` and `Holds.free` (`Full/Block.lean`). Every
rule is proved on `Holds` from the runs of the calls (`ZigLean/Os/MmapRun.lean`), with no legacy
lifting.
-/

namespace Zig
namespace Full

open FAssn

/-! ## One block's extent changes

`Ghost.ok_exts_change`, `extOne` and `blocks_set_get` are in `Ops.lean`. -/

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
    (hX : ∀ h, X h → ∀ l, h l ≠ none ↔ (l.1 = b ∧ m.heap l ≠ none ∧ m'.heap l = none))
    (hc : blk.kind ≠ .constGlobal) :
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
    hh.knowF.trans (KMono.set hb ha hc hbs), ⟨Ghost.ok_exts_change hok fun x hx => ?_, fun x => ?_,
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
    (hkeep : ∀ o c c', m.heap (b, o) = some c → m'.heap (b, o) = some c' → c'.byte = c.byte)
    (hc : blk.kind ≠ .constGlobal) :
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
  refine ⟨hdisj, hmatch, Know.sub_none _, hh.knowF.trans (KMono.set hb ha hc hbs), ?_⟩
  show GOk m' (Ghost.atExt b (ECell.auth1 nb.bytes.size nb.kind q)) rF.gh
  refine ⟨⟨⟨fun γ => ?_, fun x => ?_, hok.1.2.2.1.congr (by funext x y; simp) (by rw [els, els]),
      by simpa using hok.1.2.2.2⟩, ?_⟩,
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

/-- After a step that makes no byte of `b` live, `reblockRes` is `nb`'s full extent. -/
theorem reblockRes_bext {m m' : Mem} {b : BlockId} {nb : Block}
    (h : ∀ o, m'.heap (b, o) ≠ none → m.heap (b, o) ≠ none) :
    bext b nb.bytes.size nb.kind (reblockRes m m' b nb) := by
  refine ⟨?_, rfl, Ghost.exts_extOne b _ _⟩
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

theorem up_regionIn_bytesAt {p : Ptr} {A S a : Nat} {K : BlockKind} {bs : Array Byte} {X : FAssn}
    {r : Res} (h : (up (regionIn p A S K a bs) ⋆ X) r) : (up (bytesAt p A S K bs) ⋆ X) r :=
  sep_mono_left (fun _ hu => ⟨hu.1.2.2, hu.2⟩) h

/-- Owned bytes (at least one) record their block's address. -/
theorem Holds.addr_of_bytes {m : Mem} {r rF : Res} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {X : FAssn} {b : BlockId} {blk : Block} (hh : Holds m r rF)
    (hp : (up (bytesAt p A S K bs) ⋆ X) r) (hpb : p.block = some b) (hb : m.blocks[b]? = some blk)
    (hpos : 0 < bs.size) : A = blk.addr := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := hp
  obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell h1 hpb hpos
  obtain ⟨blk', hb', -, -, -, ha, -⟩ := hh.block (x := p.off.toNat + 0) (fc := fc)
    (show (r₁.heap ∪ r₂.heap) _ = _ by rw [FHeap.union_apply, hfc]; rfl)
  rw [hb] at hb'; cases hb'
  rw [← ha, hc]

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
  refine ⟨Holds.reblock (nb := nb) (hc := by rw [hK]; nofun) hh hpre hb hbs hsh hl rfl (by simp [nb])
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
      · simp [hx]), ?_, LDMono.set (nb := nb) hb (fun _ => hl) rfl (by rw [hnbs, hsz]; omega) hbs
        (by simp [nb])⟩
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
  have hoff : p.off.toNat = lo + k := by rw [hp0]; omega
  have hA := hh.addr_of_bytes hpre hpb hb htl
  have hu : Os.unmapCase os.pageSize lo blk.bytes.size p.off.toNat len.toNat = some (.tail (lo + k)) := by
    rw [hsz, hoff]
    have := unmapCase_tail (P := os.pageSize) (lo := lo) (S := S - lo) (k := k) (n := len.toNat) hk
      (by omega) hlen heq
    rwa [show lo + (S - lo) = S by omega] at this
  have hrun := Os.munmap_run os ⟨p, len⟩ (b := b) (blk := blk) (lo := lo) hpb hb hl hK (by rw [hp0]; omega)
    (by rw [hoff, ← hA]; exact hal) hu hs.1.single
  let m' : Mem := { m.recordAt b p.off.toNat
    (Nat.min (p.off.toNat + alignUp len.toNat os.pageSize) blk.bytes.size - p.off.toNat) .write with
      blocks := m.blocks.set! b (Os.Unmap.apply blk (.tail (lo + k))) }
  obtain ⟨hh', hpost, hld⟩ := Holds.trim (m' := m')
    (hi := lo + k) hh hpre hb hl hsz hK hpb hoff (by omega) (by omega) (by omega) rfl rfl
  have hs' : m'.FSeq := ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1, hld hs.2.2⟩
  exact ⟨(), _, _, hrun, hh'.retire hs'.2.1 _ _ _, hpost, Mem.FSeq.retire hs' _ _ _⟩

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
  have hoff : p.off.toNat = lo := by rw [hp0]; omega
  have hpos : 0 < pre.size := by have := le_alignUp len.toNat os.pageSize; omega
  have hA := hh.addr_of_bytes hpre hpb hb hpos
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
  have hh' := Holds.reblock (m' := m') (nb := nb) (hc := by rw [hK]; nofun) hh hpre hb rfl rfl hl rfl (by simp [nb, hK, BlockKind.norm])
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
  have hs' : m'.FSeq := ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩,
    hs.2.1, LDMono.set (nb := nb) hb (fun _ => hl) rfl (Nat.le_refl _) rfl
      (by simp only [nb, hK, BlockKind.mappedLo_mapped]; omega) hs.2.2⟩
  exact ⟨(), _, _, hrun, hh'.retire hs'.2.1 _ _ _, hpost, Mem.FSeq.retire hs' _ _ _⟩

/-! ## `mremap` growth in place -/

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
  have hh₂ := Holds.grow (m' := m₂) (nb := nb) (hc := by rw [hK]; nofun) hh₁ hpre hb₁ rfl rfl hl rfl rfl
    (by simp only [nb, Array.size_append]; omega)
    (fun o c c' hc hc' => by
      obtain ⟨_, e1, -, ho1, rfl⟩ := Mem.heap_some hc
      obtain ⟨_, e2, -, ho2, rfl⟩ := Mem.heap_some hc'
      rw [hb₁] at e1; cases e1; rw [hb₂] at e2; cases e2
      simp [nb, Array.getElem_append_left ho1])
  refine ⟨_, m₂, _, hrun, hh₂, sep_lift.mpr ⟨rfl, ⟨blk.addr, ?_⟩⟩,
    ⟨⟨Mem.SingleThread.forgetFrom (m := m₁) hs.1.single _ _⟩,
    hs.2.1, LDMono.grow (nb := nb) (lo := lo) (len := alignUp n os.pageSize) hb₁ hl rfl (by omega)
      (by rw [hnbs]; have := le_alignUp n os.pageSize; omega)
      (fun j o hj ho => Mem.mappingRoom_clear hroom j o hj ho)
      (Nat.le_trans (Mem.mappingRoom_le hroom) os.addrLimit_le) rfl (by simp [nb, hK]) hs₁.2.2⟩⟩
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
  let m' : Mem := { m.recordAt b (lo + newLen.toNat) (blk.bytes.size - (lo + newLen.toNat)) .write with
    blocks := m.blocks.set! b { blk with bytes := blk.bytes.extract 0 (lo + newLen.toNat) } }
  obtain ⟨hh', hpost, hld⟩ := Holds.trim (m' := m')
    (hi := lo + newLen.toNat) hh hpre hb hl hsz hK rfl (by show ((lo + newLen.toNat : Nat) : Int).toNat = _; omega)
    (by omega) hn hcut rfl rfl
  have hs' : m'.FSeq := ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1, hld hs.2.2⟩
  exact ⟨_, _, _, hrun, hh'.retire hs'.2.1 _ _ _, sep_lift.mpr ⟨rfl, hpost⟩, Mem.FSeq.retire hs' _ _ _⟩

/-! ## Whole mappings: `mmap` of a fresh block, `munmap` of a whole block

A step that creates or ends a block needs every byte of it. These are the block steps of
`Full/Block.lean`: `mmap` pushes a new live block (`Holds.push`), `munmap` of a whole mapping ends
it (`Holds.free` from its live bytes `[lo, S)`), and a moving `mremap` does both; a growth in
place is `FTotalTriple.mremapGrow'` with the old bytes framed and relabelled (`EUpd.relabel`). -/

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
  refine FTotalTriple.of_run fun m r rF hh hp hs => ?_
  have hrun := Os.mmap_run os hint len (by omega) m
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hh₁ : Holds m₁ r rF := Holds.congrMem (m := m) rfl rfl hh
  by_cases hdn : (m.mapDenied len.toNat || !os.fits (m.mapAddr os.pageSize len.toNat) len.toNat)
  · rw [if_pos hdn] at hrun
    exact ⟨_, _, r, hrun, hh₁, ⟨rfl, hp⟩, ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩
  rw [if_neg hdn] at hrun
  simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, Os.Target.fits,
    decide_eq_true_eq] at hdn
  let nb : Block :=
    { bytes := Array.replicate len.toNat (.int 0), align := os.pageSize, kind := .mapped 0,
      live := true, addr := m₁.mapAddr os.pageSize len.toNat }
  have hq := pushRes_up m₁.blocks.size nb
  simp only [nb, BlockKind.mappedLo_mapped, Array.size_replicate, Int.ofNat_zero,
    Array.extract_replicate, Nat.min_self, Nat.sub_zero] at hq
  have halig : nb.addr % os.pageSize = 0 := Mem.newAddr_mod m₁ _ _ os.pageSize_pos
  refine ⟨_, _, _, hrun, Holds.congrMem (m := { m₁ with blocks := m₁.blocks.push nb }) rfl rfl
      (hh₁.push hp (nb := nb) rfl (by simp [nb, BlockKind.mappedLo_mapped]; omega)),
    sep_lift.mpr ⟨⟨rfl, rfl⟩, m.blocks.size, nb.addr, sep_lift.mpr ⟨⟨rfl, halig, hdn.2⟩,
      sep_mono_left (fun _ h => ⟨⟨by simpa using halig, nofun, h.1⟩, h.2⟩) hq⟩⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, (Tame.mmap _ _ _ _ _ _ _ m _ _ (by rw [hrun]; rfl)).2.2 hs.2.2⟩⟩

theorem FTotalTriple.munmapWholeCore (os : Os.Target) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {len : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hS : S = lo + bs.size) (hpos : 0 < bs.size) (hA : A % os.pageSize = 0)
    (hlo : lo % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp bs.size os.pageSize) :
    FTotalTriple (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo))
      (Os.munmap os ⟨p, len⟩) (fun _ => FAssn.emp) := by
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_comm hpre)
  have hpre' := up_regionIn_bytesAt hpre
  have hoff : p.off.toNat = lo := by rw [hp0]; omega
  have hA' := hh.addr_of_bytes hpre' hpb hb hpos
  have hu : Os.unmapCase os.pageSize lo blk.bytes.size p.off.toNat len.toNat = some .whole := by
    rw [hsz, hoff, hS]; exact unmapCase_whole hpos hlen heq
  have hal : (blk.addr + p.off.toNat) % os.pageSize = 0 := by
    rw [hoff, ← hA']
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hA) (Nat.dvd_of_mod_eq_zero hlo))
  have hrun := Os.munmap_run os ⟨p, len⟩ (b := b) (blk := blk) (lo := lo) hpb hb hl hK
    (by rw [hp0]; omega) hal hu hs.1.single
  let m' : Mem := { m.recordAt b p.off.toNat
    (Nat.min (p.off.toNat + alignUp len.toNat os.pageSize) blk.bytes.size - p.off.toNat) .write with
      blocks := m.blocks.set! b { blk with live := false } }
  have hs' : m'.FSeq := ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1,
    (LDMono.set (nb := { blk with live := false }) hb (fun h => by cases h) rfl (Nat.le_refl _)
      rfl) hs.2.2⟩
  exact ⟨(), _, _, hrun, (Holds.congrMem (m' := m')
      (m := { m with blocks := m.blocks.set! b { blk with live := false } })
      rfl rfl (hh.free hpre' hpb (by omega) (by simp [hoff]) hb (by rw [hK]; nofun))).retire
      hs'.2.1 _ _ _, ⟨rfl, rfl, rfl⟩, Mem.FSeq.retire hs' _ _ _⟩

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
  have hpe : p = ⟨some b, (lo : Int)⟩ := by
    cases p; simp only at hpb hp0; rw [hpb, hp0]
  subst hpe
  have hP := os.pageSize_pos
  have hAlo : (A + lo) % os.pageSize = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hA) (Nat.dvd_of_mod_eq_zero hlo))
  refine FTotalTriple.of_run fun m r rF hh hpre hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_comm hpre)
  have hcur : blk.bytes.size - lo = bs.size := by omega
  have hpre' := up_regionIn_bytesAt hpre
  have hrun := (Os.mremap_eq (m := m) (oldLen := oldLen) (newLen := newLen) os hhas hfl hb hl hK
    (by omega) (by rw [hcur]; exact hold)).trans
      (Os.mremapLive_grow os _ b blk lo newLen flags (by omega) hs.1.single)
  let n := newLen.toNat
  let m₁ : Mem := { m with allocs := m.allocs + 1 }
  have hh₁ : Holds m₁ r rF := Holds.congrMem (m := m) rfl rfl hh
  have hs₁ : m₁.FSeq := ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩
  have hfill : mremapFill os.pageSize (blk.bytes.size - lo) n = mremapFill os.pageSize bs.size n := by
    rw [hcur]
  have hfs : (mremapFill os.pageSize bs.size n).size = n - bs.size := mremapFill_size _ _ _
  -- the failures leave the mapping as it was
  by_cases hd₁ : m.mapDenied n
  · rw [if_pos hd₁] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg hd₁] at hrun
  by_cases hmv : flags = Os.mremapMayMove ∧ (m.allocPolicy.os.mremapMoves m.allocs n = true ∨
      m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false)
  · rw [if_pos hmv] at hrun
    by_cases hf : os.fits (m.mapAddr os.pageSize n) n = false
    · rw [if_pos hf] at hrun
      exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
    rw [if_neg hf] at hrun
    -- the move: the old block ends (`Holds.free`), the grown copy is a new block (`Holds.push`)
    have hx : blk.bytes.extract lo blk.bytes.size = bs := by
      obtain ⟨r₁, r₂, hd, rfl, h1, -⟩ := hpre'
      obtain ⟨b', blk', hb', hbk', -, -, -, -, -, -, hx⟩ := (Holds.split hd hh).bytesAt_block h1 hpos
      cases hb'; rw [hb] at hbk'; cases hbk'
      simp only [Int.toNat_natCast] at hx
      rwa [← hsz] at hx
    let mr := m₁.recordAt b lo (blk.bytes.size - lo) .write
    have hdead := (Holds.congrMem (m := m) (m' := mr) rfl rfl hh).free hpre' rfl (by simp)
      (by simp [BlockKind.mappedLo_mapped]) hb (by rw [hK]; nofun)
    let nnb : Block :=
      { bytes := blk.bytes.extract lo blk.bytes.size ++ mremapFill os.pageSize (blk.bytes.size - lo) n,
        align := os.pageSize, kind := .mapped 0, live := true, addr := mr.mapAddr os.pageSize n }
    have hnb : nnb.bytes = bs ++ mremapFill os.pageSize bs.size n := by simp only [nnb, hx, hfill]
    have hnbs : nnb.bytes.size = n := by rw [hnb, Array.size_append, hfs]; omega
    have hq := pushRes_up (m.blocks.set! b { blk with live := false }).size nnb
    simp only [Array.size_set!, show nnb.kind = .mapped 0 from rfl, BlockKind.mappedLo_mapped,
      Int.ofNat_zero, Array.extract_size] at hq
    rw [hnbs, hnb] at hq
    have halig : nnb.addr % os.pageSize = 0 := Mem.newAddr_mod mr _ _ hP
    have hpush := hdead.push ⟨rfl, rfl, rfl⟩ (nb := nnb) rfl
      (by rw [hnbs]; simp [nnb, BlockKind.mappedLo_mapped]; omega)
    have hN : (mr.blocks.set! b { blk with live := false }).size = m.blocks.size := by
      simp [mr, m₁, Mem.recordAt]
    dsimp only at hpush
    rw [hN] at hpush
    refine ⟨_, _, _, hrun, Holds.congrMem rfl rfl hpush,
      sep_lift.mpr ⟨rfl, m.blocks.size, nnb.addr, 0, sep_lift.mpr ⟨⟨rfl, rfl, halig, Nat.zero_mod _⟩,
        ?_⟩⟩, ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1,
        (Tame.mremap_mono _ _ _ _ _ _ (m := m) (by rw [hrun]; rfl)).2 hs.2.2⟩⟩
    rw [Nat.zero_add]
    refine sep_mono_left (fun _ h => ?_) hq
    exact ⟨⟨by simpa using halig, nofun, h.1⟩, h.2⟩
  rw [if_neg hmv] at hrun
  by_cases ht : m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false
  · rw [if_pos ht] at hrun
    exact ⟨_, m₁, r, hrun, hh₁, sep_lift.mpr ⟨rfl, hpre⟩, hs₁⟩
  rw [if_neg ht] at hrun
  -- in place: the run of a growth without `MAYMOVE`, whose rule frames the bytes
  have hrun0 : (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none).run m =
      pure (.ok ⟨⟨some b, (lo : Int)⟩, newLen⟩, m₁.mremapGrown os.pageSize b blk lo n) := by
    rw [(Os.mremap_eq (m := m) (oldLen := oldLen) (newLen := newLen) os hhas (.inl rfl) hb hl hK
      (by omega) (by rw [hcur]; exact hold)).trans
        (Os.mremapLive_grow os _ b blk lo newLen 0 (by omega) hs.1.single), if_neg hd₁,
      if_neg (fun h => by simp [Os.mremapMayMove] at h), if_neg ht]
  have hg := (FTotalTriple.mremapGrow' os hhas (b := b) (S := lo + bs.size) (lo := lo) (q := Frac.one)
    (oldLen := oldLen) (newLen := newLen) hold0 (by rw [Nat.add_sub_cancel_left]; exact hold) (by omega)).1.frame
    (R := up (regionIn ⟨some b, (lo : Int)⟩ A (lo + bs.size) (.mapped lo) a bs)) m r rF hh
    (sep_comm hpre) hs
  rw [hrun0] at hg
  obtain ⟨r', hh', hq, hs'⟩ := hg
  obtain ⟨-, hq⟩ := sep_lift.mp (sep_assoc hq)
  obtain ⟨A₀, hq⟩ := sep_ex.mp hq
  rw [Nat.add_sub_cancel_left] at hq
  -- the old bytes, relabelled to the grown size, and the new ones are one region
  obtain ⟨r'', hh'', hq'⟩ := (EUpd.relabel (p := ⟨some b, (lo : Int)⟩) (A := A) (S := lo + bs.size)
    (S' := lo + n) (K := .mapped lo) (a := a) (bs := bs) rfl).frame _ r' rF hh' (sep_comm hq) hs'
  have hm₂ : (m₁.mremapGrown os.pageSize b blk lo n).blocks[b]? =
      some { blk with bytes := blk.bytes ++ mremapFill os.pageSize (blk.bytes.size - lo) n } := by
    rw [blocks_set_get (m := m₁) hb rfl]; simp
  have hA₀ : A₀ = A :=
    (hh''.addr_of_bytes (sep_assoc (sep_comm hq')) rfl hm₂ (by rw [hfs]; omega)).trans
      (hh''.addr_of_bytes (up_regionIn_bytesAt hq') rfl hm₂ hpos).symm
  subst hA₀
  have hadd : (⟨some b, (lo : Int)⟩ : Ptr).add bs.size = ⟨some b, ((lo + bs.size : Nat) : Int)⟩ := by
    simp [Ptr.add]
  refine ⟨_, _, r'', hrun, hh'', sep_lift.mpr ⟨rfl, b, A₀, lo, sep_lift.mpr ⟨⟨rfl, rfl, hA, hlo⟩,
    ?_⟩⟩, hs'⟩
  refine sep_mono_left (fun _ h => ?_) (sep_assoc' hq')
  obtain ⟨⟨h₁, h₂, hd, he, ⟨-, hKc, hb₁⟩, hb₂⟩, hk⟩ := And.intro (sep_up h).1 (sep_up h).2
  exact ⟨⟨by simpa using hAlo, hKc, Region.bytesAt_append.mp ⟨h₁, h₂, hd, he, hb₁, hadd ▸ hb₂⟩⟩, hk⟩

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
(which mints nothing: the block is not new) finds the new bytes already claimed. A mapping live
from `lo` carries the claim on `[lo, lo + 2^64)`: its end lies past every byte of the mapping
without a bound on `lo`. `mremap` passes the
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
          (bext b' (lo' + newLen.toNat) (.mapped lo') ⋆ bclaim b' lo' (lo' + claimEnd)))
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
      (bext b S (.mapped lo) ⋆ bclaim b lo (lo + claimEnd)))

/-- **mremap, growth of a whole mapping, with its claim** (`FTotalTriple.mremapMove'`): in place the
claim stays, a moved mapping gets a fresh one. -/
theorem FTotalTriple.mremapMoveC (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
        (bext b S (.mapped lo) ⋆ bclaim b lo (lo + claimEnd))))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPostC os.pageSize p b A S lo a bs newLen) := by
  let nb : Except ErrName Slice → Option BlockId := fun v => match v with
    | .ok s => if s.ptr = p then none else s.ptr.block
    | .error _ => none
  let lo' : Except ErrName Slice → Nat := fun v => match v with
    | .ok s => s.ptr.off.toNat
    | .error _ => 0
  refine (((FTotalTriple.mintClaimOpt nb lo' (fun v => lo' v + claimEnd)
    (FTotalTriple.mremapMove' os hhas hfl (A := A) (S := S) (lo := lo) (a := a) (bs := bs) hpb hp0 hlt hA
      hlo hold0 hold hn) ?_ ?_).frame (R := bclaim b lo (lo + claimEnd))).pre ?_).eupd_post ?_
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

attribute [fsym_arith] alignUp_pos_eq Os.Target.pageSize Os.Target.hasMremap mremapFill_size claimEnd

attribute [fsym] FTotalTriple.mmapC FTotalTriple.munmapWhole' FTotalTriple.mremapMoveC
  FTotalTriple.munmapTailR FTotalTriple.mremapShrinkR

/-! ## Thread rules (`docs/sep-threads.md`, S2)

The rules above as thread rules (`FTTotalTriple`), each `FTTotalTriple.ofSeq` of its sequential
rule and the locality of its step. `mmap` reads no record and touches no byte of an old block
(`ThreadLocal.mmap`, for every precondition). `munmap` and the `mremap` shrink record a write of
the bytes they remove, which the precondition owns (`ThreadLocal.munmap`,
`ThreadLocal.mremapShrink`), and leave a block with no byte live that was not
(`Mem.NoRevive.setBlock`). An empty cut records a zero-length write, which touches no byte and
races with nothing (`noRace_zero`). The growth in place brings bytes to life
whose history it forgets (`Mem.forgetFrom`); its thread rule comes with S1's step relation. -/

/-- The mapping that `mappingAt p` returns is `p`'s block. -/
theorem _root_.Zig.Os.mappingAt_block {p : Ptr} {m m' : Mem} {r : BlockId × Block × Nat}
    (h : ((Os.mappingAt p).run m).run = some (.ok (r, m'))) : p.block = some r.1 := by
  unfold Os.mappingAt at h
  split at h
  · exact (Conc.Proto.MemM.throw_ok h).elim
  · rename_i b hpb
    obtain ⟨a, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
    split at h₁
    · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · split at h₁
      · split at h₁
        · obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h₁
          exact hpb
        · exact (Conc.Proto.MemM.throw_ok h₁).elim
      · exact (Conc.Proto.MemM.throw_ok h₁).elim

/-- The ranges that `unmapCase` admits: nonempty, from a live offset; a prefix ends at or past
the live start. -/
theorem _root_.Zig.Os.unmapCase_some {P lo hi off n : Nat} {u : Os.Unmap}
    (hu : Os.unmapCase P lo hi off n = some u) :
    0 < n ∧ lo ≤ off ∧ off < hi ∧ ∀ E, u = .prefix E → lo ≤ E := by
  dsimp only [Os.unmapCase] at hu
  split at hu
  · cases hu
  · rename_i h0
    refine ⟨by omega, by omega, by omega, fun E hE => ?_⟩
    subst hE
    split at hu
    · cases hu
    · split at hu
      · rename_i h2; cases hu; omega
      · split at hu <;> cases hu

namespace RunFp

variable {F : Array FootprintEntry} {m₀ : Mem}

/-- `mappingAt` reads the blocks only. -/
theorem mappingAt (p : Ptr) : RunFp F m₀ (Os.mappingAt p) := by
  unfold Os.mappingAt
  split
  · rfl
  · refine get_bind rfl ?_
    split
    · rfl
    · split
      · split <;> rfl
      · rfl

/-- `munmap`, when the write of the removed bytes races in neither memory. -/
theorem munmap (os : Os.Target) (s : Slice)
    (hnr : ∀ b blk lo u, s.ptr.block = some b → m₀.blocks[b]? = some blk → blk.kind = .mapped lo →
      Os.unmapCase os.pageSize lo blk.bytes.size s.ptr.off.toNat s.len.toNat = some u →
      let n := Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size -
        s.ptr.off.toNat
      NoRace m₀ b s.ptr.off.toNat n .write ∧ NoRace (m₀.withFp F) b s.ptr.off.toNat n .write) :
    RunFp F m₀ (Os.munmap os s) := by
  unfold Os.munmap
  refine bind (mappingAt _) fun ⟨b, blk, lo⟩ m₁ h => ?_
  have h' : ((Os.mappingAt s.ptr).run m₀).run = some (.ok ((b, blk, lo), m₁)) := h
  have hpb := Os.mappingAt_block h'
  obtain ⟨rfl, hb, -, hk⟩ := Tame.mappingAt_ok h'
  dsimp only at hpb hb hk ⊢
  split
  · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
  · split
    · exact throw _
    · rename_i u hu
      obtain ⟨h1, h2⟩ := hnr b blk lo u hpb hb hk hu
      exact bind (recordAccess h1 h2) fun _ _ _ => modify rfl

/-- `mmap` reads no record. -/
theorem mmap (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (prot flags fd : BitVec 32)
    (off : BitVec 64) : RunFp F m₀ (Os.mmap os hint len prot flags fd off) := by
  unfold Os.mmap
  simp only
  split
  · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
  · split
    · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
    · refine get_set_bind rfl rfl ?_
      split
      · exact pure _
      · exact get_set_bind rfl rfl (pure _)

/-- `mremap` of the whole mapping at `p` to fewer bytes, when the write of the cut bytes races in
neither memory. -/
theorem mremapShrink (os : Os.Target) (p : Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32)
    (hshr : ∀ b blk lo, p.block = some b → m₀.blocks[b]? = some blk → blk.kind = .mapped lo →
      newLen.toNat ≤ blk.bytes.size - lo ∧
      NoRace m₀ b (lo + newLen.toNat) (blk.bytes.size - (lo + newLen.toNat)) .write ∧
      NoRace (m₀.withFp F) b (lo + newLen.toNat) (blk.bytes.size - (lo + newLen.toNat)) .write) :
    RunFp F m₀ (Os.mremap os (some p) oldLen newLen flags none) := by
  unfold Os.mremap
  simp only
  split
  · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
  · refine bind (pure p) fun p' m₁ hp => ?_
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok hp
    refine bind (mappingAt _) fun ⟨b, blk, lo⟩ m₂ h => ?_
    have h' : ((Os.mappingAt _).run _).run = some (.ok ((b, blk, lo), m₂)) := h
    have hpb := Os.mappingAt_block h'
    obtain ⟨rfl, hb, -, hk⟩ := Tame.mappingAt_ok h'
    dsimp only at hpb hb hk ⊢
    obtain ⟨hn, h1, h2⟩ := hshr b blk lo hpb hb hk
    split
    · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
    · unfold Os.mremapLive
      simp only
      split
      · exact bind (throw _) fun _ _ e => (Conc.Proto.MemM.throw_ok e).elim
      · exact bind (recordAccess h1 h2) fun _ _ _ => bind (modify' rfl) fun _ _ _ => pure _

end RunFp

namespace ThreadLocal

variable {P : FAssn}

/-- **`munmap` of bytes that `P` owns is local**: the removed bytes (the range up to the
mapping's end) are the precondition's; the block keeps no byte live that was not. -/
theorem munmap (os : Os.Target) (s : Slice)
    (hown : ∀ m r rF, Holds m r rF → P r → ∀ b blk, s.ptr.block = some b → m.blocks[b]? = some blk →
      ∀ x, s.ptr.off.toNat ≤ x →
        x < Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size →
        r.heap.erase (b, x) ≠ none) :
    ThreadLocal P (Os.munmap os s) := by
  refine ThreadLocal.intro fun m r rF hh hp hc ho => ?_
  have hpos : ∀ (blk : Block) lo u, Os.unmapCase os.pageSize lo blk.bytes.size s.ptr.off.toNat
      s.len.toNat = some u → 0 < Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize)
        blk.bytes.size - s.ptr.off.toNat := fun blk lo u hu => by
    obtain ⟨hn, -, hoff, -⟩ := Os.unmapCase_some hu
    have := le_alignUp s.len.toNat os.pageSize
    show 0 < Min.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size - s.ptr.off.toNat
    omega
  refine ⟨RunFp.munmap os s fun b blk lo u hpb hb _ hu => ?_, fun v m₀ e => ?_⟩
  · have := hpos blk lo u hu
    exact noRace_owned hc ho fun x h1 h2 => hown m r rF hh hp b blk hpb hb x h1 (by omega)
  · have e' : ((Os.munmap os s).run m.noFp).run = some (.ok (v, m₀)) := e
    unfold Os.munmap at e'
    obtain ⟨⟨b, blk, lo⟩, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok e'
    have hpb := Os.mappingAt_block h1
    obtain ⟨rfl, hb, hl, hk⟩ := Tame.mappingAt_ok h1
    dsimp only at hpb hb hl hk h2
    split at h2
    · exact (Tame.throw_bind_ok h2).elim
    · split at h2
      · exact (Conc.Proto.MemM.throw_ok h2).elim
      · rename_i u hu
        obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
        obtain ⟨-, rfl⟩ := Conc.Proto.recordAccess_ok h3
        obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
        obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h5
        have := Conc.Proto.MemM.set_ok h6
        subst this
        obtain ⟨-, -, hoff, hpre⟩ := Os.unmapCase_some hu
        have hbs : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
        have hp0 := hpos blk lo u hu
        have hown' : ∀ x, s.ptr.off.toNat ≤ x → x < s.ptr.off.toNat +
            (Nat.min (s.ptr.off.toNat + alignUp s.len.toNat os.pageSize) blk.bytes.size -
              s.ptr.off.toNat) → r.heap.erase (b, x) ≠ none :=
          fun x h1 h2 => hown m r rF hh hp b blk hpb hb x h1 (by omega)
        refine ⟨((FStepIn.recordAt (m := m.noFp) hc.1 (FHeap.erase_disjoint hh.disj) hown' hbs
            (fun _ ⟨blk', e1, e2⟩ => ?_)).trans (FStepIn.setBlock fun hK => ?_)).trans
            (FStepIn.retire fun x h1 h2 =>
              ((FHeap.erase_disjoint hh.disj) (b, x)).resolve_left (hown' x h1 h2)),
          Mem.NoRevive.setBlock (m := m) hb rfl ?_ ?_ ?_⟩
        · rw [hb] at e1; cases e1; rw [hk] at e2; cases e2
        · cases u <;> simp [Os.Unmap.apply, hk] at hK
        · cases u <;> simp [Os.Unmap.apply]
        · cases u <;> simp [Os.Unmap.apply] <;> omega
        · cases u
          · exact Nat.le_refl _
          · simp only [Os.Unmap.apply, hk, BlockKind.mappedLo]; exact hpre _ rfl
          · exact Nat.le_refl _

/-- **`mmap` is local** for every precondition: it reads no record and adds a block. -/
theorem mmap (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (prot flags fd : BitVec 32)
    (off : BitVec 64) : ThreadLocal P (Os.mmap os hint len prot flags fd off) := by
  refine ThreadLocal.intro fun m r rF hh hp hc ho => ⟨RunFp.mmap os hint len prot flags fd off,
    fun v m₀ e => ?_⟩
  have h : ((Os.mmap os hint len prot flags fd off).run m.noFp).run = some (.ok (v, m₀)) := e
  unfold Os.mmap at h
  simp only at h
  split at h
  · exact (Tame.throw_bind_ok h).elim
  split at h
  · exact (Tame.throw_bind_ok h).elim
  obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h3
  obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
  have e1 := Conc.Proto.MemM.set_ok h5
  subst e1
  have hst : FStepIn rF.heap.erase m.noFp { m.noFp with allocs := m.noFp.allocs + 1 } :=
    .of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
      Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h)
      (fun _ he hn => absurd he hn)
  split at h6
  · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h6
    exact ⟨hst, fun _ _ _ h => h⟩
  · obtain ⟨_, m₄, h7, h8⟩ := Conc.Proto.MemM.bind_ok h6
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h7
    obtain ⟨_, m₅, h9, h10⟩ := Conc.Proto.MemM.bind_ok h8
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h10
    have e2 := Conc.Proto.MemM.set_ok h9
    subst e2
    refine ⟨hst.trans (.of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      VClock.le_refl _, by simp [Mem.afterMmap], fun _ he => .inl he, fun _ he => .inl he⟩
      (fun b' hb' ⟨blk', e1, e2⟩ => ⟨blk', ?_, e2⟩) (fun _ he hn => absurd he hn)),
      Mem.NoRevive.push rfl⟩
    simp only [Mem.afterMmap, Array.getElem?_push_lt hb'] at e1
    exact (Array.getElem?_eq_getElem hb').trans e1

/-- **The `mremap` shrink of bytes that `P` owns is local**: in every memory of `P` the request
shrinks the mapping at `p`, and `P` owns the cut bytes (none for an empty cut, whose zero-length
write races with nothing). -/
theorem mremapShrink (os : Os.Target) (p : Ptr) (oldLen newLen : BitVec 64) (flags : BitVec 32)
    (hown : ∀ m r rF, Holds m r rF → P r → ∀ b blk lo, p.block = some b → m.blocks[b]? = some blk →
      blk.kind = .mapped lo → lo + newLen.toNat ≤ blk.bytes.size ∧
        ∀ x, lo + newLen.toNat ≤ x → x < blk.bytes.size → r.heap.erase (b, x) ≠ none) :
    ThreadLocal P (Os.mremap os (some p) oldLen newLen flags none) := by
  refine ThreadLocal.intro fun m r rF hh hp hc ho =>
    ⟨RunFp.mremapShrink os p oldLen newLen flags fun b blk lo hpb hb hk => ?_, fun v m₀ e => ?_⟩
  · obtain ⟨hlt, hin⟩ := hown m r rF hh hp b blk lo hpb hb hk
    exact ⟨by omega, noRace_owned hc ho fun x h1 h2 => hin x h1 (by omega)⟩
  · have h : ((Os.mremap os (some p) oldLen newLen flags none).run m.noFp).run =
        some (.ok (v, m₀)) := e
    unfold Os.mremap at h
    simp only at h
    split at h
    · exact (Tame.throw_bind_ok h).elim
    obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h1
    obtain ⟨⟨b, blk, lo⟩, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
    have hpb := Os.mappingAt_block h3
    obtain ⟨rfl, hb, hl, hk⟩ := Tame.mappingAt_ok h3
    dsimp only at hpb hb hl hk h4
    obtain ⟨hlt, hin⟩ := hown m r rF hh hp b blk lo hpb hb hk
    split at h4
    · exact (Tame.throw_bind_ok h4).elim
    unfold Os.mremapLive at h4
    simp only at h4
    split at h4
    · exact (Tame.throw_bind_ok h4).elim
    rw [if_pos (by omega)] at h4
    obtain ⟨_, m₃, h5, h6⟩ := Conc.Proto.MemM.bind_ok h4
    obtain ⟨-, rfl⟩ := Conc.Proto.recordAccess_ok h5
    obtain ⟨_, m₄, h7, h8⟩ := Conc.Proto.MemM.bind_ok h6
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h8
    have e1 := Conc.Proto.modify_ok h7
    subst e1
    have hin' : ∀ x, lo + newLen.toNat ≤ x →
        x < lo + newLen.toNat + (blk.bytes.size - (lo + newLen.toNat)) →
        r.heap.erase (b, x) ≠ none := fun x h1 h2 => hin x h1 (by omega)
    refine ⟨((FStepIn.recordAt (m := m.noFp) hc.1 (FHeap.erase_disjoint hh.disj) hin'
      (Array.getElem?_eq_some_iff.mp hb).1
        (fun _ ⟨blk', e1, e2⟩ => ?_)).trans (FStepIn.setBlock fun hK => ?_)).trans
        (FStepIn.retire fun x h1 h2 =>
          ((FHeap.erase_disjoint hh.disj) (b, x)).resolve_left (hin' x h1 h2)), ?_⟩
    · rw [hb] at e1; cases e1; rw [hk] at e2; cases e2
    · simp [hk] at hK
    exact Mem.NoRevive.setBlock (m := m) hb rfl (fun h => h)
      (by simp only [Array.size_extract]; omega) (Nat.le_refl _)

/-- The memory after a growth in place (`Mem.mremapGrown`) is a step of the thread that revives
only bytes the thread owns: the grown offsets of block `b` have no access history. -/
theorem _root_.Zig.Mem.mremapGrown_step {m : Mem} {hF : Heap} {P : Nat} {b : BlockId} {blk : Block}
    {lo n : Nat} (hb : m.blocks[b]? = some blk) (hl : blk.live = true) (hK : blk.kind = .mapped lo) :
    FStepIn hF m (m.mremapGrown P b blk lo n) ∧ m.RevivesOwned (m.mremapGrown P b blk lo n) := by
  refine ⟨(FStepIn.forgetFrom b blk.bytes.size).trans
    (FStepIn.setBlock (m := m.forgetFrom b blk.bytes.size) fun h => ⟨blk, hb, h⟩),
    fun b' x hb' hl' hd e he heb h1 h2 => ?_⟩
  have hget := blocks_set_get (m := m) (m' := m.mremapGrown P b blk lo n) hb rfl
  by_cases e' : b' = b
  · rw [e'] at hl' hd heb
    have hb₂ : (m.mremapGrown P b blk lo n).blocks[b]? =
        some { blk with bytes := blk.bytes ++ mremapFill P (blk.bytes.size - lo) n } := by
      rw [hget]; simp
    have h₁ := (heap_mapped hb₂ hl hK x).mp hl'
    have hge : blk.bytes.size ≤ x :=
      Nat.le_of_not_lt fun hlt => (heap_mapped hb hl hK x).mpr ⟨h₁.1, hlt⟩ hd
    rcases Mem.forgetFrom_entry (m := m) (b := b) (S := blk.bytes.size) (by exact he) heb with
      hc | ⟨-, hend⟩
    · rw [hc]; exact VClock.le_default _
    · omega
  · exfalso; apply hl'
    have e2 : (m.mremapGrown P b blk lo n).heap (b', x) = m.heap (b', x) := by
      unfold Mem.heap; dsimp only; rw [hget, if_neg e']
    rw [e2]; exact hd

/-- **A growth in place without `MAYMOVE` is local** under the mapping's authority: it reads no
record (`Os.mremapLive_grow0`) and revives only the grown offsets, whose history it forgets. -/
theorem mremapGrow (os : Os.Target) (hhas : os.hasMremap = true) {b : BlockId} {S lo : Nat}
    {q : Frac} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    ThreadLocal (bauth b S (.mapped lo) q) (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none) := by
  intro m r rF hh hp hc ho
  obtain ⟨blk, hb, hl, hsz, hK, -⟩ := hh.bauth (sep_emp.mpr hp)
  subst hsz
  have hrun : ∀ m₀ : Mem, m₀.blocks[b]? = some blk →
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none).run m₀ =
        if m₀.mapDenied newLen.toNat then
          Pure.pure (Except.error "OutOfMemory", { m₀ with allocs := m₀.allocs + 1 })
        else if m₀.mappingRoom os.addrLimit b blk lo (alignUp newLen.toNat os.pageSize) = false then
          Pure.pure (Except.error "OutOfMemory", { m₀ with allocs := m₀.allocs + 1 })
        else Pure.pure (Except.ok ⟨⟨some b, (lo : Int)⟩, newLen⟩,
          ({ m₀ with allocs := m₀.allocs + 1 } : Mem).mremapGrown os.pageSize b blk lo newLen.toNat) :=
    fun m₀ hb₀ => (Os.mremap_eq (m := m₀) os hhas (.inl rfl) hb₀ hl hK (by omega) hold).trans
      (Os.mremapLive_grow0 os _ b blk lo newLen (by omega))
  have e1 : m.noFp.mapDenied newLen.toNat = m.mapDenied newLen.toNat := rfl
  have e2 : m.noFp.mappingRoom os.addrLimit b blk lo (alignUp newLen.toNat os.pageSize) =
      m.mappingRoom os.addrLimit b blk lo (alignUp newLen.toNat os.pageSize) := rfl
  refine ⟨?_, fun v m' e => ?_⟩
  · rw [hrun m hb, hrun m.noFp hb, e1, e2]
    split <;> (try split) <;> rfl
  · have hb₁ : ({ m with allocs := m.allocs + 1 } : Mem).blocks[b]? = some blk := hb
    have hst₁ : FStepIn rF.heap.erase m { m with allocs := m.allocs + 1 } :=
      .of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
        Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h)
        (fun _ he hn => absurd he hn)
    rw [hrun m hb] at e
    split at e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨hst₁, (Mem.NoRevive.refl m).revivesOwned⟩
    split at e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨hst₁, (Mem.NoRevive.refl m).revivesOwned⟩
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      obtain ⟨hst₂, hrev₂⟩ := Mem.mremapGrown_step (hF := rF.heap.erase) (P := os.pageSize)
        (n := newLen.toNat) hb₁ hl hK
      exact ⟨hst₁.trans hst₂, hrev₂⟩

/-- A new block at the end is a step of the thread for every frame. -/
theorem _root_.Zig.FStepIn.push {m : Mem} {hF : Heap} (x : Block) :
    FStepIn hF m { m with blocks := m.blocks.push x } :=
  .of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
      by simp, fun _ he => .inl he, fun _ he => .inl he⟩
    (fun b' hb' ⟨blk', e1, e2⟩ => ⟨blk', by
      have e1' : (m.blocks.push x)[b']? = some blk' := e1
      rw [Array.getElem?_push_lt hb'] at e1'
      exact (Array.getElem?_eq_getElem hb').trans e1', e2⟩)
    (fun _ he hn => absurd he hn)

/-- **A growth of a whole mapping that `P` owns is local**, with or without `MAYMOVE`: in every
memory of `P` the request grows the live mapping at `p`, and `P` owns its live bytes `[lo, S)`.
The move records a write of them, which races with nothing (`Os.mremapLive_grow_of`), ends the
block and adds a new one; the growth in place revives only the grown offsets, whose history it
forgets (`Mem.mremapGrown_step`). -/
theorem mremapMove (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {lo : Nat}
    {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hold0 : 0 < oldLen.toNat)
    (hown : ∀ m r rF, Holds m r rF → P r → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      blk.kind = .mapped lo ∧
      alignUp oldLen.toNat os.pageSize = alignUp (blk.bytes.size - lo) os.pageSize ∧
      blk.bytes.size - lo < newLen.toNat ∧
      ∀ x, lo ≤ x → x < blk.bytes.size → r.heap.erase (b, x) ≠ none) :
    ThreadLocal P (Os.mremap os (some p) oldLen newLen flags none) := by
  have hpe : p = ⟨some b, (lo : Int)⟩ := by
    cases p; simp only at hpb hp0; rw [hpb, hp0]
  subst hpe
  intro m r rF hh hp hc ho
  obtain ⟨blk, hb, hl, hK, hold, hn, hin⟩ := hown m r rF hh hp
  have hin' : ∀ x, lo ≤ x → x < lo + (blk.bytes.size - lo) → r.heap.erase (b, x) ≠ none :=
    fun x h1 h2 => hin x h1 (by omega)
  have hnr := noRace_owned (k := .write) hc ho hin'
  rw [Mem.noFp_withFp] at hnr
  let n := newLen.toNat
  have hrun : ∀ m₀ : Mem, m₀.blocks[b]? = some blk → NoRace m₀ b lo (blk.bytes.size - lo) .write →
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen flags none).run m₀ =
        if m₀.mapDenied n then Pure.pure (Except.error "OutOfMemory", { m₀ with allocs := m₀.allocs + 1 })
        else if flags = Os.mremapMayMove ∧ (m₀.allocPolicy.os.mremapMoves m₀.allocs n = true ∨
            m₀.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false) then
          if os.fits (m₀.mapAddr os.pageSize n) n = false then
            Pure.pure (Except.error "OutOfMemory", { m₀ with allocs := m₀.allocs + 1 })
          else Pure.pure (Except.ok ⟨⟨some m₀.blocks.size, 0⟩, newLen⟩,
            (({ m₀ with allocs := m₀.allocs + 1 } : Mem).recordAt b lo (blk.bytes.size - lo)
              .write).mremapMoved os.pageSize b blk lo n)
        else if m₀.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) = false then
          Pure.pure (Except.error "OutOfMemory", { m₀ with allocs := m₀.allocs + 1 })
        else Pure.pure (Except.ok ⟨⟨some b, (lo : Int)⟩, newLen⟩,
          ({ m₀ with allocs := m₀.allocs + 1 } : Mem).mremapGrown os.pageSize b blk lo n) :=
    fun m₀ hb₀ hnr₀ => (Os.mremap_eq (m := m₀) os hhas hfl hb₀ hl hK (by omega) hold).trans
      (Os.mremapLive_grow_of os _ b blk lo newLen flags hn hnr₀)
  have e1 : m.noFp.mapDenied n = m.mapDenied n := rfl
  have e2 : m.noFp.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) =
      m.mappingRoom os.addrLimit b blk lo (alignUp n os.pageSize) := rfl
  have e3 : m.noFp.allocPolicy = m.allocPolicy := rfl
  have e4 : m.noFp.allocs = m.allocs := rfl
  have e5 : m.noFp.mapAddr os.pageSize n = m.mapAddr os.pageSize n := rfl
  have e6 : m.noFp.blocks.size = m.blocks.size := rfl
  refine ⟨?_, fun v m' e => ?_⟩
  · rw [hrun m hb hnr.2, hrun m.noFp hb hnr.1, e1, e2, e3, e4, e5, e6]
    split <;> (try split) <;> (try split) <;> rfl
  · have hb₁ : ({ m with allocs := m.allocs + 1 } : Mem).blocks[b]? = some blk := hb
    have hst₁ : FStepIn rF.heap.erase m { m with allocs := m.allocs + 1 } :=
      .of_stepIn ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
        Nat.le_refl _, fun _ he => .inl he, fun _ he => .inl he⟩ (fun _ _ h => h)
        (fun _ he hn => absurd he hn)
    rw [hrun m hb hnr.2] at e
    split at e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨hst₁, (Mem.NoRevive.refl m).revivesOwned⟩
    split at e
    · split at e
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
        exact ⟨hst₁, (Mem.NoRevive.refl m).revivesOwned⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
        -- the move: the owned write of the old bytes, the end of the old block, the new block
        let mr := ({ m with allocs := m.allocs + 1 } : Mem).recordAt b lo (blk.bytes.size - lo) .write
        have hbr : mr.blocks[b]? = some blk := hb
        have hrec : FStepIn rF.heap.erase { m with allocs := m.allocs + 1 } mr :=
          FStepIn.recordAt hc.1 (FHeap.erase_disjoint hh.disj) hin' (Array.getElem?_eq_some_iff.mp hb).1
            fun _ ⟨blk', h1, h2⟩ => by
              have h1' : m.blocks[b]? = some blk' := h1
              rw [hb] at h1'; cases h1'; rw [hK] at h2; cases h2
        let nnb : Block :=
          { bytes := blk.bytes.extract lo blk.bytes.size ++ mremapFill os.pageSize (blk.bytes.size - lo) n,
            align := os.pageSize, kind := .mapped 0, live := true, addr := mr.mapAddr os.pageSize n }
        let mk : Mem := { mr with blocks := mr.blocks.set! b { blk with live := false } }
        have hpush : FStepIn rF.heap.erase mk (mr.mremapMoved os.pageSize b blk lo n) :=
          FStepIn.push (m := mk) nnb
        refine ⟨((hst₁.trans hrec).trans (FStepIn.kill hbr)).trans hpush, ?_⟩
        have hk : mr.NoRevive mk := Mem.NoRevive.kill mr b blk
        have hn' : mk.NoRevive (mr.mremapMoved os.pageSize b blk lo n) := Mem.NoRevive.push rfl
        have : mr.NoRevive (mr.mremapMoved os.pageSize b blk lo n) :=
          hk.trans (by simp [mk]) hn'
        exact Mem.NoRevive.revivesOwned this
    split at e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      exact ⟨hst₁, (Mem.NoRevive.refl m).revivesOwned⟩
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.pure_inj e)
      obtain ⟨hst₂, hrev₂⟩ := Mem.mremapGrown_step (hF := rF.heap.erase) (P := os.pageSize)
        (n := newLen.toNat) hb₁ hl hK
      exact ⟨hst₁.trans hst₂, hrev₂⟩

/-- The locality of `FTotalTriple.mremapMove'`'s step: its precondition owns the mapping's live
bytes and holds its extent. -/
theorem mremapMove' (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hold0 : 0 < oldLen.toNat) (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    ThreadLocal (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.mremap os (some p) oldLen newLen flags none) :=
  mremapMove os hhas hfl hpb hp0 hold0 fun m r rF hh hp => by
    obtain ⟨hsz, hp⟩ := sep_lift.mp hp
    obtain ⟨blk, hb, hl, hS, hK, -⟩ := hh.bauth (sep_comm hp)
    refine ⟨blk, hb, hl, hK, by rw [hS]; exact hold, by rw [hS]; exact hn, fun x h1 h2 => ?_⟩
    have hoff : p.off.toNat = lo := by rw [hp0]; omega
    exact (OwnsAt.bytesAt hpb).sepL r (up_regionIn_bytesAt hp) x (by omega) (by omega)

end ThreadLocal

/-! The thread rules of the growths are `FTTotalTriple.ofSeq` of the sequential rule and the
locality of its step; the kernel composes them as they are (no separate thread rule): -/

example (os : Os.Target) (hhas : os.hasMremap = true) {b : BlockId} {S lo : Nat} {q : Frac}
    {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (bauth b S (.mapped lo) q)
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen 0 none)
      (mremapGrowPost os.pageSize b S lo newLen.toNat q newLen) :=
  FTTotalTriple.ofSeq (FTotalTriple.mremapGrow' os hhas hold0 hold hn)
    (ThreadLocal.mremapGrow os hhas hold0 hold hn)

example (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPost os.pageSize p b A S lo a bs newLen) :=
  FTTotalTriple.ofSeq (FTotalTriple.mremapMove' os hhas hfl hpb hp0 hlt hA hlo hold0 hold hn)
    (ThreadLocal.mremapMove' os hhas hfl hpb hp0 hold0 hold hn)

example (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {oldLen newLen : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn : S - lo < newLen.toNat) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆
        (bext b S (.mapped lo) ⋆ bclaim b lo (lo + claimEnd))))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fmremapPostC os.pageSize p b A S lo a bs newLen) :=
  FTTotalTriple.ofSeq (FTotalTriple.mremapMoveC os hhas hfl hpb hp0 hlt hA hlo hold0 hold hn)
    ((ThreadLocal.mremapMove' os hhas hfl hpb hp0 hold0 hold hn).frame.pre
      fun _ h => sep_assoc' (sep_mono_right (fun _ x => sep_assoc' x) h))

namespace FTTotalTriple

/-- **munmap, page tail** (`FTotalTriple.munmapTail'`), in a thread. -/
theorem munmapTail' (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo k : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = ((lo + k : Nat) : Int)) (hk : 0 < k) (hS : S = lo + k + tail.size)
    (htl : 0 < tail.size) (hal : (A + (lo + k)) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : k + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (up (bytesAt p A S' K' tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b (lo + k) (.mapped lo)) := by
  refine ofSeq (FTotalTriple.munmapTail' os hpb hp0 hk hS htl hal hlen heq)
    (ThreadLocal.munmap os _ fun m r rF hh hp b' blk hpb' hb x h1 h2 => ?_)
  rw [hpb] at hpb'; cases hpb'
  obtain ⟨blk', hb', -, hsz, -⟩ := hh.bauth (sep_comm hp)
  rw [hb] at hb'; cases hb'
  have hoff : p.off.toNat = lo + k := by rw [hp0]; omega
  simp only at h1 h2
  have hx := (Nat.lt_min.mp h2).2
  exact (OwnsAt.bytesAt hpb).sepL r hp x h1 (by omega)

/-- **munmap, page prefix** (`FTotalTriple.munmapPrefix'`), in a thread. -/
theorem munmapPrefix' (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo : Nat}
    {K' : BlockKind} {pre : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hlen : 0 < len.toNat)
    (hk : pre.size = alignUp len.toNat os.pageSize) (hlt : lo + pre.size < S)
    (hal : (A + lo) % os.pageSize = 0) :
    FTTotalTriple (up (bytesAt p A S' K' pre) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b S (.mapped (lo + pre.size))) := by
  refine ofSeq (FTotalTriple.munmapPrefix' os hpb hp0 hlen hk hlt hal)
    (ThreadLocal.munmap os _ fun m r rF hh hp b' blk hpb' hb x h1 h2 => ?_)
  rw [hpb] at hpb'; cases hpb'
  have hoff : p.off.toNat = lo := by rw [hp0]; omega
  simp only at h1 h2
  have hx := (Nat.lt_min.mp h2).1
  exact (OwnsAt.bytesAt hpb).sepL r hp x h1 (by omega)

/-- **munmap of a whole mapping** (`FTotalTriple.munmapWhole'`), in a thread. -/
theorem munmapWhole' (os : Os.Target) {p : Ptr} {b : BlockId} {A S lo a : Nat}
    {bs : Array Byte} {len : BitVec 64} (hpb : p.block = some b) (hp0 : p.off = (lo : Int))
    (hlt : lo < S) (hA : A % os.pageSize = 0) (hlo : lo % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (⟪bs.size = S - lo⟫ ⋆ (up (regionIn p A S (.mapped lo) a bs) ⋆ bext b S (.mapped lo)))
      (Os.munmap os ⟨p, len⟩) (fun _ => FAssn.emp) := by
  refine ofSeq (FTotalTriple.munmapWhole' os hpb hp0 hlt hA hlo hlen heq)
    (ThreadLocal.munmap os _ fun m r rF hh hp b' blk hpb' hb x h1 h2 => ?_)
  rw [hpb] at hpb'; cases hpb'
  obtain ⟨hsz, hp⟩ := sep_lift.mp hp
  obtain ⟨blk', hb', -, hS, -⟩ := hh.bauth (sep_comm hp)
  rw [hb] at hb'; cases hb'
  have hp' := up_regionIn_bytesAt hp
  have hoff : p.off.toNat = lo := by rw [hp0]; omega
  simp only at h1 h2
  have hx := (Nat.lt_min.mp h2).2
  exact (OwnsAt.bytesAt hpb).sepL r hp' x h1 (by omega)

/-- **munmap of a page tail from its region** (`FTotalTriple.munmapTailR`), in a thread. -/
theorem munmapTailR (os : Os.Target) {p : Ptr} {b : BlockId} {A S S' lo a : Nat}
    {K' : BlockKind} {tail : Array Byte} {len : BitVec 64} (hpb : p.block = some b)
    (hp0 : 0 ≤ p.off) (hk : lo < p.off.toNat) (hS : S = p.off.toNat + tail.size)
    (htl : 0 < tail.size) (hal : (A + p.off.toNat) % os.pageSize = 0) (hlen : 0 < len.toNat)
    (heq : p.off.toNat - lo + alignUp len.toNat os.pageSize = alignUp (S - lo) os.pageSize) :
    FTTotalTriple (up (regionIn p A S' K' a tail) ⋆ bext b S (.mapped lo)) (Os.munmap os ⟨p, len⟩)
      (fun _ => bext b p.off.toNat (.mapped lo)) := by
  have e : lo + (p.off.toNat - lo) = p.off.toNat := by omega
  have t := FTTotalTriple.munmapTail' os (k := p.off.toNat - lo) (A := A) (S := S) (S' := S') (K' := K')
    (tail := tail) (len := len) hpb (by rw [e]; omega) (by omega) (by omega) htl (by rw [e]; exact hal)
    hlen heq
  rw [e] at t
  exact t.conseq (fun _ h => up_regionIn_bytesAt h) fun _ _ h => h

/-- **mmap** (`FTotalTriple.mmap'`), in a thread. -/
theorem mmap' (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (hlen : 0 < len.toNat) :
    FTTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPost os.pageSize os.addrLimit len) :=
  ofSeq (FTotalTriple.mmap' os hint len hlen) (ThreadLocal.mmap _ _ _ _ _ _ _)

/-- **mmap with the new mapping's claim** (`FTotalTriple.mmapC`), in a thread. -/
theorem mmapC (os : Os.Target) (hint : Option Ptr) (len : BitVec 64) (hlen : 0 < len.toNat) :
    FTTotalTriple FAssn.emp (Os.mmap os hint len os.protReadWrite os.mapPrivateAnonymous Os.noFd 0)
      (fmmapPostC os.pageSize os.addrLimit len) :=
  ofSeq (FTotalTriple.mmapC os hint len hlen) (ThreadLocal.mmap _ _ _ _ _ _ _)

/-- **mremap, shrink** (`FTotalTriple.mremapShrink'`), in a thread. -/
theorem mremapShrink' (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTTotalTriple (up (bytesAt ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩ A S' K' cut) ⋆
        bext b S (.mapped lo))
      (Os.mremap os (some ⟨some b, (lo : Int)⟩) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨⟨some b, (lo : Int)⟩, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  refine ofSeq (FTotalTriple.mremapShrink' os hhas hfl hold0 hold hn0 hn hcut)
    (ThreadLocal.mremapShrink os _ _ _ _ fun m r rF hh hp b' blk lo' hpb hb hk => ?_)
  cases hpb
  obtain ⟨blk', hb', -, hsz, hK, -⟩ := hh.bauth (sep_comm hp)
  rw [hb] at hb'; cases hb'
  rw [hk] at hK; cases hK
  refine ⟨by omega, fun x h1 h2 => ?_⟩
  exact (OwnsAt.bytesAt (p := ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩) rfl).sepL r hp x
    (by simp only [Int.toNat_natCast]; omega) (by simp only [Int.toNat_natCast]; omega)

/-- **mremap shrinking from the cut bytes' region** (`FTotalTriple.mremapShrinkR`), in a
thread. -/
theorem mremapShrinkR (os : Os.Target) (hhas : os.hasMremap = true) {flags : BitVec 32}
    (hfl : flags = 0 ∨ flags = Os.mremapMayMove) {b : BlockId} {A S S' lo a : Nat} {K' : BlockKind}
    {cut : Array Byte} {oldLen newLen : BitVec 64} {p : Ptr} (hpb : p.block = some b)
    (hp0 : p.off = (lo : Int)) (hold0 : 0 < oldLen.toNat)
    (hold : alignUp oldLen.toNat os.pageSize = alignUp (S - lo) os.pageSize)
    (hn0 : 0 < newLen.toNat) (hn : lo + newLen.toNat ≤ S) (hcut : cut.size = S - (lo + newLen.toNat)) :
    FTTotalTriple (up (regionIn (p.add newLen.toNat) A S' K' a cut) ⋆ bext b S (.mapped lo))
      (Os.mremap os (some p) oldLen newLen flags none)
      (fun x => ⟪x = .ok ⟨p, newLen⟩⟫ ⋆ bext b (lo + newLen.toNat) (.mapped lo)) := by
  obtain ⟨pb, po⟩ := p
  simp only at hpb hp0; subst hpb hp0
  have e : (⟨some b, (lo : Int)⟩ : Ptr).add newLen.toNat = ⟨some b, ((lo + newLen.toNat : Nat) : Int)⟩ := by
    simp [Ptr.add]
  rw [e]
  exact (mremapShrink' os hhas hfl hold0 hold hn0 hn hcut).conseq (fun _ h => up_regionIn_bytesAt h)
    fun _ _ h => h

end FTTotalTriple

end Full
end Zig
