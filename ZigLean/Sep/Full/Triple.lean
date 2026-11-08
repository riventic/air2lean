import ZigLean.Sep.Full.Res
import ZigLean.Conc.Lemmas
import ZigLean.Sep.Base.Block
import ZigLean.Sep.Full.Disjoint

/-!
# Full-state triples (prototype, `docs/sep-full-state.md`)

`FTriple P c Q` is `Triple` (`ZigLean/Sep/Triple.lean`) over full-state resources
(`ZigLean/Sep/Full/Res.lean`): a memory holds a resource `r` with the frame `rF` (`Holds`) if its
live bytes are exactly the disjoint union of the two, **each byte meets its atomic tag
constraint** (`FMatch`), and **the knowledge of both is true in it** (every `known b A` names an
existing block at its address).
The memory invariant is `Mem.FSeq`: `Mem.Seq`, a well-formed atomic layout, and live blocks at
disjoint addresses (`Mem.LiveDisjoint`). The ghost states of a resource and its frame compose
(`Ghost.Ok`).

* **Structural rules**: `conseq`, `frame`, `ret`, `bind`, `ex`, `lift`; `drop` forgets knowledge
  and ghost state. The frame is in the definition, so the frame rule holds for every program; the
  frame now includes the tags of its bytes and its knowledge.
* **`Tame` programs**: a program that keeps the atomic layout and every block's address and keeps
  live blocks apart (`Tame`: `Tame.load`, `.store`, `.alloc`, `.free`, `.ptrAddr`, closed under
  `pure` and `bind`). No legacy triple is lifted; every rule is proved on `Holds`.
* **Knowledge** (`know_intro`): owning a byte of block `b` gives `known b A` for its address `A`;
  `ptrAddr` (`@intFromPtr`) of a pointer into `b` needs only `known b A`, so it works after `free`
  (`FTriple.ptrAddr`, obstruction O1).
-/

namespace Zig
namespace Full

open FAssn Conc

/-- The memory invariant of `FTriple`: one thread (`Mem.Seq`), a well-formed atomic layout, and
live blocks at disjoint addresses (`Mem.LiveDisjoint`, stage 3 of `docs/sep-full-state.md`). -/
def _root_.Zig.Mem.FSeq (m : Mem) : Prop := m.Seq ∧ ShapesWF (shapes m) ∧ m.LiveLayout

/-! ### `Mem.FSeq` of a concrete memory is decidable

So the kernel decides it (`decide +kernel`) for a memory that a concrete run computes, e.g. the
memory in which a refutation applies a triple (`AllocArena.ArenaObstruction.not_fallocSpec_arena`). -/

theorem _root_.Zig.Mem.liveDisjoint_iff (m : Mem) : m.LiveDisjoint ↔
    ∀ i (hi : i < m.blocks.size) j (hj : j < m.blocks.size), i ≠ j → m.blocks[j].live = true →
      m.blocks[i].clearOf (m.blocks[j].addr + m.blocks[j].kind.mappedLo)
        (m.blocks[j].bytes.size - m.blocks[j].kind.mappedLo) = true := by
  constructor
  · intro h i hi j hj hne hl
    exact h i j _ _ hne (Array.getElem?_eq_getElem hi) (Array.getElem?_eq_getElem hj) hl
  · intro h b b' blk blk' hne hb hb' hl
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp hb'
    exact h b hi b' hj hne hl

instance (m : Mem) : Decidable m.LiveDisjoint := decidable_of_iff' _ (Mem.liveDisjoint_iff m)

theorem _root_.Zig.Mem.liveBounded_iff (m : Mem) : m.LiveBounded ↔
    ∀ i (hi : i < m.blocks.size), m.blocks[i].live = true →
      m.blocks[i].addr + m.blocks[i].bytes.size ≤ 2 ^ 63 := by
  constructor
  · intro h i hi hl; exact h i _ (Array.getElem?_eq_getElem hi) hl
  · intro h b blk hb hl
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    exact h b hi hl

instance (m : Mem) : Decidable m.LiveBounded := decidable_of_iff' _ (Mem.liveBounded_iff m)

instance (m : Mem) : Decidable m.LiveLayout := inferInstanceAs (Decidable (_ ∧ _))

instance (m : Mem) : Decidable m.SingleThread := inferInstanceAs (Decidable (_ ∧ _))

instance (m : Mem) : Decidable m.Seq := decidable_of_iff _ ⟨fun h => ⟨h⟩, fun h => h.single⟩

instance (s t : Shape) : Decidable (Apart s t) := inferInstanceAs (Decidable (_ → _))

instance (sh : List Shape) : Decidable (ShapesWF sh) := inferInstanceAs (Decidable (_ ∧ _))

instance (m : Mem) : Decidable m.FSeq := inferInstanceAs (Decidable (_ ∧ _))

/-- `m` holds the resource `r` and the frame `rF`: their disjoint union with the cells their
read shares read matches `m` (its live bytes, each byte's tag constraint: `SMatch`, `FMatch`),
their knowledge is true in `m`, and their ghost states compose (`Ghost.Ok`). -/
structure Holds (m : Mem) (r rF : Res) : Prop where
  disj : FHeap.Disjoint r.heap rF.heap
  heap : SMatch m (r.heap ∪ rF.heap) (r.gh.add rF.gh).share
  know : Know.Sub r.know m.kn
  knowF : Know.Sub rF.know m.kn
  ghost : GOk m r.gh rF.gh

/-- Partial correctness without a panic, over full-state resources (module doc). -/
def FTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq

namespace FTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FSeq) :
    FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨v, m', r', hr, hh', hq, hs'⟩ := h m r rF hh hp hs
  rw [hr]; exact ⟨r', hh', hq, hs'⟩

theorem conseq (ht : FTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTriple P' c Q' := by
  intro m r rF hh hp' hs
  have := ht m r rF hh (hp _ hp') hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', a, b, s⟩ := this; exact ⟨r', a, hq _ _ b, s⟩

theorem pre (ht : FTriple P c Q) (hp : ∀ r, P' r → P r) : FTriple P' c Q := conseq ht hp (fun _ _ h => h)

theorem post (ht : FTriple P c Q) (hq : ∀ v r, Q v r → Q' v r) : FTriple P c Q' :=
  conseq ht (fun _ h => h) hq

/-- **The frame rule.** The frame's bytes, their atomic tags and its knowledge stay. -/
theorem frame (ht : FTriple P c Q) : FTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  intro m r rF hh hpr hs
  obtain ⟨rP, rR, hd, rfl, hp, hr⟩ := hpr
  obtain ⟨hdisj, hheap, hk, hkF, hg⟩ := hh
  obtain ⟨hPF, hRF⟩ := FHeap.disjoint_union_left.mp hdisj
  have := ht m rP ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩
    ⟨FHeap.disjoint_union_right.mpr ⟨hd, hPF⟩,
      by rw [← FHeap.union_assoc, ← Ghost.add_assoc]; exact hheap, hk.left,
      hk.right.union hkF, GOk.assoc.mp hg⟩ hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd', hh', hk', hkF', hg'⟩, hq, hs'⟩ := this
    obtain ⟨hQR, hQF⟩ := FHeap.disjoint_union_right.mp hd'
    exact ⟨⟨r'.heap ∪ rR.heap, r'.know.union rR.know, r'.gh.add rR.gh⟩,
      ⟨FHeap.disjoint_union_left.mpr ⟨hQF, hRF⟩,
        by rw [FHeap.union_assoc, Ghost.add_assoc]; exact hh',
        hk'.union hkF'.left, hkF'.right, GOk.assoc.mpr hg'⟩, ⟨r', rR, hQR, rfl, hq, hr⟩, hs'⟩

/-- Frame on the left. -/
theorem frameL (ht : FTriple P c Q) : FTriple (R ⋆ P) c (fun v => R ⋆ Q v) :=
  conseq (frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem ret (v : α) : FTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m r _ hh hq hs => ⟨v, m, r, rfl, hh, hq, hs⟩

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : FTriple P (pure v : MemM α) Q :=
  pre (ret v) hq

theorem bind {S : β → FAssn} {f : α → MemM β} (hc : FTriple P c Q)
    (hf : ∀ v, FTriple (Q v) (f v) S) : FTriple P (c >>= f) S := by
  intro m r rF hh hp hs
  have h1 := hc m r rF hh hp hs
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h1; exact h1
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨r', hh', hq, hs'⟩
      exact hf v m' r' rF hh' hq hs'

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, FTriple (P x) c Q) : FTriple (FAssn.ex P) c Q := by
  intro m r rF hh ⟨x, hp⟩ hs
  exact h x m r rF hh hp hs

theorem lift {φ : Prop} (h : φ → FTriple P c Q) : FTriple (⟪φ⟫ ⋆ P) c Q := by
  intro m r rF hh hp hs
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m r rF hh hp hs

/-- Knowledge and ghost state (anything that owns no bytes and no stack token) can be forgotten.
A stack token cannot: the memory demands it (`Ghost.Affine`, `StackAuth`). -/
theorem drop {K : α → FAssn} (ht : FTriple P c (fun v => Q v ⋆ K v))
    (hK : ∀ v r, K v r → r.heap = FHeap.empty ∧ r.gh.Affine) : FTriple P c Q := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd, hm, hk, hkF, hg⟩, ⟨r₁, r₂, -, rfl, hq, hk2⟩, hs'⟩ := this
    obtain ⟨e, ha⟩ := hK _ _ hk2
    simp only [e, FHeap.union_empty] at hd hm
    rw [ha.share_add] at hm
    exact ⟨r₁, ⟨hd, hm, hk.left, hkF, GOk.mono hg ha⟩, hq, hs'⟩

/-- A step that does not change the memory and returns: every assertion stays. -/
theorem of_pure_run (h : ∀ m, m.FSeq → ∃ v, c.run m = pure (v, m)) (hq : ∀ v r, P r → Q v r) :
    FTriple P c Q :=
  of_run fun m r _ hh hp hs => by
    obtain ⟨v, hv⟩ := h m hs
    exact ⟨v, m, r, hv, hh, hq v r hp, hs⟩

end FTriple

/-! ## Knowledge rules -/

/-- A cell of an owned full heap is a cell of the memory up to its block's size and mapping
start (`Cell.norm`). -/
theorem Holds.cellN {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {c : FCell}
    (hc : r.heap l = some c) : ∃ c', m.heap l = some c' ∧ c'.norm = c.cell.norm :=
  hh.heap.cell (by rw [FHeap.union_apply, hc]; rfl)

/-- A live byte read as the cell `fc` (up to `Cell.norm`) is in a live block whose size is above
it, at the cell's address and kind. -/
theorem Mem.block_of_cell {m : Mem} {b : BlockId} {x : Nat} {fc : FCell}
    (h : ∃ c, m.heap (b, x) = some c ∧ c.norm = fc.cell.norm) : ∃ blk, m.blocks[b]? = some blk ∧
      blk.live = true ∧ x < blk.bytes.size ∧ blk.kind.mappedLo ≤ x ∧ fc.cell.addr = blk.addr ∧
      fc.cell.kind.norm = blk.kind.norm := by
  obtain ⟨c, hc, hn⟩ := h
  obtain ⟨blk, hb, hl, hx, he⟩ := Mem.heap_some hc
  obtain ⟨blk', hb', hlo⟩ := Mem.heap_some_lo hc
  rw [hb] at hb'; cases hb'
  have ha := congrArg Cell.addr hn
  have hk := congrArg Cell.kind hn
  subst he
  exact ⟨blk, hb, hl, hx, hlo, ha.symm, hk.symm⟩

/-- **An owned byte is a live byte**: owning byte `x` of block `b` gives a live block whose size
is above `x` (and whose mapping start is at most `x`), at the cell's address. In-bounds facts
come from ownership (`docs/sep-full-state.md` §Block extents). -/
theorem Holds.block {m : Mem} {r rF : Res} (hh : Holds m r rF) {b : BlockId} {x : Nat} {fc : FCell}
    (h : r.heap (b, x) = some fc) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      x < blk.bytes.size ∧ blk.kind.mappedLo ≤ x ∧ fc.cell.addr = blk.addr ∧
      fc.cell.kind.norm = blk.kind.norm :=
  Mem.block_of_cell (hh.cellN h)

/-- **A share reads a live byte** (`SMatch.share_cell`): a positive fraction of `fc` at `l` gives
the memory's cell there, as an exclusive cell does (`Holds.cellN`). -/
theorem Holds.cellS {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {fc : FCell}
    (hq : 0 < (r.gh.share l fc).val) : ∃ c', m.heap l = some c' ∧ c'.norm = fc.cell.norm :=
  hh.heap.share_cell (Ghost.add_share _ _ _) hq

/-! ### Cells with their block's actual extent (`Res.fix`)

A rule that needs the memory's exact cells reads them off `r.fix m`: under `Holds`, it holds the
same bytes with their actual sizes and kinds (`Holds.fix`, `Exact`), and its frame `rF.fix m` is
the frame up to `Cell.norm` (`FHeap.Sim`), so a post that holds with it holds with `rF`
(`Holds.congrF`, `FTriple.of_fix`). -/

/-- Every cell of `r` is `m`'s live byte there, its block's size and kind included. -/
def Exact (m : Mem) (r : Res) : Prop := ∀ l fc, r.heap l = some fc → m.heap l = some fc.cell

/-- Two full heaps with the same cells up to `Cell.norm`, with the same tags. -/
def FHeap.Sim (h₁ h₂ : FHeap) : Prop :=
  ∀ l, (h₁ l).map (fun fc => (fc.cell.norm, fc.atom)) = (h₂ l).map (fun fc => (fc.cell.norm, fc.atom))

theorem FHeap.Sim.none {h₁ h₂ : FHeap} (hs : FHeap.Sim h₁ h₂) {l : Loc} : h₁ l = none ↔ h₂ l = none := by
  have := hs l
  constructor
  · intro e; rw [e] at this; cases e2 : h₂ l with
    | none => rfl
    | some _ => rw [e2] at this; cases this
  · intro e; rw [e] at this; cases e2 : h₁ l with
    | none => rfl
    | some _ => rw [e2] at this; cases this

theorem FHeap.Sim.some {h₁ h₂ : FHeap} (hs : FHeap.Sim h₁ h₂) {l : Loc} {fc : FCell}
    (h : h₂ l = some fc) : ∃ fc', h₁ l = some fc' ∧ fc'.cell.norm = fc.cell.norm ∧ fc'.atom = fc.atom := by
  have := hs l
  rw [h] at this
  cases e : h₁ l with
  | none => rw [e] at this; cases this
  | some fc' =>
    rw [e] at this
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨fc', rfl, this.1, this.2⟩

theorem FHeap.Sim.symm {h₁ h₂ : FHeap} (hs : FHeap.Sim h₁ h₂) : FHeap.Sim h₂ h₁ := fun l => (hs l).symm

theorem FHeap.Sim.refl (h : FHeap) : FHeap.Sim h h := fun _ => rfl

theorem FHeap.Sim.norm {h₁ h₂ : FHeap} (hs : FHeap.Sim h₁ h₂) (l : Loc) :
    (h₁ l).map (fun fc => fc.cell.norm) = (h₂ l).map (fun fc => fc.cell.norm) := by
  have := congrArg (Option.map Prod.fst) (hs l)
  simpa [Option.map_map, Function.comp_def] using this

theorem FHeap.Sim.union {a a' b b' : FHeap} (ha : FHeap.Sim a a') (hb : FHeap.Sim b b') :
    FHeap.Sim (a ∪ b) (a' ∪ b') := fun l => by
  have e1 := ha l
  simp only [FHeap.union_apply]
  cases x : a l <;> cases y : a' l <;> rw [x, y] at e1
  · exact hb l
  · cases e1
  · cases e1
  · exact e1

/-- **`SMatch` sees cells up to `Cell.norm`**: a heap with the same cells up to it, with the same
tags, matches with the same shares. -/
theorem SMatch.sim {m : Mem} {h h' : FHeap} {s : Loc → SCell} (hm : SMatch m h s)
    (hs : FHeap.Sim h' h) : SMatch m h' s := by
  have hu : FHeap.Sim (h' ∪ SCells s) (h ∪ SCells s) := hs.union (FHeap.Sim.refl _)
  refine ⟨⟨fun l => by rw [hm.whole.1 l]; exact (hu.norm l).symm, fun l fc hl => ?_⟩,
    fun l => ?_, hm.total⟩
  · obtain ⟨fc', h1, -, ha⟩ := hu.symm.some hl
    rw [← ha]; exact hm.whole.2 l fc' h1
  · rcases hm.apart l with e | e
    · exact .inl (hs.none.mpr e)
    · exact .inr e

/-- The resource and the frame swapped. -/
theorem Holds.swap {m : Mem} {r rF : Res} (hh : Holds m r rF) : Holds m rF r :=
  ⟨hh.disj.symm, by rw [FHeap.union_comm hh.disj.symm, Ghost.add_comm]; exact hh.heap, hh.knowF,
    hh.know,
    by have := hh.ghost; unfold GOk at this ⊢; rw [Ghost.Ok.comm, Ghost.add_comm]; exact this⟩

/-- A frame that is the same up to `Cell.norm` (and keeps its knowledge and ghost state) is held
by the same memory. -/
theorem Holds.congrF {m : Mem} {r rF rF' : Res} (hh : Holds m r rF) (hs : FHeap.Sim rF'.heap rF.heap)
    (hk : rF'.know = rF.know) (hg : rF'.gh = rF.gh) : Holds m r rF' := by
  refine ⟨fun l => ?_, ?_, hh.know, hk ▸ hh.knowF, hg ▸ hh.ghost⟩
  · rcases hh.disj l with e | e
    · exact .inl e
    · exact .inr (hs.none.mpr e)
  · rw [hg]; exact hh.heap.sim (FHeap.Sim.union (FHeap.Sim.refl _) hs)

theorem FMatch.fix_cell {m : Mem} {h : FHeap} (hm : FMatch m h) {l : Loc} {fc : FCell}
    (hl : h l = some fc) : ∃ c, m.heap l = some c ∧ h.fix m l = some ⟨c, fc.atom⟩ ∧
      c.norm = fc.cell.norm := by
  obtain ⟨c, hc, hn⟩ := hm.cell hl
  obtain ⟨blk, hb, -, hx, he⟩ := Mem.heap_some hc
  refine ⟨c, hc, ?_, hn⟩
  have hby := congrArg Cell.byte hn
  have ha := congrArg Cell.addr hn
  simp only [Cell.norm] at hby ha
  simp only [FHeap.fix, hl, Option.map_some, hb, Option.some.injEq, FCell.mk.injEq, and_true]
  rw [he]; rw [he] at hby ha
  cases fc with | mk cell atom => cases cell; simp_all

theorem SMatch.fix_cell {m : Mem} {h : FHeap} {s : Loc → SCell} (hm : SMatch m h s) {l : Loc}
    {fc : FCell} (hl : h l = some fc) : ∃ c, m.heap l = some c ∧ h.fix m l = some ⟨c, fc.atom⟩ ∧
      c.norm = fc.cell.norm := by
  obtain ⟨c, hc, hf, hn⟩ := hm.whole.fix_cell (l := l) (fc := fc) (by simp [hl])
  refine ⟨c, hc, ?_, hn⟩
  rw [FHeap.fix_union, FHeap.union_apply] at hf
  cases e : h.fix m l with
  | none => exact absurd (FHeap.fix_none.mp e) (by simp [hl])
  | some x => rw [e, Option.some_or] at hf; exact hf

/-- A heap with its cells' actual sizes and kinds is the heap up to `Cell.norm`. -/
theorem SMatch.fix_sim {m : Mem} {h : FHeap} {s : Loc → SCell} (hm : SMatch m h s) :
    FHeap.Sim (h.fix m) h := fun l => by
  cases e : h l with
  | none => simp [FHeap.fix, e]
  | some fc =>
    obtain ⟨c, -, hf, hn⟩ := hm.fix_cell e
    simp only [hf, Option.map_some, hn]

/-- Under `Holds`, the resource and the frame with their actual sizes and kinds are held. -/
theorem Holds.fix {m : Mem} {r rF : Res} (hh : Holds m r rF) : Holds m (r.fix m) (rF.fix m) :=
  ⟨FHeap.fix_disjoint hh.disj, by
    show SMatch m (r.heap.fix m ∪ rF.heap.fix m) (r.gh.add rF.gh).share
    rw [← FHeap.fix_union]; exact hh.heap.sim hh.heap.fix_sim, hh.know, hh.knowF, hh.ghost⟩

theorem Holds.fix_exact {m : Mem} {r rF : Res} (hh : Holds m r rF) : Exact m (r.fix m) := by
  intro l fc hl
  simp only [Res.fix, FHeap.fix, Option.map_eq_some_iff] at hl
  obtain ⟨fc0, h0, rfl⟩ := hl
  have hu : (r.heap ∪ rF.heap) l = some fc0 := by simp [h0]
  obtain ⟨c, hc, hf, -⟩ := hh.heap.fix_cell hu
  simp only [FHeap.fix, hu, Option.map_some, Option.some.injEq] at hf
  rw [hf]; exact hc

/-- An owned cell, with its block's actual size and kind. -/
theorem Holds.fix_of {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {fc : FCell}
    (h : r.heap l = some fc) : ∃ blk, m.blocks[l.1]? = some blk ∧
      (r.fix m).heap l = some ⟨{ fc.cell with size := blk.bytes.size, kind := blk.kind }, fc.atom⟩ := by
  obtain ⟨b, x⟩ := l
  obtain ⟨blk, hb, -⟩ := hh.block h
  exact ⟨blk, hb, by simp [Res.fix, FHeap.fix, h, hb]⟩

theorem Holds.fix_exactF {m : Mem} {r rF : Res} (hh : Holds m r rF) : Exact m (rF.fix m) :=
  hh.swap.fix_exact

theorem Holds.fix_sim {m : Mem} {r rF : Res} (hh : Holds m r rF) : FHeap.Sim (rF.fix m).heap rF.heap := by
  intro l
  cases e : rF.heap l with
  | none => simp [Res.fix, FHeap.fix, e]
  | some fc =>
    have hl : (r.heap ∪ rF.heap) l = some fc := by
      rcases hh.disj l with e' | e'
      · simp [e', e]
      · rw [e] at e'; cases e'
    obtain ⟨c, -, hf, hn⟩ := hh.heap.fix_cell hl
    rw [FHeap.fix_union] at hf
    have hr : r.heap l = none := by rcases hh.disj l with e' | e' <;> simp_all
    simp only [FHeap.union_apply, (FHeap.fix_none (m := m)).mpr hr, Option.none_or] at hf
    simp only [Res.fix, hf, Option.map_some, hn]

/-- The live bytes of a memory that holds `r` and `rF` with their exact cells, and no read
shares. -/
theorem Holds.heap_exact {m : Mem} {r rF : Res} (hh : Holds m r rF) (hx : Exact m r)
    (hxF : Exact m rF) (hns : ∀ l, ((r.gh.add rF.gh).share l).Empty) :
    m.heap = r.heap.erase ∪ rF.heap.erase := by
  funext l
  simp only [Heap.union_apply, FHeap.erase]
  cases e : r.heap l with
  | some fc => simp [hx l fc e]
  | none =>
    cases e' : rF.heap l with
    | some fc => simp [hxF l fc e']
    | none => exact hh.heap.none (by simp [e, e']) (SCell.cell_eq_none (hns l))

/-- **The live bytes of a memory are an exact resource's cells and others** (the frame's, the
cells read shares read). -/
theorem Exact.heap_split {m : Mem} {r : Res} (hx : Exact m r) :
    ∃ hF, m.heap = r.heap.erase ∪ hF :=
  ⟨fun l => if r.heap l = none then m.heap l else none, funext fun l => by
    simp only [Heap.union_apply, FHeap.erase]
    cases e : r.heap l with
    | some fc => simp [hx l fc e]
    | none => simp⟩

/-- **Rules from exact cells.** To prove a triple, it is enough to prove it for resources whose
cells are the memory's exact cells, if the precondition survives reading the actual sizes
(`r.fix m`); the frame is the actual frame up to `Cell.norm`. -/
theorem FTriple.of_fix {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.FSeq →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FSeq) :
    FTriple P c Q := by
  intro m r rF hh hp hs
  have := h m (r.fix m) (rF.fix m) hh.fix hh.fix_exact hh.fix_exactF (hP m r rF hh hp) hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    exact ⟨r', hh'.congrF hh.fix_sim.symm rfl rfl, hq, hs'⟩

/-- A frame byte meets its tag constraint. -/
theorem Holds.tagF {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {fc : FCell}
    (hc : rF.heap l = some fc) : TagSat (shapes m) l.1 l.2 fc.atom := by
  refine hh.heap.tag (l := l) (fc := fc) ?_
  rcases hh.disj l with e | e
  · rw [FHeap.union_apply, e, Option.none_or, hc]
  · rw [e] at hc; cases hc

/-! ### The bytes a resource holds (§Read shares) -/

/-- **The bytes a resource holds**: its exclusive cells and the bytes it holds a read share of.
A thread's race ownership covers them (`FTTriple`): which bytes these are is fixed by the memory
and the frame (`Holds.owned_sub`), because the memory accounts for every byte's shares exactly
(`SCell.Total`). Only the domain counts (`Mem.OwnsC`, `FootprintEntry.Touches`). -/
noncomputable def Res.owned (r : Res) : Heap := fun l =>
  ((r.heap l).map (·.cell)).or ((r.gh.share l).cell.map (·.cell))

theorem Res.owned_ne {r : Res} {l : Loc} :
    r.owned l ≠ none ↔ r.heap l ≠ none ∨ (r.gh.share l).Pos := by
  simp only [Res.owned, ne_eq, Option.or_eq_none_iff, Option.map_eq_none_iff,
    SCell.cell_eq_none_iff]
  grind

theorem Res.owned_of_heap {r : Res} {l : Loc} (h : r.heap l ≠ none) : r.owned l ≠ none :=
  Res.owned_ne.mpr (.inl h)

/-- A byte a resource does not own is not in its heap. -/
theorem Res.heap_of_owned {r : Res} {l : Loc} (h : r.owned l = none) : r.heap l = none :=
  Classical.byContradiction fun e => Res.owned_of_heap e h

theorem Res.owned_of_erase {r : Res} {l : Loc} (h : r.heap.erase l ≠ none) : r.owned l ≠ none :=
  Res.owned_of_heap fun e => h (by simp [FHeap.erase, e])

/-- A byte of a resource made of two parts is a byte of one of them. -/
theorem Res.owned_sep {r r₁ r₂ : Res} (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) {l : Loc} :
    r.owned l ≠ none ↔ r₁.owned l ≠ none ∨ r₂.owned l ≠ none := by
  simp only [Res.owned_ne, hh, hg, FHeap.union_apply, ne_eq, Option.or_eq_none_iff,
    Ghost.add_share, SCell.pos_add_iff]
  grind

/-- The owned bytes of the two parts own the bytes of the whole (`Mem.OwnsC.union`). -/
theorem Res.owned_sub_union {r r₁ r₂ : Res} (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) {l : Loc} (hl : r.owned l ≠ none) :
    (r₁.owned ∪ r₂.owned) l ≠ none := fun hn => by
  simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
  rcases (Res.owned_sep hh hg).mp hl with h | h
  · exact h hn.1
  · exact h hn.2

/-- Reading the actual sizes and kinds keeps the owned bytes. -/
theorem Res.owned_fix {m : Mem} {r : Res} {l : Loc} : (r.fix m).owned l ≠ none ↔ r.owned l ≠ none := by
  simp only [Res.owned_ne, Res.fix, ne_eq, FHeap.fix_none]

/-- Ghost state without shares (a counter cell, a token) adds nothing to the owned set. -/
theorem Res.owned_addGh {h : FHeap} {k : Know} {a g : Ghost}
    (hb : g.share = fun _ => SCell.zero := by rfl) :
    (⟨h, k, a.add g⟩ : Res).owned = (⟨h, k, a⟩ : Res).owned := by
  funext l; simp only [Res.owned, Ghost.share_add_none hb]

/-- Without shares, a resource owns exactly the bytes of its cells. -/
theorem Res.owned_eq_erase {r : Res} (hs : r.gh.share = fun _ => SCell.zero := by rfl) :
    r.owned = r.heap.erase := by
  funext l
  simp only [Res.owned, hs, SCell.cell_eq_none SCell.empty_zero, Option.map_none, Option.or_none]
  rfl

/-- A resource with no cell and no share owns nothing (`emp`, `rnil`, a mode token). -/
theorem Res.owned_eq_empty {r : Res} (hh : r.heap = FHeap.empty)
    (hs : r.gh.share = fun _ => SCell.zero := by rfl) : r.owned = Heap.empty := by
  rw [Res.owned_eq_erase hs, hh]; rfl

/-- A resource without ghost state owns exactly its cells. -/
theorem Res.owned_plain {r : Res} (hg : r.gh = Ghost.unit) {l : Loc} (h : r.heap l = none) :
    r.owned l = none := by
  rw [Res.owned_eq_erase (by rw [hg]; rfl)]
  simp [FHeap.erase, h]

/-- No share of a byte where a resource or its frame has an exclusive cell. -/
theorem Holds.not_pos_of_heap {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (h : (r.heap ∪ rF.heap) l ≠ none) : ¬ ((r.gh.add rF.gh).share l).Pos := by
  rw [← SCell.cell_eq_none_iff]
  exact (hh.heap.apart l).resolve_left h

/-- At a byte a resource holds as a cell, and no share of, the frame holds no share. -/
theorem Holds.frame_share_zero {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (hu : r.gh.share l = SCell.zero) (hl : r.heap l ≠ none) : rF.gh.share l = SCell.zero := by
  have hn : ¬ ((r.gh.add rF.gh).share l).Pos := hh.not_pos_of_heap (by
    simp only [FHeap.union_apply]; intro e; exact hl (Option.or_eq_none_iff.mp e).1)
  rw [Ghost.add_share, hu, SCell.zero_add, SCell.not_pos_iff] at hn
  exact hn.eq

/-- A live byte that neither the resource nor the frame holds exclusively is shared. -/
theorem Holds.pos_of_live {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc} {c : Cell}
    (hc : m.heap l = some c) (h : (r.heap ∪ rF.heap) l = none) : ((r.gh.add rF.gh).share l).Pos := by
  refine Classical.byContradiction fun hp => ?_
  rw [hh.heap.none h (SCell.cell_eq_none_iff.mpr hp)] at hc; cases hc

/-- A byte a resource holds is live, and not the frame's exclusive cell. -/
theorem Holds.live_of_owned {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (hl : r.owned l ≠ none) : (∃ c, m.heap l = some c) ∧ rF.heap l = none := by
  rcases Res.owned_ne.mp hl with h' | h'
  · obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp h'
    obtain ⟨c, hc, -⟩ := hh.heap.cell (l := l) (fc := fc) (by simp [hfc])
    exact ⟨⟨c, hc⟩, (hh.disj l).resolve_left h'⟩
  · have hn : SCells (r.gh.add rF.gh).share l ≠ none := by
      show ((r.gh.add rF.gh).share l).cell ≠ none
      rw [ne_eq, SCell.cell_eq_none_iff, Classical.not_not, Ghost.add_share]
      exact SCell.pos_add_iff.mpr (.inl h')
    obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp hn
    have hx := (hh.heap.apart l).resolve_right (by rw [hfc]; simp)
    obtain ⟨c, hc, -⟩ := hh.heap.whole.cell (l := l) (fc := fc) (by simp [hx, hfc])
    simp only [FHeap.union_apply, Option.or_eq_none_iff] at hx
    exact ⟨⟨c, hc⟩, hx.2⟩

/-- **The bytes a resource holds are fixed by the frame**: if a memory holds `r` next to `rF`
and another (or the same) memory holds `r'` next to `rF`, a byte live in the first that `r'`
holds, `r` holds. A byte is the frame's, or the resource's (exclusively or by a share: the
memory accounts for the whole of a shared byte, `SCell.Total`). -/
theorem Holds.owned_sub' {m m' : Mem} {r r' rF : Res} (hh : Holds m r rF) (hh' : Holds m' r' rF)
    {l : Loc} (hlive : ∃ c, m.heap l = some c) (hl : r'.owned l ≠ none) : r.owned l ≠ none := by
  by_cases hr' : r.heap l ≠ none
  · exact Res.owned_of_heap hr'
  have hr : r.heap l = none := Classical.byContradiction hr'
  obtain ⟨c₀, hc₀⟩ := hlive
  have hrF := (hh'.live_of_owned hl).2
  -- under `r` it is shared, wholly (`SCell.Total`)
  have hP := hh.pos_of_live hc₀ (by simp [hr, hrF])
  obtain ⟨c, e⟩ := (hh.heap.total l).resolve_left fun e => by
    rw [e] at hP; exact SCell.not_pos_iff.mpr SCell.empty_zero hP
  refine Res.owned_ne.mpr (.inr (Classical.byContradiction fun hn => ?_))
  -- if `r` held none of it, the frame would hold the whole, and `r'` nothing
  have eF : rF.gh.share l = SCell.of c Frac.one := by
    rw [← e, Ghost.add_share, (SCell.not_pos_iff.mp hn).eq, SCell.zero_add]
  have h1 : (rF.gh.share l c).val = 1 := by rw [eF, SCell.of_self]; rfl
  rcases Res.owned_ne.mp hl with h' | h'
  · exact hh'.not_pos_of_heap (l := l) (by simp [h'])
      (by rw [Ghost.add_share]; exact SCell.pos_add_iff.mpr (.inr ⟨c, by rw [h1]; decide⟩))
  · have hv : ((rF.gh.share l).add (r'.gh.share l)).Valid := by
      rw [SCell.add_comm, ← Ghost.add_share]; exact hh'.heap.valid l
    exact SCell.not_pos_iff.mpr (hv.whole h1) h'

/-- **The bytes a resource holds are fixed by the memory and the frame**: next to the same frame,
a memory holds no resource with a byte another one it holds lacks (`owned_sub'`). So an update
(`EUpd`) never gives a thread a byte: a read share becomes exclusive only with its byte already
held. -/
theorem Holds.owned_sub {m : Mem} {r r' rF : Res} (hh : Holds m r rF) (hh' : Holds m r' rF)
    {l : Loc} (hl : r'.owned l ≠ none) : r.owned l ≠ none :=
  hh.owned_sub' hh' (hh'.live_of_owned hl).1 hl

/-- A byte the resource holds exclusively is no byte of the frame. -/
theorem Holds.frame_not_owned {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (h : r.heap l ≠ none) : rF.owned l = none := by
  refine Classical.byContradiction fun hn => ?_
  rcases Res.owned_ne.mp hn with h' | h'
  · rcases hh.disj l with e | e
    · exact h e
    · exact h' e
  · exact hh.not_pos_of_heap (l := l) (by simpa [Option.or_eq_none_iff] using fun e => absurd e h)
      (by rw [Ghost.add_share]; exact SCell.pos_add_iff.mpr (.inr h'))

/-- **Every live byte is owned** by the resource or the frame: an exclusive cell or a share. -/
theorem Holds.owned_of_live {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (hl : m.heap l ≠ none) : r.owned l ≠ none ∨ rF.owned l ≠ none := by
  by_cases hs : SCells (r.gh.add rF.gh).share l = none
  · cases e : (r.heap ∪ rF.heap) l with
    | none => exact absurd (hh.heap.none e hs) hl
    | some _ =>
      rw [FHeap.union_apply] at e
      cases e₁ : r.heap l with
      | some _ => exact .inl (Res.owned_of_heap (by simp [e₁]))
      | none => rw [e₁, Option.none_or] at e; exact .inr (Res.owned_of_heap (by simp [e]))
  · have hp : ((r.gh.add rF.gh).share l).Pos :=
      Classical.byContradiction fun hn => hs (SCell.cell_eq_none_iff.mpr hn)
    rw [Ghost.add_share] at hp
    rcases SCell.pos_add_iff.mp hp with h | h
    · exact .inl (Res.owned_ne.mpr (.inr h))
    · exact .inr (Res.owned_ne.mpr (.inr h))

/-- The resource's exclusive bytes and the frame's owned bytes are apart: an access to the
former steps outside the frame. -/
theorem Holds.erase_disj_owned {m : Mem} {r rF : Res} (hh : Holds m r rF) :
    Heap.Disjoint r.heap.erase rF.owned := fun l => by
  cases e : r.heap l with
  | none => exact .inl (by simp [FHeap.erase, e])
  | some _ => exact .inr (hh.frame_not_owned (by simp [e]))

/-! ### Exclusive and shared bytes (§Read shares, slice F4, option R)

A thread's race ownership (`Mem.OwnsRes`, `ZigLean/Sep/Full/Thread.lean`) splits a resource's
bytes in two. **Exclusive bytes** (`Res.excl`): its cells and the bytes it holds a *whole* share
of; no one else can read them, so the thread owns every recorded access to them (`Mem.Owns`).
**Shared bytes** (`Res.shared`): the bytes it holds a *partial* share of; another thread may read
them at the same time, so the thread owns only every recorded write to them (`Mem.OwnsR`).

A whole share counts as exclusive, so turning it into a cell or a cell into it changes no
thread's ownership (`Holds.excl_sub'`), and every update lifts into a thread (`FTTriple.eupd`).
A share becomes whole in a thread only where a part gains the other pieces from another part or
the protocol's rest (`FOwned.move`, a lock's acquire), which then needs `Mem.Owns` of the bytes:
the order a protocol's RMWs give (`tests/roadmap/sep-full/ShareRaceCX.lean`). -/

/-- A share holding some cell at least whole. -/
def SCell.Whole (a : SCell) : Prop := ∃ c, 1 ≤ (a c).val

theorem SCell.Whole.pos {a : SCell} (h : a.Whole) : a.Pos :=
  let ⟨c, hc⟩ := h; ⟨c, by grind⟩

theorem SCell.Whole.add {a : SCell} (b : SCell) (h : a.Whole) : (a.add b).Whole :=
  let ⟨c, hc⟩ := h; ⟨c, by rw [SCell.add_val]; have := (b c).nonneg; grind⟩

theorem SCell.Whole.add' (a : SCell) {b : SCell} (h : b.Whole) : (a.add b).Whole := by
  rw [SCell.add_comm]; exact h.add a

/-- Next to a whole share, a valid frame holds nothing. -/
theorem SCell.Whole.frame {a b : SCell} (hv : (a.add b).Valid) (h : a.Whole) : b.Empty := by
  obtain ⟨c, hc⟩ := h
  have h1 := (hv.of_add).2 c
  exact hv.whole (c := c) (by grind)

open Classical in
/-- **The exclusive bytes** of a resource: its cells and its whole shares (module doc). -/
noncomputable def Res.excl (r : Res) : Heap := fun l =>
  if r.heap l ≠ none ∨ (r.gh.share l).Whole then r.owned l else none

open Classical in
/-- **The shared bytes** of a resource: its partial shares (module doc). -/
noncomputable def Res.shared (r : Res) : Heap := fun l =>
  if r.heap l ≠ none ∨ (r.gh.share l).Whole then none else r.owned l

/-- Ghost state without shares changes neither the exclusive nor the shared bytes. -/
theorem Res.excl_addGh {h : FHeap} {k : Know} {a g : Ghost}
    (hb : g.share = fun _ => SCell.zero := by rfl) :
    (⟨h, k, a.add g⟩ : Res).excl = (⟨h, k, a⟩ : Res).excl := by
  funext l; simp only [Res.excl, Res.owned_addGh hb]; rw [Ghost.share_add_none hb]

theorem Res.shared_addGh {h : FHeap} {k : Know} {a g : Ghost}
    (hb : g.share = fun _ => SCell.zero := by rfl) :
    (⟨h, k, a.add g⟩ : Res).shared = (⟨h, k, a⟩ : Res).shared := by
  funext l; simp only [Res.shared, Res.owned_addGh hb]; rw [Ghost.share_add_none hb]

theorem Res.excl_ne {r : Res} {l : Loc} :
    r.excl l ≠ none ↔ r.heap l ≠ none ∨ (r.gh.share l).Whole := by
  unfold Res.excl
  split
  · rename_i h
    refine ⟨fun _ => h, fun _ => Res.owned_ne.mpr ?_⟩
    rcases h with h | h
    · exact .inl h
    · exact .inr h.pos
  · rename_i h; simp only [ne_eq, not_true_eq_false, false_iff]; exact h

theorem Res.shared_ne {r : Res} {l : Loc} :
    r.shared l ≠ none ↔ r.heap l = none ∧ ¬ (r.gh.share l).Whole ∧ (r.gh.share l).Pos := by
  unfold Res.shared
  split
  · rename_i h; simp only [ne_eq, not_true_eq_false, false_iff]; grind
  · rename_i h
    rw [Res.owned_ne]
    grind

theorem Res.excl_of_heap {r : Res} {l : Loc} (h : r.heap l ≠ none) : r.excl l ≠ none :=
  Res.excl_ne.mpr (.inl h)

theorem Res.excl_of_erase {r : Res} {l : Loc} (h : r.heap.erase l ≠ none) : r.excl l ≠ none :=
  Res.excl_of_heap fun e => h (by simp [FHeap.erase, e])

theorem Res.owned_of_excl {r : Res} {l : Loc} (h : r.excl l ≠ none) : r.owned l ≠ none := by
  rcases Res.excl_ne.mp h with h | h
  · exact Res.owned_of_heap h
  · exact Res.owned_ne.mpr (.inr h.pos)

theorem Res.owned_of_shared {r : Res} {l : Loc} (h : r.shared l ≠ none) : r.owned l ≠ none :=
  Res.owned_ne.mpr (.inr (Res.shared_ne.mp h).2.2)

/-- A byte a resource holds is exclusive or shared. -/
theorem Res.excl_or_shared {r : Res} {l : Loc} (h : r.owned l ≠ none) :
    r.excl l ≠ none ∨ r.shared l ≠ none := by
  by_cases hx : r.heap l ≠ none ∨ (r.gh.share l).Whole
  · exact .inl (Res.excl_ne.mpr hx)
  · refine .inr (Res.shared_ne.mpr ⟨?_, ?_, ?_⟩)
    · exact Classical.byContradiction fun e => hx (.inl e)
    · exact fun e => hx (.inr e)
    · rcases Res.owned_ne.mp h with e | e
      · exact absurd (.inl e) hx
      · exact e

/-- An access to a byte a resource holds touches its exclusive or its shared bytes. -/
theorem _root_.Zig.FootprintEntry.Touches.excl_or_shared {e : FootprintEntry} {r : Res}
    (h : e.Touches r.owned) : e.Touches r.excl ∨ e.Touches r.shared :=
  let ⟨x, h1, h2, h3⟩ := h
  (Res.excl_or_shared h3).imp (fun h => ⟨x, h1, h2, h⟩) (fun h => ⟨x, h1, h2, h⟩)

theorem Res.excl_shared_disj {r : Res} {l : Loc} (h : r.excl l ≠ none) : r.shared l = none := by
  refine Classical.byContradiction fun hs => ?_
  obtain ⟨h1, h2, -⟩ := Res.shared_ne.mp hs
  rcases Res.excl_ne.mp h with e | e
  · exact e h1
  · exact h2 e

/-- An exclusive byte of a part is an exclusive byte of the whole. -/
theorem Res.excl_sep {r r₁ r₂ : Res} (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) {l : Loc} (h : r₁.excl l ≠ none ∨ r₂.excl l ≠ none) :
    r.excl l ≠ none := by
  refine Res.excl_ne.mpr ?_
  rw [hh, hg, Ghost.add_share, FHeap.union_apply]
  rcases h with h | h <;> rcases Res.excl_ne.mp h with e | e
  · exact .inl fun hn => e (Option.or_eq_none_iff.mp hn).1
  · exact .inr (e.add _)
  · exact .inl fun hn => e (Option.or_eq_none_iff.mp hn).2
  · exact .inr (e.add' _)

/-- A shared byte of the whole that a part holds is a shared byte of the part. -/
theorem Res.shared_sep {r r₁ r₂ : Res} (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) {l : Loc} (h : r.shared l ≠ none) (h₁ : r₁.owned l ≠ none) :
    r₁.shared l ≠ none := by
  obtain ⟨hn, hw, -⟩ := Res.shared_ne.mp h
  rw [hh, FHeap.union_apply, Option.or_eq_none_iff] at hn
  rw [hg, Ghost.add_share] at hw
  refine Res.shared_ne.mpr ⟨hn.1, fun e => hw (e.add _), ?_⟩
  rcases Res.owned_ne.mp h₁ with e | e
  · exact absurd hn.1 e
  · exact e

theorem Res.shared_sep' {r r₁ r₂ : Res} (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) {l : Loc} (h : r.shared l ≠ none) (h₂ : r₂.owned l ≠ none) :
    r₂.shared l ≠ none := by
  obtain ⟨hn, hw, -⟩ := Res.shared_ne.mp h
  rw [hh, FHeap.union_apply, Option.or_eq_none_iff] at hn
  rw [hg, Ghost.add_share] at hw
  refine Res.shared_ne.mpr ⟨hn.2, fun e => hw (e.add' _), ?_⟩
  rcases Res.owned_ne.mp h₂ with e | e
  · exact absurd hn.2 e
  · exact e

/-- Without shares, a resource's exclusive bytes are its cells' bytes, and it has no shared byte. -/
theorem Res.excl_eq_erase {r : Res} (hs : r.gh.share = fun _ => SCell.zero := by rfl) :
    (∀ l, r.excl l ≠ none ↔ r.heap l ≠ none) ∧ ∀ l, r.shared l = none := by
  have hw : ∀ l, ¬ (r.gh.share l).Whole := fun l ⟨c, hc⟩ => by
    rw [hs] at hc; exact absurd hc (by rw [SCell.zero_val]; decide)
  refine ⟨fun l => ?_, fun l => Classical.byContradiction fun h => ?_⟩
  · rw [Res.excl_ne]; exact ⟨fun h => h.resolve_right (hw l), .inl⟩
  · obtain ⟨-, -, hp⟩ := Res.shared_ne.mp h
    rw [hs] at hp; exact SCell.not_pos_iff.mpr SCell.empty_zero hp

/-- **An assertion without partial shares**: every resource it holds has no shared byte
(`Res.shared`), so its bytes are all exclusive. Such a resource never gathers a read share at a
join or a lock acquire (`FOwned.join`, `FLock.NoGather.of_R`). It is closed under `⋆` and `∃`, and
every assertion without ghost shares has it (`Unshared.of_share`). -/
def FAssn.Unshared (P : FAssn) : Prop := ∀ r, P r → ∀ l, r.shared l = none

namespace FAssn.Unshared

theorem of_share {P : FAssn} (h : ∀ r, P r → r.gh.share = fun _ => SCell.zero) : P.Unshared :=
  fun r hr => (Res.excl_eq_erase (h r hr)).2

theorem of_gh {P : FAssn} (h : ∀ r, P r → r.gh = Ghost.unit) : P.Unshared :=
  of_share fun r hr => by rw [h r hr]; rfl

theorem up (P : Assn) : (FAssn.up P).Unshared := of_gh fun _ h => h.2.2
theorem emp : FAssn.emp.Unshared := of_gh fun _ h => h.2.2
theorem lift (φ : Prop) : (FAssn.lift φ).Unshared := of_gh fun _ h => h.2.2.2
theorem bauth (b : BlockId) (S : Nat) (K : BlockKind) (q : Frac) : (Zig.Full.bauth b S K q).Unshared :=
  of_share fun _ h => by rw [h.2.2]; rfl
theorem bext (b : BlockId) (S : Nat) (K : BlockKind) : (Zig.Full.bext b S K).Unshared :=
  Unshared.bauth b S K Frac.one

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, (P x).Unshared) : (FAssn.ex P).Unshared :=
  fun r ⟨x, hx⟩ => h x r hx

theorem sep {P Q : FAssn} (hP : P.Unshared) (hQ : Q.Unshared) : (P ⋆ Q).Unshared := by
  rintro r ⟨r₁, r₂, -, rfl, h₁, h₂⟩ l
  refine Classical.byContradiction fun hs => ?_
  have hp := (Res.shared_ne.mp hs).2.2
  simp only [Ghost.add_share] at hp
  rcases SCell.pos_add_iff.mp hp with hp | hp
  · exact Res.shared_sep rfl rfl hs (Res.owned_ne.mpr (.inr hp)) (hP r₁ h₁ l)
  · exact Res.shared_sep' rfl rfl hs (Res.owned_ne.mpr (.inr hp)) (hQ r₂ h₂ l)

end FAssn.Unshared

/-- **Next to a byte the resource holds, the frame holds at most a partial share of it**: not a
cell (`Holds.erase_disj_owned`, the heap's apartness), not a whole share (`SCell.Whole.frame`).
So a read of the resource's bytes touches only the frame's read shares (`FStepIn`'s `hR`). -/
theorem Holds.frame_shared {m : Mem} {r rF : Res} (hh : Holds m r rF) {l : Loc}
    (hr : r.owned l ≠ none) (hF : rF.owned l ≠ none) : rF.shared l ≠ none := by
  -- `r` holds no cell there, so it holds a positive share
  have hrh : r.heap l = none := by
    have := (hh.erase_disj_owned l).resolve_right hF
    simpa [FHeap.erase] using this
  have hrp : (r.gh.share l).Pos := (Res.owned_ne.mp hr).resolve_left (· hrh)
  have hFh : rF.heap l = none := Classical.byContradiction fun e =>
    hh.not_pos_of_heap (l := l) (by simpa [FHeap.union_apply, hrh] using e)
      (by rw [Ghost.add_share]; exact SCell.pos_add_iff.mpr (.inl hrp))
  refine Res.shared_ne.mpr ⟨hFh, fun hw => ?_, (Res.owned_ne.mp hF).resolve_left (· hFh)⟩
  have hv : ((rF.gh.share l).add (r.gh.share l)).Valid := by
    rw [SCell.add_comm, ← Ghost.add_share]; exact hh.heap.valid l
  exact SCell.not_pos_iff.mpr (hw.frame hv) hrp

/-- **The exclusive bytes are fixed by the memory and the frame** (`Holds.owned_sub'`): next to the
same frame, a byte live in the first memory that the second resource holds exclusively (a cell
or a whole share), the first holds exclusively. An update turns a whole share into a cell and
back, never a partial share into either. -/
theorem Holds.excl_sub' {m m' : Mem} {r r' rF : Res} (hh : Holds m r rF) (hh' : Holds m' r' rF)
    {l : Loc} (hlive : ∃ c, m.heap l = some c) (hl : r'.excl l ≠ none) : r.excl l ≠ none := by
  -- the frame holds nothing of the byte
  have hF : rF.heap l = none ∧ (rF.gh.share l).Empty := by
    rcases Res.excl_ne.mp hl with h | h
    · refine ⟨(hh'.disj l).resolve_left h, ?_⟩
      have hn := hh'.not_pos_of_heap (l := l) (by simp [FHeap.union_apply, h])
      rw [Ghost.add_share, SCell.pos_add_iff] at hn
      exact SCell.not_pos_iff.mp fun hp => hn (.inr hp)
    · have hv : ((r'.gh.share l).add (rF.gh.share l)).Valid := by
        rw [← Ghost.add_share]; exact hh'.heap.valid l
      refine ⟨?_, h.frame hv⟩
      have hp : ((r'.gh.add rF.gh).share l).Pos := by rw [Ghost.add_share]; exact (h.add _).pos
      have := (hh'.heap.apart l).resolve_right (by
        show ¬ ((r'.gh.add rF.gh).share l).cell = none
        rw [SCell.cell_eq_none_iff, Classical.not_not]; exact hp)
      simp only [FHeap.union_apply, Option.or_eq_none_iff] at this
      exact this.2
  obtain ⟨c₀, hc₀⟩ := hlive
  rcases hh.owned_of_live (l := l) (by simp [hc₀]) with h | h
  · by_cases hr : r.heap l ≠ none
    · exact Res.excl_of_heap hr
    · have hr' : r.heap l = none := Classical.byContradiction hr
      -- `r` holds a share of the byte, and with an empty frame it is the whole
      have hP := hh.pos_of_live hc₀ (by simp [FHeap.union_apply, hr', hF.1])
      obtain ⟨c, e⟩ := (hh.heap.total l).resolve_left fun e => by
        rw [e] at hP; exact SCell.not_pos_iff.mpr SCell.empty_zero hP
      rw [Ghost.add_share, hF.2.eq, SCell.add_zero] at e
      exact Res.excl_ne.mpr (.inr ⟨c, by rw [e, SCell.of_self]; decide⟩)
  · exfalso
    rcases Res.owned_ne.mp h with e | e
    · exact e hF.1
    · exact SCell.not_pos_iff.mpr hF.2 e

/-- **Knowledge true in the memory can be added at any time** (a fact of `Mem.kn m` is
persistent, so whoever holds it later keeps it true). -/
theorem Holds.addKnow {m : Mem} {r rF : Res} {k : Know} (hk : Know.Sub k m.kn)
    (hh : Holds m r rF) : Holds m ⟨r.heap, r.know.union k, r.gh⟩ rF :=
  ⟨hh.disj, hh.heap, hh.know.union hk, hh.knowF, hh.ghost⟩

/-- **A block known dead is dead in the memory** (`dead`, `KFact.dead`). -/
theorem Holds.dead {m : Mem} {r rF : Res} {b : BlockId} {R : FAssn} (hh : Holds m r rF)
    (h : (dead b ⋆ R) r) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = false := by
  obtain ⟨r₁, r₂, -, rfl, ⟨-, hk, -⟩, -⟩ := h
  exact hh.know (.dead b) (.inl (by rw [hk]; rfl))

/-- **Knowledge from ownership.** Owning a byte of block `b`, whose cell has the address `A`,
gives `known b A`. -/
theorem FTriple.know_intro {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {b : BlockId}
    {A : Nat} (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : FTriple (P ⋆ known b A) c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨x, fc, hx, hA⟩ := hc r hp
  have hkn : m.kn (.addr b A) := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hx
    exact ⟨blk, hblk, by rw [← hA, ha]⟩
  have hres : (P ⋆ known b A) ⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩ :=
    ⟨r, ⟨FHeap.empty, Know.single (.addr b A), Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩
  exact ht m _ rF (hh.addKnow (Know.sub_single hkn)) hres hs

theorem ptrAddr_run {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (off : Int) : (ptrAddr ⟨some b, off⟩).run m = pure ((blk.addr : Int) + off, m) := by
  simp [ptrAddr, hb, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont]

/-- Address resolution returns the numeric address without changing memory or refuses an
unknown block. A known block's address remains usable after it is freed. -/
theorem ptrAddr_cases (p : Ptr) (m : Mem) :
    (∃ a, (Zig.ptrAddr p).run m = pure (a, m)) ∨
      (Zig.ptrAddr p).run m = (throw .illegal : Result (Int × Mem)) := by
  rcases p with ⟨b, off⟩
  cases b with
  | none => exact .inl ⟨off, rfl⟩
  | some b =>
    cases hb : m.blocks[b]? with
    | none => exact .inr (by simp [Zig.ptrAddr, hb, zig_unfold])
    | some blk => exact .inl ⟨(blk.addr : Int) + off, ptrAddr_run hb off⟩

/-- Actual block-address alignment gives the unchanged-memory address run; a footprint or
the allocation's alignment field alone does not imply this fact. -/
theorem ptrAddr_aligned {m : Mem} {b : BlockId} {blk : Block} {off align : Nat}
    (hb : m.blocks[b]? = some blk) (ha : (blk.addr + off) % align = 0) :
    ∃ a, (Zig.ptrAddr ⟨some b, (off : Int)⟩).run m = pure (a, m) ∧ a % (align : Int) = 0 := by
  refine ⟨(blk.addr : Int) + off, ptrAddr_run hb off, ?_⟩
  exact_mod_cast ha

/-- Two successful address resolutions in the same memory have the same value. -/
theorem ptrAddr_value_eq {p : Ptr} {m : Mem} {a a' : Int}
    (ha : (Zig.ptrAddr p).run m = pure (a, m))
    (ha' : (Zig.ptrAddr p).run m = pure (a', m)) : a = a' := by
  rw [ha] at ha'
  simpa [zig_unfold, ExceptT.run] using congrArg ExceptT.run ha'

/-- A protocol's address resolution preserves memory and scheduling depth. A refused block
must be permitted by its error policy. -/
theorem _root_.Zig.Conc.Proto.WP.ptrAddr {Tgt γ : Type} {P : Proto Tgt γ} {p : Ptr}
    {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}
    {Q : Int → (ThreadId → γ) → Mem → Nat → Prop}
    (herr : ∀ er, ((Zig.ptrAddr p).run m).run = some (.error er) → P.ErrOk er)
    (h : ∀ a, (Zig.ptrAddr p).run m = pure (a, m) → Q a G m n) :
    P.WP t (ConcM.liftMem (Zig.ptrAddr p) : ConcM Tgt Int) Q G m n := by
  rcases ptrAddr_cases p m with ⟨a, ha⟩ | he
  · refine Proto.WP.liftMem (fun er hr => (Proto.MemM.noErr_of_run ha er hr).elim) (fun a' m' hr => ?_)
      (fun hn => by rw [ha] at hn; cases hn)
    rw [ha] at hr
    cases hr
    exact ⟨rfl, h a ha⟩
  · refine Proto.WP.liftMem herr (fun _ _ hr => by rw [he] at hr; cases hr)
      (fun hn => by rw [he] at hn; cases hn)

/-- **`@intFromPtr` of a pointer into block `b`, live or freed** (O1): only the knowledge of its
address is needed. -/
theorem FTriple.ptrAddr {b : BlockId} {A : Nat} (off : Int) :
    FTriple (known b A) (Zig.ptrAddr ⟨some b, off⟩) (fun a => ⟪a = (A : Int) + off⟫ ⋆ known b A) :=
  FTriple.of_run fun m r _ hh hp hs => by
    obtain ⟨blk, hblk, hA⟩ := hh.know (.addr b A) (by rw [hp.2.1]; rfl)
    exact ⟨_, m, r, ptrAddr_run hblk off, hh, sep_lift.mpr ⟨by rw [hA], hp⟩, hs⟩

theorem ptrAddr_none_run (m : Mem) (off : Int) : (Zig.ptrAddr ⟨none, off⟩).run m = pure (off, m) := rfl

/-- `@intFromPtr` of a pointer without a block (an integer handle): no knowledge needed. -/
theorem FTriple.ptrAddr_none {P : FAssn} (off : Int) :
    FTriple P (Zig.ptrAddr ⟨none, off⟩) (fun a => ⟪a = off⟫ ⋆ P) :=
  FTriple.of_run fun m r _ hh hp hs =>
    ⟨off, m, r, ptrAddr_none_run m off, hh, sep_lift.mpr ⟨rfl, hp⟩, hs⟩

/-- `@ptrFromInt` changes nothing and never fails. Its result may point into a dead block (or a
frame block), which a later access checks; with more than one covering block it carries no
provenance (`Zig.ptrFromAddr`, `docs/address-reuse.md`). -/
theorem ptrFromAddr_run (n : Nat) (m : Mem) :
    ∃ v, (Zig.ptrFromAddr n).run m = pure (v, m) := by
  unfold Zig.ptrFromAddr
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, pure, ExceptT.pure, Option.bind_some]
  generalize (Array.filterMap _ m.blocks.zipIdx).toList = l
  rcases l with _ | ⟨⟨b, blk⟩, _ | ⟨x, rest⟩⟩ <;> try exact ⟨_, rfl⟩
  cases m.allocPolicy.provenance
  · exact ⟨_, rfl⟩
  · repeat' split
    all_goals exact ⟨_, rfl⟩

/-- `@ptrFromInt` frames everything. -/
theorem FTriple.ptrFromAddr {P : FAssn} (n : Nat) :
    FTriple P (Zig.ptrFromAddr n) (fun _ => P) :=
  FTriple.of_run fun m r _ hh hp hs => by
    obtain ⟨v, e⟩ := ptrFromAddr_run n m
    exact ⟨v, m, r, e, hh, hp, hs⟩

/-! ## Lifting legacy triples -/

/-- `c` keeps the atomic layout and every block's address, keeps live blocks apart, and keeps
the memory's authority over the counter cell (`MemAuth.Keep`: no stack push, no step). -/
def Tame {α : Type} (c : MemM α) : Prop :=
  ∀ m v m', (c.run m).run = some (.ok (v, m')) →
    shapes m' = shapes m ∧ KMono m m' ∧ LDMono m m' ∧ MemAuth.Keep m m'

namespace Tame

variable {α β : Type}

theorem pure' (v : α) : Tame (pure v : MemM α) := fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
  exact ⟨rfl, KMono.refl _, LDMono.refl _, MemAuth.Keep.refl _⟩

theorem bind {c : MemM α} {f : α → MemM β} (hc : Tame c) (hf : ∀ v, Tame (f v)) :
    Tame (c >>= f) := fun m v m'' h => by
  obtain ⟨a, m', h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨s1, k1, d1, a1⟩ := hc m a m' h1
  obtain ⟨s2, k2, d2, a2⟩ := hf a m' v m'' h2
  exact ⟨s2.trans s1, k1.trans k2, d1.trans d2, a1.trans a2⟩

/-- A step that changes only clocks, footprint and bytes or liveness of blocks. -/
theorem of_eq {c : MemM α}
    (h : ∀ m v m', (c.run m).run = some (.ok (v, m')) →
      m'.atomics = m.atomics ∧ KMono m m' ∧ LDMono m m' ∧ MemAuth.Keep m m') :
    Tame c := fun m v m' hr => by
  obtain ⟨ha, hk, hd, hm⟩ := h m v m' hr
  exact ⟨by simp [shapes, ha], hk, hd, hm⟩

theorem loadBytes (p : Ptr) (n a : Nat) (k : AccessKind) : Tame (Zig.loadBytes p n a k) :=
  of_eq fun _ _ _ h => by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := Conc.Proto.loadBytes_ok h
    exact ⟨Mem.readAt_atomics, KMono.of_blocks Mem.readAt_blocks,
      LDMono.of_blocks Mem.readAt_blocks,
      MemAuth.Keep.of_blocks Mem.readAt_blocks Mem.readAt_stacks (by rw [Mem.readAt_place])
        Mem.readAt_ticks⟩

theorem lift (r : Result α) : Tame (StateT.lift r : MemM α) := of_eq fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h
  exact ⟨rfl, KMono.refl _, LDMono.refl _, MemAuth.Keep.refl _⟩

theorem get' : Tame (get : MemM Mem) := of_eq fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h
  exact ⟨rfl, KMono.refl _, LDMono.refl _, MemAuth.Keep.refl _⟩

theorem load (T : Type) [Enc T] (a : Nat) (p : Ptr) : Tame (Zig.load T a p) :=
  bind (loadBytes p _ a .read) fun bs => bind get' fun m => lift (decodeLoad m.blocks bs)

theorem storeBytes (p : Ptr) (a : Nat) (bs : Array Byte) (k : AccessKind) :
    Tame (Zig.storeBytes p a bs k) := of_eq fun m _ _ h => by
  obtain ⟨b, blk, o, hacc, hk, -, rfl⟩ := Conc.Proto.storeBytes_ok h
  have hb := (access_eq hacc).2.1
  have hsz : (writeBytes blk.bytes o bs).size = blk.bytes.size := by
    obtain ⟨-, -, -, h0, hn, -, rfl⟩ := access_eq hacc
    rw [writeBytes_size _ _ _ (by omega)]
  exact ⟨rfl, KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs })
    hb rfl hk rfl, LDMono.set (nb := { blk with bytes := writeBytes blk.bytes o bs })
    hb id rfl (by simp only; rw [hsz]; exact Nat.le_refl _) rfl,
    MemAuth.Keep.set (nb := { blk with bytes := writeBytes blk.bytes o bs }) hb rfl rfl rfl hsz rfl
      rfl rfl rfl⟩

theorem store {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : Tame (Zig.store a p v) :=
  storeBytes p a _ .write

/-- `alloc` of a block that no stack budget charges (every kind but `.stack`). A stack block is
not `Tame`: under a budget it pushes an entry, which needs the thread's stack token
(`tests/roadmap/stack-region/Tokens.lean`, `push_without_sp_cx`). -/
theorem alloc (kind : BlockKind) (size align : Nat) (hk : kind ≠ .stack) :
    Tame (Zig.alloc kind size align) :=
  of_eq fun m v m' h => by
    cases hroom : m.allocOk kind size align
    · rw [alloc_run_noRoom m hroom] at h; cases h
    rw [alloc_run_eq m hroom] at h
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
    exact ⟨rfl, KMono.push rfl, LDMono.alloc hroom rfl (by simp) rfl,
      MemAuth.Keep.allocOther (by cases kind <;> first | rfl | exact absurd rfl hk)⟩

theorem free (p : Ptr) : Tame (Zig.free p) := of_eq fun m v m' h => by
  have hkeep := MemAuth.Keep.free h
  unfold Zig.free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · exact (Conc.Proto.MemM.throw_ok h₁).elim
  · split at h₁
    · rename_i b _ blk hblk
      split at h₁
      · rename_i hc
        split at h₁
        · exact (Conc.Proto.MemM.throw_ok h₁).elim
        · have := Conc.Proto.MemM.set_ok h₁
          subst this
          exact ⟨rfl, KMono.set (blk' := { blk with live := false }) hblk rfl hc.2.2 rfl,
            LDMono.set (nb := { blk with live := false }) hblk (by simp) rfl (Nat.le_refl _) rfl, hkeep⟩
      · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

theorem ptrAddr (p : Ptr) : Tame (Zig.ptrAddr p) := of_eq fun m v m' h => by
  unfold Zig.ptrAddr at h
  split at h
  · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
    exact ⟨rfl, KMono.refl _, LDMono.refl _, MemAuth.Keep.refl _⟩
  · obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
    split at h₁
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h₁
      exact ⟨rfl, KMono.refl _, LDMono.refl _, MemAuth.Keep.refl _⟩
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

end Tame

/-! ## Size-free legacy assertions (the strength log, `ZigLean/Sep/Full/Strength.lean`)

A legacy assertion's cells record their block's size and kind; a full-state cell pins neither
(`FMatch`). A legacy assertion that does not depend on the sizes it records, except on blocks
whose full extent it owns (`SizeFree E P`, with the extents `E`, `upE P E`), holds of the
memory's actual cells (`upE_fix`): the strength log reads a full-state triple back as a legacy
one with it. Nothing lifts a legacy triple. -/

/-- `P` holds of every heap with the same cells up to their sizes and mapping starts
(`Cell.norm`), one size and kind per block, that agrees with it on the blocks of `E`. -/
def SizeFree (E : BlockId → Option (Nat × BlockKind)) (P : Assn) : Prop :=
  ∀ h h', P h → (∀ l, (h l).map Cell.norm = (h' l).map Cell.norm) →
    (∀ l c, h l = some c → (E l.1).isSome → h' l = some c) →
    (∀ l l' c c', h' l = some c → h' l' = some c' → l.1 = l'.1 → c.size = c'.size ∧ c.kind = c'.kind) →
    P h'

theorem upE_fix {P : Assn} {E : BlockId → Option (Nat × BlockKind)} (hsf : SizeFree E P)
    (hpin : ∀ h, P h → ∀ l c S K, h l = some c → E l.1 = some (S, K) → c.size = S ∧ c.kind = K)
    {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : upE P E r) : P (r.fix m).heap.erase := by
  have hr : FHeap.Sim (r.fix m).heap r.heap := hh.swap.fix_sim
  refine hsf _ _ hp.1 (fun l => ?_) (fun l c hc hE => ?_) (fun l l' c c' h1 h2 he => ?_)
  · have := hr l
    simp only [FHeap.erase, Option.map_map]
    cases e1 : r.heap l <;> cases e2 : (r.fix m).heap l <;> rw [e1, e2] at this <;> simp_all [Function.comp_def]
  · simp only [FHeap.erase, Option.map_eq_some_iff] at hc
    obtain ⟨fc, hfc, rfl⟩ := hc
    obtain ⟨SK, hSK⟩ := Option.isSome_iff_exists.mp hE
    obtain ⟨S, K⟩ := SK
    obtain ⟨hS, hK⟩ := hpin _ hp.1 l fc.cell S K (by simp [FHeap.erase, hfc]) hSK
    -- the authority over `l.1` is the resource's: the block has that extent
    have hauth : 0 < ((r.gh.add rF.gh).extent l.1).auth (S, K) := by
      rw [hp.2.2]; simp [Ghost.add, ECell.add, Ghost.exts, hSK, ECell.auth1]; omega
    obtain ⟨blk, hb, -, hbs, hbk, -⟩ := (hh.ghost.2.1 l.1).1 S K hauth
    simp only [FHeap.erase, Res.fix, FHeap.fix, hfc, Option.map_some, hb, Option.some.injEq]
    rw [hbs, hbk, ← hS, ← hK]
  · simp only [FHeap.erase, Option.map_eq_some_iff] at h1 h2
    obtain ⟨_, h1, rfl⟩ := h1
    obtain ⟨_, h2, rfl⟩ := h2
    simp only [Res.fix, FHeap.fix, Option.map_eq_some_iff] at h1 h2
    obtain ⟨fc, hfc, rfl⟩ := h1
    obtain ⟨fc', hfc', rfl⟩ := h2
    obtain ⟨blk, hb, -⟩ := hh.fix_of hfc
    obtain ⟨blk', hb', -⟩ := hh.fix_of hfc'
    rw [← he] at hb'
    rw [hb] at hb'; cases hb'
    simp [hb, ← he]

/-- **A resource holding the full extent of `b` leaves the frame only dormant claims on `b`**
(no authority claim, no live share, no tag of a future epoch). -/
theorem full_excl {g gF : Ghost} (hok : Ghost.Ok g gF) {b : BlockId} {S : Nat} {K : BlockKind}
    (hg : g.extent b = ECell.auth1 S K Frac.one) : (gF.extent b).Dormant (g.add gF).ls := by
  have hv := hok.1.2.1 b
  have e : (g.add gF).extent b = (ECell.auth1 S K Frac.one).add (gF.extent b) := by
    simp only [Ghost.add, hg]
  rw [e] at hv
  exact ECell.dormant_of_auth1 hv.1 hv.2

/-- A legacy `bytesAt`-style assertion: its bytes are size-free. -/
theorem SizeFree.bytesAt_ex {p : Ptr} {bs : Array Byte} {φ : Nat → Nat → BlockKind → Prop}
    (hφ : ∀ A S K S' K', φ A S K → K'.norm = K.norm → φ A S' K') :
    SizeFree (fun _ => none) (fun h => ∃ A S K, φ A S K ∧ bytesAt p A S K bs h) := by
  intro h h' ⟨A, S, K, hφA, b, hb, h0, hl⟩ hn _ hco
  by_cases hpos : bs.size = 0
  · refine ⟨A, S, K, hφA, b, hb, h0, fun l => ?_⟩
    have e := hn l
    rw [hl l, if_neg (by omega)] at e
    cases e' : h' l with
    | none => rw [if_neg (by omega)]
    | some _ => rw [e'] at e; cases e
  · -- the cell at `p` gives the block's size and kind in `h'`
    have hin : (b, p.off.toNat).1 = b ∧ p.off.toNat ≤ (b, p.off.toNat).2 ∧
        (b, p.off.toNat).2 < p.off.toNat + bs.size := ⟨rfl, Nat.le_refl _, by simp; omega⟩
    have e0 := hn (b, p.off.toNat)
    rw [hl _, if_pos hin] at e0
    cases e1 : h' (b, p.off.toNat) with
    | none => rw [e1] at e0; cases e0
    | some c0 =>
      rw [e1] at e0
      have hk0 := congrArg Cell.kind (Option.some.inj e0)
      simp only [Cell.norm] at hk0
      refine ⟨A, c0.size, c0.kind, hφ A S K c0.size c0.kind hφA hk0.symm, b, hb, h0, fun l => ?_⟩
      have e := hn l
      rw [hl l] at e
      split
      · rename_i hc
        rw [if_pos hc] at e
        cases e2 : h' l with
        | none => rw [e2] at e; cases e
        | some c =>
          rw [e2] at e
          have hc' := Option.some.inj e
          obtain ⟨hs, hk⟩ := hco l (b, p.off.toNat) c c0 e2 e1 hc.1
          simp only [Cell.norm, Cell.mk.injEq] at hc'
          cases c; simp_all
      · rename_i hc
        rw [if_neg hc] at e
        cases e2 : h' l with
        | none => rfl
        | some _ => rw [e2] at e; cases e

/-- `pts` is size-free. -/
theorem SizeFree.pts {T : Type} [Enc T] (p : Ptr) (a : Nat) (v : T) :
    SizeFree (fun _ => none) (pts p a v) := by
  intro h h' hp hn hE hco
  obtain ⟨A, S, K, bs, hal, hsz, hdec, hb, hK⟩ := hp
  obtain ⟨A', S', K', ⟨hal', hK'⟩, hb'⟩ := SizeFree.bytesAt_ex (p := p) (bs := bs)
    (φ := fun A _ K => (A + p.off.toNat) % a = 0 ∧ K ≠ .constGlobal)
    (fun A S K S' K' ⟨h1, h2⟩ hk => ⟨h1, fun e => h2 (by subst e; cases K <;> simp_all [BlockKind.norm])⟩)
    h h' ⟨A, S, K, ⟨hal, hK⟩, hb⟩ hn hE hco
  exact ⟨A', S', K', bs, hal', hsz, hdec, hb', hK'⟩

theorem ECell.dormant_unit (ls : LStat) : ECell.unit.Dormant ls :=
  ⟨fun _ => rfl, fun _ h => by
    rcases h with ⟨t, -, h⟩ | ⟨_, _, -, h⟩
    · rcases t with _ | ⟨γ, e⟩ <;> simp [ECell.unit, Frac.zero] at h
    · simp [ECell.unit, Frac.zero] at h,
    fun _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem ExtTrue.unit (m : Mem) : ExtTrue m Ghost.unit := fun _ =>
  ⟨fun _ _ h => by simp [Ghost.unit, ECell.unit] at h, fun _ h => absurd h ((ECell.dormant_unit _).2.1 _)⟩

theorem ECell.tagOk_unit (ls : LStat) : ECell.unit.TagOk ls :=
  ⟨fun n N E => ⟨fun _ _ => 0, by have := (ECell.dormant_unit ls).mass_zero .root n N E; grind,
    fun _ _ _ _ ha => by have := (ECell.dormant_unit ls).mass_zero ha n N E; grind⟩,
    (ECell.dormant_unit ls).2.2⟩

theorem Ghost.CValid.unit : Ghost.unit.CValid :=
  ⟨fun _ _ => ⟨ECell.valid_unit, ECell.tagOk_unit _⟩, 0, fun _ _ _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem ClFresh.unit (m : Mem) : ClFresh m Ghost.unit := fun _ _ _ => rfl

/-- No ghost state composes in every memory without stack budgets. (A memory with a budget
demands the thread's stack token, `StackAuth`.) -/
theorem GOk.unit {m : Mem} (hm : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    GOk m Ghost.unit Ghost.unit :=
  ⟨⟨⟨fun _ => .inl fun _ => rfl, fun _ => by
      simpa [Ghost.add, Ghost.unit] using And.intro ECell.valid_unit (ECell.tagOk_unit _),
      by simpa using Ghost.CValid.unit, by simpa using ACell.valid_unit⟩,
    0, fun _ _ => ⟨by simp [Ghost.add, Ghost.unit], fun _ _ _ => by simp [Ghost.add, Ghost.unit, ECell.add, ECell.unit, Frac.zero, Frac.add] <;> grind,
      fun _ _ _ _ => rfl⟩⟩,
    by simpa using ExtTrue.unit m, by simpa using ClFresh.unit m, by simpa using MemAuth.unit hm⟩

/-- The full extents of `E` with the one of `b` split off. -/
theorem Ghost.exts_split {E : BlockId → Option (Nat × BlockKind)} {b : BlockId} {S : Nat}
    {K : BlockKind} (h : E b = some (S, K)) :
    Ghost.exts E = (Ghost.atExt b (ECell.auth1 S K Frac.one)).add
      (Ghost.exts fun x => if x = b then none else E x) := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.atExt, Ghost.exts, Ghost.unit]
  · funext x
    simp only [Ghost.add, Ghost.atExt, Ghost.exts]
    by_cases hx : x = b
    · subst hx; simp [h]
    · simp [hx]
  · funext x y; simp [Ghost.add, Ghost.atExt, Ghost.exts, Ghost.unit]
  · simp
  · funext l; simp [Ghost.add, Ghost.atExt, Ghost.exts, Ghost.unit]

/-- A legacy assertion with the full extent of one block. -/
theorem up_sep_bext {P : Assn} {b : BlockId} {S : Nat} {K : BlockKind} {r : Res}
    (h : (up P ⋆ bext b S K) r) : upE P (fun x => if x = b then some (S, K) else none) r := by
  obtain ⟨r₁, r₂, -, rfl, ⟨hp, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  refine ⟨by simpa [h2] using hp, by simp [k1, k2, Know.union_none], ?_⟩
  simp only [g1, g2, Ghost.unit_add]
  ext1
  · funext γ; simp [Ghost.atExt, Ghost.exts, Ghost.unit]
  · funext x; simp only [Ghost.atExt, Ghost.exts]; split <;> simp_all
  · funext x y; simp [Ghost.atExt, Ghost.exts, Ghost.unit]
  · simp
  · funext l; simp [Ghost.atExt, Ghost.exts, Ghost.unit]

/-! ## Address disjointness of live blocks (stage 3) -/

/-- **Owned bytes of two different blocks lie at disjoint addresses**: owning bytes `x` and `y`
of `b` and `x'` and `y'` of `b'` puts byte `x` of `b` before byte `y'` of `b'` or byte `x'` of
`b'` before byte `y` of `b` (from ownership and `Mem.LiveDisjoint`, part of `Mem.FSeq`: the live
bytes of two blocks are apart; a block may lie below an OS mapping's live bytes, MM-19). Taking
the last and the first owned byte of each gives the owned ranges; whole blocks need their extents
(`bext`). -/
theorem Holds.apart {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq)
    {b b' : BlockId} {x y x' y' : Nat} {fc gc fc' gc' : FCell} (hbb : b ≠ b')
    (h1 : r.heap (b, x) = some fc) (hy : r.heap (b, y) = some gc)
    (h2 : r.heap (b', x') = some fc') (hy' : r.heap (b', y') = some gc') :
    fc.cell.addr + x < fc'.cell.addr + y' ∨ fc'.cell.addr + x' < fc.cell.addr + y := by
  obtain ⟨blk, hb, hl, hx, -, ha, -⟩ := hh.block h1
  obtain ⟨blk', hb', hl', hx', -, ha', -⟩ := hh.block h2
  obtain ⟨blk₁, hb₁, -, hy₁, hlo, -, -⟩ := hh.block hy
  obtain ⟨blk₁', hb₁', -, hy₁', hlo', -, -⟩ := hh.block hy'
  rw [hb] at hb₁; cases hb₁
  rw [hb'] at hb₁'; cases hb₁'
  have := clearOf_iff.mp (hs.2.2.1 b b' blk blk' hbb hb hb' hl')
  rw [ha, ha']
  rcases this with h | h | h | h | h
  · simp_all
  all_goals omega

/-- **The `apart` rule**: owning bytes `x` and `y` of `b` (address `A`) and `x'` and `y'` of `b'`
(address `A'`) gives the fact that byte `x` lies before byte `y'` or byte `x'` before byte `y`
(`Holds.apart`). -/
theorem FTriple.apart {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {b b' : BlockId}
    {A x y A' x' y' : Nat} (hbb : b ≠ b')
    (hc : ∀ r, P r → (∃ fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A) ∧
      (∃ fc, r.heap (b, y) = some fc) ∧ (∃ fc, r.heap (b', x') = some fc ∧ fc.cell.addr = A') ∧
      ∃ fc, r.heap (b', y') = some fc)
    (ht : FTriple (⟪A + x < A' + y' ∨ A' + x' < A + y⟫ ⋆ P) c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨⟨fc, h1, rfl⟩, ⟨gc, hy⟩, ⟨fc', h2, rfl⟩, ⟨gc', hy'⟩⟩ := hc r hp
  exact ht m r rF hh (sep_lift.mpr ⟨hh.apart hs hbb h1 hy h2 hy', hp⟩) hs

end Full
end Zig
