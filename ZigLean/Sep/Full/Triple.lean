import ZigLean.Sep.Full.Res
import ZigLean.Conc.Lemmas
import ZigLean.Sep.Block
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
* **Lifting** (`ofTriple`): a legacy `Triple P c Q` of a program that keeps the atomic layout and
  every block's address and keeps live blocks apart (`Tame`) is a full triple of `up P` and
  `up Q` (the result's bytes are unconstrained). Every primitive of plain generated code is `Tame` (`Tame.load`, `.store`, `.alloc`, `.free`, `.ptrAddr`, closed
  under `pure` and `bind`), so the legacy rules carry over unchanged.
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

/-- `m` holds the resource `r` and the frame `rF`: their disjoint union matches `m` (its live
bytes, each byte's tag constraint: `FMatch`), their knowledge is true in `m`, and their ghost
states compose (`Ghost.Ok`). -/
structure Holds (m : Mem) (r rF : Res) : Prop where
  disj : FHeap.Disjoint r.heap rF.heap
  heap : FMatch m (r.heap ∪ rF.heap)
  know : Know.Sub r.know m.kn
  knowF : Know.Sub rF.know m.kn
  ghost : GOk m r.gh rF.gh

/-- Partial correctness without a panic, over full-state resources (module doc). -/
def FTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
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
    ⟨FHeap.disjoint_union_right.mpr ⟨hd, hPF⟩, by rw [← FHeap.union_assoc]; exact hheap, hk.left,
      hk.right.union hkF, GOk.assoc.mp hg⟩ hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd', hh', hk', hkF', hg'⟩, hq, hs'⟩ := this
    obtain ⟨hQR, hQF⟩ := FHeap.disjoint_union_right.mp hd'
    exact ⟨⟨r'.heap ∪ rR.heap, r'.know.union rR.know, r'.gh.add rR.gh⟩,
      ⟨FHeap.disjoint_union_left.mpr ⟨hQF, hRF⟩, by rw [FHeap.union_assoc]; exact hh',
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
    | error e => intro h1; exact h1.elim
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

/-- Knowledge and ghost state (anything that owns no bytes) can be forgotten. -/
theorem drop {K : α → FAssn} (ht : FTriple P c (fun v => Q v ⋆ K v))
    (hK : ∀ v r, K v r → r.heap = FHeap.empty) : FTriple P c Q := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd, hm, hk, hkF, hg⟩, ⟨r₁, r₂, -, rfl, hq, hk2⟩, hs'⟩ := this
    have e := hK _ _ hk2
    simp only [e, FHeap.union_empty] at hd hm
    exact ⟨r₁, ⟨hd, hm, hk.left, hkF, GOk.mono hg⟩, hq, hs'⟩

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

/-- **An owned byte is a live byte**: owning byte `x` of block `b` gives a live block whose size
is above `x` (and whose mapping start is at most `x`), at the cell's address. In-bounds facts
come from ownership (`docs/sep-full-state.md` §Block extents). -/
theorem Holds.block {m : Mem} {r rF : Res} (hh : Holds m r rF) {b : BlockId} {x : Nat} {fc : FCell}
    (h : r.heap (b, x) = some fc) : ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
      x < blk.bytes.size ∧ blk.kind.mappedLo ≤ x ∧ fc.cell.addr = blk.addr ∧
      fc.cell.kind.norm = blk.kind.norm := by
  obtain ⟨c, hc, hn⟩ := hh.cellN h
  obtain ⟨blk, hb, hl, hx, he⟩ := Mem.heap_some hc
  obtain ⟨blk', hb', hlo⟩ := Mem.heap_some_lo hc
  rw [hb] at hb'; cases hb'
  have ha := congrArg Cell.addr hn
  have hk := congrArg Cell.kind hn
  subst he
  exact ⟨blk, hb, hl, hx, hlo, ha.symm, hk.symm⟩

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

theorem FHeap.Sim.norm {h₁ h₂ : FHeap} (hs : FHeap.Sim h₁ h₂) (l : Loc) :
    (h₁ l).map (fun fc => fc.cell.norm) = (h₂ l).map (fun fc => fc.cell.norm) := by
  have := congrArg (Option.map Prod.fst) (hs l)
  simpa [Option.map_map, Function.comp_def] using this

/-- The resource and the frame swapped. -/
theorem Holds.swap {m : Mem} {r rF : Res} (hh : Holds m r rF) : Holds m rF r :=
  ⟨hh.disj.symm, by rw [FHeap.union_comm hh.disj.symm]; exact hh.heap, hh.knowF, hh.know,
    by have := hh.ghost; unfold GOk at this ⊢; rw [Ghost.Ok.comm, Ghost.add_comm]; exact this⟩

/-- A frame that is the same up to `Cell.norm` (and keeps its knowledge and ghost state) is held
by the same memory. -/
theorem Holds.congrF {m : Mem} {r rF rF' : Res} (hh : Holds m r rF) (hs : FHeap.Sim rF'.heap rF.heap)
    (hk : rF'.know = rF.know) (hg : rF'.gh = rF.gh) : Holds m r rF' := by
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hl => ?_⟩, hh.know, hk ▸ hh.knowF, hg ▸ hh.ghost⟩
  · rcases hh.disj l with e | e
    · exact .inl e
    · exact .inr (hs.none.mpr e)
  · rw [hh.heap.1 l]
    simp only [FHeap.union_apply]
    cases e : r.heap l with
    | some _ => rfl
    | none => simp only [Option.none_or]; exact (hs.norm l).symm
  · simp only [FHeap.union_apply] at hl
    cases e : r.heap l with
    | some fc0 =>
      rw [e] at hl; cases hl
      exact hh.heap.2 l fc (by simp [e])
    | none =>
      rw [e, Option.none_or] at hl
      obtain ⟨fc', h', -, ha⟩ := hs.symm.some hl
      rw [← ha]
      exact hh.heap.2 l fc' (by simp [e, h'])

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

/-- Under `Holds`, the resource and the frame with their actual sizes and kinds are held. -/
theorem Holds.fix {m : Mem} {r rF : Res} (hh : Holds m r rF) : Holds m (r.fix m) (rF.fix m) := by
  refine ⟨FHeap.fix_disjoint hh.disj, ⟨fun l => ?_, fun l fc hl => ?_⟩, hh.know, hh.knowF, hh.ghost⟩
  · show _ = ((r.heap.fix m ∪ rF.heap.fix m) l).map _
    rw [← FHeap.fix_union]
    cases e : (r.heap ∪ rF.heap) l with
    | none => rw [hh.heap.none e, (FHeap.fix_none (m := m)).mpr e]; rfl
    | some fc =>
      obtain ⟨c, hc, hf, -⟩ := hh.heap.fix_cell e
      rw [hc, hf]; rfl
  · simp only [Res.fix] at hl
    rw [← FHeap.fix_union] at hl
    simp only [FHeap.fix, Option.map_eq_some_iff] at hl
    obtain ⟨fc0, h0, rfl⟩ := hl
    have := hh.heap.2 l fc0 h0
    split <;> exact this

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

/-- The live bytes of a memory that holds `r` and `rF` with their exact cells. -/
theorem Holds.heap_exact {m : Mem} {r rF : Res} (hh : Holds m r rF) (hx : Exact m r)
    (hxF : Exact m rF) : m.heap = r.heap.erase ∪ rF.heap.erase := by
  funext l
  simp only [Heap.union_apply, FHeap.erase]
  cases e : r.heap l with
  | some fc => simp [hx l fc e]
  | none =>
    cases e' : rF.heap l with
    | some fc => simp [hxF l fc e']
    | none => exact hh.heap.none (by simp [e, e'])

/-- **Rules from exact cells.** To prove a triple, it is enough to prove it for resources whose
cells are the memory's exact cells, if the precondition survives reading the actual sizes
(`r.fix m`); the frame is the actual frame up to `Cell.norm`. -/
theorem FTriple.of_fix {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.FSeq →
      match (c.run m).run with
      | none => True
      | some (.error _) => False
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
  refine hh.heap.2 l fc ?_
  rcases hh.disj l with e | e
  · rw [FHeap.union_apply, e, Option.none_or, hc]
  · rw [e] at hc; cases hc

/-- **Knowledge from ownership.** Owning a byte of block `b`, whose cell has the address `A`,
gives `known b A`. -/
theorem FTriple.know_intro {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {b : BlockId}
    {A : Nat} (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : FTriple (P ⋆ known b A) c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨x, fc, hx, hA⟩ := hc r hp
  have hkn : m.kn b A := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hx
    exact ⟨blk, hblk, by rw [← hA, ha]⟩
  have hres : (P ⋆ known b A) ⟨r.heap, r.know.union fun b' A' => b' = b ∧ A' = A, r.gh⟩ :=
    ⟨r, ⟨FHeap.empty, fun b' A' => b' = b ∧ A' = A, Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩
  have hk : Know.Sub (r.know.union fun b' A' => b' = b ∧ A' = A) m.kn :=
    hh.know.union fun b' A' h => by obtain ⟨rfl, rfl⟩ := h; exact hkn
  exact ht m ⟨r.heap, r.know.union fun b' A' => b' = b ∧ A' = A, r.gh⟩ rF
    ⟨hh.disj, hh.heap, hk, hh.knowF, hh.ghost⟩ hres hs

theorem ptrAddr_run {m : Mem} {b : BlockId} {blk : Block} (hb : m.blocks[b]? = some blk)
    (off : Int) : (ptrAddr ⟨some b, off⟩).run m = pure ((blk.addr : Int) + off, m) := by
  simp [ptrAddr, hb, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.bind, ExceptT.bindCont]

/-- **`@intFromPtr` of a pointer into block `b`, live or freed** (O1): only the knowledge of its
address is needed. -/
theorem FTriple.ptrAddr {b : BlockId} {A : Nat} (off : Int) :
    FTriple (known b A) (Zig.ptrAddr ⟨some b, off⟩) (fun a => ⟪a = (A : Int) + off⟫ ⋆ known b A) :=
  FTriple.of_run fun m r _ hh hp hs => by
    obtain ⟨blk, hblk, hA⟩ := hh.know b A (by rw [hp.2.1]; exact ⟨rfl, rfl⟩)
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

/-- `c` keeps the atomic layout and every block's address, and keeps live blocks apart. -/
def Tame {α : Type} (c : MemM α) : Prop :=
  ∀ m v m', (c.run m).run = some (.ok (v, m')) → shapes m' = shapes m ∧ KMono m m' ∧ LDMono m m'

namespace Tame

variable {α β : Type}

theorem pure' (v : α) : Tame (pure v : MemM α) := fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h; exact ⟨rfl, KMono.refl _, LDMono.refl _⟩

theorem bind {c : MemM α} {f : α → MemM β} (hc : Tame c) (hf : ∀ v, Tame (f v)) :
    Tame (c >>= f) := fun m v m'' h => by
  obtain ⟨a, m', h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨s1, k1, d1⟩ := hc m a m' h1
  obtain ⟨s2, k2, d2⟩ := hf a m' v m'' h2
  exact ⟨s2.trans s1, k1.trans k2, d1.trans d2⟩

/-- A step that changes only clocks, footprint and bytes or liveness of blocks. -/
theorem of_eq {c : MemM α}
    (h : ∀ m v m', (c.run m).run = some (.ok (v, m')) →
      m'.atomics = m.atomics ∧ KMono m m' ∧ LDMono m m') :
    Tame c := fun m v m' hr => by
  obtain ⟨ha, hk, hd⟩ := h m v m' hr
  exact ⟨by simp [shapes, ha], hk, hd⟩

theorem loadBytes (p : Ptr) (n a : Nat) (k : AccessKind) : Tame (Zig.loadBytes p n a k) :=
  of_eq fun _ _ _ h => by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := Conc.Proto.loadBytes_ok h
    exact ⟨rfl, KMono.of_blocks rfl, LDMono.of_blocks rfl⟩

theorem lift (r : Result α) : Tame (StateT.lift r : MemM α) := of_eq fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact ⟨rfl, KMono.refl _, LDMono.refl _⟩

theorem get' : Tame (get : MemM Mem) := of_eq fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h; exact ⟨rfl, KMono.refl _, LDMono.refl _⟩

theorem load (T : Type) [Enc T] (a : Nat) (p : Ptr) : Tame (Zig.load T a p) :=
  bind (loadBytes p _ a .read) fun bs => bind get' fun m => lift (decodeLoad m.blocks bs)

theorem storeBytes (p : Ptr) (a : Nat) (bs : Array Byte) (k : AccessKind) :
    Tame (Zig.storeBytes p a bs k) := of_eq fun _ _ _ h => by
  obtain ⟨b, blk, o, hacc, -, -, rfl⟩ := Conc.Proto.storeBytes_ok h
  exact ⟨rfl, KMono.set (blk' := { blk with bytes := writeBytes blk.bytes o bs })
    (access_eq hacc).2.1 rfl rfl, LDMono.set (nb := { blk with bytes := writeBytes blk.bytes o bs })
    (access_eq hacc).2.1 id rfl (by
      obtain ⟨-, -, -, h0, hn, -, rfl⟩ := access_eq hacc
      simp only; rw [writeBytes_size _ _ _ (by omega)]; exact Nat.le_refl _) rfl⟩

theorem store {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : Tame (Zig.store a p v) :=
  storeBytes p a _ .write

theorem alloc (kind : BlockKind) (size align : Nat) : Tame (Zig.alloc kind size align) :=
  of_eq fun m v m' h => by
    cases hroom : m.roomFor size align
    · rw [alloc_run_noRoom m hroom] at h; cases h
    rw [alloc_run_eq m hroom] at h
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
    exact ⟨rfl, KMono.push rfl, LDMono.alloc hroom rfl (by simp) rfl⟩

theorem free (p : Ptr) : Tame (Zig.free p) := of_eq fun m v m' h => by
  unfold Zig.free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · exact (Conc.Proto.MemM.throw_ok h₁).elim
  · split at h₁
    · rename_i b _ blk hblk
      split at h₁
      · split at h₁
        · exact (Conc.Proto.MemM.throw_ok h₁).elim
        · have := Conc.Proto.MemM.set_ok h₁
          subst this
          exact ⟨rfl, KMono.set (blk' := { blk with live := false }) hblk rfl rfl,
            LDMono.set (nb := { blk with live := false }) hblk (by simp) rfl (Nat.le_refl _) rfl⟩
      · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

theorem ptrAddr (p : Ptr) : Tame (Zig.ptrAddr p) := of_eq fun m v m' h => by
  unfold Zig.ptrAddr at h
  split at h
  · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h; exact ⟨rfl, KMono.refl _, LDMono.refl _⟩
  · obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
    split at h₁
    · obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h₁; exact ⟨rfl, KMono.refl _, LDMono.refl _⟩
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

end Tame

/-! ## Lifting legacy triples (`docs/sep-full-state.md` §The bridge from the legacy layer)

A legacy assertion's cells record their block's size and kind; a full-state cell pins neither
(`FMatch`). So a legacy triple lifts when its precondition does not depend on the sizes it
records, except on blocks whose full extent it owns (`SizeFree E P`, with the extents `E` in the
precondition, `upE P E`), and when the program changes the extent of no block whose claims the
frame may hold: either every block of `P`'s bytes is pinned by `E` (the frame then has a byte of
every block it has a claim on, and the legacy frame keeps that byte, size and kind included), or
the program keeps every other block (`Keeps`). The post owns the full extents of the blocks it
has bytes of that are pinned or that `P` had no bytes of (new blocks among them). -/

/-- `P` holds of every heap with the same cells up to their sizes and mapping starts
(`Cell.norm`), one size and kind per block, that agrees with it on the blocks of `E`. -/
def SizeFree (E : BlockId → Option (Nat × BlockKind)) (P : Assn) : Prop :=
  ∀ h h', P h → (∀ l, (h l).map Cell.norm = (h' l).map Cell.norm) →
    (∀ l c, h l = some c → (E l.1).isSome → h' l = some c) →
    (∀ l l' c c', h' l = some c → h' l' = some c' → l.1 = l'.1 → c.size = c'.size ∧ c.kind = c'.kind) →
    P h'

/-- An assertion whose bytes all lie in blocks of `E` is size-free relative to `E`. -/
theorem SizeFree.of_pinned {E : BlockId → Option (Nat × BlockKind)} {P : Assn}
    (h : ∀ h, P h → ∀ l c, h l = some c → (E l.1).isSome) : SizeFree E P := by
  intro h₁ h₂ hp hn he _
  have e : h₂ = h₁ := by
    funext l
    cases e1 : h₁ l with
    | some c => exact he l c e1 (h h₁ hp l c e1)
    | none => have := hn l; rw [e1] at this; cases e2 : h₂ l <;> simp_all
  rw [e]; exact hp

/-- `c` keeps every block outside `D` that is live: live, with the same size and kind. -/
def Keeps {α : Type} (D : BlockId → Prop) (c : MemM α) : Prop :=
  ∀ m v m', (c.run m).run = some (.ok (v, m')) → ∀ b blk, ¬ D b → m.blocks[b]? = some blk →
    blk.live = true → ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = true ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind

namespace Keeps

variable {α β : Type} {D : BlockId → Prop}

theorem of_keepsExt {c : MemM α} (h : ∀ m v m', (c.run m).run = some (.ok (v, m')) → KeepsExt m m') :
    Keeps D c := fun m v m' hr b blk _ hb hl => h m v m' hr b blk hb hl

theorem pure' (v : α) : Keeps D (pure v : MemM α) := of_keepsExt fun _ _ _ h => by
  obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h; exact KeepsExt.refl _

theorem bind {c : MemM α} {f : α → MemM β} (hc : Keeps D c) (hf : ∀ v, Keeps D (f v)) :
    Keeps D (c >>= f) := fun m v m'' h b blk hD hb hl => by
  obtain ⟨a, m', h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨blk', hb', hl', hs, hk⟩ := hc m a m' h1 b blk hD hb hl
  obtain ⟨blk'', hb'', hl'', hs', hk'⟩ := hf a m' v m'' h2 b blk' hD hb' hl'
  exact ⟨blk'', hb'', hl'', hs'.trans hs, hk'.trans hk⟩

theorem loadBytes (p : Ptr) (n a : Nat) (k : AccessKind) : Keeps D (Zig.loadBytes p n a k) :=
  of_keepsExt fun _ _ _ h => by
    obtain ⟨-, -, -, -, -, -, rfl⟩ := Conc.Proto.loadBytes_ok h
    exact KeepsExt.of_blocks rfl

theorem load (T : Type) [Enc T] (a : Nat) (p : Ptr) : Keeps D (Zig.load T a p) :=
  bind (loadBytes p _ a .read) fun _ => bind (of_keepsExt fun _ _ _ h => by
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.get_ok h; exact KeepsExt.refl _) fun _ =>
    of_keepsExt fun _ _ _ h => by obtain ⟨-, rfl⟩ := Conc.Proto.MemM.lift_ok h; exact KeepsExt.refl _

theorem storeBytes (p : Ptr) (a : Nat) (bs : Array Byte) (k : AccessKind) :
    Keeps D (Zig.storeBytes p a bs k) := of_keepsExt fun _ _ _ h => by
  obtain ⟨b, blk, o, hacc, -, -, rfl⟩ := Conc.Proto.storeBytes_ok h
  exact KeepsExt.set (nb := { blk with bytes := writeBytes blk.bytes o bs }) (access_eq hacc).2.1 rfl
    (by obtain ⟨-, -, -, h0, hn, -, rfl⟩ := access_eq hacc
        simp only; rw [writeBytes_size _ _ _ (by omega)]) rfl rfl

theorem store {T : Type} [Enc T] (a : Nat) (p : Ptr) (v : T) : Keeps D (Zig.store a p v) :=
  storeBytes p a _ .write

theorem alloc (kind : BlockKind) (size align : Nat) : Keeps D (Zig.alloc kind size align) :=
  of_keepsExt fun m v m' h => by
    cases hroom : m.roomFor size align
    · rw [alloc_run_noRoom m hroom] at h; cases h
    rw [alloc_run_eq m hroom] at h
    obtain ⟨-, rfl⟩ := Conc.Proto.MemM.pure_ok h
    exact KeepsExt.push rfl

/-- `free p` keeps every block but `p`'s. -/
theorem free (p : Ptr) : Keeps (fun b => p.block = some b) (Zig.free p) := by
  intro m v m' h b' x hD hx hl
  unfold Zig.free at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok hg
  split at h₁
  · exact (Conc.Proto.MemM.throw_ok h₁).elim
  · rename_i b hpb
    split at h₁
    · rename_i blk hblk
      split at h₁
      · split at h₁
        · exact (Conc.Proto.MemM.throw_ok h₁).elim
        have := Conc.Proto.MemM.set_ok h₁
        subst this
        have hne : b ≠ b' := fun e => hD (by rw [hpb, e])
        exact ⟨x, by simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hne, hx], hl, rfl, rfl⟩
      · exact (Conc.Proto.MemM.throw_ok h₁).elim
    · exact (Conc.Proto.MemM.throw_ok h₁).elim

end Keeps

/-- The postcondition of a lifted triple: the legacy post, and the full extents `E'` of the blocks
it has bytes of that were pinned by `E` or that the precondition had no bytes of (blocks outside
`B`). -/
def upPost (Q : Assn) (B : BlockId → Prop) (E : BlockId → Option (Nat × BlockKind)) : FAssn :=
  fun r => ∃ E', upE Q E' r ∧ ∀ l c, r.heap l = some c → (B l.1 → (E l.1).isSome) →
    E' l.1 = some (c.cell.size, c.cell.kind)

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
    obtain ⟨blk, hb, -, hbs, hbk, -⟩ := (hh.ghost.2 l.1).1 S K hauth
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

/-- What the frame's claims on block `b` give: a live block with a live byte. -/
theorem claim_byte {m : Mem} {g : Ghost} (ht : ExtTrue m g) {b : BlockId}
    (hc : (g.extent b).Claims g.ls) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ m.heap (b, blk.kind.mappedLo) ≠ none := by
  rcases hc with ⟨S, K, h⟩ | ⟨k, h⟩
  · obtain ⟨blk, hb, hl, hS, hK, hlo⟩ := (ht b).1 S K h
    refine ⟨blk, hb, hl, ?_⟩
    rw [Mem.heap_of hb, dif_pos ⟨hl, by rw [hS, hK]; exact hlo, Nat.le_refl _⟩]; simp
  · obtain ⟨blk, hb, hl, -, hlo⟩ := (ht b).2 k h
    refine ⟨blk, hb, hl, ?_⟩
    rw [Mem.heap_of hb, dif_pos ⟨hl, hlo, Nat.le_refl _⟩]; simp

/-- **A resource holding the full extent of `b` leaves the frame only dormant claims on `b`**
(no authority claim, no live share, no tag of a future epoch). -/
theorem full_excl {g gF : Ghost} (hok : Ghost.Ok g gF) {b : BlockId} {S : Nat} {K : BlockKind}
    (hg : g.extent b = ECell.auth1 S K Frac.one) : (gF.extent b).Dormant (g.add gF).ls := by
  have hv := hok.1.2 b
  have e : (g.add gF).extent b = (ECell.auth1 S K Frac.one).add (gF.extent b) := by
    simp only [Ghost.add, hg]
  rw [e] at hv
  exact ECell.dormant_of_auth1 hv.1 hv.2

open Classical in
/-- **Lifting a legacy triple** (`docs/sep-full-state.md` §The bridge from the legacy layer):
`P`'s bytes lie in the blocks `B`, `P` is size-free outside the pinned blocks `E` (whose cells
record their extents and whose full extents the precondition owns), and the program changes no
block the frame may have a claim on: every block of `B` is pinned, or the program keeps every
block outside `E`. -/
theorem FTriple.ofTriple {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    {E : BlockId → Option (Nat × BlockKind)} {B : BlockId → Prop}
    (ht : Triple P c Q) (hc : Tame c)
    (hB : ∀ h, P h → ∀ l c, h l = some c → B l.1)
    (hpin : ∀ h, P h → ∀ l c S K, h l = some c → E l.1 = some (S, K) → c.size = S ∧ c.kind = K)
    (hsf : SizeFree E P)
    (hk : (∀ b, B b → (E b).isSome) ∨ Keeps (fun b => (E b).isSome) c) :
    FTriple (upE P E) c (fun v => upPost (Q v) B E) := by
  intro m r rF hh hp hs
  have hx := hh.fix_exact
  have hxF := hh.fix_exactF
  have hP₀ := upE_fix hsf hpin hh hp
  have heq := hh.fix.heap_exact hx hxF
  have := ht m _ _ (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj)) heq hP₀ hs.1
  revert this
  cases hrun : (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h; exact h
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨hQ, hdQ, hmQ, hq, hs'⟩
      obtain ⟨hsh, hkm, hld⟩ := hc m v m' hrun
      have hrE : r.gh = Ghost.exts E := hp.2.2
      -- frame bytes: the legacy frame keeps them exactly
      have hFkeep : ∀ l fc, rF.heap l = some fc → m'.heap l = m.heap l := by
        intro l fc hl
        have h1 : (rF.fix m).heap.erase l = m.heap l := by
          have := hxF l; simp only [FHeap.erase]
          cases e : (rF.fix m).heap l with
          | none => simp [Res.fix, FHeap.fix, hl] at e
          | some fc' => rw [this fc' e]; rfl
        rw [hmQ, heq]
        simp only [Heap.union_apply]
        have hQn : hQ l = none := by
          rcases hdQ l with e | e
          · exact e
          · simp [FHeap.erase, Res.fix, FHeap.fix, hl] at e
        have hrn : (r.fix m).heap.erase l = none := by
          rcases hh.disj l with e | e
          · simp [FHeap.erase, Res.fix, FHeap.fix, e]
          · rw [e] at hl; cases hl
        rw [hQn, hrn]; rfl
      -- a frame byte pins its block's extent
      have hFblk : ∀ b o fc blk, rF.heap (b, o) = some fc → m.blocks[b]? = some blk →
          ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
            blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
        intro b o fc blk hl hb
        obtain ⟨c0, hc0, -⟩ := hh.swap.cellN hl
        have e := hFkeep (b, o) fc hl
        rw [hc0] at e
        obtain ⟨blk', hb', hl', _, he'⟩ := Mem.heap_some e
        obtain ⟨blk0, hb0, hl0, _, he0⟩ := Mem.heap_some hc0
        rw [hb] at hb0; cases hb0
        rw [he0] at he'
        simp only [Cell.mk.injEq] at he'
        exact ⟨blk', hb', by rw [hl', hl0], he'.2.2.1.symm, he'.2.2.2.symm⟩
      -- a block with a frame claim and no frame byte is kept
      have hep : (r.gh.add rF.gh).ls = rF.gh.ls := by rw [hrE]; exact Ghost.ls_exts_add
      have hvF : ∀ b, (rF.gh.extent b).Valid ∧ (rF.gh.extent b).TagOk rF.gh.ls := fun b => by
        have hv := hh.ghost.1.1.2 b
        have hle : (rF.gh.extent b).Le ((r.gh.add rF.gh).extent b) := ECell.le_add' _ _
        refine ⟨ECell.Valid.of_add (b := r.gh.extent b) ?_, ECell.TagOk.of_le (ls' := (r.gh.add rF.gh).ls)
          (fun _ _ _ h => by rw [hep]; exact h) hh.ghost.1.1.uniq hle hv.2⟩
        rw [ECell.add_comm]; exact hv.1
      have hfrm : ∀ b, (rF.gh.extent b).Claims rF.gh.ls → ((r.gh.add rF.gh).extent b).Claims (r.gh.add rF.gh).ls :=
        fun b h => h.mono (fun _ _ _ h => by rw [hep]; exact h) (ECell.le_add' _ _)
      have hclaim : ∀ b, (rF.gh.extent b).Claims rF.gh.ls →
          ∀ blk, m.blocks[b]? = some blk → ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
            blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
        intro b hcl blk hb
        have hEb : (E b).isSome = false := by
          cases hE : E b with
          | none => rfl
          | some SK =>
            obtain ⟨S, K⟩ := SK
            have hu := full_excl hh.ghost.1 (b := b) (S := S) (K := K)
              (by rw [hrE]; simp [Ghost.exts, hE])
            rw [hep] at hu
            exfalso
            rcases hcl with ⟨S', K', h⟩ | ⟨k, h⟩
            · rw [hu.1] at h; exact Nat.lt_irrefl 0 h
            · exact hu.2.1 k h
        have ht : ExtTrue m (r.gh.add rF.gh) := hh.ghost.2
        obtain ⟨blk0, hb0, hl0, hbyte⟩ := claim_byte ht (b := b) (hfrm b hcl)
        rw [hb] at hb0; cases hb0
        by_cases hF : ∃ o fc, rF.heap (b, o) = some fc
        · obtain ⟨o, fc, hfc⟩ := hF
          exact hFblk b o fc blk hfc hb
        · have hrb : B b := by
            cases e : (r.heap ∪ rF.heap) (b, blk.kind.mappedLo) with
            | none => exact absurd (hh.heap.none e) hbyte
            | some fc =>
              simp only [FHeap.union_apply] at e
              cases e1 : r.heap (b, blk.kind.mappedLo) with
              | none => rw [e1, Option.none_or] at e; exact absurd ⟨_, fc, e⟩ hF
              | some fc1 => exact hB _ hp.1 (b, blk.kind.mappedLo) fc1.cell (by simp [FHeap.erase, e1])
          rcases hk with hk | hk
          · have := hk b hrb; rw [hEb] at this; cases this
          · obtain ⟨blk', hb', hl', hs1, hk1⟩ := hk m v m' hrun b blk (by simp [hEb]) hb hl0
            exact ⟨blk', hb', by rw [hl', hl0], hs1, hk1⟩
      -- the new extents: blocks with post bytes, pinned or outside `B`
      let E' : BlockId → Option (Nat × BlockKind) := fun b =>
        match m'.blocks[b]? with
        | some blk => if blk.live = true ∧ blk.kind.mappedLo < blk.bytes.size ∧
            (∃ o, hQ (b, o) ≠ none) ∧ (B b → (E b).isSome) then some (blk.bytes.size, blk.kind) else none
        | none => none
      -- no frame claim on a block of `E'`
      have hE'F : ∀ b, (E' b).isSome → (rF.gh.extent b).Dormant rF.gh.ls := by
        intro b hb
        cases hbm : m'.blocks[b]? with
        | none => simp [E', hbm] at hb
        | some blk' =>
          simp only [E', hbm] at hb
          split at hb
          · rename_i hcond
            obtain ⟨-, -, ⟨o, ho⟩, hBE⟩ := hcond
            by_cases hEb : (E b).isSome
            · obtain ⟨⟨S, K⟩, hE⟩ := Option.isSome_iff_exists.mp hEb
              have := full_excl hh.ghost.1 (b := b) (S := S) (K := K) (by rw [hrE]; simp [Ghost.exts, hE])
              rwa [hep] at this
            · -- `P` had no byte of `b`; a frame claim would give the frame a byte there
              have hnB : ¬ B b := fun h => hEb (hBE h)
              by_cases hcl : ¬ (rF.gh.extent b).Claims rF.gh.ls
              · exact ECell.dormant_of_not_claims hcl (hvF b).2.2
              exfalso
              replace hcl := Classical.not_not.mp hcl
              have ht : ExtTrue m (r.gh.add rF.gh) := hh.ghost.2
              obtain ⟨blk, hb0, -, hbyte⟩ := claim_byte ht (b := b) (hfrm b hcl)
              -- the frame owns byte `(b, lo)`, so `b` keeps its extent, and every post byte of `b` was live
              have hrn : ∀ o, r.heap (b, o) = none := fun o => by
                cases e : r.heap (b, o) with
                | none => rfl
                | some fc => exact absurd (hB _ hp.1 (b, o) fc.cell (by simp [FHeap.erase, e])) hnB
              have hFlo : ∃ fc, rF.heap (b, blk.kind.mappedLo) = some fc := by
                cases e : (r.heap ∪ rF.heap) (b, blk.kind.mappedLo) with
                | none => exact absurd (hh.heap.none e) hbyte
                | some fc =>
                  simp only [FHeap.union_apply, hrn, Option.none_or] at e
                  exact ⟨fc, e⟩
              obtain ⟨fc0, hfc0⟩ := hFlo
              obtain ⟨blk'', hb'', hl'', hs'', hk''⟩ := hFblk b _ fc0 blk hfc0 hb0
              rw [hbm] at hb''; cases hb''
              -- the post byte `(b, o)` is live in `m'`, hence in `m`, hence a frame byte
              have hlive : m'.heap (b, o) ≠ none := by
                rw [hmQ]; simp only [Heap.union_apply]
                cases e : hQ (b, o) with
                | none => exact absurd e ho
                | some _ => simp
              have hlive' : m.heap (b, o) ≠ none := by
                rw [Mem.heap_of hbm] at hlive
                rw [Mem.heap_of hb0]
                split at hlive
                · rename_i hc
                  rw [dif_pos ⟨by rw [← hl'']; exact hc.1, by rw [← hs'']; exact hc.2.1,
                    by rw [← hk'']; exact hc.2.2⟩]; simp
                · exact absurd rfl hlive
              have hFo : rF.heap (b, o) ≠ none := by
                cases e : (r.heap ∪ rF.heap) (b, o) with
                | none => exact absurd (hh.heap.none e) hlive'
                | some fc =>
                  simp only [FHeap.union_apply, hrn, Option.none_or] at e
                  rw [e]; simp
              rcases hdQ (b, o) with e | e
              · exact ho e
              · apply hFo
                simpa [FHeap.erase, Res.fix, FHeap.fix] using e
          · cases hb
      let hQ' : FHeap := fun l => (hQ l).map fun c => ⟨c, none⟩
      have hQe : hQ'.erase = hQ := by
        funext l; simp only [FHeap.erase, hQ', Option.map_map]; cases hQ l <;> rfl
      have hgF : Ghost.Ok (Ghost.exts E') rF.gh := by
        have hok := hh.ghost.1
        refine ⟨⟨fun γ => ?_, fun b => ?_⟩, ?_⟩
        · have := hok.1.1 γ
          simpa [Ghost.add, Ghost.exts, hrE] using this
        · rw [Ghost.ls_exts_add]
          by_cases hb : (E' b).isSome
          · obtain ⟨⟨S, K⟩, hS⟩ := Option.isSome_iff_exists.mp hb
            rw [show (Ghost.add (Ghost.exts E') rF.gh).extent b =
              (ECell.auth1 S K Frac.one).add (rF.gh.extent b) by simp [Ghost.add, Ghost.exts, hS]]
            exact (hE'F b hb).auth1_ok
          · have hn : E' b = none := by simpa using hb
            rw [show (Ghost.add (Ghost.exts E') rF.gh).extent b = rF.gh.extent b by
              simp [Ghost.add, Ghost.exts, hn]]
            exact hvF b
        · obtain ⟨N, hN⟩ := hok.2
          refine ⟨N, fun γ hγ => ⟨by have := (hN γ hγ).1; simpa [Ghost.add, Ghost.exts, hrE] using this,
            fun b e k => ?_, fun γ' e' M e => by
              have := (hN γ hγ).2.2 γ' e' M e; simpa [Ghost.add, Ghost.exts, hrE] using this⟩⟩
          have h1 := (hN γ hγ).2.1 b e k
          rw [hrE] at h1
          rw [((Ghost.exts_add_tags E' rF.gh b).2 γ e k).1, ((Ghost.exts_add_tags E' rF.gh b).2 γ e k).2]
          rwa [((Ghost.exts_add_tags E rF.gh b).2 γ e k).1, ((Ghost.exts_add_tags E rF.gh b).2 γ e k).2] at h1
      refine ⟨⟨hQ', Know.none, Ghost.exts E'⟩,
        ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hl => ?_⟩, Know.sub_none _, hh.knowF.trans hkm,
          hgF, fun b => ?_⟩,
        ⟨E', ⟨by show Q v hQ'.erase; rw [hQe]; exact hq, rfl, rfl⟩, fun l c hl hBE => ?_⟩,
        ⟨hs', by rw [hsh]; exact hs.2.1, hld hs.2.2⟩⟩
      · rcases hdQ l with e | e
        · left; simp [hQ', e]
        · right
          cases h2 : rF.heap l with
          | none => rfl
          | some fc => simp [FHeap.erase, Res.fix, FHeap.fix, h2] at e
      · -- the post cells and the frame's cells up to `Cell.norm`
        rw [hmQ]
        simp only [Heap.union_apply, FHeap.union_apply, hQ']
        cases e : hQ l with
        | some c0 => rfl
        | none =>
          simp only [Option.map_none, Option.none_or]
          have := hh.fix_sim.norm l
          simp only [Res.fix] at this
          rw [← this]
          simp only [FHeap.erase, Option.map_map]; rfl
      · cases e : hQ l with
        | some c0 =>
          simp only [FHeap.union_apply, hQ', e, Option.map_some, Option.some_or,
            Option.some.injEq] at hl
          subst hl; trivial
        | none =>
          simp only [FHeap.union_apply, hQ', e, Option.map_none, Option.none_or] at hl
          rw [hsh]; exact hh.tagF hl
      · -- the extent claims hold in `m'`
        have ht : ExtTrue m (r.gh.add rF.gh) := hh.ghost.2
        show ECell.TrueIn _ _ _ _
        rw [Ghost.ls_exts_add]
        by_cases hb : (E' b).isSome
        · have hu := hE'F b hb
          obtain ⟨⟨S, K⟩, hS⟩ := Option.isSome_iff_exists.mp hb
          have hX : (Ghost.add (Ghost.exts E') rF.gh).extent b = (ECell.auth1 S K Frac.one).add (rF.gh.extent b) := by
            simp [Ghost.add, Ghost.exts, hS]
          rw [hX]
          cases hbm : m'.blocks[b]? with
          | none => simp [E', hbm] at hS
          | some blk' =>
            simp only [E', hbm] at hS
            split at hS
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hS
              obtain ⟨rfl, rfl⟩ := hS
              refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
              · simp only [ECell.add, hu.1, Nat.add_zero, ECell.auth1] at hp'
                split at hp'
                · rename_i he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
                  exact ⟨blk', hbm, hcond.1, rfl, rfl, hcond.2.1⟩
                · cases hp'
              · rw [hu.req_auth1 hk']; exact ⟨blk', hbm, hcond.1, Nat.zero_le _, hcond.2.1⟩
            · cases hS
        · have hn : E' b = none := by simpa using hb
          have hfr : (Ghost.add (Ghost.exts E') rF.gh).extent b = rF.gh.extent b := by
            simp [Ghost.add, Ghost.exts, hn]
          rw [hfr]
          refine ⟨fun S K hp' => ?_, fun k hk' => ?_⟩
          · obtain ⟨blk, hb0, hl0, hS0, hK0, hlo⟩ := (ht b).1 S K (by simp only [Ghost.add, ECell.add]; omega)
            obtain ⟨blk', hb', hl', hs1, hk1⟩ := hclaim b (.inl ⟨S, K, hp'⟩) blk hb0
            exact ⟨blk', hb', by rw [hl', hl0], hs1.trans hS0, hk1.trans hK0, hlo⟩
          · obtain ⟨blk, hb0, hl0, hk0, hlo⟩ := (ht b).2 k
              (hk'.mono (fun _ _ _ h => by rw [hep]; exact h) (ECell.le_add' _ _))
            obtain ⟨blk', hb', hl', hs1, hk1⟩ := hclaim b (.inr ⟨k, hk'⟩) blk hb0
            exact ⟨blk', hb', by rw [hl', hl0], by omega, by rw [hk1, hs1]; exact hlo⟩
      · -- a post byte's block has its extent in `E'`
        simp only [hQ', Option.map_eq_some_iff] at hl
        obtain ⟨c0, hc0, rfl⟩ := hl
        have hm' : m'.heap l = some c0 := by rw [hmQ]; simp [hc0]
        obtain ⟨blk, hb, hlv, hx, he⟩ := Mem.heap_some hm'
        obtain ⟨blk0, hb0, hlo⟩ := Mem.heap_some_lo hm'
        rw [hb] at hb0; cases hb0
        simp only [E', hb]
        rw [if_pos ⟨hlv, by omega, ⟨l.2, by simp [hc0]⟩, hBE⟩, he]

/-- Ghost state can be forgotten from a held resource. -/
theorem Holds.dropGhost {m : Mem} {r rF : Res} {a b : Ghost} (hh : Holds m r rF) (hg : r.gh = a.add b) :
    Holds m ⟨r.heap, r.know, a⟩ rF :=
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, GOk.mono (by rw [← hg]; exact hh.ghost)⟩

/-- A lifted triple whose post's extents are forgotten. -/
theorem FTriple.forgetExt {α : Type} {P : FAssn} {c : MemM α} {Q : α → Assn}
    {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)}
    (ht : FTriple P c (fun v => upPost (Q v) B E)) : FTriple P c (fun v => up (Q v)) := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', ⟨E', ⟨hq, hk, hg⟩, -⟩, hs'⟩ := this
    exact ⟨⟨r'.heap, r'.know, Ghost.unit⟩, hh'.dropGhost (b := Ghost.exts E') (by rw [hg, Ghost.unit_add]),
      ⟨hq, hk, rfl⟩, hs'⟩

/-- **Lifting a size-free legacy triple** of a program that keeps every live block: the legacy
pre- and postcondition under `up`. -/
theorem FTriple.ofTriple_up {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn}
    (ht : Triple P c Q) (hc : Tame c) (hsf : SizeFree (fun _ => none) P)
    (hk : Keeps (fun _ => False) c) : FTriple (up P) c (fun v => up (Q v)) :=
  (FTriple.ofTriple (E := fun _ => none) (B := fun _ => True) ht hc (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ h => by cases h) hsf (.inr (fun m v m' h b blk _ => hk m v m' h b blk id))).forgetExt.pre
    fun _ h => upE_none.mpr h

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

theorem GOk.unit (m : Mem) : GOk m Ghost.unit Ghost.unit :=
  ⟨⟨⟨fun _ => .inl fun _ => rfl, fun _ => by
      simpa [Ghost.add, Ghost.unit] using And.intro ECell.valid_unit (ECell.tagOk_unit _)⟩,
    0, fun _ _ => ⟨rfl, fun _ _ _ => by simp [Ghost.add, Ghost.unit, ECell.add, ECell.unit, Frac.zero, Frac.add] <;> grind,
      fun _ _ _ _ => rfl⟩⟩,
    by simpa using ExtTrue.unit m⟩

/-- The full extents of `E` with the one of `b` split off. -/
theorem Ghost.exts_split {E : BlockId → Option (Nat × BlockKind)} {b : BlockId} {S : Nat}
    {K : BlockKind} (h : E b = some (S, K)) :
    Ghost.exts E = (Ghost.atExt b (ECell.auth1 S K Frac.one)).add
      (Ghost.exts fun x => if x = b then none else E x) := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.atExt, Ghost.exts]
  · funext x
    simp only [Ghost.add, Ghost.atExt, Ghost.exts]
    by_cases hx : x = b
    · subst hx; simp [h]
    · simp [hx]

/-- A legacy assertion with the full extent of one block. -/
theorem up_sep_bext {P : Assn} {b : BlockId} {S : Nat} {K : BlockKind} {r : Res}
    (h : (up P ⋆ bext b S K) r) : upE P (fun x => if x = b then some (S, K) else none) r := by
  obtain ⟨r₁, r₂, -, rfl, ⟨hp, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  refine ⟨by simpa [h2] using hp, by simp [k1, k2, Know.union_none], ?_⟩
  simp only [g1, g2, Ghost.unit_add]
  ext1
  · funext γ; simp [Ghost.atExt, Ghost.exts]
  · funext x; simp only [Ghost.atExt, Ghost.exts]; split <;> simp_all

/-- A lifted post with a byte of block `b` whose extent it owns: the legacy part, the full extent
of `b`, and other extents (no bytes, no knowledge). -/
theorem upPost_bext {Q : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)} {r : Res}
    {b : BlockId} {S : Nat} {K : BlockKind} (h : upPost Q B E r)
    (hc : ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.size = S ∧ fc.cell.kind = K ∧ (B b → (E b).isSome)) :
    ((up Q ⋆ bext b S K) ⋆ fun r => r.heap = FHeap.empty ∧ r.know = Know.none) r := by
  obtain ⟨E', ⟨hq, hk, hg⟩, hcov⟩ := h
  obtain ⟨x, fc, hfc, hs, hkd, hBE⟩ := hc
  have hE : E' b = some (S, K) := by rw [hcov (b, x) fc hfc hBE, hs, hkd]
  refine ⟨⟨r.heap, Know.none, Ghost.atExt b (ECell.auth1 S K Frac.one)⟩,
    ⟨FHeap.empty, Know.none, Ghost.exts fun x => if x = b then none else E' x⟩,
    FHeap.disjoint_empty _, ?_, ⟨⟨r.heap, Know.none, Ghost.unit⟩,
      ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 S K Frac.one)⟩, FHeap.disjoint_empty _,
      by simp [Know.union_none], ⟨hq, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩
  rw [res_eta r, hk, hg, Ghost.exts_split hE]
  simp [Know.union_none]

/-! ## Address disjointness of live blocks (stage 3) -/

/-- **Owned bytes of two different blocks lie at disjoint addresses**: owning byte `x` of `b`
and byte `x'` of `b'` puts byte `x` of `b` before `b'` or byte `x'` of `b'` before `b` (from
ownership and `Mem.LiveDisjoint`, part of `Mem.FSeq`). Taking the last owned byte of each gives
the owned ranges and one past them; whole blocks need their extents (`bext`). -/
theorem Holds.apart {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq)
    {b b' : BlockId} {x x' : Nat} {fc fc' : FCell} (hbb : b ≠ b') (h1 : r.heap (b, x) = some fc)
    (h2 : r.heap (b', x') = some fc') :
    fc.cell.addr + x < fc'.cell.addr ∨ fc'.cell.addr + x' < fc.cell.addr := by
  obtain ⟨blk, hb, hl, hx, -, ha, -⟩ := hh.block h1
  obtain ⟨blk', hb', hl', hx', -, ha', -⟩ := hh.block h2
  have := clearOf_iff.mp (hs.2.2.1 b b' blk blk' hbb hb hb' hl')
  rw [ha, ha']
  rcases this with h | h | h | h | h
  · simp_all
  · omega
  · omega
  · right; omega
  · left; omega

/-- **The `apart` rule**: owning byte `x` of `b` (address `A`) and byte `x'` of `b'` (address
`A'`) gives the fact that they lie apart, each before the other block. -/
theorem FTriple.apart {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {b b' : BlockId}
    {A x A' x' : Nat} (hbb : b ≠ b')
    (hc : ∀ r, P r → (∃ fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A) ∧
      ∃ fc, r.heap (b', x') = some fc ∧ fc.cell.addr = A')
    (ht : FTriple (⟪A + x < A' ∨ A' + x' < A⟫ ⋆ P) c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨⟨fc, h1, rfl⟩, ⟨fc', h2, rfl⟩⟩ := hc r hp
  exact ht m r rF hh (sep_lift.mpr ⟨hh.apart hs hbb h1 h2, hp⟩) hs

end Full
end Zig
