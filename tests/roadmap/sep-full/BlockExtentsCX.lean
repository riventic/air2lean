import ZigLean.Sep.Full.Triple
import ZigLean.Sep.Full.Toy

/-!
# Block extents: what the legacy lift loses (phase-2 obstruction, `docs/sep-full-state.md` §Block extents)

Kernel-checked against a copy of the approved `Holds` (not in `ZigLean/Sep/Full` yet).

`HoldsN` is the block-extent `Holds` of `docs/sep-full-state.md` §Block extents: cells are
compared after normalization (`Cell.norm`: size 0, `.mapped lo` as `.mapped 0`), and a resource
has an exclusive extent component `ext`, exact in the memory (live, size, kind).

* `cell_size_triple` / `no_cell_size_triple`: in today's model, a byte's cell pins its block's
  size, so `ptrProject` one past a size that only a cell records is formed. Under `HoldsN` the
  same lifted precondition holds in a memory whose block is shorter, and the step throws. This is
  `FBA.own`'s pin byte (`buffer.ptr + end_index` with `end_index = cap` and the pin before the
  buffer) and the arena's `NodeFacts.fit` (`buf + end_index` of a full node).
* `free_triple_today` / `no_free_without_ext`: in today's model, owning every byte of a block is
  enough to end it. Under `HoldsN` the frame may own the block's extent, so no lift of a step
  that ends or resizes a block exists without `bext` in its precondition. This is
  `PageSpec.free_spec`/`resize_spec`/`remap_spec` (munmap/mremap), whose tokens are `up`
  (`inv_legacy : LegacyTokens (inv own) legacy own`), so they cannot carry `bext`.
-/

namespace Zig.Full.ExtCX
open FAssn

def BlockKind.norm : BlockKind → BlockKind
  | .mapped _ => .mapped 0
  | k => k

def Cell.norm (c : Cell) : Cell := { c with size := 0, kind := BlockKind.norm c.kind }

abbrev Ext := BlockId → Option (Nat × BlockKind)

structure XRes where
  res : Res
  ext : Ext

def ExtExact (m : Mem) (e : Ext) : Prop :=
  ∀ b S K, e b = some (S, K) → ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧
    blk.bytes.size = S ∧ blk.kind = K

/-- The approved `Holds` (normalized cells, exclusive exact extents). -/
structure HoldsN (m : Mem) (r rF : XRes) : Prop where
  disj : FHeap.Disjoint r.res.heap rF.res.heap
  heap : ∀ l, (m.heap l).map Cell.norm = ((r.res.heap ∪ rF.res.heap) l).map (Cell.norm ∘ FCell.cell)
  tags : ∀ l fc, (r.res.heap ∪ rF.res.heap) l = some fc → TagSat (shapes m) l.1 l.2 fc.atom
  extDisj : ∀ b, r.ext b = none ∨ rF.ext b = none
  ext : ExtExact m r.ext
  extF : ExtExact m rF.ext
  know : Know.Sub r.res.know m.kn
  knowF : Know.Sub rF.res.know m.kn
  ghost : Ghost.Ok r.res.gh rF.res.gh

abbrev XAssn := XRes → Prop

/-- A legacy assertion: its bytes (any tags), no knowledge, no ghost state, no extents. -/
def upX (P : Assn) : XAssn := fun r => up P r.res ∧ r.ext = fun _ => none

def FTripleN {α : Type} (P : XAssn) (c : MemM α) (Q : α → XAssn) : Prop :=
  ∀ m r rF, HoldsN m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ r', HoldsN m' r' rF ∧ Q v r' ∧ m'.FSeq

/-! ## The memory: one live 1-byte heap block at address 16 -/

def blk1 : Block := { bytes := #[.int 0], align := 1, kind := .heap, live := true, addr := 16 }
def m1 : Mem := { blocks := #[blk1] }
def q : Ptr := ⟨some 0, 0⟩

theorem m1_heap (l : Loc) :
    m1.heap l = if l = (0, 0) then some ⟨.int 0, 16, 1, .heap⟩ else none := by
  obtain ⟨b, o⟩ := l
  simp only [Mem.heap, m1, blk1]
  rcases b with _ | b
  · rcases o with _ | o <;> simp [BlockKind.mappedLo]
  · simp

theorem seq1 : m1.FSeq := by
  refine ⟨⟨⟨by decide, by simp [m1]⟩⟩, ⟨by simp [shapes, m1], by simp [shapes, m1]⟩, ?_⟩
  intro b b' blk blk' hne hb hb' _
  simp only [m1] at hb hb'
  rcases b with _ | b <;> rcases b' with _ | b' <;> simp at hb hb' hne

theorem ok_unit : Ghost.Ok Ghost.unit Ghost.unit :=
  ⟨fun _ => .inl fun _ => rfl, 0, fun _ _ => rfl⟩

/-- A resource owning byte `(0, 0)` with the cell `c`. -/
def own1 (c : Cell) : FHeap := fun l => if l = (0, 0) then some ⟨c, none⟩ else none

theorem own1_bytesAt (S : Nat) :
    bytesAt q 16 S .heap #[.int 0] (own1 ⟨.int 0, 16, S, .heap⟩).erase := by
  refine ⟨0, rfl, by decide, fun l => ?_⟩
  obtain ⟨b, o⟩ := l
  simp only [FHeap.erase, own1, q]
  by_cases h : (b, o) = ((0 : Nat), (0 : Nat))
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    simp only [Prod.mk.injEq, not_and] at h
    by_cases hb : b = 0
    · subst hb; have : o ≠ 0 := h rfl; simp; omega
    · simp [hb]

/-- `m1` holds a resource that owns byte `(0, 0)` with a cell recording size `S`, and the frame
`rF`, which owns no bytes. -/
theorem holds1 (S : Nat) (eF : Ext) (heF : ExtExact m1 eF) :
    HoldsN m1 ⟨⟨own1 ⟨.int 0, 16, S, .heap⟩, Know.none, Ghost.unit⟩, fun _ => none⟩
      ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, eF⟩ := by
  refine ⟨fun _ => .inr rfl, fun l => ?_, fun l fc hfc => ?_, fun _ => .inl rfl,
    fun _ _ _ h => (by cases h), heF, Know.sub_none _, Know.sub_none _, (by simpa using ok_unit)⟩
  · rw [m1_heap]
    by_cases h : l = (0, 0)
    · simp [h, own1, Cell.norm, BlockKind.norm]
    · simp [h, own1, FHeap.empty]
  · have : fc.atom = none := by
      simp only [FHeap.union_apply, FHeap.empty, Option.or_none, own1] at hfc
      split at hfc
      · cases hfc; rfl
      · cases hfc
    simp [TagSat, this]

/-! ## 1. A cell no longer pins its block's size (FBA's pin byte, the arena's `NodeFacts.fit`) -/

/-- **Today**: a byte whose cell records size `2` makes `q + 2` formable (the cell is the block's,
size included). -/
theorem cell_size_triple {A : Nat} {x : Byte} :
    FTriple (up (bytesAt q A 2 .heap #[x])) (ptrProject q (·.add 2))
      (fun p => ⟪p = q.add 2⟫ ⋆ up (bytesAt q A 2 .heap #[x])) := by
  refine FTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨⟨b, hb, -, hl⟩, -⟩ := id hp
  have hq : q.block = some 0 := rfl
  rw [hq] at hb; cases hb
  have h0 := hl (0, 0)
  simp only [q, show ((0 : Int)).toNat = 0 from rfl] at h0
  have hc : r.heap.erase (0, 0) = some ⟨x, A, 2, .heap⟩ := by simpa using h0
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, hcell⟩ := hc
  obtain ⟨blk, hblk, -, -, -, hsz⟩ := hh.block hfc
  have hsz2 : blk.bytes.size = 2 := by rw [← hsz, hcell]
  exact ⟨_, m, r, ptrProject_add_run (inBounds_of rfl hblk (by decide) (by simp [q]))
    (inBounds_of rfl hblk (by simp [q, Ptr.add]) (by simp [q, Ptr.add, hsz2])),
    hh, sep_lift.mpr ⟨rfl, ⟨⟨0, rfl, by decide, hl⟩, hp.2⟩⟩, hs⟩

theorem run_project : ((ptrProject q (·.add 2)).run m1).run = some (.error .illegal) := by
  first | rfl | simp [ptrProject, StateT.run, Mem.inBounds, m1, blk1, q, Ptr.add]

/-- **Approved model**: the same lifted precondition holds in `m1`, whose block has 1 byte, and
`q + 2` throws `.illegal`. So no lift of `cell_size_triple` exists, for any postcondition. -/
theorem no_cell_size_triple (Q : Ptr → XAssn) :
    ¬ FTripleN (upX (bytesAt q 16 2 .heap #[.int 0])) (ptrProject q (·.add 2)) Q := by
  intro h
  have hx := h m1 _ _ (holds1 2 (fun _ => none) fun _ _ _ e => by cases e)
    ⟨⟨own1_bytesAt 2, rfl, rfl⟩, rfl⟩ seq1
  rw [run_project] at hx
  exact hx

/-! ## 2. Owning every byte no longer ends a block (PageSpec's munmap/mremap through `up` tokens) -/

/-- **Today**: owning every byte of a block is enough to free it (`FTriple.free'`). -/
theorem free_triple_today {A : Nat} {x : Byte} :
    FTriple (up (bytesAt q A 1 .heap #[x])) (free q) (fun _ => emp) :=
  FTriple.free' rfl rfl (by decide)

theorem run_free : ∃ m', ((free q).run m1).run = some (.ok ((), m')) ∧
    m'.blocks[0]? = some { blk1 with live := false } :=
  ⟨_, rfl, rfl⟩

/-- **Approved model**: the frame owns the block's extent `bext 0 1 .heap`; `free` ends the block,
so no resource holds `m'` with that frame. No lift of `free_triple_today` exists. -/
theorem no_free_without_ext (Q : Unit → XAssn) :
    ¬ FTripleN (upX (bytesAt q 16 1 .heap #[.int 0])) (free q) Q := by
  intro h
  let eF : Ext := fun b => if b = 0 then some (1, .heap) else none
  have heF : ExtExact m1 eF := by
    intro b S K e
    by_cases hb : b = 0
    · subst hb; simp only [eF, if_pos rfl, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨blk1, rfl, rfl, rfl, rfl⟩
    · simp [eF, hb] at e
  have hx := h m1 _ _ (holds1 1 eF heF) ⟨⟨own1_bytesAt 1, rfl, rfl⟩, rfl⟩ seq1
  obtain ⟨m', hr, hb⟩ := run_free
  rw [hr] at hx
  obtain ⟨r', hh, -, -⟩ := hx
  obtain ⟨blk, hblk, hlive, -, -⟩ := hh.extF 0 1 .heap (by simp [eF])
  rw [hb] at hblk; cases hblk
  simp at hlive

end Zig.Full.ExtCX

#print axioms Zig.Full.ExtCX.cell_size_triple
#print axioms Zig.Full.ExtCX.no_cell_size_triple
#print axioms Zig.Full.ExtCX.free_triple_today
#print axioms Zig.Full.ExtCX.no_free_without_ext
