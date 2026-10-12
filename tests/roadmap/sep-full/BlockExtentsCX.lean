import ZigLean.Sep.Full.Toy
import ZigLean.Sep.Full.Extent

/-!
# Why cells no longer carry their block's size (regression, `docs/sep-full-state.md` §Block extents)

The full-state logic first matched a resource's cells exactly, size and mapping start included
(`HoldsCell` below, a copy of the old `Holds`). Then every change of a block's size changes the
cells of every owner of one of its bytes, so the owner of a block cannot grow it in place while
others hold bytes in it (O-G, `docs/alloc-arena.md`: the arena grows its first node through
`page_allocator` while clients hold grants in it). The logic now compares cells without their
size (`Cell.norm`, `FMatch`) and makes a block's extent a resource of its own (`bext`, shares).

What a cell no longer gives, and where it comes from now:

* **The size, beyond the owned bytes.** `cell_size_old`: in the old model a byte whose cell
  records size `2` makes `q + 2` formable. `no_cell_size`: in the new model the same `up`
  precondition holds in a memory whose block has one byte, and the step throws. So a legacy
  assertion that reads a size from a cell lifts only if it is size-free or its block's extent is
  owned (`FTriple.ofTriple`); `cell_size_bext`: with the extent the step is formed. (The
  fixed-buffer allocator's pin byte and the arena's `NodeFacts.fit` read sizes this way.)
* **Ending the block.** `no_free_without_ext`: owning every byte is not enough to `free` a block,
  since the frame may own its extent; `FTriple.free'` takes the extent.
-/

namespace Zig.Full.ExtCX
open FAssn

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
  refine ⟨⟨⟨by decide, by simp [m1]⟩⟩, ⟨by simp [shapes, m1], by simp [shapes, m1]⟩, ?_, fun b blk hb _ => ?_⟩
  · intro b b' blk blk' hne hb hb' _
    simp only [m1] at hb hb'
    rcases b with _ | b <;> rcases b' with _ | b' <;> simp at hb hb' hne
  · simp only [m1] at hb
    rcases b with _ | b <;> simp at hb
    subst hb; simp [blk1]

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

/-- The frame's full extent of block 0. -/
def gF : Ghost := Ghost.atExt 0 (ECell.auth1 1 .heap Frac.one)

theorem gF_ok : GOk m1 Ghost.unit gF := by
  refine ⟨⟨⟨fun γ => by simpa [Ghost.add, gF, Ghost.atExt, Ghost.unit] using (GOk.unit m1).1.1.1 γ,
    fun b => ?_⟩, 0, fun _ _ => ⟨rfl, fun b e k => ?_, fun _ _ _ _ => rfl⟩⟩, fun b => ?_⟩
  · simp only [Ghost.add, Ghost.unit, gF, Ghost.atExt, ECell.unit_add]
    split
    · have := (ECell.dormant_unit (Ghost.ls ⟨fun γ => GCell.unit.add GCell.unit,
        fun b' => if b' = 0 then ECell.auth1 1 .heap Frac.one else ECell.unit⟩)).auth1_ok
        (S := 1) (K := .heap)
      rwa [ECell.add_unit] at this
    · exact ⟨ECell.valid_unit, ECell.tagOk_unit _⟩
  · simp only [Ghost.add, Ghost.unit, gF, Ghost.atExt, ECell.unit_add]
    split <;> exact ⟨rfl, rfl⟩
  · show ECell.TrueIn _ _ _ _
    simp only [Ghost.add, Ghost.unit, gF, Ghost.atExt, ECell.unit_add]
    split
    · rename_i hb; subst hb
      refine ⟨fun S K h => ?_, fun k h => ?_⟩
      · simp only [ECell.auth1] at h
        split at h
        · rename_i e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨blk1, rfl, rfl, rfl, rfl, by decide⟩
        · cases h
      · have := (ECell.dormant_unit _).req_auth1 (by rwa [ECell.add_unit])
        subst this; exact ⟨blk1, rfl, rfl, by decide, by decide⟩
    · exact (ExtTrue.unit m1) b

/-- `m1` holds a resource that owns byte `(0, 0)` with a cell recording size `S`, and a frame
with the ghost state `g` and no bytes. -/
theorem holds1 (S : Nat) (g : Ghost) (hg : GOk m1 Ghost.unit g) :
    Holds m1 ⟨own1 ⟨.int 0, 16, S, .heap⟩, Know.none, Ghost.unit⟩ ⟨FHeap.empty, Know.none, g⟩ := by
  refine ⟨fun _ => .inr rfl, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _, Know.sub_none _, hg⟩
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

/-! ## 1. A cell no longer pins its block's size -/

/-- The old `Holds`: the cells match the memory's live bytes exactly, size included. -/
structure HoldsCell (m : Mem) (r rF : Res) : Prop where
  disj : FHeap.Disjoint r.heap rF.heap
  heap : m.heap = (r.heap ∪ rF.heap).erase

/-- The old triple, over `HoldsCell`. -/
def FTripleCell {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, HoldsCell m r rF → P r → m.FSeq →
    match (c.run m).run with
    | none => True
    | some (.error _) => False
    | some (.ok (v, m')) => ∃ r', HoldsCell m' r' rF ∧ Q v r' ∧ m'.FSeq

/-- **Old model**: a byte whose cell records size `2` makes `q + 2` formable. -/
theorem cell_size_old {A : Nat} {x : Byte} :
    FTripleCell (up (bytesAt q A 2 .heap #[x])) (ptrProject q (·.add 2))
      (fun _ => up (bytesAt q A 2 .heap #[x])) := by
  intro m r rF hh hp hs
  obtain ⟨⟨b, hb, -, hl⟩, -⟩ := id hp
  have hq : q.block = some 0 := rfl
  rw [hq] at hb; cases hb
  have h0 := hl (0, 0)
  simp only [q, show ((0 : Int)).toNat = 0 from rfl] at h0
  have hc : m.heap (0, 0) = some ⟨x, A, 2, .heap⟩ := by
    rw [hh.heap, FHeap.erase_union]; simp only [Heap.union_apply]; simp [h0]
  obtain ⟨blk, hblk, -, _, he⟩ := Mem.heap_some hc
  have hsz : blk.bytes.size = 2 := by have := congrArg Cell.size he; simpa using this.symm
  rw [ptrProject_add_run (inBounds_of rfl hblk (by decide) (by simp [q]))
    (inBounds_of rfl hblk (by simp [q, Ptr.add]) (by simp [q, Ptr.add, hsz]))]
  exact ⟨r, hh, hp, hs⟩

theorem run_project : ((ptrProject q (·.add 2)).run m1).run = some (.error .illegal) := by
  first | rfl | simp [ptrProject, StateT.run, Mem.inBounds, m1, blk1, q, Ptr.add]

/-- **New model**: the same `up` precondition holds in `m1`, whose block has one byte, and `q + 2`
throws `.illegal`: no triple, for any postcondition. -/
theorem no_cell_size (Q : Ptr → FAssn) :
    ¬ FTriple (up (bytesAt q 16 2 .heap #[.int 0])) (ptrProject q (·.add 2)) Q := by
  intro h
  have hx := h m1 _ _ (holds1 2 Ghost.unit (by simpa [gF] using GOk.unit m1)) ⟨own1_bytesAt 2, rfl, rfl⟩ seq1
  rw [run_project] at hx
  exact hx

/-- **New model, with the extent**: the block's full extent gives its size. -/
theorem cell_size_bext {A : Nat} {x : Byte} :
    FTriple (up (bytesAt q A 2 .heap #[x]) ⋆ bext 0 2 .heap) (ptrProject q (·.add 2))
      (fun _ => up (bytesAt q A 2 .heap #[x]) ⋆ bext 0 2 .heap) := by
  refine FTriple.of_run fun m r rF hh hp hs => ?_
  have hE := up_sep_bext hp
  have hauth : 0 < ((r.gh.add rF.gh).extent 0).auth (2, .heap) := by
    rw [hE.2.2]; simp [Ghost.add, ECell.add, Ghost.exts, ECell.auth1]; omega
  obtain ⟨blk, hblk, -, hsz, -, -⟩ := (hh.ghost.2 0).1 2 .heap hauth
  exact ⟨_, m, r, ptrProject_add_run (inBounds_of rfl hblk (by decide) (by simp [q]))
    (inBounds_of rfl hblk (by simp [q, Ptr.add]) (by simp [q, Ptr.add, hsz])), hh, hp, hs⟩

/-! ## 2. Owning every byte no longer ends a block -/

theorem run_free : ∃ m', ((free q).run m1).run = some (.ok ((), m')) ∧
    m'.blocks[0]? = some { blk1 with live := false } := by
  have hr : m1.freeRaces 0 1 = false := freeRaces_of_singleThread seq1.1.single 0 1
  exact ⟨_, by simp [free, q, m1, blk1] at hr ⊢; simp [hr]; rfl, rfl⟩

/-- **New model**: the frame owns the block's full extent; `free` ends the block, so no resource
holds the memory after it with that frame. `FTriple.free'` takes the extent. -/
theorem no_free_without_ext (Q : Unit → FAssn) :
    ¬ FTriple (up (bytesAt q 16 1 .heap #[.int 0])) (free q) Q := by
  intro h
  have hx := h m1 _ _ (holds1 1 gF gF_ok) ⟨own1_bytesAt 1, rfl, rfl⟩ seq1
  obtain ⟨m', hr, hb⟩ := run_free
  rw [hr] at hx
  obtain ⟨r', hh, -, -⟩ := hx
  have hauth : 0 < ((r'.gh.add gF).extent 0).auth (1, .heap) := by
    simp [Ghost.add, ECell.add, gF, Ghost.atExt, ECell.auth1]
  obtain ⟨blk, hblk, hlive, -⟩ := (hh.ghost.2 0).1 1 .heap hauth
  rw [hb] at hblk; cases hblk
  simp at hlive

end Zig.Full.ExtCX

-- `ci.yml` (Full-state separation logic) requires only the standard axioms.
#print axioms Zig.Full.ExtCX.cell_size_old
#print axioms Zig.Full.ExtCX.no_cell_size
#print axioms Zig.Full.ExtCX.cell_size_bext
#print axioms Zig.Full.ExtCX.no_free_without_ext
-- The extent updates (`ZigLean/Sep/Full/Extent.lean`): lend, give back, join at the higher
-- bound, weaken, and the fact a share gives.
#print axioms Zig.Full.EUpd.lend
#print axioms Zig.Full.EUpd.unlend
#print axioms Zig.Full.EUpd.join
#print axioms Zig.Full.EUpd.weaken
#print axioms Zig.Full.bshare_split
#print axioms Zig.Full.Holds.bshare
-- Epoch-tagged shares (`docs/sep-full-state.md` §Epoch-tagged shares): lend a tagged share with
-- a receipt, give it back during its epoch, revoke a past epoch's share, the fact a tagged share
-- gives, the ledger updates that read the tags (new ledger, next epoch), the full extent leaving
-- only dormant claims, and the legacy bridge.
#print axioms Zig.Full.EUpd.lendT
#print axioms Zig.Full.EUpd.returnT
#print axioms Zig.Full.EUpd.revoke
#print axioms Zig.Full.Upd.alloc
#print axioms Zig.Full.Upd.bump
#print axioms Zig.Full.full_excl
#print axioms Zig.Full.FTriple.ofTriple
