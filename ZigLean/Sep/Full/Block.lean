import ZigLean.Sep.Full.Toy
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Mem.AllocLemmas

/-!
# Blocks in the full-state logic (`docs/proof-framework.md`, library `Full/Block`)

Step rules for `fsym` about making and ending blocks:

* `FTotalTriple.free`: `free` of a whole block (its bytes and its full extent `bext`) returns and
  leaves nothing (total).
* `FTriple.alloc`, `FTriple.allocStack`: a new block of `size > 0` bytes: its bytes (undefined),
  its full extent and an aligned address. These are partial: `alloc` throws `.stackOverflow`
  when the address space has no room (`Mem.roomFor`, premise STK-01), which a partial triple
  counts as no result. A total rule needs the room as a resource of the precondition: that
  resource does not exist yet (docs/proof-framework.md: "stack room").
-/

namespace Zig
namespace Full

open FAssn

/-- `free` returns from every memory that holds a whole block with its full extent. -/
theorem FReturns.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FReturns (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) := by
  intro m r rF hh hp hs
  have hcells : ∀ h, bytesAt p A S K bs h → ∀ l c, h l = some c → l.1 = b ∧ c.size = S ∧ c.kind = K := by
    intro h hb l c hc
    obtain ⟨b', hb', -, hl⟩ := hb
    rw [hpb] at hb'; cases hb'
    rw [hl l] at hc
    split at hc
    · rename_i hin; cases hc; exact ⟨hin.1, rfl, rfl⟩
    · cases hc
  have hP := upE_fix (E := fun x => if x = b then some (S, K) else none)
    (SizeFree.of_pinned fun h hp l c hc => by simp [(hcells h hp l c hc).1])
    (fun h hp l c S' K' hc hE => by
      obtain ⟨e, hs', hk⟩ := hcells h hp l c hc
      simp only [e, ite_true, Option.some.injEq, Prod.mk.injEq] at hE
      exact ⟨hE.1 ▸ hs', hE.2 ▸ hk⟩) hh (up_sep_bext hp)
  obtain ⟨m', hr, -⟩ := free_run hP (hh.fix.heap_exact hh.fix_exact hh.fix_exactF)
    (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj)) hS h0 hpos hs.1 hK
  exact ⟨(), m', hr⟩

/-- **`free` of a whole block** (total): its bytes and its full extent go. A `const` global is
never freed (`free` of one is illegal). -/
@[fsym] theorem FTotalTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => emp) :=
  ⟨FTriple.free' hpb hS h0 hpos hK, FReturns.free hpb hS h0 hpos hK⟩

/-- **`alloc` of `size > 0` bytes** (partial: no room is a stack overflow): the bytes, the full
extent of the new block and an aligned address. -/
@[fsym] theorem FTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align)
    (hpos : 0 < size) (hk : kind.mappedLo = 0) :
    FTriple emp (Zig.alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) :=
  FTriple.alloc' kind size align ha hpos hk

/-- **The stack block of an escaping local** (`allocStack`, partial as `FTriple.alloc`). -/
@[fsym] theorem FTriple.allocStack (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple emp (Zig.allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ bext b size .stack)) :=
  FTriple.alloc .stack size align ha hpos rfl

/-! ## Heap blocks: `rawAlloc` and `poisonFree` (`ZigLean/Mem/Alloc.lean`) -/

/-- A step that runs as `c'` from a memory `m'` that holds the same resources (for example the
memory after a bookkeeping step that changes no block) has the triple of `c'`. -/
theorem FTotalTriple.of_runEq {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (h : ∀ m r rF, Holds m r rF → P r → m.FSeq →
      ∃ (c' : MemM α) (m' : Mem), c.run m = c'.run m' ∧ Holds m' r rF ∧ m'.FSeq ∧ FTotalTriple P c' Q) :
    FTotalTriple P c Q := by
  refine ⟨fun m r rF hh hp hs => ?_, fun m r rF hh hp hs => ?_⟩ <;>
    obtain ⟨c', m', e, hh', hs', ht⟩ := h m r rF hh hp hs <;> rw [e]
  · exact ht.1 m' r rF hh' hp hs'
  · exact ht.2 m' r rF hh' hp hs'

/-- What `rawAlloc n align` returns: `null` and nothing, or a new heap block of `n` undefined
bytes with its full extent at an `align`-aligned address. -/
def rawAllocPost (n align : Nat) : Option Ptr → FAssn
  | none => emp
  | some p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A n .heap (Array.replicate n .undef)) ⋆ bext b n .heap)

/-- The memory after the attempt count of `rawAlloc` holds what the memory held. -/
theorem allocs_holds {m : Mem} {r rF : Res} (hh : Holds m r rF) (hs : m.FSeq) :
    Holds { m with allocs := m.allocs + 1 } r rF ∧ ({ m with allocs := m.allocs + 1 } : Mem).FSeq :=
  ⟨Holds.congrMem (m := m) rfl rfl hh, ⟨⟨hs.1.single⟩, hs.2.1, hs.2.2⟩⟩

/-- **`rawAlloc` of `n > 0` bytes** (total, for every failure policy): `null` and nothing (the
failure decision, or no room in the address space), or a new heap block. -/
@[fsym] theorem FTotalTriple.rawAlloc (n align : Nat) (ha : 0 < align) (hpos : 0 < n) :
    FTotalTriple emp (Zig.rawAlloc n align) (rawAllocPost n align) := by
  classical
  refine FTotalTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨hh₁, hs₁⟩ := allocs_holds hh hs
  rw [rawAlloc_eq]
  by_cases hdn : m.allocDenied n
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte], hh₁, hp, hs₁⟩
  cases hroom : m.roomFor n align
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte]; rfl, hh₁, hp, hs₁⟩
  have hrun := alloc_run_eq { m with allocs := m.allocs + 1 } (kind := .heap)
    (by simpa using hroom)
  have ht := FTriple.alloc .heap n align ha hpos rfl _ r rF hh₁ hp hs₁
  rw [hrun] at ht
  obtain ⟨r', hh', hq, hs'⟩ := ht
  exact ⟨some _, _, r', by simp [hdn, hrun], hh', hq, hs'⟩

/-- **`rawAlloc` of no bytes** (total): `null`, or a pointer to offset 0 of a new block without
bytes, which nothing can own. -/
theorem FTotalTriple.rawAllocZero (align : Nat) (ha : 0 < align) :
    FTotalTriple emp (Zig.rawAlloc 0 align)
      (fun q => ⟪∀ p, q = some p → p.block.isSome ∧ p.off = 0⟫) := by
  classical
  refine FTotalTriple.of_run fun m r rF hh hp hs => ?_
  obtain ⟨hh₁, hs₁⟩ := allocs_holds hh hs
  rw [rawAlloc_eq]
  by_cases hdn : m.allocDenied 0
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte], hh₁, ⟨by simp, hp⟩, hs₁⟩
  cases hroom : m.roomFor 0 align
  · exact ⟨none, _, r, by simp only [hdn, ↓reduceIte]; rfl, hh₁, ⟨by simp, hp⟩, hs₁⟩
  have hrun := alloc_run_eq { m with allocs := m.allocs + 1 } (kind := .heap)
    (by simpa using hroom)
  have ht := FTriple.allocZero .heap align ha rfl _ r rF hh₁ hp hs₁
  rw [hrun] at ht
  obtain ⟨r', hh', hq, hs'⟩ := ht
  exact ⟨some ⟨some m.blocks.size, 0⟩, _, r', by simp [hdn, hrun], hh',
    ⟨fun p e => by cases e; exact hq.1, hq.2⟩, hs'⟩

/-- **`poisonFree` of a whole heap block** (total): the poison write and the free. Its bytes and
its full extent go. -/
@[fsym] theorem FTotalTriple.poisonFree {p : Ptr} {A S : Nat} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) :
    FTotalTriple (up (bytesAt p A S .heap bs) ⋆ bext b S .heap) (Zig.poisonFree p S)
      (fun _ => emp) := by
  refine FTotalTriple.of_runEq fun m r rF hh hp hs => ?_
  obtain ⟨blk, hb, hl, hsz, hK, hlo⟩ := hh.bauth (sep_comm hp)
  simp only [BlockKind.mappedLo] at hlo
  have hacc : m.access p S 1 = pure (b, blk, 0) := by
    simp [Mem.access, hpb, hb, hl, h0, hsz, hK, BlockKind.mappedLo, Nat.mod_one]
  let m₂ := m.recordAt b 0 S .write
  have hacc₂ : m₂.access p S 1 = pure (b, blk, 0) := hacc
  refine ⟨Zig.free p, m₂, ?_, Holds.congrMem (m := m) rfl rfl hh,
    ⟨⟨singleThread_recordAt hs.1.single _ _ _ _⟩, hs.2.1, hs.2.2⟩,
    FTotalTriple.free hpb hS h0 hlo (by decide)⟩
  have e1 : (Zig.poisonFree p S).run m = (recordAccess b 0 S .write >>= fun _ => rawFree p S).run m := by
    simp [Zig.poisonFree, zig_unfold, hacc, hK, hsz, get, getThe, MonadStateOf.get, StateT.get]
  have e2 : (rawFree p S).run m₂ = (Zig.free p).run m₂ := by
    simp [rawFree, zig_unfold, hacc₂, hK, hsz, get, getThe, MonadStateOf.get, StateT.get]
  rw [e1, StateT.run_bind, recordAccess_run (noRace_of_singleThread hs.1.single _ _ _ _)]
  exact e2

end Full
end Zig
