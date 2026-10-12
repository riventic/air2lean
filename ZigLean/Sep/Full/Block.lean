import ZigLean.Sep.Full.Claims
import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Ops
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.ThreadStep
import ZigLean.Mem.AllocLemmas

/-!
# Blocks in the full-state logic (`docs/proof-framework.md`, library `Full/Block`)

Step rules for `fsym` about making and ending blocks:

* `FTotalTriple.free`: `free` of a whole block (its bytes and its full extent `bext`) returns and
  leaves nothing (total).
* `FTriple.alloc`, `FTriple.allocStack`: a new block of `size > 0` bytes: its bytes (undefined),
  its full extent and an aligned address. These are partial: `alloc` throws `.stackOverflow`
  when there is no room (`Mem.allocOk`: the address space, and for a stack block of a thread
  with a budget its reserve; premise STK-01), which a partial triple counts as no result. A
  total rule needs the room as a resource of the precondition: that resource does not exist yet
  (docs/proof-framework.md: "stack room").

The rules are proved on `Holds` directly (no legacy lifting): `Holds.alloc` (the memory after a
new block holds its bytes and full extent, `newBlockRes`, with the same frame) and `Holds.free`
(the memory with a block ended holds nothing more, from its bytes and full extent). Each rule
is also a thread rule (`FTTriple.alloc`, `FTTriple.allocZero`, `FTTotalTriple.free`): the
sequential triple and the step's locality (`ZigLean/Sep/Full/ThreadStep.lean`).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Making a block (native) -/

/-- The live bytes after `alloc`: the new block's undefined bytes, and the old ones. -/
theorem afterAlloc_heap (m : Mem) (kind : BlockKind) (size align : Nat) (l : Loc) :
    (m.afterAlloc kind size align).heap l =
      if l.1 = m.blocks.size ∧ l.2 < size ∧ kind.mappedLo ≤ l.2 then
        some ⟨.undef, m.allocAddr kind size align, size, kind⟩
      else m.heap l := by
  obtain ⟨x, y⟩ := l
  by_cases hx : x = m.blocks.size
  · subst hx
    have hn : m.heap (m.blocks.size, y) = none := by simp [Mem.heap]
    rw [hn]
    simp only [Mem.heap, Mem.afterAlloc, Array.getElem?_push_size, true_and, Array.size_replicate]
    by_cases hc : y < size ∧ kind.mappedLo ≤ y
    · rw [dite_eq_left hc, ite_eq_left hc]; simp
    · rw [dite_eq_right hc, ite_eq_right hc]
  · simp only [Mem.heap, Mem.afterAlloc, Array.getElem?_push, hx, ↓reduceIte, false_and]

/-- The resource of a new block `b`: its `size` undefined bytes at address `A`, and its full
extent. -/
def newBlockRes (b : BlockId) (A size : Nat) (kind : BlockKind) : Res :=
  ⟨fun l => if l.1 = b ∧ l.2 < size then some ⟨⟨.undef, A, size, kind⟩, none⟩ else none,
    Know.none, Ghost.exts (extOne b size kind)⟩

/-- **A new block** (`alloc` of `size > 0` bytes, kind without a mapping start): the memory after
it holds the new block's bytes and full extent (`newBlockRes`) with the same frame. The frame has
no byte of the block and no claim on it: it did not exist. -/
theorem Holds.alloc {m : Mem} {r rF : Res} (hh : Holds m r rF) (hr : emp r) {kind : BlockKind}
    {size align : Nat} (hpos : 0 < size) (hk : kind.mappedLo = 0) :
    Holds (m.afterAlloc kind size align)
      (newBlockRes m.blocks.size (m.allocAddr kind size align) size kind) rF := by
  obtain ⟨hr0, -, hrg⟩ := hr
  obtain ⟨b, hbe⟩ : ∃ b, b = m.blocks.size := ⟨_, rfl⟩
  rw [← hbe]
  let nb : Block :=
    { bytes := Array.replicate size .undef, align, kind, live := true,
      addr := m.allocAddr kind size align }
  have hget : ∀ x, (m.afterAlloc kind size align).blocks[x]? =
      if x = b then some nb else m.blocks[x]? := fun x => by
    simp only [Mem.afterAlloc, Array.getElem?_push]; by_cases hx : x = b <;> simp [hx, hbe, nb]
  have hnone : m.blocks[b]? = none := by simp [hbe]
  -- the frame's bytes and claims are on old blocks
  have hFb : ∀ l fc, rF.heap l = some fc → l.1 ≠ b := fun l fc hl e => by
    obtain ⟨blk, hb, -⟩ := hh.swap.block (b := l.1) (x := l.2) hl
    rw [e, hnone] at hb; cases hb
  have hok : Ghost.Ok (Ghost.exts fun _ => none) rF.gh := by
    rw [Ghost.exts_none, ← hrg]; exact hh.ghost.1
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have hv := hok.1.2.1 b
    rw [show ((Ghost.exts fun _ => none).add rF.gh).extent b = rF.gh.extent b by simp,
      Ghost.ls_exts_add] at hv
    refine ECell.dormant_of_not_claims (fun hc => ?_) hv.2.2
    have ht := hh.ghost.2.1 b
    rw [hrg, Ghost.unit_add] at ht
    rcases hc with ⟨S, K, h⟩ | ⟨k, h⟩
    · obtain ⟨blk, hb, -⟩ := ht.1 S K h; rw [hnone] at hb; cases hb
    · obtain ⟨blk, hb, -⟩ := ht.2 k h; rw [hnone] at hb; cases hb
  refine ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _,
    hh.knowF.trans (KMono.push rfl), ⟨Ghost.ok_exts_change hok fun x hx => ?_, fun x => ?_, ?_⟩⟩
  · -- disjoint: the frame has no byte of `b`
    by_cases hc : l.1 = b ∧ l.2 < size
    · right
      cases e : rF.heap l with
      | none => rfl
      | some fc => exact absurd hc.1 (hFb l fc e)
    · left; simp only [newBlockRes]; rw [ite_eq_right hc]
  · -- the cells up to `Cell.norm`
    rw [afterAlloc_heap, ← hbe]
    simp only [FHeap.union_apply, newBlockRes, hk, Nat.zero_le, and_true]
    by_cases hc : l.1 = b ∧ l.2 < size
    · rw [ite_eq_left hc, ite_eq_left hc]
      cases e : rF.heap l with
      | none => rfl
      | some fc => exact absurd hc.1 (hFb l fc e)
    · rw [ite_eq_right hc, ite_eq_right hc, Option.none_or]
      have := hh.heap.1 l
      rwa [FHeap.union_apply, hr0, FHeap.empty, Option.none_or] at this
  · -- tags: the new cells have none, the frame's are as before
    simp only [FHeap.union_apply, newBlockRes] at hfc
    split at hfc
    · cases hfc; trivial
    · exact hh.tagF (by simpa using hfc)
  · -- the frame has no claim on the new block
    have : x = b := Classical.byContradiction fun hne => by simp [extOne, hne] at hx
    subst this; exact hdorm
  · -- the extent claims hold in the new memory
    show ECell.TrueIn _ _ _ _
    simp only [newBlockRes]
    rw [Ghost.ls_exts_add]
    have ht := hh.ghost.2.1 x
    rw [hrg, Ghost.unit_add] at ht
    by_cases hx : x = b
    · rw [hx]
      rw [show ((Ghost.exts (extOne b size kind)).add rF.gh).extent b =
        (ECell.auth1 size kind Frac.one).add (rF.gh.extent b) by simp [Ghost.add, Ghost.exts, extOne]]
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · simp only [ECell.add, hdorm.1, Nat.add_zero, ECell.auth1] at hp'
        split at hp'
        · rename_i he; simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          exact ⟨_, by rw [hget, ite_eq_left rfl], rfl, by simp [nb], rfl, by rw [hk]; exact hpos⟩
        · cases hp'
      · rw [hdorm.req_auth1 hk']
        exact ⟨_, by rw [hget, ite_eq_left rfl], rfl, by simp [nb], by simp [nb, hk, hpos]⟩
    · rw [show ((Ghost.exts (extOne b size kind)).add rF.gh).extent x = rF.gh.extent x by
        simp [Ghost.add, Ghost.exts, extOne, hx]]
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · obtain ⟨blk, hb, rest⟩ := ht.1 S' K' hp'
        exact ⟨blk, by rw [hget, ite_eq_right hx]; exact hb, rest⟩
      · obtain ⟨blk, hb, rest⟩ := ht.2 k hk'
        exact ⟨blk, by rw [hget, ite_eq_right hx]; exact hb, rest⟩
  · -- no byte claim on a block not yet made
    have hc := ClFresh.frame (hrg ▸ hh.ghost.2.2 : ClFresh m (Ghost.unit.add rF.gh))
    exact (hc.mono (by simp [Mem.afterAlloc])).congr (Ghost.exts_add_cl _ _)

/-- `alloc` of `size > 0` bytes: the bytes and the new block's full extent. -/
theorem FTriple.alloc' (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) := by
  intro m r rF hh hp hs
  cases hroom : m.allocOk kind size align
  · rw [alloc_run_noRoom m hroom]
  rw [alloc_run_eq m hroom]
  refine ⟨_, hh.alloc hp hpos hk, ⟨m.allocAddr kind size align, m.blocks.size,
    sep_lift.mpr ⟨⟨rfl, rfl, m.allocAddr_mod kind size align ha⟩, ?_⟩⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩
  refine ⟨⟨(newBlockRes m.blocks.size (m.allocAddr kind size align) size kind).heap, Know.none,
      Ghost.unit⟩,
    ⟨FHeap.empty, Know.none, Ghost.atExt m.blocks.size (ECell.auth1 size kind Frac.one)⟩,
    FHeap.disjoint_empty _, ?_, ⟨⟨m.blocks.size, rfl, by simp, fun l => ?_⟩, rfl, rfl⟩,
    rfl, rfl, rfl⟩
  · simp only [newBlockRes, FHeap.union_empty, Know.union_none, Ghost.unit_add, Ghost.exts_extOne]
  · simp only [FHeap.erase, newBlockRes, Int.toNat_zero, Nat.zero_le, true_and, Nat.zero_add,
      Array.size_replicate, Nat.sub_zero]
    split
    · rename_i hc; simp [hc.2]
    · rfl

/-- After `alloc` of no bytes the memory holds what it held: the new block has no live byte. -/
theorem Holds.allocZero {m : Mem} {r rF : Res} (hh : Holds m r rF) (kind : BlockKind) (align : Nat) :
    Holds (m.afterAlloc kind 0 align) r rF := by
  have e : (m.afterAlloc kind 0 align).heap = m.heap := funext fun l => by
    rw [afterAlloc_heap]; exact ite_eq_right fun h => absurd h.2.1 (Nat.not_lt_zero _)
  exact ⟨hh.disj, ⟨fun l => by rw [e]; exact hh.heap.1 l, fun l fc h => hh.heap.2 l fc h⟩,
    hh.know.trans (KMono.push rfl), hh.knowF.trans (KMono.push rfl),
    hh.ghost.keep (KeepsExt.push rfl) (by simp [Mem.afterAlloc])⟩

/-- `alloc` of no bytes: a pointer to offset 0 of a new block. The block has no byte, so there is
nothing to own (an extent needs a live byte: `Holds.bauth`). -/
theorem FTriple.allocZero (kind : BlockKind) (align : Nat) :
    FTriple emp (alloc kind 0 align) (fun p => ⟪p.block.isSome ∧ p.off = 0⟫) := by
  intro m r rF hh hp hs
  cases hroom : m.allocOk kind 0 align
  · rw [alloc_run_noRoom m hroom]
  rw [alloc_run_eq m hroom]
  exact ⟨r, hh.allocZero kind align, ⟨⟨rfl, rfl⟩, hp⟩,
    ⟨⟨hs.1.single⟩, hs.2.1, LDMono.alloc hroom rfl (by simp) rfl hs.2.2⟩⟩

/-- A run of `alloc` creates the block it returns. -/
theorem alloc_fresh {kind : BlockKind} {size align : Nat} {m m' : Mem} {p : Ptr} {b : BlockId}
    (h : ((alloc kind size align).run m).run = some (.ok (p, m'))) (hb : p.block = some b) :
    m.blocks.size ≤ b ∧ b < m'.blocks.size := by
  unfold alloc at h
  obtain ⟨_, m₁, h1, h2⟩ := Conc.Proto.MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.get_ok h1
  split at h2
  · obtain ⟨_, m₂, h3, h4⟩ := Conc.Proto.MemM.bind_ok h2
    have e := Conc.Proto.MemM.set_ok h3
    obtain ⟨rfl, rfl⟩ := Conc.Proto.MemM.pure_ok h4
    subst e
    cases hb
    simp [Mem.afterAlloc]
  · exact (Conc.Proto.MemM.throw_ok h2).elim

/-- **`alloc` with the claim on the new block's bytes** (`FTriple.mintClaimOpt`): the bytes, the
full extent and the exclusive claim on `[0, size)`. -/
theorem FTriple.allocC (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTriple emp (alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ (bext b size kind ⋆ bclaim b 0 size))) := by
  refine (FTriple.mintClaimOpt (fun p => p.block) (fun _ => 0) (fun _ => size)
    (FTriple.alloc' kind size align ha hpos hk) (fun m v m' b h e => alloc_fresh h e)
    fun _ b r _ hq => noCl_ex (fun A => noCl_ex fun b => noCl_sep (noCl_lift _)
      (noCl_sep (noCl_up _) (noCl_bauth _ _ _ _))) r hq b).post fun p r h => ?_
  obtain ⟨A, h⟩ := sep_ex.mp h
  obtain ⟨b, h⟩ := sep_ex.mp h
  obtain ⟨hφ, h⟩ := sep_lift.mp (sep_assoc h)
  rw [hφ.1] at h
  exact ⟨A, b, sep_lift.mpr ⟨hφ, sep_assoc h⟩⟩

/-- `allocStack` (a stack local whose address escapes) with the claim on its bytes. -/
theorem FTriple.allocStackC (size align : Nat) (ha : 0 < align) (hpos : 0 < size) :
    FTriple emp (allocStack size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size .stack (Array.replicate size .undef)) ⋆ (bext b size .stack ⋆ bclaim b 0 size))) :=
  FTriple.allocC .stack size align ha hpos

/-! ## Ending a block (native) -/

/-- **A block ends under its bytes and its full extent**: the resource owns every byte of block
`b` (all `S` bytes from offset 0) and its full extent. The memory with `b` dead holds nothing
with the same frame: the frame has no byte of `b` and only dormant claims on it. -/
theorem Holds.free {m : Mem} {r rF : Res} {p : Ptr} {A S : Nat} {K : BlockKind}
    {bs : Array Byte} {b : BlockId} {blk : Block} (hh : Holds m r rF)
    (hp : (up (bytesAt p A S K bs) ⋆ bext b S K) r) (hpb : p.block = some b) (hS : bs.size = S)
    (h0 : p.off = 0) (hb : m.blocks[b]? = some blk) (hK : blk.kind ≠ .constGlobal) :
    Holds { m with blocks := m.blocks.set! b { blk with live := false } }
      ⟨FHeap.empty, Know.none, Ghost.unit⟩ rF := by
  obtain ⟨⟨b', hb', -, hl⟩, -, hrg⟩ := up_sep_bext hp
  rw [hpb] at hb'; cases hb'
  replace hrg : r.gh = Ghost.exts (extOne b S K) := hrg
  obtain ⟨blk', hb₁, -, hsz, -, -⟩ := hh.bauth (sep_comm hp)
  rw [hb] at hb₁; cases hb₁
  have hget := blocks_set_get hb (m' := { m with blocks := m.blocks.set! b { blk with live := false } }) rfl
  -- the resource owns exactly the bytes `0 … S - 1` of `b`; the frame none of `b`
  have hown : ∀ y, y < S → r.heap (b, y) ≠ none := fun y hy => by
    have e := hl (b, y)
    rw [ite_eq_left ⟨rfl, by omega, by rw [h0]; simp; omega⟩] at e
    intro hn; simp [FHeap.erase, hn] at e
  have hrb : ∀ l : Loc, l.1 ≠ b → r.heap l = none := fun l hx => by
    have e := hl l
    rw [ite_eq_right fun h => hx h.1] at e
    simpa [FHeap.erase] using e
  have hFb : ∀ y, rF.heap (b, y) = none := fun y => by
    cases e : rF.heap (b, y) with
    | none => rfl
    | some fc =>
      obtain ⟨blk', hb', -, hy, -⟩ := hh.swap.block e
      rw [hb] at hb'; cases hb'
      exact absurd ((hh.disj (b, y)).resolve_left (hown y (by omega))) (by simp [e])
  have hok : Ghost.Ok (Ghost.exts (extOne b S K)) rF.gh := hrg ▸ hh.ghost.1
  have hdorm : (rF.gh.extent b).Dormant rF.gh.ls := by
    have := full_excl hok (b := b) (S := S) (K := K) (by simp [Ghost.exts, extOne])
    rwa [Ghost.ls_exts_add] at this
  have hheap : ∀ l : Loc, ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).heap l =
      if l.1 = b then none else m.heap l := fun ⟨x, y⟩ => by
    simp only [Mem.heap, hget]
    by_cases hx : x = b <;> simp [hx]
  refine ⟨fun _ => .inl rfl, ⟨fun l => ?_, fun l fc hfc => ?_⟩, Know.sub_none _,
    hh.knowF.trans (KMono.set (blk' := { blk with live := false }) hb rfl hK rfl),
    ⟨?_, fun x => ?_, ?_⟩⟩
  · -- the frame's cells, outside `b`
    rw [hheap, FHeap.empty_union]
    by_cases hx : l.1 = b
    · rw [ite_eq_left hx, show l = (b, l.2) from Prod.ext hx rfl, hFb]; rfl
    · rw [ite_eq_right hx]
      have := hh.heap.1 l
      rwa [FHeap.union_apply, hrb l hx, Option.none_or] at this
  · exact hh.tagF (by simpa [FHeap.empty] using hfc)
  · -- the ghost states compose without `b`'s extent
    have := Ghost.ok_exts_change (E' := fun _ => none) hok fun _ h => by simp at h
    rwa [Ghost.exts_none] at this
  · -- the frame's extent claims hold: on `b` it has none
    show ECell.TrueIn _ _ _ _
    rw [Ghost.unit_add]
    by_cases hx : x = b
    · subst hx
      exact ⟨fun S' K' h => absurd (hdorm.1 (S', K') ▸ h) (Nat.lt_irrefl 0),
        fun k h => (hdorm.2.1 k h).elim⟩
    · have ht := hh.ghost.2.1 x
      rw [hrg, Ghost.ls_exts_add,
        show ((Ghost.exts (extOne b S K)).add rF.gh).extent x = rF.gh.extent x by
          simp [Ghost.add, Ghost.exts, extOne, hx]] at ht
      refine ⟨fun S' K' hp' => ?_, fun k hk' => ?_⟩
      · obtain ⟨blk₀, hb₀, rest⟩ := ht.1 S' K' hp'
        exact ⟨blk₀, by rw [hget, ite_eq_right hx]; exact hb₀, rest⟩
      · obtain ⟨blk₀, hb₀, rest⟩ := ht.2 k hk'
        exact ⟨blk₀, by rw [hget, ite_eq_right hx]; exact hb₀, rest⟩
  · -- no byte claim on a block not yet made
    rw [Ghost.unit_add]
    exact (ClFresh.frame hh.ghost.2.2).mono (by simp)

/-! ## Step rules (`fsym`) -/

-- `hpos` is not needed (an extent of no bytes does not exist), but the rule keeps its statement.
set_option linter.unusedVariables false in
/-- **`free` of a whole block** (total): its bytes and its full extent go. A `const` global is
never freed (`free` of one is illegal). -/
@[fsym] theorem FTotalTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => emp) :=
  FTotalTriple.of_run fun m r rF hh hp hs => by
    obtain ⟨blk, hb, hl, hsz, hk, -⟩ := hh.bauth (sep_comm hp)
    have hK' : blk.kind ≠ .constGlobal := hk ▸ hK
    refine ⟨(), _, _, ?_, hh.free hp hpb hS h0 hb hK', ⟨rfl, rfl, rfl⟩,
      ⟨⟨hs.1.single⟩, hs.2.1, LDMono.set (nb := { blk with live := false }) hb
        (fun h => by cases h) rfl (Nat.le_refl _) rfl hs.2.2⟩⟩
    simp [Zig.free, hpb, hb, hl, h0, hsz, hK', freeRaces_of_singleThread hs.1.single, zig_unfold,
      set, StateT.set, MonadStateOf.set]

/-- `free` of a whole block, not a `const` global: its bytes and its full extent go. -/
theorem FTriple.free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (free p) (fun _ => emp) :=
  (FTotalTriple.free hpb hS h0 hpos hK).1

/-- `free` returns from every memory that holds a whole block with its full extent. -/
theorem FReturns.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FReturns (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) :=
  (FTotalTriple.free hpb hS h0 hpos hK).2

/-! ## Thread rules -/

/-- `alloc` of `size > 0` bytes in a thread: the bytes and the new block's full extent. -/
theorem FTTriple.alloc (kind : BlockKind) (size align : Nat) (ha : 0 < align) (hpos : 0 < size)
    (hk : kind.mappedLo = 0 := by first | rfl | simp_all [BlockKind.mappedLo]) :
    FTTriple emp (Zig.alloc kind size align) (fun p => FAssn.ex fun A : Nat => FAssn.ex fun b : BlockId =>
      ⟪p.block = some b ∧ p.off = 0 ∧ A % align = 0⟫ ⋆
        (up (bytesAt p A size kind (Array.replicate size .undef)) ⋆ bext b size kind)) :=
  FTTriple.ofSeq (FTriple.alloc' kind size align ha hpos hk) (ThreadLocal.alloc kind size align)

/-- `alloc` of no bytes in a thread: a pointer to offset 0 of a new block. -/
theorem FTTriple.allocZero (kind : BlockKind) (align : Nat) :
    FTTriple emp (Zig.alloc kind 0 align) (fun p => ⟪p.block.isSome ∧ p.off = 0⟫) :=
  FTTriple.ofSeq (FTriple.allocZero kind align) (ThreadLocal.alloc kind 0 align)

/-- **`free` of a whole block in a thread** (total): its bytes and its full extent go. The thread
owns every byte of the block, so no access to it races with its end. -/
theorem FTTotalTriple.free {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal) :
    FTTotalTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (Zig.free p) (fun _ => emp) :=
  FTTotalTriple.ofSeq (FTotalTriple.free hpb hS h0 hpos hK)
    (ThreadLocal.free hpb fun m r _ hh hp blk hb x hx => by
      obtain ⟨blk', hb', -, hsz, -⟩ := hh.bauth (sep_comm hp)
      rw [hb] at hb'; cases hb'
      exact (OwnsAt.bytesAt hpb).sepL r hp x (by simp [h0]) (by simp [h0]; omega))

/-- `free` of a whole block in a thread, not a `const` global: its bytes and its full extent go. -/
theorem FTTriple.free' {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTTriple (up (bytesAt p A S K bs) ⋆ bext b S K) (free p) (fun _ => emp) :=
  (FTTotalTriple.free hpb hS h0 hpos hK).toPartial

/-- `free'` of the block in front of a frame `R`: the frame stays. -/
theorem FTTriple.free_front {R : FAssn} {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {b : BlockId} (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S)
    (hK : K ≠ .constGlobal := by decide) :
    FTTriple ((up (bytesAt p A S K bs) ⋆ bext b S K) ⋆ R) (free p) (fun _ => R) :=
  (free' hpb hS h0 hpos hK).frame.post fun _ _ h => sep_emp.mp (sep_comm h)

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
theorem FTotalTriple.rawAllocZero (align : Nat) :
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
  have ht := FTriple.allocZero .heap align _ r rF hh₁ hp hs₁
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
