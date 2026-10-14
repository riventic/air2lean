import ZigLean.Sep.Full.Mmap

/-!
# Why a shrink takes the grant's whole share (regression, `docs/sep-full-state.md` §`FAllocSpec` refined)

The refined `FAllocSpec.resize` lets a growth take any part `q' ≤ q` of the grant's extent share,
but a shrink only the whole share (`n < len → q' = q`). This file shows why, on the page
allocator's shrink, a `munmap` of a mapping's tail: with only half of the mapping's extent in the
precondition, the other half can sit in the frame, at a bound past the new end, and no
postcondition can keep the frame true.

The scenario, on one mapping of two pages (block `0`, `8192` bytes, `.mapped 0`):

* the mapping's full extent is lent in halves (`EUpd.lend`): the **resource** holds the tail page's
  bytes and the authority with half the fraction; the **frame** holds the first page's bytes and a
  share of the other half at bound `8192`;
* `munmap` of the tail page succeeds in this memory (`Os.munmap_run`), leaving `4096` bytes.

`frame_breaks`: after the `munmap`, no resource `r'` makes the memory hold `r'` next to the frame
(the frame's share claims `8192` bytes, `Holds.bshare`). `no_partial_shrink`: so no `FTriple`
from the tail and half the authority exists for this `munmap`, whatever the postcondition. With
the whole extent (`bext`) the frame has no live claim on the block (`full_excl`), and the rule
holds: `FTotalTriple.munmapTail'`.
-/

namespace Zig.Full.ShrinkCX
open FAssn

/-! ## The memory: one live mapping of two pages at address 4096 -/

/-- The mapping's bytes (irreducible: no proof evaluates them). -/
@[irreducible] def bs2 : Array Byte := Array.replicate 8192 (.int 0)
def blk2 : Block := { bytes := bs2, align := 4096, kind := .mapped 0, live := true, addr := 4096 }
def m2 : Mem := { blocks := #[blk2] }

/-- The cell of every byte of the mapping. -/
def c0 : Cell := ⟨.int 0, 4096, 8192, .mapped 0⟩

theorem bs2_get (o : Nat) (h : o < bs2.size) : bs2[o] = .int 0 := by unfold bs2; simp

@[simp] theorem bs2_size : bs2.size = 8192 := by unfold bs2; simp

theorem m2_heap (l : Loc) : m2.heap l = if l.1 = 0 ∧ l.2 < 8192 then some c0 else none := by
  obtain ⟨b, o⟩ := l
  rcases b with _ | b
  · by_cases ho : o < 8192
    · simp [Mem.heap, m2, blk2, ho, c0, bs2_get]
    · simp [Mem.heap, m2, blk2, ho]
  · simp [Mem.heap, m2]

theorem seq2 : m2.FSeq := by
  refine ⟨⟨⟨by decide, by simp [m2]⟩⟩, ⟨by simp [shapes, m2], by simp [shapes, m2]⟩, ?_, fun b blk hb _ => ?_⟩
  · intro b b' blk blk' hne hb hb' _
    simp only [m2] at hb hb'
    rcases b with _ | b <;> rcases b' with _ | b' <;> simp at hb hb' hne
  · simp only [m2] at hb
    rcases b with _ | b <;> simp at hb
    subst hb; simp [blk2, bs2_size]

/-! ## The resources -/

/-- Owned bytes of the mapping, `[lo, hi)`. -/
def own (lo hi : Nat) : FHeap := fun l => if l.1 = 0 ∧ lo ≤ l.2 ∧ l.2 < hi then some ⟨c0, none⟩ else none

/-- The tail page `[4096, 8192)` at `pT`. -/
def pT : Ptr := ⟨some 0, 4096⟩

@[irreducible] def tl : Array Byte := Array.replicate 4096 (.int 0)

@[simp] theorem tl_size : tl.size = 4096 := by unfold tl; simp

theorem tl_get (i : Nat) (h : i < 4096) : tl[i]! = .int 0 := by unfold tl; simp [h]

theorem own_bytesAt : bytesAt pT 4096 8192 (.mapped 0) tl (own 4096 8192).erase := by
  refine ⟨0, rfl, by decide, fun l => ?_⟩
  obtain ⟨b, o⟩ := l
  simp only [FHeap.erase, own, pT, tl_size, show ((4096 : Int)).toNat = 4096 from rfl]
  by_cases h : b = 0 ∧ 4096 ≤ o ∧ o < 8192
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, by omega⟩]
    simp [c0, tl_get (o - 4096) (by omega)]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1, by omega⟩)]; rfl

/-- The full extent of the mapping. -/
def gE : Ghost := Ghost.atExt 0 (ECell.auth1 8192 (.mapped 0) Frac.one)

theorem gE_ok : GOk m2 Ghost.unit gE := by
  refine ⟨⟨⟨fun γ => by simpa [Ghost.add, gE, Ghost.atExt, Ghost.unit] using (GOk.unit (m := m2)).1.1.1 γ,
    fun b => ?_, Ghost.CValid.congr (g := Ghost.unit) (by funext x y; simp [gE, Ghost.atExt, Ghost.unit])
      (by funext γ e p; simp [Ghost.ls, Ghost.add, gE, Ghost.atExt, Ghost.unit]) Ghost.CValid.unit,
      by simpa [gE] using ACell.valid_unit⟩,
    0, fun _ _ => ⟨by simp [Ghost.add, gE, Ghost.atExt, Ghost.unit], fun b e k => ?_,
      fun _ _ _ _ => rfl⟩⟩, fun b => ?_,
    fun _ _ _ => by simp [gE, Ghost.atExt, Ghost.unit],
    by simpa [gE] using MemAuth.unit (m := m2) (Mem.noStack_of_stacks rfl)⟩
  · simp only [Ghost.add, Ghost.unit, gE, Ghost.atExt, ECell.unit_add]
    split
    · have := (ECell.dormant_unit (Ghost.ls ⟨fun γ => GCell.unit.add GCell.unit,
        fun b' => if b' = 0 then ECell.auth1 8192 (.mapped 0) Frac.one else ECell.unit, fun _ _ => ECell.unit,
        ACell.unit.add ACell.unit⟩)).auth1_ok
        (S := 8192) (K := .mapped 0)
      rwa [ECell.add_unit] at this
    · exact ⟨ECell.valid_unit, ECell.tagOk_unit _⟩
  · simp only [Ghost.add, Ghost.unit, gE, Ghost.atExt, ECell.unit_add]
    split <;> exact ⟨rfl, rfl⟩
  · show ECell.TrueIn _ _ _ _
    simp only [Ghost.add, Ghost.unit, gE, Ghost.atExt, ECell.unit_add]
    split
    · rename_i hb; subst hb
      refine ⟨fun S K h => ?_, fun k h => ?_⟩
      · simp only [ECell.auth1] at h
        split at h
        · rename_i e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨blk2, rfl, rfl, bs2_size, rfl, by decide⟩
        · cases h
      · have := (ECell.dormant_unit _).req_auth1 (by rwa [ECell.add_unit])
        subst this; exact ⟨blk2, rfl, rfl, by simp [bs2_size], by simp [bs2_size, blk2]⟩
    · exact (ExtTrue.unit m2) b

/-- The bytes `[0, 4096)` and `[4096, 8192)` match the memory. -/
theorem fmatch2 : FMatch m2 (own 4096 8192 ∪ own 0 4096) := by
  refine ⟨fun l => ?_, fun l fc hfc => ?_⟩
  · rw [m2_heap]
    obtain ⟨b, o⟩ := l
    simp only [FHeap.union_apply, own]
    by_cases h1 : b = 0 ∧ 4096 ≤ o ∧ o < 8192
    · rw [if_pos (show b = 0 ∧ o < 8192 from ⟨h1.1, h1.2.2⟩), if_pos h1]; rfl
    · rw [if_neg h1]
      by_cases h2 : b = 0 ∧ 0 ≤ o ∧ o < 4096
      · rw [if_pos (show b = 0 ∧ o < 8192 from ⟨h2.1, by omega⟩), if_pos h2]; rfl
      · rw [if_neg (show ¬ (b = 0 ∧ o < 8192) from fun h3 =>
          if ho : 4096 ≤ o then h1 ⟨h3.1, ho, h3.2⟩ else h2 ⟨h3.1, Nat.zero_le _, by omega⟩), if_neg h2]; rfl
  · have : fc.atom = none := by
      simp only [FHeap.union_apply, own] at hfc
      split at hfc
      · cases hfc; rfl
      · split at hfc
        · cases hfc; rfl
        · cases hfc
    simp [TagSat, this]

/-- Half of the whole fraction. -/
def hf : Frac := Frac.one.half

theorem hf_pos : 0 < hf.val := Frac.half_pos (by decide)

/-- **The split state**: the resource holds the tail page and half the authority, the frame the
first page and a share of the other half at bound `8192` (from the full extent by `EUpd.lend`). -/
theorem split_state : ∃ gA gS : Ghost, Holds m2 ⟨own 4096 8192, Know.none, gA⟩ ⟨own 0 4096, Know.none, gS⟩ ∧
    bauth 0 8192 (.mapped 0) hf ⟨FHeap.empty, Know.none, gA⟩ ∧
    bshare 0 hf 8192 none ⟨FHeap.empty, Know.none, gS⟩ := by
  -- the full extent, next to all the bytes
  have h0 : Holds m2 ⟨FHeap.empty, Know.none, gE⟩ ⟨own 4096 8192 ∪ own 0 4096, Know.none, Ghost.unit⟩ :=
    Holds.swap ⟨fun _ => .inr rfl, by rw [FHeap.union_empty]; exact fmatch2, Know.sub_none _,
      Know.sub_none _, gE_ok⟩
  have hb : bauth 0 8192 (.mapped 0) (hf.add hf) ⟨FHeap.empty, Know.none, gE⟩ := by
    rw [hf, Frac.half_add_half]; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨r₁, h1, hp⟩ := EUpd.lend (b := 0) (S := 8192) (K := .mapped 0) (k := 8192) (q₁ := hf)
    (Nat.le_refl _) hf_pos _ _ _ h0 hb seq2
  obtain ⟨ra, rs, -, rfl, ha, hs⟩ := hp
  have ea := bauth_eq ha
  have es := bshare_eq hs
  subst ea es
  refine ⟨_, _, ⟨fun l => ?_, fmatch2, Know.sub_none _, Know.sub_none _, ?_⟩, ha, hs⟩
  · obtain ⟨b, o⟩ := l
    simp only [own]
    by_cases h : b = 0 ∧ 4096 ≤ o ∧ o < 8192
    · right; rw [if_neg (show ¬ (b = 0 ∧ 0 ≤ o ∧ o < 4096) from fun h' => by omega)]
    · left; rw [if_neg h]
  · simpa only [Ghost.add_unit] using GOk.assoc.mp h1.ghost

/-! ## The `munmap` of the tail page -/

/-- The memory after the `munmap`. -/
theorem munmap_run2 : ∃ m', (Os.munmap .linux ⟨pT, 4096⟩).run m2 = pure ((), m') ∧
    m'.blocks[0]? = some { blk2 with bytes := bs2.extract 0 4096 } := by
  have hu := unmapCase_tail (P := 4096) (lo := 0) (S := 8192) (k := 4096) (n := 4096) (by decide)
    (by decide) (by decide) (by decide)
  simp only [Nat.zero_add] at hu
  refine ⟨_, Os.munmap_run .linux ⟨pT, 4096⟩ (b := 0) (blk := blk2) (lo := 0) (u := .tail 4096) rfl rfl rfl
    rfl (by decide) (by decide) (by rw [show blk2.bytes.size = 8192 from bs2_size]; exact hu)
    seq2.1.single, ?_⟩
  simp [m2, Os.Unmap.apply, blk2]

/-- **The frame breaks**: after the `munmap`, the frame's share at `8192` cannot be held. -/
theorem frame_breaks {m' : Mem} (hb : m'.blocks[0]? = some { blk2 with bytes := bs2.extract 0 4096 })
    {gS : Ghost} (hs : bshare 0 hf 8192 none ⟨FHeap.empty, Know.none, gS⟩) (r' : Res) :
    ¬ Holds m' r' ⟨own 0 4096, Know.none, gS⟩ := by
  intro hh
  have hF : (bshare 0 hf 8192 ⋆ (fun r => r = ⟨own 0 4096, Know.none, Ghost.unit⟩))
      ⟨own 0 4096, Know.none, gS⟩ := by
    refine ⟨⟨FHeap.empty, Know.none, gS⟩, ⟨own 0 4096, Know.none, Ghost.unit⟩, fun _ => .inl rfl, ?_, hs, rfl⟩
    simp [FHeap.empty_union, Know.none_union]
  obtain ⟨blk, hblk, -, hk, -⟩ := hh.swap.bshare hF
  rw [hb] at hblk; cases hblk
  simp [bs2_size] at hk

/-- **No triple from half the authority**: no `FTriple` from the tail page and half the mapping's
authority exists for the `munmap` of the tail, whatever the postcondition `Q`. -/
theorem no_partial_shrink (Q : Unit → FAssn) :
    ¬ FTriple (up (bytesAt pT 4096 8192 (.mapped 0) tl) ⋆ bauth 0 8192 (.mapped 0) hf)
      (Os.munmap .linux ⟨pT, 4096⟩) Q := by
  intro ht
  obtain ⟨gA, gS, hh, ha, hs⟩ := split_state
  have hp : (up (bytesAt pT 4096 8192 (.mapped 0) tl) ⋆ bauth 0 8192 (.mapped 0) hf)
      ⟨own 4096 8192, Know.none, gA⟩ := by
    refine ⟨⟨own 4096 8192, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, gA⟩, fun _ => .inr rfl, ?_,
      ⟨own_bytesAt, rfl, rfl⟩, ha⟩
    simp [FHeap.union_empty, Know.union_none]
  obtain ⟨m', hrun, hb⟩ := munmap_run2
  have := ht _ _ _ hh hp seq2
  rw [hrun] at this
  obtain ⟨r', hh', -, -⟩ := this
  exact frame_breaks hb hs r' hh'

end Zig.Full.ShrinkCX

#print axioms Zig.Full.ShrinkCX.frame_breaks
#print axioms Zig.Full.ShrinkCX.no_partial_shrink
