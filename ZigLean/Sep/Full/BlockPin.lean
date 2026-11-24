import ZigLean.Sep.Full.Word

/-!
# A block pinned by its extent in a lock's rest

A lock's invariant keeps the bytes of its rest only up to `Cell.norm` (`FLock.Inv.restCell`): a
cell's size and kind are its block's, which the rest's cells do not fix. A rest that also holds an
authority claim of the block's extent (`bauth`, `bext`) fixes them: the block is live with the
claim's size and kind in every memory where the invariant holds (`FLock.Inv.pinned`), so a byte
that the rest holds with its cell of one memory has that cell in the other
(`FLock.Inv.cell_pinned`, `FLock.Inv.cells_pinned` for a word's cells). A client's base keeps the
claim (`Res.Pins`) and gets the exact cells that `Word.hist_fstep`, `Word.Ok.fstep` and
`FRw.Inv.stepIn` (`hcells`) take over a step on a thread's own part.
-/

namespace Zig

/-- **Cells that agree up to `Cell.norm` in one block of one size and kind are equal** (a cell is
its byte with the block's address, size and kind). -/
theorem Mem.heap_eq_of_norm {m m' : Mem} {b : BlockId} {S : Nat} {K : BlockKind} {x : Nat}
    (hb : ∃ blk, m.blocks[b]? = some blk ∧ blk.bytes.size = S ∧ blk.kind = K)
    (hb' : ∃ blk, m'.blocks[b]? = some blk ∧ blk.bytes.size = S ∧ blk.kind = K)
    (hn : (m'.heap (b, x)).map Cell.norm = (m.heap (b, x)).map Cell.norm) :
    m'.heap (b, x) = m.heap (b, x) := by
  obtain ⟨blk, hb, hs, hk⟩ := hb
  obtain ⟨blk', hb', hs', hk'⟩ := hb'
  cases e : m.heap (b, x) with
  | none => rw [e] at hn; simpa using hn
  | some c =>
    cases e' : m'.heap (b, x) with
    | none => rw [e, e'] at hn; cases hn
    | some c' =>
      rw [e, e'] at hn
      obtain ⟨k, hk0, -, -, rfl⟩ := Mem.heap_some e
      obtain ⟨k', hk0', -, -, rfl⟩ := Mem.heap_some e'
      rw [hb] at hk0; cases hk0
      rw [hb'] at hk0'; cases hk0'
      simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq] at hn
      simp only [Option.some.injEq, Cell.mk.injEq]
      exact ⟨hn.1, hn.2.1, by rw [hs', hs], by rw [hk', hk]⟩

namespace Full

open FAssn Conc

/-- `r` holds an authority claim of block `b`'s extent: `S` bytes of kind `K` (`bauth`, `bext`). -/
def Res.Pins (r : Res) (b : BlockId) (S : Nat) (K : BlockKind) : Prop :=
  0 < (r.gh.extent b).auth (S, K)

namespace Res.Pins

variable {a c : Res} {b : BlockId} {S : Nat} {K : BlockKind}

theorem left (h : a.Pins b S K) : (rsum a c).Pins b S K :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)

theorem right (h : c.Pins b S K) : (rsum a c).Pins b S K :=
  Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)

/-- A resource with the block's authority (`bauth`; `bext` at the whole fraction) pins it. -/
theorem of_bauth {r : Res} {R : FAssn} {q : Frac} (h : (bauth b S K q ⋆ R) r) : r.Pins b S K := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  refine left ?_
  rw [bauth_eq h1]
  simp [Res.Pins, Ghost.atExt, ECell.auth1]

end Res.Pins

namespace FLock

variable {γ : Type} {L : FLock γ} {n nb : Nat} {W : Word n nb}

/-- **A block that the rest pins is live with the claim's size and kind** (`Res.Pins`; the
lock's complete rest holds, `Holds.extTrue`). -/
theorem Inv.pinned {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {b : BlockId}
    {S : Nat} {K : BlockKind} (hp : rX.Pins b S K) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧
      K.mappedLo < S := by
  obtain ⟨rL, ho, -⟩ := hi.restIn
  obtain ⟨rT, -, hh⟩ := ho.holds
  exact (hh.swap.extTrue b).1 S K (Res.Pins.right (Res.Pins.right hp))

/-- **A byte of a pinned block that the rest after a step holds with its cell before it has the
same cell** (module doc): the invariant after the step has it up to `Cell.norm`
(`Inv.restCell`), and the block has one size and kind in both memories (`Inv.pinned`). -/
theorem Inv.cell_pinned {G G' : ThreadId → γ} {rX rX' : Res} {m m' : Mem} (hi : L.Inv G rX m)
    (hi' : L.Inv G' rX' m') {b : BlockId} {S : Nat} {K : BlockKind} (hp : rX.Pins b S K)
    (hp' : rX'.Pins b S K) {x : Nat} {c : Cell} (hc : m.heap (b, x) = some c)
    (hr : rX'.heap (b, x) = some ⟨c, none⟩) : m'.heap (b, x) = m.heap (b, x) := by
  obtain ⟨blk, hb, -, hs, hk, -⟩ := hi.pinned hp
  obtain ⟨blk', hb', -, hs', hk', -⟩ := hi'.pinned hp'
  refine Mem.heap_eq_of_norm ⟨blk, hb, hs, hk⟩ ⟨blk', hb', hs', hk'⟩ ?_
  rw [hi'.restCell hr, hc]; rfl

/-- **A step that keeps the rest keeps the cells of a word in a block that the rest pins**
(`Inv.cell_pinned` at the word's cells in the rest; the word's bytes are live before the step). -/
theorem Inv.cells_pinned {G G' : ThreadId → γ} {rX rY : Res} {m m' : Mem} (hi : L.Inv G rX m)
    (hi' : L.Inv G' (rsum (W.cellsR m) rY) m') {S : Nat} {K : BlockKind} (hp : rX.Pins W.b S K)
    (hp' : (rsum (W.cellsR m) rY).Pins W.b S K) (h0 : ∀ l, W.In l → m.heap l ≠ none) :
    ∀ l, W.In l → m'.heap l = m.heap l := by
  rintro ⟨b, x⟩ hl
  obtain rfl : b = W.b := hl.1
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (h0 _ hl)
  exact hi.cell_pinned hi' hp hp' hc (by simp [FHeap.union_apply, cellsAt_of hl, hc])

end FLock

end Full
end Zig
