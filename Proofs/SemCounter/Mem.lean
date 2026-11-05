import Proofs.SemCounter.Protocol

/-!
# The memory's part of `semaphoreCounter`'s rest

The memory facts of the protocol's rest (`UM`, `Proofs/SemCounter/Protocol.lean`) over the steps of
the program: the cells of the condition's words in the rest (`Rest`), the `SemCounter` block
(`BlkOk`, pinned by its extent in the rest), and `UM` over a step of the lock's code
(`UM.lstep`), a stop (`UM.atStop`), a step of a thread on its own part or on the mutex's resource
(`UM_stepIn`), and a step at one of the condition's words (`UM_own_native`). As in
`Proofs/Handoff/Protocol.lean`, for the `SemCounter`'s layout: `io` at 0, the mutex at 24, the
condition's words at 28 and 32.
-/

namespace Zig
namespace SemCounter

open Conc Conc.Proto Full Full.FAssn

theorem res_eq {a b : Res} (hh : a.heap = b.heap) (hk : a.know = b.know) (hg : a.gh = b.gh) :
    a = b := by
  cases a; cases b; simp only at hh hk hg; subst hh hk hg; rfl

theorem ws_box {l : Zig.Loc} (h : WS.In l) : BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, by simp [WS] at h3; omega⟩

theorem we_box {l : Zig.Loc} (h : WE.In l) : BoxW l := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by simp [WE] at h2; omega, by simp [WE] at h3; omega⟩

/-- A byte of the two words is in one of them. -/
theorem box_cases {l : Zig.Loc} (h : BoxW l) : WS.In l ∨ WE.In l := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases a : l.2 < 32
  · exact .inl ⟨h1, h2, a⟩
  · exact .inr ⟨h1, by simp [WE]; omega, by simp [WE]; omega⟩

/-! ## The rest: the condition's words' cells -/

/-- A word of the two in the rest: its cells and the others. -/
theorem Rest.split {rX : Res} {m : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → BoxW l)
    (h : Rest rX m) : ∃ rY, rX = rsum (W.cellsR m) rY ∧ ∀ l, W.In l → rY.heap l = none := by
  obtain ⟨rIO, -, hIO, rfl⟩ := h
  refine ⟨rsum (cellsAt (fun l => BoxW l ∧ ¬ W.In l) m) rIO, res_eq ?_ ?_ ?_, fun l hl => ?_⟩
  · funext l
    simp only [FHeap.union_apply, Word.cellsR]
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), cellsAt_none (fun h => h.2 hw), hIO l (hW l hw)]
      simp
    · rw [cellsAt_none hw]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of (W := fun l => BoxW l ∧ ¬ W.In l) ⟨hb, hw⟩]; simp
      · rw [cellsAt_none hb, cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => hb h.1)]
        simp
  · simp [cellsAt, Word.cellsR, Know.none_union]
  · simp [cellsAt, Word.cellsR]
  · simp only [FHeap.union_apply]
    rw [cellsAt_none (W := fun l => BoxW l ∧ ¬ W.In l) (fun h => h.2 hl), hIO l (hW l hl)]; rfl

/-- After a step that changes only the bytes of the word `W` among the two (the other's cells
stay), the rest has `W`'s new cells. -/
theorem Rest.step {rX rY : Res} {m m' : Mem} {W : Word 32 4} (hW : ∀ l, W.In l → BoxW l)
    (h : Rest rX m) (hX : rX = rsum (W.cellsR m) rY) (hY : ∀ l, W.In l → rY.heap l = none)
    (hm : ∀ l, BoxW l → ¬ W.In l → m'.heap l = m.heap l) :
    Rest (rsum (W.cellsR m') rY) m' := by
  obtain ⟨rIO, hR, hIO, rfl⟩ := h
  have hk : rY.know = rIO.know := by
    have := congrArg Res.know hX; simpa [cellsAt, Word.cellsR, Know.none_union] using this.symm
  have hg : rY.gh = rIO.gh := by
    have := congrArg Res.gh hX; simpa [cellsAt, Word.cellsR] using this.symm
  refine ⟨rIO, hR, hIO, res_eq ?_ ?_ ?_⟩
  · funext l
    have hl := congrFun (congrArg Res.heap hX) l
    simp only [FHeap.union_apply, Word.cellsR] at hl ⊢
    by_cases hw : W.In l
    · rw [cellsAt_of hw, cellsAt_of (hW l hw), hY l hw, hIO l (hW l hw)]
    · rw [cellsAt_none hw, Option.none_or] at hl ⊢
      rw [← hl]
      by_cases hb : BoxW l
      · rw [cellsAt_of hb, cellsAt_of hb, hm l hb hw]
      · rw [cellsAt_none hb, cellsAt_none hb]
  · simp [cellsAt, Word.cellsR, Know.none_union, hk]
  · simp [cellsAt, Word.cellsR, hg]

/-- A step that keeps the cells of the two words keeps the rest. -/
theorem Rest.congr {rX : Res} {m m' : Mem} (h : Rest rX m)
    (hm : ∀ l, BoxW l → m'.heap l = m.heap l) : Rest rX m' := by
  obtain ⟨rIO, hR, hIO, rfl⟩ := h
  refine ⟨rIO, hR, hIO, res_eq ?_ rfl rfl⟩
  funext l
  simp only [FHeap.union_apply]
  by_cases hb : BoxW l
  · rw [cellsAt_of hb, cellsAt_of hb, hm l hb]
  · rw [cellsAt_none hb, cellsAt_none hb]

/-- `blk_of` for a rest whose ghost state is `io`'s. -/
theorem blk_ofG {G : ThreadId → Gh} {rX rIO : Res} {m : Mem} (hi : L.Inv G rX m)
    (hIO : IoRest rIO) (hg : rX.gh = rIO.gh) : BlkOk m := by
  obtain ⟨rL, ho, -⟩ := hi.rest
  obtain ⟨rT, -, hh⟩ := ho.holds
  have he := hh.swap.extTrue
  obtain ⟨A, bs, -, -, -, r₁, r₂, -, rfl, -, h2⟩ := hIO
  simp only at he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [hg, Ghost.add_comm] at he; replace he := ExtTrue.of_add he
  rw [bauth_eq h2] at he
  obtain ⟨blk, h1, h2, h3, h4, -⟩ := (he 0).1 48 .stack (by simp [Ghost.atExt, ECell.auth1])
  exact ⟨blk, h1, h2, h3, h4⟩

/-- **The `SemCounter` is block 0**: live, 48 bytes on the stack (the extent in the rest). -/
theorem blk_of {G : ThreadId → Gh} {rX : Res} {m m₀ : Mem} (hi : L.Inv G rX m)
    (hr : Rest rX m₀) : BlkOk m := by
  obtain ⟨rIO, hIO, -, rfl⟩ := hr
  exact blk_ofG hi hIO (by simp [cellsAt])

theorem heap_blk {m : Mem} {blk : Block} (hb : m.blocks[0]? = some blk) (hl : blk.live = true)
    (hk : blk.kind = .stack) {x : Nat} (hx : x < blk.bytes.size) :
    m.heap (0, x) = some ⟨blk.bytes[x], blk.addr, blk.bytes.size, blk.kind⟩ := by
  simp [Mem.heap, hb, hl, hx, hk, BlockKind.mappedLo]

/-- A byte of the `SemCounter` that the rest after a step holds with its cell before it: the same
cell (the block is pinned). -/
theorem cell_eq {G' : ThreadId → Gh} {rX' : Res} {m m' : Mem} (hbk : BlkOk m)
    (hbk' : BlkOk m') (hi' : L.Inv G' rX' m') {x : Nat} (hx : x < 48)
    (hr : rX'.heap (0, x) = (m.heap (0, x)).map fun c => ⟨c, none⟩) :
    m'.heap (0, x) = m.heap (0, x) := by
  obtain ⟨blk, hb, hlv, hs, hk⟩ := hbk
  obtain ⟨blk', hb', hlv', hs', hk'⟩ := hbk'
  have e := heap_blk hb hlv hk (by omega : x < blk.bytes.size)
  have e' := heap_blk hb' hlv' hk' (by omega : x < blk'.bytes.size)
  rw [e] at hr
  have hrc := hi'.restCell (l := (0, x)) hr
  rw [e', e]
  rw [e'] at hrc
  simp only [Option.map_some, Option.some.injEq, Cell.norm, Cell.mk.injEq] at hrc
  obtain ⟨hby, had, -⟩ := hrc
  simp only [Option.some.injEq, Cell.mk.injEq]
  exact ⟨hby, had, by omega, by rw [hk, hk']⟩

/-- **A step that keeps the rest keeps the condition's words' cells**: the lock's invariant after
it has them up to `Cell.norm`, and the extent in the rest pins the block. -/
theorem cells_same {G' : ThreadId → Gh} {rX : Res} {m m' : Mem} (hbk : BlkOk m)
    (hi' : L.Inv G' rX m') (hr : Rest rX m) : ∀ l, BoxW l → m'.heap l = m.heap l := by
  rintro ⟨b, x⟩ hl
  obtain ⟨h0, h1, h2⟩ := hl
  simp only at h0 h1 h2; subst h0
  refine cell_eq hbk (blk_of hi' hr) hi' (by omega) ?_
  obtain ⟨rIO, -, hIO, rfl⟩ := hr
  have hB : BoxW (0, x) := ⟨rfl, h1, h2⟩
  simp only [FHeap.union_apply, cellsAt_of hB, hIO (0, x) hB, Option.or_none]

/-! ## The lock's word and the rest -/

theorem apS : WS.ApartL L.toLockWord := .inr (.inl (by simp [WS, L, FLock.prod]))
theorem apE : WE.ApartL L.toLockWord := .inr (.inl (by simp [WE, L, FLock.prod]))

/-- A byte of the two words is not the mutex's. -/
theorem box_notL {l : Zig.Loc} (h : BoxW l) : ¬ L.In l := fun ⟨_, h2, h3⟩ => by
  obtain ⟨-, h5, -⟩ := h; simp [L, FLock.prod] at h2 h3; omega

/-- The access `e` of the mutex's word is not to `io`. -/
theorem io_notL {e : FootprintEntry} (h : e.off = L.o) : ¬ IoR e := fun ⟨_, _, h2⟩ => by
  simp [L, FLock.prod] at h; omega

/-- A step of the lock's code keeps the `SemCounter`: it writes at most the mutex's bytes. -/
theorem BlkOk.lstep {t : ThreadId} {m m' : Mem} (hb : BlkOk m) (hs : L.Step t m m') :
    BlkOk m' := by
  obtain ⟨blk, hb, hl, hsz, hk⟩ := hb
  rcases hs.blocks with e | ⟨blk', bs, h1, -, h3, h4, h5⟩
  · exact ⟨blk, by rw [e]; exact hb, hl, hsz, hk⟩
  · have h1' : m.blocks[0]? = some blk' := h1
    rw [hb] at h1'; cases h1'
    refine ⟨{ blk with bytes := writeBytes blk.bytes 24 bs }, ?_, hl, ?_, hk⟩
    · rw [h5]; show (m.blocks.set! 0 _)[0]? = _
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt
        (Array.getElem?_eq_some_iff.mp hb).1]; rfl
    · show (writeBytes blk.bytes 24 bs).size = 48
      rw [writeBytes_size _ _ _ (by rw [h3]; exact h4), hsz]

/-- The rest has the bytes of `io`. -/
theorem rest_io {rX : Res} {m : Mem} (hr : Rest rX m) {x : Nat} (hx : x < 16) :
    rX.heap (0, x) ≠ none := by
  obtain ⟨rIO, ⟨A, bs, -, hbs, -, r₁, r₂, -, rfl, h1, -⟩, -, rfl⟩ := hr
  have := (up_bytesAt_some h1 rfl (0, x)).mpr ⟨rfl, by simp [cPtr], by simp [cPtr, hbs]; omega⟩
  simp only [FHeap.union_apply, ne_eq, Option.or_eq_none_iff, not_and]
  intro _ h; exact absurd h this

/-- The rest has the cells of the two words. -/
theorem rest_box {rX : Res} {m : Mem} (hr : Rest rX m) (hw : ∀ l, BoxW l → m.heap l ≠ none)
    {l : Zig.Loc} (hl : BoxW l) : rX.heap.erase l ≠ none := by
  obtain ⟨rIO, -, -, rfl⟩ := hr
  have := cellsAt_some hl (hw l hl) (m := m)
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff, Option.or_eq_none_iff,
    not_and]
  intro h; exact absurd h this

/-- The words' cells are live. -/
theorem box_live {G : ThreadId → Gh} {rX : Res} {m : Mem} (hu : UM G rX m) {l : Zig.Loc}
    (hl : BoxW l) : m.heap l ≠ none := by
  rcases box_cases hl with h | h
  · exact hu.ws.cellIn h
  · exact hu.we.cellIn h

/-- The frame of a step on a part with the mutex's word and the rest `rX` (`FLock.Inv.wp_liftM`):
it has the rest's bytes, and the mutex's. -/
theorem frame_rest {rX : Res} {m : Mem} {l : Zig.Loc} (h : rX.heap.erase l ≠ none) :
    (rsum (L.wordR m) rX).heap.erase l ≠ none := by
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and] at h ⊢
  intro _; exact h

theorem frame_word {G : ThreadId → Gh} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {x : Nat}
    (h1 : L.o ≤ x) (h2 : x < L.o + 4) :
    (rsum (L.wordR m) rX).heap.erase (L.b, x) ≠ none := by
  have := LockWord.wordR_some hi.w.blk (l := (L.b, x)) ⟨rfl, h1, h2⟩
  simp only [FHeap.erase, FHeap.union_apply, ne_eq, Option.map_eq_none_iff,
    Option.or_eq_none_iff, not_and]
  intro h; exact absurd h this

/-! ## `UM` over the steps -/

/-- **`UM` over a step of the lock's code** (it reads the client's places only). -/
theorem UM.lstep {G G' : ThreadId → Gh} {rX : Res} {m m' : Mem} {t : ThreadId} (hu : UM G rX m)
    (hs : L.Step t m m') (hX : xs G' = xs G) : UM G' rX m' := by
  refine ⟨by rw [hX]; unfold Shape at *; rw [hs.threads]; exact hu.shape, fun e he hr => ?_,
    hu.rest.congr fun l hl => hs.heap (box_notL hl), hu.blk.lstep hs,
    (hu.ws.lockStep hs apS).1, (hu.we.lockStep hs apE).1, fun w hw => ?_⟩
  · rcases hs.fp e he with h' | ⟨-, ho', -⟩
    · rcases hu.io e h' hr with ⟨hk, h''⟩ | h''
      · exact .inl ⟨hk, hs.someLe h''⟩
      · exact .inr (hs.allLe h'')
    · exact absurd hr (io_notL ho')
  · by_cases hl : w.2 = L.ptr
    · exact .inl hl
    · exact hu.q w ((hs.waiters_mem w hl).mp hw)

/-- A stop keeps `UM`: it reads no current thread. -/
theorem UM.atStop {G : ThreadId → Gh} {rX : Res} {m : Mem} (t : ThreadId) (hu : UM G rX m) :
    UM G rX { m with current := t } :=
  have wordOk : ∀ W : Word 32 4, W.Ok m → W.Ok { m with current := t } :=
    fun _ hw => (hw.fields_native (m' := { m with current := t })
      rfl rfl rfl rfl (fun _ => VClock.le_refl _)).1
  ⟨hu.shape, hu.io, hu.rest, hu.blk, wordOk _ hu.ws, wordOk _ hu.we, hu.q⟩

/-- **`UM` over a native framed step** (`FStepIn` with `io`, the mutex's word and the condition's
words in its frame), with the words' validity after it given. -/
theorem UM_frame_native {G G' : ThreadId → Gh} {rX rX' : Res} {m m' : Mem} {hF : Heap}
    (hu : UM G rX m) (hs : FStepIn hF m m')
    (hio : ∀ x, x < 16 → hF (0, x) ≠ none)
    (hrest : Rest rX' m') (hbk : BlkOk m') (hwS : WS.Ok m') (hwE : WE.Ok m')
    (hX : xs G' = xs G) : UM G' rX' m' := by
  refine ⟨by rw [hX]; unfold Shape at *; rw [hs.threads]; exact hu.shape, fun e he hr => ?_,
    hrest, hbk, hwS, hwE, fun w hw => by rw [hs.waiters] at hw; exact hu.q w hw⟩
  rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨-, hnt, -⟩
  · obtain ⟨-, hb, hk, ho, hl, hc⟩ := hn
    rcases hu.io e₀ he₀ ⟨hb.symm.trans hr.1, by have := hr.2.1; omega,
      by have := hr.2.2; omega⟩ with ⟨hk', h''⟩ | h''
    · exact .inl ⟨hk.trans hk', Conc.someLe_mono hs.threads (fun u _ => hs.clock u)
        (LockWord.someLe_le hc h'')⟩
    · exact .inr (Conc.allLe_mono hs.threads (fun u _ => hs.clock u)
        fun u hu => VClock.le_trans hc (h'' u hu))
  · refine absurd ⟨e.off, Nat.le_refl _, by have := hr.2.1; omega, ?_⟩ hnt
    rw [hr.1]; exact hio _ hr.2.2

/-- **A step of `t` on its own part or on the mutex's resource keeps `UM`** (an `FStepIn` that keeps
the mutex's word and the rest: `FLock.Inv.wp_liftM`, `FSem.Move.hold`), with the condition's
words' writes; the lock's invariant after it (with any ghost values `G'`) pins the
`SemCounter`. -/
theorem UM_stepIn {G G' G'' : ThreadId → Gh} {rX : Res} {m m' : Mem}
    (hu : UM G rX m)
    (hs : FStepIn (rsum (L.wordR m) rX).heap.erase m m') (hi' : L.Inv G' rX m')
    (hX : xs G'' = xs G) :
    UM G'' rX m' ∧ WS.hist m' = WS.hist m ∧ WE.hist m' = WE.hist m := by
  have hcs := cells_same hu.blk hi' hu.rest
  have facts : ∀ (W : Word 32 4), (∀ l, W.In l → BoxW l) → W.Ok m →
      W.Ok m' ∧ W.hist m' = W.hist m := by
    intro W hW hw
    have hcover : ∀ l, W.In l → (rsum (L.wordR m) rX).heap.erase l ≠ none :=
      fun l hl => frame_rest (rest_box hu.rest (fun _ => box_live hu) (hW l hl))
    have hnorm : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
      intro l hl
      rw [hcs l (hW l hl)]
    exact ⟨hw.fstep hs hcover hnorm, Word.hist_fstep hw hs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (fun _ => ws_box) hu.ws
  obtain ⟨hwE, hhE⟩ := facts _ (fun _ => we_box) hu.we
  exact ⟨UM_frame_native hu hs
    (fun x hx => frame_rest (by simpa [FHeap.erase] using rest_io hu.rest hx))
    (hu.rest.congr hcs) (blk_of hi' hu.rest) hwS hwE hX, hhS, hhE⟩

/-- One of the two condition's words. -/
def Two (W : Word 32 4) : Prop := W = WS ∨ W = WE

theorem two_box {W : Word 32 4} (h : Two W) : ∀ l, W.In l → BoxW l := by
  rcases h with rfl | rfl
  · exact fun _ => ws_box
  · exact fun _ => we_box

theorem two_apart {W W' : Word 32 4} (h : Two W) (h' : Two W') :
    W' = W ∨ ∀ l, W'.In l → ¬ W.In l := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;>
    first
      | exact .inl rfl
      | exact .inr fun l ⟨_, a, b⟩ ⟨_, c, d⟩ => by simp only [WS, WE] at a b c d; omega

theorem two_b {W : Word 32 4} (h : Two W) : W.b = 0 := by
  rcases h with rfl | rfl <;> rfl

theorem two_o {W : Word 32 4} (h : Two W) : 28 ≤ W.o := by
  rcases h with rfl | rfl <;> simp [WS, WE]

theorem two_ap {W : Word 32 4} (h : Two W) : W.ApartL L.toLockWord := by
  rcases h with rfl | rfl
  · exact apS
  · exact apE

/-- Two words whose bytes are apart: the condition of `Word.keep_op`. -/
theorem apart_of {W W' : Word 32 4} (h : ∀ l, W'.In l → ¬ W.In l) :
    W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o := by
  by_cases hb : W.b = W'.b
  · refine .inr (Classical.byContradiction fun hc => ?_)
    by_cases h2 : W'.o ≤ W.o
    · exact h (W'.b, W.o) ⟨rfl, h2, by dsimp only; omega⟩
        ⟨hb.symm, Nat.le_refl _, by dsimp only; omega⟩
    · exact h (W'.b, W'.o) ⟨rfl, Nat.le_refl _, by dsimp only; omega⟩
        ⟨hb.symm, by dsimp only; omega, by dsimp only; omega⟩
  · exact .inl hb

/-- The two words: the same, or apart (`FCond.MStep.word`). -/
theorem two_word {W W' : Word 32 4} (h : Two W) (h' : Two W') :
    W' = W ∨ W.b ≠ W'.b ∨ W.o + 4 ≤ W'.o ∨ W'.o + 4 ≤ W.o :=
  (two_apart h h').imp_right apart_of

/-- An access at one of the two words is in the `SemCounter` past the mutex. -/
theorem two_fp {e : FootprintEntry} {W : Word 32 4} (hW : Two W)
    (h : e.block = W.b ∧ e.off = W.o) : e.block = 0 ∧ 28 ≤ e.off :=
  ⟨h.1.trans (two_b hW), h.2 ▸ two_o hW⟩

/-- The `SemCounter` after a step that keeps each block as live, as large and of the same kind
(`FCond.MStep.block`). -/
theorem BlkOk.of_block {m m' : Mem} (h : BlkOk m)
    (hb : ∀ (b : BlockId) (blk : Block), m.blocks[b]? = some blk → ∃ blk', m'.blocks[b]? = some blk' ∧
      blk'.live = blk.live ∧ blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind) :
    BlkOk m' := by
  obtain ⟨blk, h1, h2, h3, h4⟩ := h
  obtain ⟨blk', e1, e2, e3, e4⟩ := hb _ _ h1
  exact ⟨blk', e1, by rw [e2]; exact h2, by rw [e3]; exact h3, by rw [e4]; exact h4⟩

/-- **A step of `t` at one of the condition's words on its own part** (an `FStepIn` with the
mutex's word and the rest without `W`'s cells in its frame): `UM` with `W`'s new cells, the other
word kept. -/
theorem UM_own_native {G G' : ThreadId → Gh} {rY : Res} {m m' : Mem}
    {W : Word 32 4} (hW2 : Two W)
    (hu : UM G (rsum (W.cellsR m) rY) m)
    (hY : ∀ l, W.In l → rY.heap l = none)
    (hs : FStepIn (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase m m')
    (hw' : W.Ok m') (hh : W.hist m' = W.hist m)
    (hi' : L.Inv G' (rsum (W.cellsR m') rY) m') (hX : xs G' = xs G) :
    UM G' (rsum (W.cellsR m') rY) m' ∧ WS.hist m' = WS.hist m ∧ WE.hist m' = WE.hist m := by
  have hWb := two_box hW2
  obtain ⟨rIO, hIO, hIOoff, hrX⟩ := hu.rest
  have hg : rY.gh = rIO.gh := by
    have := congrArg Res.gh hrX; simpa [cellsAt, Word.cellsR] using this
  have hbk' := blk_ofG hi' hIO (by simp [cellsAt, Word.cellsR, hg])
  have hcs : ∀ l, BoxW l → ¬ W.In l → m'.heap l = m.heap l := by
    rintro ⟨b, x⟩ hl hw
    obtain ⟨h0, h1, h2⟩ := hl
    simp only at h0 h1 h2; subst h0
    refine cell_eq hu.blk hbk' hi' (by omega) ?_
    have := congrFun (congrArg Res.heap hrX) (0, x)
    simp only [FHeap.union_apply] at this ⊢
    rw [cellsAt_none hw, Option.none_or] at this ⊢
    rw [this, cellsAt_of (W := BoxW) ⟨rfl, h1, h2⟩, hIOoff _ ⟨rfl, h1, h2⟩, Option.or_none]
  have hrest := Rest.step hWb ⟨rIO, hIO, hIOoff, hrX⟩ rfl hY hcs
  have facts : ∀ W', Two W' → W'.Ok m' ∧ W'.hist m' = W'.hist m := by
    intro W' hW'
    rcases two_apart hW2 hW' with rfl | hap
    · exact ⟨hw', hh⟩
    · have hw : W'.Ok m := by
        rcases hW' with rfl | rfl
        · exact hu.ws
        · exact hu.we
      have hcover : ∀ l, W'.In l →
          (rsum (L.wordR m) (rsum (W.cellsR m) rY)).heap.erase l ≠ none :=
        fun l hl => frame_rest (rest_box hu.rest (fun _ => box_live hu) (two_box hW' l hl))
      have hnorm : ∀ l, W'.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm := by
        intro l hl
        rw [hcs l (two_box hW' l hl) (hap l hl)]
      exact ⟨hw.fstep hs hcover hnorm, Word.hist_fstep hw hs hcover hnorm⟩
  obtain ⟨hwS, hhS⟩ := facts _ (.inl rfl)
  obtain ⟨hwE, hhE⟩ := facts _ (.inr rfl)
  exact ⟨UM_frame_native hu hs
    (fun x hx => frame_rest (by simpa [FHeap.erase] using rest_io hu.rest hx))
    hrest hbk' hwS hwE hX, hhS, hhE⟩

/-! ## The threads -/

/-- The threads' shape after a step that keeps every program place. -/
theorem Shape.congr {Y Y' : ThreadId → Ph} {m m' : Mem} (h : Shape Y m)
    (hth : m'.threads = m.threads) (hY : Y' = Y) : Shape Y' m' := by
  subst hY; unfold Shape at *; rw [hth]; exact h

end SemCounter
end Zig
