import ZigLean.Conc.Word
import ZigLean.Sep.Full.LockRules

/-!
# A shared atomic word, over full-state resources

A word of a sync object that no thread owns (the state and the epoch of a condition, the state
of an event; `ZigLean/Conc/Word.lean`) is a part of the protocol's rest: its bytes are in the rest
as the memory's cells (`Word.cellsR W m = cellsAt W.In m`, `ZigLean/Sep/Full/ThreadRest.lean`),
so no thread's part has them and no step of a thread on its own part touches them. The facts about
the word's values and clocks (`Word.Ok`, `Word.hist`, the ops `Ok.load`, `Ok.rmw`, `Ok.cas`) are
facts of the memory model and stay in `ZigLean/Conc/Word.lean`. This file connects them to the
full-state lock (`FLock`, `ZigLean/Sep/Full/Lock.lean`):

- **An op at the word is a step at its bytes** (`Word.Op.rest`, a `RestStep`), so it keeps every
  part and the rest of the rest (`FOwned.restStep`), and it keeps a lock's invariant whose rest has
  the word's cells (`FLock.Inv.wordOp`).
- **A step of the lock's code keeps the word** (`Word.keep_lockWordStep`).
- **A step of a thread on its own part keeps the word** (`Word.keepK_fstep`): its frame has the
  word's cells, which stay up to `Cell.norm` (`FLock.Inv.cellsN`).
- **A futex wait at the word** by a thread out of the lock's code (`away`) keeps the lock's
  invariant (`FLock.Inv.waitOff`, `FLock.Inv.spuriousOff`); so does a futex wake at it
  (`FLock.Inv.wakeOff`).

A rest that has the word's cells of an older memory, the same up to `Cell.norm`, is the rest with
the word's cells of the new memory (`FLock.Inv.congrX`).

From `ZigLean/Conc/Word.lean` this file uses only facts of the memory model (`Word.Ok`, `Op`,
`Keep`, `KeepK`, `hist`, the op facts); it uses none of the legacy concurrent logic there or in
its imports (`Conc.Lock`, `Lock.Inv`, `Word.Apart`, `keep_lockStep`, `Lock.Inv.wordOp`,
`offWord`), which the full-state lock replaces.
-/

namespace Zig

namespace Conc
namespace Word

open Full

variable {n nb : Nat} (W : Word n nb)

/-- The byte `l` is a byte of the word. -/
def In (l : Zig.Loc) : Prop := l.1 = W.b ∧ W.o ≤ l.2 ∧ l.2 < W.o + nb

instance (l : Zig.Loc) : Decidable (W.In l) := by unfold In; infer_instance

/-- The word's cells, as a resource of the protocol's rest. -/
abbrev cellsR (m : Mem) : Res := cellsAt W.In m

/-- The lock's word and `W` do not overlap. -/
def ApartL (L : LockWord) : Prop := L.b ≠ W.b ∨ L.o + 4 ≤ W.o ∨ W.o + nb ≤ L.o

variable {W}

/-- The word's cells depend only on the blocks. -/
theorem cellsR_congr {m m' : Mem} (h : m'.blocks = m.blocks) : W.cellsR m' = W.cellsR m := by
  have : m'.heap = m.heap := by funext ⟨b, x⟩; simp only [Mem.heap, h]
  simp only [cellsR, cellsAt, this]

/-- A word apart from the lock's is at another place. -/
theorem ApartL.ne {L : LockWord} (hap : W.ApartL L) : L.b ≠ W.b ∨ L.o ≠ W.o := by
  have := W.sz_pos
  rcases hap with h | h | h
  · exact .inl h
  · exact .inr (by omega)
  · exact .inr (by omega)

/-- A 32-bit word apart from the lock's has another pointer. -/
theorem ApartL.ptr_ne {W : Word 32 4} {L : LockWord} (hap : W.ApartL L) : W.ptr ≠ L.ptr := fun e => by
  simp only [Word.ptr, LockWord.ptr, Ptr.mk.injEq, Option.some.injEq, Int.natCast_inj] at e
  rcases hap.ne with h | h
  · exact h e.1.symm
  · exact h e.2.symm

theorem cellKey_norm (c : Cell) : cellKey c.norm = cellKey c := by
  obtain ⟨b, a, s, k⟩ := c
  cases k <;> rfl

/-- The blocks after an op at the word, from the block of the word. -/
theorem BlkStep.eq_set {m m' : Mem} (h : W.BlkStep m m') {blk : Block}
    (hb : m.blocks[W.b]? = some blk) : ∃ blk', m'.blocks[W.b]? = some blk' ∧
      blk'.addr = blk.addr ∧ blk'.live = blk.live ∧ blk'.kind = blk.kind ∧
      blk'.bytes.size = blk.bytes.size ∧ m'.blocks = m.blocks.set! W.b blk' := by
  obtain ⟨blk', hb', ha, hl, hk, hs, -⟩ := h.word blk hb
  refine ⟨blk', hb', ha, hl, hk, hs, ?_⟩
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  apply Array.ext_getElem? fun i => ?_
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : W.b = i
  · subst e; simp [hlt, hb']
  · simp only [e, ↓reduceIte]; exact h.other i (Ne.symm e)

theorem keys_toList (m : Mem) : (keys m).toList = shapes m := by
  simp [keys, shapes, ALoc.shape]

/-- The bytes of the word are live in a memory where it is `Ok`. -/
theorem Ok.cellIn {m : Mem} (hw : W.Ok m) {l : Zig.Loc} (hl : W.In l) : m.heap l ≠ none := by
  obtain ⟨b, x⟩ := l
  obtain ⟨h1, h2, h3⟩ := hl
  simp only at h1 h2 h3; subst h1
  exact hw.cell h2 h3

/-- **An op at the word is a step at its bytes** (`RestStep`). -/
theorem Op.rest {t : ThreadId} {m m' : Mem} (hop : W.Op t m m') (hw : W.Ok m) (hw' : W.Ok m') :
    RestStep W.In m m' := by
  have hsz0 := W.sz_pos
  obtain ⟨blk, hb, hl, hsz, -, hk, -⟩ := hw.blk
  obtain ⟨blk', hb', ha', hl', hk', hs', hset⟩ := hop.blocks.eq_set hb
  have hlt : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  refine ⟨hop.threads, hop.csize, hop.clocks, hop.bsize, fun l hl => hop.cells l hl,
    fun l hl => hw'.cellIn hl, KMono.set hb ha' hk hset,
    KeepsExt.set hb hl' hs' hk' hset,
    fun hd => LDMono.set hb (fun h => by rw [← hl']; exact h) ha' (Nat.le_of_eq hs') hset
      (Nat.le_of_eq (by rw [hk'])) hd,
    fun b x hx => ?_, fun hwf => ?_, fun e he => ?_,
    MemAuth.Keep.set (m' := { m' with current := m.current }) hb hset hl' ha' hs' hk' hop.aux.1
      (by rw [hop.aux.2.1]) hop.aux.2.2, hop.cov⟩
  · rcases hop.atoms with e | ⟨e, -⟩
    · rw [← keys_toList, e, keys_toList]
    · rw [← keys_toList, e, Array.toList_push, keys_toList, tagOf_append_single]
      have : ¬ Full.Covers b x (W.b, W.o, nb) := fun ⟨h1, h2, h3⟩ => hx ⟨h1.symm, h2, h3⟩
      simp [this]
  · rcases hop.atoms with e | ⟨e, hno⟩
    · rw [← keys_toList, e, keys_toList]; exact hwf
    · rw [← keys_toList, e, Array.toList_push, keys_toList]
      refine ⟨fun s hs => ?_, List.pairwise_append.mpr ⟨hwf.2, by simp, fun a ha b hb => ?_⟩⟩
      · rcases List.mem_append.mp hs with h | h
        · exact hwf.1 s h
        · simp at h; subst h; exact hsz0
      · simp at hb; subst hb
        obtain ⟨l, hlm, rfl⟩ : ∃ l ∈ m.atomics, ALoc.shape l = a := by
          simpa [shapes] using ha
        intro hlb
        simp only [ALoc.shape] at hlb ⊢
        by_cases h1 : l.off < W.o + nb
        · by_cases h2 : W.o < l.off + l.len
          · exact absurd ⟨hlb, hw.only l hlm hlb h1 h2⟩ (hno l hlm)
          · exact .inl (by omega)
        · exact .inr (by omega)
  · rcases hop.fp e he with h | ⟨h1, h2, h3, -, -⟩
    · exact .inl h
    · refine .inr ⟨fun x hx1 hx2 => ⟨h1, by omega, by omega⟩, by
        rw [h1]; exact hlt⟩

/-- **A step of the lock's code keeps a word apart from the lock's.** -/
theorem keep_lockWordStep {L : LockWord} {t : ThreadId} {m m' : Mem} (hs : L.Step t m m')
    (hap : W.ApartL L) : W.Keep m m' := by
  have hsz0 := W.sz_pos
  refine ⟨fun x h1 h2 => hs.heap ?_, fun i l => ?_, fun l hl => ?_, fun e he => ?_,
    fun _ h => hs.allLe h, fun _ h => hs.someLe h⟩
  · rintro ⟨hb, h3, h4⟩; simp only at hb h3 h4
    rcases hap with h | h | h
    · exact h hb.symm
    · omega
    · omega
  · exact hs.locs.same W.b W.o (hap.ne.imp Ne.symm Ne.symm) i l
  · rcases hs.locs.new l hl with h | ⟨hb, ho, hlen⟩
    · exact .inl h
    · rcases hap with h | h | h
      · exact .inr (.inl (by rw [hb]; exact h))
      · exact .inr (.inr (.inl (by omega)))
      · exact .inr (.inr (.inr (by omega)))
  · rcases hs.fp e he with h | ⟨hb, ho, hl, -⟩
    · exact .inl h
    · refine .inr fun ⟨hb', x, h1, h2, h3, h4⟩ => ?_
      rw [hb] at hb'
      rcases hap with h | h | h
      · exact h hb'
      · omega
      · omega

/-- The word's location stays under an atomic-location map whose frame has the word's bytes. -/
theorem loc_amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (ha : AMap hF m m' σ)
    (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb) (l : ALoc) :
    (∃ i, W.Loc m' i l) ↔ (∃ i, W.Loc m i l) := by
  have := W.sz_pos
  refine (ha.first_iff (p := fun l => l.block == W.b && l.off == W.o)
    (fun l l' hb ho _ => by simp [hb, ho]) (fun i l hfi hl x h1 h2 => ?_)
    (fun l hp hpos => ⟨l.off, Nat.le_refl _, by omega, ?_⟩) l).symm
  · have hlen := hok i l ⟨hfi, hl⟩
    have hp : (l.block == W.b && l.off == W.o) = true := by
      have := Array.of_findIdx?_eq_some hfi; rw [hl] at this; exact this
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hb, ho⟩ := hp
    rw [hb]; exact hwF _ ⟨rfl, by omega, by omega⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, hp.2]; exact hwF _ ⟨rfl, Nat.le_refl _, by omega⟩

/-- **The word's location stays** over a step whose frame `hF` has the word (`FStepIn`): the
word's location (if any) has the word's bytes (`hok`), so it is in the frame. -/
theorem loc_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb) (l : ALoc) :
    (∃ i, W.Loc m' i l) ↔ (∃ i, W.Loc m i l) := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact loc_amap ha hwF hok l

/-- **A step of a thread on its own part keeps the word** (`FStepIn`): its frame `hF` has the
word's bytes, the word's location has them (`hok`), and the word's cells stay up to `Cell.norm`
(`FLock.Inv.cellsN`). -/
theorem keepK_fstep {m m' : Mem} {hF : Heap}
    (hs : FStepIn hF m m') (hwF : ∀ l, W.In l → hF l ≠ none) (hok : ∀ i l, W.Loc m i l → l.len = nb)
    (hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    W.KeepK m m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hs.clock
  obtain ⟨σ, ha⟩ := hs.atomics
  refine ⟨fun x h1 h2 => ?_, loc_fstep hs hwF hok, fun l hl => ?_, fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u (hs.threads ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hs.threads ▸ hu, VClock.le_trans hle (hcl u)⟩⟩
  · have := congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)
    simpa [Option.map_map, Function.comp_def, cellKey_norm] using this
  · rcases ha.mem hl with h | ⟨hpos, hoff⟩
    · exact .inl h
    · refine .inr (Classical.byContradiction fun hc => ?_)
      simp only [not_or, Nat.not_le, ne_eq, Classical.not_not] at hc
      obtain ⟨hb, h1, h2⟩ := hc
      have := W.sz_pos
      have hx := hoff (if W.o ≤ l.off then l.off else W.o) (by split <;> omega)
        (by split <;> omega)
      rw [hb] at hx
      exact hwF _ ⟨rfl, by split <;> omega, by split <;> omega⟩ hx
  · rcases hs.fp e he with h | ⟨-, hnt, -⟩
    · exact .inl h
    · exact .inr fun hh => hnt (touches_of hh fun x h1 h2 => hwF _ ⟨rfl, h1, h2⟩)

/-! ### The memory facts of an op, for the steps of a sync object's code

A step of a futex-based sync object's code (`FEvent.MStep`, `FCond.MStep`) is an op at one of
its words, a futex wait's sleep (an op that keeps the word's writes, then a new waiter), or a
change of the current thread, the futex queue or the woken threads only. The lemmas
`FEvent.MStep.*` and `FCond.MStep.*` give what such a step does to the memory, from these facts of
an op. -/

/-- The block `b` after an op at the word: as live, as large and of the same kind. -/
theorem Op.block {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {b : BlockId} {blk : Block}
    (hb : m.blocks[b]? = some blk) : ∃ blk', m'.blocks[b]? = some blk' ∧ blk'.live = blk.live ∧
      blk'.bytes.size = blk.bytes.size ∧ blk'.kind = blk.kind := by
  by_cases e : b = W.b
  · subst e
    obtain ⟨blk', h1, -, h2, h3, h4, -⟩ := h.blocks.word blk hb
    exact ⟨blk', h1, h2, h4, h3⟩
  · exact ⟨blk, by rw [h.blocks.other b e]; exact hb, rfl, rfl, rfl⟩

/-- An op at the word keeps the atomic location of a lock's word apart from it. -/
theorem Op.lockLoc {t : ThreadId} {m m' : Mem} (h : W.Op t m m') {L : LockWord}
    (hap : W.ApartL L) {i : Nat} {l : ALoc} (hl : L.Loc m i l) : L.Loc m' i l :=
  (h.locs.same _ _ hap.ne i l).mpr hl

/-- An op at the word: a new access is at the word. -/
theorem Op.fpAt {t : ThreadId} {m m' : Mem} (h : W.Op t m m') :
    ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ (e.block = W.b ∧ e.off = W.o) := fun e he =>
  (h.fp e he).imp id fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩

/-- An op at the word keeps a word `W'` apart from it that is valid before: valid after it,
with the same writes. -/
theorem Op.word {n' nb' : Nat} {W' : Word n' nb'} {t : ThreadId} {m m' : Mem} (h : W.Op t m m')
    (hok : W'.Ok m) (hap : W.b ≠ W'.b ∨ W.o + nb ≤ W'.o ∨ W'.o + nb' ≤ W.o) :
    W'.Ok m' ∧ W'.hist m' = W'.hist m :=
  ⟨hok.keep (keep_op h hap), hist_keep hok (keep_op h hap)⟩

/-- A change of the futex queue keeps every word. -/
theorem keep_waiters (m : Mem) (ws : Array (ThreadId × Ptr)) : W.Keep m { m with waiters := ws } :=
  keep_of rfl rfl rfl rfl fun _ => VClock.le_refl _

end Word
end Conc

namespace Full

open FAssn Conc Proto

namespace FLock

variable {γ : Type} {L : FLock γ} {n nb : Nat} {W : Word n nb}

/-- A rest with the same bytes up to `Cell.norm` and the same knowledge and ghost state. -/
theorem Inv.congrX {G : ThreadId → γ} {rX rX' : Res} {m : Mem} (hi : L.Inv G rX m)
    (hs : FHeap.Sim rX'.heap rX.heap) (hk : rX'.know = rX.know) (hg : rX'.gh = rX.gh) :
    L.Inv G rX' m := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hn : ∀ l, rX'.heap l = none ↔ rX.heap l = none := fun l => hs.none
  refine ⟨hi.w, ⟨rL, ho.congrRest (fun l => ?_) (by simp [hk]) (by simp [hg]), hLoff,
    fun l => (hLX l).imp id (fun h => (hn l).mpr h), hF, hnF⟩,
    LockWord.off_erase.mpr fun l hl => (hn l).mpr (LockWord.off_erase.mp hi.xoff l hl), hi.pdisj,
    hi.idle, hi.res⟩
  have := hs l
  simp only [FHeap.union_apply]
  cases (L.wordR m).heap l <;> cases rL.heap l <;> simp_all

/-- A byte of the rest is the memory's, up to `Cell.norm`. -/
theorem Inv.restCell {G : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m) {l : Zig.Loc}
    {fc : FCell} (hl : rX.heap l = some fc) : (m.heap l).map Cell.norm = some fc.cell.norm := by
  obtain ⟨rL, ho, -, hLX, -⟩ := hi.rest
  have hrL : rL.heap l = none := (hLX l).resolve_right (by simp [hl])
  have hwr : (L.wordR m).heap l = none := by
    by_cases hin : L.In l
    · have := LockWord.off_erase.mp hi.xoff l hin
      simp [hl] at this
    · exact cellsAt_none hin
  exact ho.rest_cell (by simp only [FHeap.union_apply, hl, hwr, hrL, Option.none_or])

/-- **Bytes of the rest are the memory's**: a part `r` of the rest with the bytes `bs` at `p`
(`0 < bs.size`): `p`'s block holds `bs` there. -/
theorem Inv.restBytes {G : ThreadId → γ} {rX r : Res} {m : Mem} (hi : L.Inv G rX m) {p : Ptr}
    {A S : Nat} {K : BlockKind} {bs : Array Byte} {b : BlockId} (hp : up (bytesAt p A S K bs) r)
    (hpb : p.block = some b) (hsub : ∀ l fc, r.heap l = some fc → rX.heap l = some fc)
    (hpos : 0 < bs.size) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.bytes.extract p.off.toNat (p.off.toNat + bs.size) = bs := by
  have cell : ∀ j (hj : j < bs.size), ∃ blk, m.blocks[b]? = some blk ∧
      blk.bytes[p.off.toNat + j]? = some bs[j] := by
    intro j hj
    obtain ⟨fc, hfc, hc⟩ := up_bytesAt_cell hp hpb hj
    have hn := hi.restCell (hsub _ _ hfc)
    cases e : m.heap (b, p.off.toNat + j) with
    | none => rw [e] at hn; cases hn
    | some c =>
      rw [e] at hn
      obtain ⟨blk, hb, -, hx, rfl⟩ := Mem.heap_some e
      have hbyte := congrArg Cell.byte (Option.some.inj hn)
      simp only [Cell.norm, hc] at hbyte
      exact ⟨blk, hb, by rw [Array.getElem?_eq_getElem hx, hbyte, getElem!_pos bs j hj]⟩
  obtain ⟨blk, hb, -⟩ := cell 0 hpos
  obtain ⟨blk', hb', hlast⟩ := cell (bs.size - 1) (by omega)
  rw [hb] at hb'; cases hb'
  have hlt := (Array.getElem?_eq_some_iff.mp hlast).1
  refine ⟨blk, hb, Array.ext (by simp only [Array.size_extract]; omega) fun j h1 h2 => ?_⟩
  obtain ⟨blk', hb', hx⟩ := cell j h2
  rw [hb] at hb'; cases hb'
  simp only [Array.getElem_extract]
  exact (Array.getElem?_eq_some_iff.mp hx).2

/-- The word's cells of the rest are the memory's, up to `Cell.norm`. -/
theorem Inv.cellsN {G : ThreadId → γ} {rY : Res} {m₀ m : Mem}
    (hi : L.Inv G (rsum (W.cellsR m₀) rY) m) {l : Zig.Loc} (hl : W.In l)
    (h0 : m₀.heap l ≠ none) : (m.heap l).map Cell.norm = (m₀.heap l).map Cell.norm := by
  cases e : m₀.heap l with
  | none => exact absurd e h0
  | some c =>
    rw [hi.restCell (fc := ⟨c, none⟩) (by simp [FHeap.union_apply, cellsAt_of hl, e])]; rfl

/-- **An op at a shared word apart from the lock's keeps the lock's invariant**, whose rest has
the word's cells: the rest gets the word's new cells. -/
theorem Inv.wordOp {G : ThreadId → γ} {rY : Res} {t : ThreadId} {m m' : Mem}
    (hi : L.Inv G (rsum (W.cellsR m) rY) m) (hWY : ∀ l, W.In l → rY.heap l = none) (hw : W.Ok m)
    (hw' : W.Ok m') (hop : W.Op t m m') (hap : W.ApartL L.toLockWord) :
    L.Inv G (rsum (W.cellsR m') rY) m' := by
  have hsz0 := W.sz_pos
  have hjb : joinedB m' = joinedB m := LockWord.joinedB_congr hop.threads
  have hown : L.own G m' = L.own G m := by funext u; unfold FLock.own; rw [hjb]
  have hnw : ∀ l, L.In l → ¬ W.In l := by
    rintro ⟨b, x⟩ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩; simp only at h1 h2 h3 h4 h5 h6
    rcases hap with h | h | h
    · exact h (h1.symm.trans h4)
    · omega
    · omega
  have hLcells : ∀ x, L.o ≤ x → x < L.o + 4 → m'.heap (L.b, x) = m.heap (L.b, x) :=
    fun x h1 h2 => hop.cells _ (hnw _ ⟨rfl, h1, h2⟩)
  obtain ⟨hblk', hcur⟩ := LockWord.word_congr hLcells hi.w.blk
  have hU32 : ∀ v, L.U32 m' v ↔ L.U32 m v := fun v => by unfold LockWord.U32; rw [hcur]
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hap.ne i l
  have hWb : W.b < m.blocks.size := by
    obtain ⟨blk, hb, -⟩ := hw.blk; exact (Array.getElem?_eq_some_iff.mp hb).1
  have hcl : ∀ u < m.threads.size, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true :=
    fun u _ => hop.clocks u
  -- a new access is at the word, so it does not touch the lock's word
  have hnL : ∀ e ∈ m'.footprint, e ∉ m.footprint → ¬ L.Hits e := by
    intro e he hn ⟨hb, x, h1, h2, h3, h4⟩
    rcases hop.fp e he with h' | ⟨hb', ho, hl, -⟩
    · exact hn h'
    · rw [hb'] at hb; rw [ho] at h1; rw [ho, hl] at h2
      rcases hap with h | h | h
      · exact h hb.symm
      · omega
      · omega
  have hwi : L.WInv (L.pl G) m' := by
    refine ⟨by rw [hop.csize, hop.threads]; exact hi.w.csize, fun u hu => ?_, hblk', ?_, hi.w.one,
      ⟨fun l hl hb h1 h2 => ?_, fun i l hl => ?_, fun i l hl => ?_⟩, fun e he hh => ?_,
      fun i l hl => ?_, by rw [hop.waiters]; exact hi.w.fq, fun hp => ?_,
      fun u hu => let ⟨i, l, hl, hw⟩ := hi.w.owner u hu; ⟨i, l, (hloc i l).mpr hl, hw⟩⟩
    · rw [hop.threads, hjb]; exact hi.w.live u hu
    · obtain ⟨w, hw', hu, hz⟩ := hi.w.word; exact ⟨w, hw', (hU32 _).mpr hu, hz⟩
    · rcases hop.locs.new l hl with h | ⟨hb', ho, hlen⟩
      · exact hi.w.loc.only l h hb h1 h2
      · rw [ho] at h1; rw [ho, hlen] at h2; rw [hb'] at hb
        rcases hap with h | h | h
        · exact absurd hb.symm h
        · omega
        · omega
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hi.w.loc.ok i l ((hloc i l).mp hl)
      exact ⟨h1, h2, h3, h4, by rw [h5, hcur]⟩
    · exact (hi.w.loc.plain i l ((hloc i l).mp hl)).of_fp fun e he =>
        (hop.fp e he).imp id fun h => plainHit_atomic h.2.2.2.1
    · by_cases hm : e ∈ m.footprint
      · rcases hi.w.wfp e hm hh with ⟨ha, hs⟩ | ha
        · exact .inl ⟨ha, LockWord.someLe_mono hop.threads hcl hs⟩
        · exact .inr (LockWord.LiveLe.mono hop.threads hcl ha)
      · exact absurd hh (hnL e he hm)
    · obtain ⟨h1, h2⟩ := hi.w.rel i l ((hloc i l).mp hl)
      exact ⟨LockWord.someLe_mono hop.threads hcl h1,
        fun u hu => VClock.le_trans (h2 u hu) (hop.clocks u)⟩
    · obtain ⟨v, hv, hq, h1, h2⟩ := hi.w.wit (hop.waiters ▸ hp)
      exact ⟨v, hop.threads ▸ hv, hop.waiters ▸ hq, h1, fun hh => (hU32 _).mpr (h2 hh)⟩
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  -- the rest as `cells W ⋆ (word ⋆ (rL ⋆ rY))`
  have hWw : FHeap.Disjoint (W.cellsR m).heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  have hXY := FHeap.disjoint_union_right.mp hLX
  -- `rL` has no byte of the word
  have hLW : ∀ l, W.In l → rL.heap l = none := fun l hl =>
    (hXY.1 l).resolve_right (cellsAt_some hl (hw.cellIn hl))
  have hLW' : FHeap.Disjoint rL.heap (W.cellsR m').heap := fun l => by
    by_cases hl : W.In l
    · exact .inl (hLW l hl)
    · exact .inr (cellsAt_none hl)
  have hWw' : FHeap.Disjoint (W.cellsR m').heap (L.wordR m).heap := fun l => by
    by_cases hl : W.In l
    · exact .inr (cellsAt_none fun h => hnw l h hl)
    · exact .inl (cellsAt_none hl)
  -- regroup `word ⋆ (rL ⋆ (C ⋆ rY))` as `C ⋆ (word ⋆ (rL ⋆ rY))`
  have regroup : ∀ C : Res, FHeap.Disjoint C.heap (L.wordR m).heap → FHeap.Disjoint rL.heap C.heap →
      rsum (L.wordR m) (rsum rL (rsum C rY)) = rsum C (rsum (L.wordR m) (rsum rL rY)) := by
    intro C h1 h2
    rw [← rsum_assoc (a := rL), rsum_comm h2, rsum_assoc, ← rsum_assoc (a := L.wordR m),
      rsum_comm h1.symm, rsum_assoc]
  have hwR : L.wordR m' = L.wordR m := by
    simp only [LockWord.wordR, cellsAt]
    congr 1; funext ⟨b, x⟩
    split
    · rename_i hl; obtain ⟨h1, h2, h3⟩ := hl; simp only at h1 h2 h3; subst h1
      rw [hLcells x h2 h3]
    · rfl
  rw [regroup _ hWw hXY.1] at ho
  have ho' := ho.restStep (hop.rest hw hw') (fun l hl => hw.cellIn hl) (fun l hl => by
    simp only [FHeap.union_apply, cellsAt_none (fun h => hnw l h hl), hLW l hl, hWY l hl]; rfl)
  rw [← regroup _ hWw' hLW', ← hwR, ← hown] at ho'
  refine ⟨hwi, ⟨rL, ho', hLoff, FHeap.disjoint_union_right.mpr ⟨hLW', hXY.2⟩, fun hF' => ?_, hnF⟩,
    LockWord.off_erase.mpr fun l hl => ?_, hi.pdisj, hi.idle, hi.res⟩
  · obtain ⟨hR, hO⟩ := hF hF'
    refine ⟨hR, fun e he htc => ?_⟩
    by_cases hm : e ∈ m.footprint
    · rcases hO e hm (htc.imp id fun h => by rw [← hop.bsize]; exact h) with h | ⟨i, l, hl, hle⟩
      · exact .inl (LockWord.LiveLe.mono hop.threads hcl h)
      · exact .inr ⟨i, l, (hloc i l).mpr hl, hle⟩
    · rcases hop.fp e he with h | ⟨hb, heo, hlen, -⟩
      · exact absurd h hm
      · rcases htc with ⟨x, h1, h2, h3⟩ | hbe
        · rw [hb] at h3; rw [heo] at h1; rw [heo, hlen] at h2
          exact absurd (by simp [FHeap.erase, hLW (W.b, x) ⟨rfl, h1, by omega⟩]) h3
        · rw [hb, hop.bsize] at hbe; exact absurd hWb (Nat.not_lt.mpr hbe)
  · have := LockWord.off_erase.mp hi.xoff l hl
    simp only [FHeap.union_apply, Option.or_eq_none_iff]
      at this ⊢
    exact ⟨cellsAt_none fun h => hnw l hl h, this.2⟩

/-! ## A futex wait and a futex wake at the word -/

/-- The same memory, but `current`, the futex queue and the woken threads, with ghost values `G'`
whose word invariant holds there and that have the same parts, resources and holders. -/
theorem Inv.requeue {G G' : ThreadId → γ} {rX : Res} {m : Mem} (hi : L.Inv G rX m)
    (c : ThreadId) (ws : Array (ThreadId × Ptr)) (wk : Array ThreadId)
    (hw : L.WInv (L.pl G') { m with current := c, waiters := ws, woken := wk })
    (hpart : ∀ u, L.part (G' u) = L.part (G u)) (hheld : ∀ u, L.held (G' u) = L.held (G u))
    (hholds : ∀ u, L.ph (G' u) = .holds ↔ L.ph (G u) = .holds)
    (hg : ∀ u, L.ph (G' u) ≠ .gone → L.ph (G u) ≠ .gone) (hR : ∀ r, L.R G r ↔ L.R G' r) :
    L.Inv G' rX { m with current := c, waiters := ws, woken := wk } := by
  obtain ⟨rL, ho, hLoff, hLX, hF, hnF⟩ := hi.rest
  have hown : L.own G' { m with current := c, waiters := ws, woken := wk } = L.own G m := by
    funext u; unfold FLock.own; rw [hpart, hheld]; rfl
  have hfree := free_iff_of (L := L) hholds
  refine ⟨hw, ⟨rL, ?_, hLoff, hLX, fun hF' => ?_, fun h => hnF fun h' => h (hfree.mpr h')⟩,
    hi.xoff, fun u => by rw [hpart, hheld]; exact hi.pdisj u,
    fun u hu => by rw [hheld]; exact hi.idle u ((not_congr (hholds u)).mp hu),
    fun u hu => by rw [hheld]; exact (hR _).mp (hi.res u ((hholds u).mp hu))⟩
  · rw [hown]
    have : LockWord.wordR L.toLockWord { m with current := c, waiters := ws, woken := wk } =
        L.wordR m := rfl
    rw [this]; exact ho.keep rfl rfl rfl rfl rfl
  · obtain ⟨h1, h2⟩ := hF (hfree.mp hF')
    exact ⟨(hR _).mp h1, (h2.weaken hg).mono rfl rfl rfl (fun _ => VClock.le_refl _)
      fun e he => .inl he⟩

/-- Thread `t`, which does not hold the lock, goes to `out` at a stop (`current := t`) where the
word's invariant holds with `t` at `out`. -/
theorem Inv.toOut {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId} (hi : L.Inv G rX m)
    (hc : m.current = t) (hnh : L.ph (G t) ≠ .holds) (hng : L.ph (G t) ≠ .gone)
    (hw : L.WInv (upd (L.pl G) t .out) m) :
    L.Inv (upd G t (L.set (G t) .out rnil)) rX m := by
  have hupd : ∀ u, L.ph (upd G t (L.set (G t) .out rnil) u) = if u = t then .out else L.ph (G u) :=
    fun u => by unfold upd; split <;> simp [L.ph_set]
  have := hi.requeue m.current m.waiters m.woken (G' := upd G t (L.set (G t) .out rnil))
    (by rw [pl_upd_set]; exact hw)
    (fun u => by
      unfold upd; split
      · rename_i e; subst e; rw [L.part_set]
      · rfl)
    (fun u => by
      unfold upd; split
      · rename_i e; subst e; rw [L.held_set, hi.idle _ hnh]
      · rfl)
    (fun u => by rw [hupd]; split <;> simp_all)
    (fun u hu => by rw [hupd] at hu; split at hu <;> simp_all)
    (fun r => by rw [L.R_set])
  exact this

/-- A futex wait of thread `t` (`away`, not in the queue) at a shared word `W` (its bytes in the
protocol's rest, apart from the lock's word). If it sleeps, the lock's invariant holds with `t` in
the queue; else `t` goes to `out`. -/
theorem Inv.waitOff {W : Word 32 4} {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    {e : BitVec 32} {b : Bool} (hi : L.Inv G rX m) (hph : L.ph (G t) = .away) (hW : W.Ok m)
    (hap : W.ApartL L.toLockWord) (hX : ∀ l, W.In l → rX.heap l ≠ none)
    (hq : m.waiters.any (·.1 == t) = false)
    (h : ((Thread.futexWait W.ptr e).run { m with current := t }).run = some (.ok (b, m'))) :
    if b then L.Inv G rX m' else
      (m'.current = t ∧ L.Inv (upd G t (L.set (G t) .out rnil)) rX m') := by
  have hng : L.ph (G t) ≠ .gone := by rw [hph]; decide
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  obtain ⟨ht, -⟩ := hi.ht hng
  obtain ⟨blk₀, hb₀, -, -, ha₀, -⟩ := hW.access
  have hWb : W.b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb₀).1
  have hoff : ∀ bid blk o, m.access W.ptr 4 4 = pure (bid, blk, o) →
      bid ≠ L.b ∨ o + 4 ≤ L.o ∨ L.o + 4 ≤ o := fun bid blk o ha => by
    rw [ha₀] at ha; cases ha
    rcases hap with h | h | h
    · exact .inl (Ne.symm h)
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  have hw := hi.w.waitOff (t := t) (by exact hph) hap.ptr_ne hoff hq h
  -- the relabel of `t` from `away` to `out`, at a memory with the same parts
  have hrel : ∀ M : Mem, L.Inv G rX M → M.current = t →
      L.WInv (upd (L.pl G) t .out) M → L.Inv (upd G t (L.set (G t) .out rnil)) rX M :=
    fun _ hiM hc hwM => hiM.toOut hc hnh hng hwM
  rcases futexWait_eq h with ⟨-, rfl, rfl⟩ | ⟨-, bid, blk, o, v, ha, -, -, hc⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact ⟨by first | rfl | trivial, hrel _ (hi.requeue t m.waiters _ (hi.w.same t m.seen m.nextMsg _ |>.groups m.groups)
      (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h) (fun _ => Iff.rfl)) rfl hw.2⟩
  have ha' : m.access W.ptr 4 4 = pure (bid, blk, o) := ha
  rw [ha₀] at ha'; cases ha'
  have hiR : L.Inv G rX (({ m with current := t } : Mem).recordAt W.b W.o 4 .atomicRead) :=
    (hi.cur t).recordX (by decide) rfl ht hWb (by decide)
      (fun x h1 h2 => hX _ ⟨rfl, h1, h2⟩)
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · simp only [↓reduceIte] at hw ⊢
    exact hiR.requeue t _ _ hw (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h)
      (fun _ => Iff.rfl)
  · simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact ⟨hw.1, hrel _ hiR rfl hw.2⟩

/-- A spurious return of a futex wait of thread `t` (`away`, not in the queue) at a shared word:
`t` goes to `out` with the memory before the wait. -/
theorem Inv.spuriousOff {G : ThreadId → γ} {rX : Res} {m : Mem} {t : ThreadId}
    (hi : L.Inv G rX m) (hph : L.ph (G t) = .away) (hq : m.waiters.any (·.1 == t) = false) :
    L.Inv (upd G t (L.set (G t) .out rnil)) rX { m with current := t } :=
  (hi.cur t).toOut rfl (by rw [hph]; decide) (by rw [hph]; decide) (hi.w.spuriousOff (t := t) (by exact hph) hq).2

/-- A futex wake by thread `t` at a shared word apart from the lock's: the lock's invariant
holds. -/
theorem Inv.wakeOff {W : Word 32 4} {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    {k : Nat} {cs : List Nat} (hi : L.Inv G rX m) (hap : W.ApartL L.toLockWord)
    (h : ((Thread.futexWake W.ptr k cs).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Inv G rX m' := by
  have hw := hi.w.wakeOff hap.ptr_ne h
  have hm' := Proto.modify_ok h
  subst hm'
  exact hi.requeue t _ _ hw (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h)
    (fun _ => Iff.rfl)

end FLock

end Full
end Zig

/-! ## Per-thread observed-message floors

The floor is a position in the word's history, derived from `Mem.seen` and distinct
message ids. Reads may advance it; steps disjoint from the framed word preserve it,
including when retiring another location reindexes the word. These are memory-model
facts for the full-state protocol library, not additional client assumptions. -/

namespace Zig
namespace Conc
namespace Word

open Proto

variable {n nb : Nat} {W : Word n nb}

variable (W) in
/-- Thread `u`'s floor at the word (module doc): the position of the message of the word's
location that `u` read or wrote last (`Mem.seenAt`); `0` without one. -/
def ownPos (m : Mem) (u : ThreadId) : Nat :=
  match m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i => ((m.seenAt u i).bind (m.atomics[i]!).pos).getD 0
  | none => 0

variable (W) in
/-- The word's messages have distinct ids, each below the message counter. -/
def Fresh (m : Mem) : Prop :=
  ∀ i l, W.Loc m i l → ∀ j (hj : j < l.msgs.size),
    l.msgs[j].id < m.nextMsg ∧ l.pos l.msgs[j].id = some j

theorem ownPos_loc {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (u : ThreadId) :
    W.ownPos m u = ((m.seenAt u i).bind l.pos).getD 0 := by
  unfold ownPos; rw [hl.1]; simp only; rw [(loc_get hl).2.2]

theorem ownPos_none {m : Mem} (h : ∀ i l, ¬ W.Loc m i l) (u : ThreadId) : W.ownPos m u = 0 := by
  unfold ownPos
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | none => rfl
  | some i => exact absurd (loc_of_find hf) (h _ _)

/-- The same locations and views: the same floors. -/
theorem ownPos_of_eq {m m' : Mem} (ha : m'.atomics = m.atomics) (hs : m'.seen = m.seen)
    (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  unfold ownPos Mem.seenAt; rw [ha, hs]

theorem Fresh.of_eq {m m' : Mem} (hf : W.Fresh m) (ha : m'.atomics = m.atomics)
    (hn : m.nextMsg ≤ m'.nextMsg) : W.Fresh m' := fun i l hl j hj =>
  let ⟨h1, h2⟩ := hf i l (by unfold Loc at hl ⊢; rwa [ha] at hl) j hj
  ⟨Nat.lt_of_lt_of_le h1 hn, h2⟩

/-- **Thread `t`'s floor is at most where its next read may read** (`floorPos`). -/
theorem ownPos_le_floor {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) :
    W.ownPos m m.current ≤ floorPos m i := by
  rw [ownPos_loc hl]
  refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_max_right _ _)
  rw [← (loc_get hl).2.2]
  split
  · rename_i id heq
    have hs : m.seenAt m.current i = some id := by
      unfold Mem.seenAt; exact (congrArg (Option.map (·.2.2)) heq : _)
    rw [hs]; rfl
  · rename_i heq
    have hs : m.seenAt m.current i = none := by
      unfold Mem.seenAt; exact (congrArg (Option.map (·.2.2)) heq : _)
    rw [hs]; rfl

/-! ## Steps that keep the word -/

/-- The word's location is found by its block and offset alone. -/
theorem pred_congr (l l' : ALoc) (hb : l.block = l'.block) (ho : l.off = l'.off)
    (_ : l.len = l'.len) :
    (l.block == W.b && l.off == W.o) = (l'.block == W.b && l'.off == W.o) := by
  simp [hb, ho]

/-- The word's location (of the word's size, `hok`) lies in a frame that has the word's bytes,
and every location at the word has a byte of it. -/
theorem frame_has {m : Mem} {hF : Heap}
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) :
    (∀ i l, m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) = some i →
      m.atomics[i]? = some l → l.In hF) ∧
    (∀ l : ALoc, (l.block == W.b && l.off == W.o) = true → 0 < l.len →
      ∃ x, l.off ≤ x ∧ x < l.off + l.len ∧ hF (l.block, x) ≠ none) := by
  have := W.sz_pos
  refine ⟨fun i l hfi hl x h1 h2 => ?_, fun l hp hpos => ⟨l.off, Nat.le_refl _, by omega, ?_⟩⟩
  · have hL : W.Loc m i l := ⟨hfi, hl⟩
    obtain ⟨hb, ho⟩ := loc_at hL
    have hlen := hok i l hL
    rw [hb]; exact hwF x (by omega) (by omega)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hp.1, hp.2]; exact hwF W.o (Nat.le_refl _) (by omega)

/-- Atomic-location transport keeps every thread's floor at a fully framed word, independently
of changes to queues, the OS state or the selected current thread. -/
theorem ownPos_amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (ha : AMap hF m m' σ)
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  obtain ⟨hin, hcov⟩ := frame_has hwF hok
  cases hf : m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find hf
    obtain ⟨j, hij, hl'⟩ := ha.frame i _ hl.2 (hin i _ hf hl.2)
    have hL' : W.Loc m' j (m.atomics[i]!) := ⟨ha.first_eq pred_congr hin hcov hf hij, hl'⟩
    rw [ownPos_loc hl, ownPos_loc hL', ha.seenAt_frame hl.2 (hin i _ hf hl.2) hij u]
  | none =>
    have hn : ∀ i l, ¬ W.Loc m i l := fun i l hl => by rw [hl.1] at hf; cases hf
    refine (ownPos_none (fun j l hl => ?_) u).trans (ownPos_none hn u).symm
    obtain ⟨i, hi⟩ := (ha.first_iff pred_congr hin hcov l).mpr ⟨j, hl⟩
    exact hn i l hi

/-- **A step of a thread on its own part keeps every thread's floor** at a word whose bytes its
frame has (`FStepIn`; `hok`: the word's location has the word's size, as under `Word.Ok`). -/
theorem ownPos_fstep {m m' : Mem} {hF : Heap} (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) (u : ThreadId) : W.ownPos m' u = W.ownPos m u := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact ownPos_amap ha hwF hok u

/-- Atomic-location transport and a nondecreasing message counter preserve framed freshness. -/
theorem Fresh.amap {m m' : Mem} {hF : Heap} {σ : Nat → Option Nat} (hf : W.Fresh m)
    (ha : AMap hF m m' σ) (hn : m.nextMsg ≤ m'.nextMsg)
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) : W.Fresh m' := by
  intro j l hl k hk
  obtain ⟨i, hi⟩ := (loc_amap ha
    (fun ⟨b, x⟩ hx => by
      obtain ⟨hb, h1, h2⟩ := hx
      change b = W.b at hb
      change hF (b, x) ≠ none
      rw [hb]
      exact hwF x h1 h2) hok l).mp ⟨j, hl⟩
  obtain ⟨h1, h2⟩ := hf i l hi k hk
  exact ⟨Nat.lt_of_lt_of_le h1 hn, h2⟩

theorem Fresh.fstep {m m' : Mem} {hF : Heap} (hf : W.Fresh m) (hs : FStepIn hF m m')
    (hwF : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) ≠ none)
    (hok : ∀ i l, W.Loc m i l → l.len = nb) : W.Fresh m' := by
  obtain ⟨σ, ha⟩ := hs.atomics
  exact hf.amap ha hs.nextMsg hwF hok

/-! ## The ops at the word -/

/-- A floor is a position of a nonempty location, including the default position zero. -/
theorem ownPos_lt {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l)
    (h0 : 0 < l.msgs.size) (u : ThreadId) : W.ownPos m u < l.msgs.size := by
  rw [ownPos_loc hl]
  cases hs : m.seenAt u i with
  | none => exact h0
  | some id =>
    simp only [Option.bind_some]
    cases hp : l.pos id with
    | none => exact h0
    | some j =>
      exact ALoc.pos_lt hp

/-- Actual preparation at a valid word either keeps its location or creates its singleton
history. Its shape and floors do not require fresh ids; freshness, when present, is preserved. -/
theorem prepare {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    ∃ l, W.Loc m' li l ∧ l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧ (W.Fresh m → W.Fresh m') ∧
      (∀ u, W.ownPos m' u = W.ownPos m u) ∧ m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  let mr := m.recordAt W.b W.o nb k
  have hfr (hf : W.Fresh m) : W.Fresh mr := hf.of_eq rfl (Nat.le_refl _)
  have hpos (u : ThreadId) : W.ownPos mr u = W.ownPos m u := ownPos_of_eq rfl rfl u
  cases he : mr.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) with
  | some i =>
    have hl := loc_of_find he
    have hl0 : W.Loc m i (mr.atomics[i]!) := hl
    obtain ⟨hlen, h0, hc, hlast, _⟩ := hw.loc i _ hl0
    have hpl : PlainLe mr W.b W.o nb (mr.atomics[i]!).lastClock :=
      (hw.plain i _ hl0).of_fp fun e he => by
        simp only [mr, Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact .inl he
        · exact .inr (plainHit_atomic hk)
    obtain ⟨rfl, rfl⟩ := locIdx_found he hlen hlast hpl h
    exact ⟨_, hl, hlen, h0, hc, hfr, hpos, Nat.le_refl _, rfl⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := locIdx_new he (noOverlap_of_only he hw.only) h
    let nl := firstLoc mr W.b W.o nb
    have hnl : W.Loc { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 }
        mr.atomics.size nl := by
      refine ⟨?_, by simp⟩
      show (mr.atomics.push nl).findIdx? _ = _
      rw [Array.findIdx?_push, he]; simp [nl, firstLoc]
    have h0 : 0 < nl.msgs.size := by simp [nl, firstLoc]
    refine ⟨nl, hnl, rfl, h0, ?_, ?_, ?_, Nat.le_succ _, rfl⟩
    · intro j hj; simp [nl, firstLoc] at hj
    · intro _ i l hl j hj
      obtain ⟨rfl, rfl⟩ := loc_unique hl hnl
      have : j = 0 := by simpa [nl, firstLoc] using hj
      subst j
      simp [nl, firstLoc, firstMsg, ALoc.pos]
    · intro u
      have hnew := ownPos_lt hnl h0 u
      have hold : W.ownPos mr u = 0 := ownPos_none (fun i l hl => by rw [hl.1] at he; cases he) u
      have : W.ownPos { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 } u = 0 := by
        simpa [nl, firstLoc] using hnew
      change W.ownPos { mr with atomics := mr.atomics.push nl, nextMsg := mr.nextMsg + 1 } u = _
      exact this.trans (hold.symm.trans (hpos u))

/-- Preparation preserves every floor and freshness without an operation-transport judgment. -/
theorem prepare_seen {m m' : Mem} {li : Nat} {k : AccessKind} (hw : W.Ok m)
    (hf : W.Fresh m) (hk : k.isAtomic = true)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    ∃ l, W.Loc m' li l ∧ l.len = nb ∧ 0 < l.msgs.size ∧ l.Chain ∧ W.Fresh m' ∧
      (∀ u, W.ownPos m' u = W.ownPos m u) ∧ m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨l, hl, hlen, h0, hch, hfr, hpos, hn, hc⟩ := prepare hw hk h
  exact ⟨l, hl, hlen, h0, hch, hfr hf, hpos, hn, hc⟩

/-- The valid word cannot be contained in a frame disjoint from its bytes. -/
theorem loc_notIn {m : Mem} {i : Nat} {l : ALoc} {hF : Heap} (hl : W.Loc m i l)
    (hlen : l.len = nb) (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) :
    ¬ (m.atomics[i]!).In hF := by
  rw [(loc_get hl).2.2]
  intro hin
  obtain ⟨hb, ho⟩ := loc_at hl
  have hx := hin W.o (by omega) (by have := W.sz_pos; omega)
  rw [hb] at hx
  exact hx (hoff W.o (Nat.le_refl _) (by have := W.sz_pos; omega))

/-- The actual preparation carries the existing atomic-location map. Recording the access
does not change atomic locations or views, so it composes with the actual `locIdx` map. -/
theorem prepare_amap {m m' : Mem} {li : Nat} {k : AccessKind} {hF : Heap} (hw : W.Ok m)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨blk, hb, _, hsz, _⟩ := hw.blk
  have hs := FStepIn.locIdx (m := m.recordAt W.b W.o nb k) W.sz_pos hoff ⟨blk, hb, hsz⟩ h
  obtain ⟨σ, ha⟩ := hs.atomics
  have hr : AMap hF m (m.recordAt W.b W.o nb k) some := AMap.of_eq rfl rfl
  exact ⟨hs.nextMsg, _, hr.trans ha rfl⟩

/-- A completed load carries the frame's atomic locations and views. This is obtained from
its actual preparation and read, for every memory order, without an `Op` transport premise. -/
theorem atomicLoad_amap {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, _, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, _, _, _, _, hc₁⟩ := prepare hw rfl hp
  obtain ⟨a, sn, next, hmem⟩ := locIdx_updates hp
  have hcs : m₁.current < m₁.clocks.size := by rw [hmem]; simpa [Mem.recordAt] using hc
  have hs := FStepIn.loadM hcs ord ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff)
  obtain ⟨hn, σ, hσ⟩ := prepare_amap hw hoff hp
  obtain ⟨τ, hτ⟩ := hs.atomics
  exact ⟨Nat.le_trans hn hs.nextMsg, _, hσ.trans hτ hc₁⟩

/-- The recorded access remains at the current clock after actual preparation. -/
theorem prepare_rec {m m' : Mem} {li : Nat} {k : AccessKind}
    (hc : m.current < m.clocks.size)
    (h : ((locIdx W.b W.o nb).run (m.recordAt W.b W.o nb k)).run = some (.ok (li, m'))) :
    W.Rec m' m'.current ∧ m'.current < m'.clocks.size ∧ m'.blocks = m.blocks := by
  obtain ⟨a, sn, next, rfl⟩ := locIdx_updates h
  exact ⟨rec_recordAt rfl hc, by simpa [Mem.recordAt] using hc, rfl⟩

/-- The actual newest-message RMW preserves a disjoint frame's atomic locations and views. -/
theorem rmwM_amap {m : Mem} {li pos : Nat} {l : ALoc} {hF : Heap}
    (hl : W.Loc m li l) (hlen : l.len = nb) (hpos : pos + 1 = l.msgs.size)
    (hc : m.current < m.clocks.size) (hrec : W.Rec m m.current)
    (hb : ∃ blk, m.blocks[W.b]? = some blk)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (ord : AtomicOrder) (new : BitVec n) :
    m.nextMsg ≤ (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new).nextMsg ∧
      ∃ σ, AMap hF m (rmwM m li pos ord ((m.atomics[li]!).msgs[pos]!) new) σ := by
  obtain ⟨blk, hb⟩ := hb
  obtain ⟨e, he, heb, heo, hel, hec⟩ := hrec
  obtain ⟨hlb, hlo⟩ := loc_at hl
  have hl0 := (loc_get hl).2.2
  have hs := FStepIn.rmwM (hF := hF) (li := li) (pos := pos) (blk := blk) (e := e)
    ord ((m.atomics[li]!).msgs[pos]!) new hc
    (by rw [hl0]; exact hpos) (by rw [hl0, hlb]; exact hb) (loc_notIn hl hlen hoff)
    he (by rw [hl0, hlb]; exact heb) (by rw [hl0, hlo]; exact heo) hel hec
    (by rw [hl0, getElem!_pos l.msgs pos (by omega)]; exact Array.getElem_mem _)
  exact ⟨hs.nextMsg, hs.atomics⟩

/-- Every completed RMW operation uses actual preparation and the actual newest-message write. -/
theorem atomicRmw_amap {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} {hF : Heap} (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, hb, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, h0, hch, _, _, _, hc₁⟩ := prepare hw rfl hp
  obtain ⟨hrec, hcs, hblocks⟩ := prepare_rec hc hp
  have hpos : pos + 1 = l.msgs.size := by
    have := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
    rw [(loc_get hl).2.2] at this
    omega
  obtain ⟨hn, σ, hσ⟩ := prepare_amap hw hoff hp
  obtain ⟨hn', τ, hτ⟩ := rmwM_amap hl hlen hpos hcs hrec
    ⟨_, by rw [hblocks]; exact hb⟩ hoff ord (op.apply signed old v)
  exact ⟨Nat.le_trans hn hn', _, hσ.trans hτ hc₁⟩

/-- A successful CAS records its write, then performs the actual newest-message RMW. -/
theorem casRmw_amap {m : Mem} {li c pos : Nat} {l : ALoc} {hF : Heap}
    {expected new : BitVec n} (hl : W.Loc m li l) (hlen : l.len = nb) (hch : l.Chain)
    (hr : (casOpts m li expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[li]!).msgs[pos]!).bytes).run = some (.ok expected))
    (hc : m.current < m.clocks.size) (hb : ∃ blk, m.blocks[W.b]? = some blk)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) (ord : AtomicOrder) :
    m.nextMsg ≤ (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
      ((m.atomics[li]!).msgs[pos]!) new).nextMsg ∧
      ∃ σ, AMap hF m (rmwM (m.recordAt W.b W.o nb .atomicWrite) li pos ord
        ((m.atomics[li]!).msgs[pos]!) new) σ := by
  have hpos := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hpos hj
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) li l := hl
  obtain ⟨hn, σ, ha⟩ := rmwM_amap (pos := pos) hlr hlen (by omega)
    (by simpa [Mem.recordAt] using hc) (rec_recordAt rfl hc) hb hoff ord new
  have hr : AMap hF m (m.recordAt W.b W.o nb .atomicWrite) some := AMap.of_eq rfl rfl
  exact ⟨hn, _, hr.trans ha rfl⟩

/-- Both branches of a completed strong CAS carry the actual disjoint-frame map. -/
theorem cmpxchg_amap {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, hblk, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _, _, _, hc₁⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨hn, σ, hσ⟩ := prepare_amap hw hoff hp
  rcases hb with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [W.sz_eq]
    obtain ⟨hn', τ, hτ⟩ := casRmw_amap (new := new) hl hlen hch hr hv hcs
      ⟨_, by rw [hblocks]; exact hblk⟩ hoff succ
    exact ⟨Nat.le_trans hn hn', _, hσ.trans hτ hc₁⟩
  · have hs := FStepIn.loadM hcs fail ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff)
    obtain ⟨τ, hτ⟩ := hs.atomics
    exact ⟨Nat.le_trans hn hs.nextMsg, _, hσ.trans hτ hc₁⟩

/-- Weak CAS carries the same map for success, mismatches and matching-value spurious failures. -/
theorem cmpxchgWeak_amap {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} {hF : Heap}
    (hw : W.Ok m) (hc : m.current < m.clocks.size)
    (hoff : ∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, hblk, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, hlen, _, hch, _, _, _, hc₁⟩ := prepare hw rfl hp
  obtain ⟨_, hcs, hblocks⟩ := prepare_rec hc hp
  obtain ⟨hn, σ, hσ⟩ := prepare_amap hw hoff hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    rw [W.sz_eq]
    obtain ⟨hn', τ, hτ⟩ := casRmw_amap (new := new) hl hlen hch hj hv hcs
      ⟨_, by rw [hblocks]; exact hblk⟩ hoff succ
    exact ⟨Nat.le_trans hn hn', _, hσ.trans hτ hc₁⟩
  · have hs := FStepIn.loadM hcs fail ((m₁.atomics[li]!).msgs[pos]!) (loc_notIn hl hlen hoff)
    obtain ⟨τ, hτ⟩ := hs.atomics
    exact ⟨Nat.le_trans hn hs.nextMsg, _, hσ.trans hτ hc₁⟩

/-- Normalize a whole family of actual disjoint-frame maps to the explicitly named actor.
The counter fact follows at the empty frame; no destination `current` fact is needed. -/
theorem amap_for_actor {m m' : Mem} {t : ThreadId} (hc : m.current = t)
    (h : ∀ hF, (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) →
      m.nextMsg ≤ m'.nextMsg ∧ ∃ σ, AMap hF m m' σ) :
    m.nextMsg ≤ m'.nextMsg ∧ ∀ hF,
      (∀ x, W.o ≤ x → x < W.o + nb → hF (W.b, x) = none) →
      ∃ σ, AMap hF { m with current := t } { m' with current := t } σ := by
  refine ⟨(h (fun _ => none) (fun _ _ _ => rfl)).1, fun hF hoff => ?_⟩
  obtain ⟨_, σ, ha⟩ := h hF hoff
  exact ⟨σ, ha.withCurrent hc⟩

/-- The scheduler's futex compare/sleep records an access and changes only its queue or woken
set. Unlike an atomic-load operation, it does not select an atomic-history message. -/
theorem futexWait_fields {m m' : Mem} {p : Ptr} {e : BitVec 32} {b : Bool}
    (h : ((Thread.futexWait p e).run m).run = some (.ok (b, m'))) :
    m'.atomics = m.atomics ∧ m'.seen = m.seen ∧ m'.nextMsg = m.nextMsg := by
  rcases futexWait_eq h with ⟨_, rfl, rfl⟩ | ⟨_, bid, blk, o, v, _, _, _, hcase⟩
  · exact ⟨rfl, rfl, rfl⟩
  rcases hcase with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- The current thread observes message `id` of the word's location. -/
theorem ownPos_observe {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (id u : Nat) :
    W.ownPos (observeM m i id) u = if u = m.current then (l.pos id).getD 0 else W.ownPos m u := by
  have hl' : W.Loc (observeM m i id) i l := hl
  rw [ownPos_loc hl', ownPos_loc hl, seenAt_observe]
  by_cases hu : u = m.current <;> simp [hu]

/-- A read of message `j` of the word's location (`loadM`): the reader's floor is `j`, the
other floors stay. -/
theorem loadM_seen {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (hf : W.Fresh m) {j : Nat}
    (hj : j < l.msgs.size) (ord : AtomicOrder) :
    W.ownPos (loadM m i ord (l.msgs[j]!)) m.current = j ∧
      (∀ u, u ≠ m.current → W.ownPos (loadM m i ord (l.msgs[j]!)) u = W.ownPos m u) ∧
      W.Fresh (loadM m i ord (l.msgs[j]!)) := by
  have hobs : ∀ u, W.ownPos (loadM m i ord (l.msgs[j]!)) u =
      W.ownPos (observeM m i (l.msgs[j]!).id) u := by
    intro u; unfold loadM; dsimp only; split
    · exact ownPos_of_eq rfl rfl u
    · rfl
  refine ⟨?_, fun u hu => ?_, hf.of_eq (by unfold loadM; split <;> rfl)
    (by unfold loadM; split <;> exact Nat.le_refl _)⟩
  · rw [hobs, ownPos_observe hl, if_pos rfl, getElem!_pos l.msgs j hj, (hf i l hl j hj).2]; rfl
  · rw [hobs, ownPos_observe hl, ite_eq_right hu]

/-- Every admitted read choice, at every atomic order, preserves freshness and advances only
the reader's floor. An unconstrained `observeM` does not have this property. -/
theorem loadM_read_seen {m : Mem} {i c j : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hr : (readOpts m i false)[c]? = some j) (ord : AtomicOrder) :
    W.Fresh (loadM m i ord (l.msgs[j]!)) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (loadM m i ord (l.msgs[j]!)) u := by
  have hj := readOpts_lt hr
  rw [(loc_get hl).2.2] at hj
  obtain ⟨ha, ho, hf'⟩ := loadM_seen hl hf hj ord
  refine ⟨hf', fun u => ?_⟩
  by_cases hu : u = m.current
  · subst u; rw [ha]; exact Nat.le_trans (ownPos_le_floor hl) (floor_le hr)
  · rw [ho u hu]; exact Nat.le_refl _

/-- The bytes returned by a read belong to the message at its resulting caller-local floor. -/
theorem loadM_seen_val {m : Mem} {i j : Nat} {l : ALoc} {v : BitVec n}
    (hl : W.Loc m i l) (hf : W.Fresh m) (hj : j < l.msgs.size)
    (hv : (intOfBytes n (l.msgs[j]!).bytes).run = some (.ok v)) (ord : AtomicOrder) :
    j < (W.hist (loadM m i ord (l.msgs[j]!))).size ∧
      (W.hist (loadM m i ord (l.msgs[j]!)))[j]!.Val v ∧
      W.ownPos (loadM m i ord (l.msgs[j]!)) m.current = j := by
  have ha : (loadM m i ord (l.msgs[j]!)).atomics = m.atomics := by
    unfold loadM; split <;> rfl
  have hL : W.Loc (loadM m i ord (l.msgs[j]!)) i l := by
    unfold Loc; rw [ha]; exact hl
  exact ⟨by rw [hist_size hL]; exact hj, val_of hL hj hv, (loadM_seen hl hf hj ord).1⟩

/-- A completed load at the word satisfies the floor property for its actual selected message. -/
theorem atomicLoad_seen {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rw [(loc_get hl).2.2]
  obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hr ord
  refine ⟨hf', fun u => by rw [← he u]; exact hm u, ?_, (loadM_current _ _ _ _).trans hc⟩
  exact Nat.le_trans hn (by unfold loadM; split <;> exact Nat.le_refl _)

/-- The actual selected message of a load is the reader's new floor. The witness uses the
resulting history, so it composes with any existing rule that preserves that history. -/
theorem atomicLoad_read_seen {m m' : Mem} {c : Nat} {ord : AtomicOrder} {v : BitVec n}
    (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicLoadAt c ord nb W.ptr).run m).run = some (.ok (v, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val v ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := atomicLoad_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₀, _, _, _, ha, _⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  have hj := readOpts_lt hr
  rw [(loc_get hl).2.2] at hj hv ⊢
  refine ⟨pos, ?_⟩
  rw [← hc]
  exact loadM_seen_val hl hf₁ hj hv ord

/-- A message with a fresh id at the end of the word's location keeps the ids fresh and no floor
smaller, and it is at the end. -/
theorem fresh_push {m M : Mem} {i : Nat} {l : ALoc} {x : Msg} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hL : W.Loc M i { l with msgs := l.msgs.push x }) (hx : x.id = m.nextMsg)
    (hn : M.nextMsg = m.nextMsg + 1) (hs : M.seen = m.seen) :
    W.Fresh M ∧ (∀ u, W.ownPos m u ≤ W.ownPos M u) ∧
      ({ l with msgs := l.msgs.push x } : ALoc).pos x.id = some l.msgs.size := by
  have hold : ∀ id k, l.pos id = some k →
      ({ l with msgs := l.msgs.push x } : ALoc).pos id = some k := by
    intro id k h
    unfold ALoc.pos at h ⊢
    rw [Array.findIdx?_push, h]; rfl
  have hnew : ({ l with msgs := l.msgs.push x } : ALoc).pos x.id = some l.msgs.size := by
    have hnone : l.msgs.findIdx? (·.id == x.id) = none := by
      rw [Array.findIdx?_eq_none_iff]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hy
      have := (hf i l hl k hk).1
      simpa using (by omega : l.msgs[k].id ≠ x.id)
    unfold ALoc.pos
    rw [Array.findIdx?_push, hnone]; simp
  refine ⟨fun i' l' hl' k hk => ?_, fun u => ?_, hnew⟩
  · obtain ⟨e1, e2⟩ := loc_unique hL hl'
    subst e1 e2
    rw [hn]
    simp only [Array.size_push] at hk
    by_cases hk' : k < l.msgs.size
    · simp only [Array.getElem_push, hk', ↓reduceDIte]
      obtain ⟨h1, h2⟩ := hf i l hl k hk'
      exact ⟨by omega, hold _ _ h2⟩
    · obtain rfl : k = l.msgs.size := by omega
      simp only [Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte]
      exact ⟨by omega, hnew⟩
  · have hsa : M.seenAt u i = m.seenAt u i := by unfold Mem.seenAt; rw [hs]
    rw [ownPos_loc hl, ownPos_loc hL, hsa]
    cases m.seenAt u i with
    | none => exact Nat.le_refl _
    | some id =>
      show (l.pos id).getD 0 ≤ (({ l with msgs := l.msgs.push x } : ALoc).pos id).getD 0
      cases hp : l.pos id with
      | none => exact Nat.zero_le _
      | some k => rw [hold _ _ hp]; exact Nat.le_refl _

/-- The location `i` with another location of the same place. -/
theorem loc_set {m : Mem} {i : Nat} {l l' : ALoc} (hl : W.Loc m i l) (hb : l'.block = l.block)
    (ho : l'.off = l.off) :
    (m.atomics.set! i l').findIdx? (fun l => l.block == W.b && l.off == W.o) = some i ∧
      (m.atomics.set! i l')[i]? = some l' := by
  obtain ⟨hi, -, -⟩ := loc_get hl
  refine ⟨?_, ?_⟩
  · have hfirst : (m.atomics.set! i l').findIdx? (fun l => l.block == W.b && l.off == W.o) =
        m.atomics.findIdx? (fun l => l.block == W.b && l.off == W.o) :=
      Conc.findIdx?_congr (by simp) fun j hj hj' => by
        simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hj']
        by_cases e : i = j
        · simp only [e, ↓reduceIte]
          subst j
          simp [(Array.getElem?_eq_some_iff.mp hl.2).2, hb, ho]
        · simp [e]
    exact hfirst.trans hl.1
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [hi]

/-- Inserting immediately after the newest message keeps the word at the same location. -/
theorem loc_insert_last {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hp : pos + 1 = l.msgs.size) (msg : Msg) :
    W.Loc (insertM m i (pos + 1) msg) i { l with msgs := l.msgs.push msg } := by
  unfold Loc
  rw [insertM_atomics, (loc_get hl).2.2, hp, Conc.Proto.insertIdxIfInBounds_size_self]
  exact loc_set hl rfl rfl

/-- An RMW of the newest message of the word's location (`rmwM`): the writer's floor is the new
message, at the end; no other floor gets smaller. -/
theorem rmwM_seen {m : Mem} {i : Nat} {l : ALoc} (hl : W.Loc m i l) (hf : W.Fresh m) {pos : Nat}
    (hpos : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.ownPos (rmwM m i pos ord rd new) m.current = l.msgs.size ∧
      (∀ u, u ≠ m.current → W.ownPos m u ≤ W.ownPos (rmwM m i pos ord rd new) u) ∧
      W.Fresh (rmwM m i pos ord rd new) := by
  obtain ⟨m₂, ha₂, hs₂, hn₂, hc₂, e⟩ : ∃ m₂ : Mem, m₂.atomics = m.atomics ∧ m₂.seen = m.seen ∧
      m₂.nextMsg = m.nextMsg ∧ m₂.current = m.current ∧
      rmwM m i pos ord rd new = observeM (insertM m₂ i (pos + 1) (rmwMsg m₂ ord rd new)) i
        m₂.nextMsg := by
    unfold rmwM; dsimp only; split
    · exact ⟨acqM m rd.relClock, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨m, rfl, rfl, rfl, rfl, rfl⟩
  rw [e]
  have hl₂ : W.Loc m₂ i l := by unfold Loc; rw [ha₂]; exact hl
  have hf₂ : W.Fresh m₂ := hf.of_eq ha₂ (Nat.le_of_eq hn₂.symm)
  have hl0 := (loc_get hl₂).2.2
  generalize hmsg : rmwMsg m₂ ord rd new = msg
  have hid : msg.id = m₂.nextMsg := by rw [← hmsg]; rfl
  have hMa : (insertM m₂ i (pos + 1) msg).atomics =
      m₂.atomics.set! i { l with msgs := l.msgs.push msg } := by
    rw [insertM_atomics, hl0, hpos, Conc.Proto.insertIdxIfInBounds_size_self]
  generalize hM : insertM m₂ i (pos + 1) msg = M at hMa
  have hL : W.Loc M i { l with msgs := l.msgs.push msg } := by
    unfold Loc; rw [hMa]; exact loc_set hl₂ rfl rfl
  have hMs : M.seen = m₂.seen := by rw [← hM]; exact insertM_seen
  have hMn : M.nextMsg = m₂.nextMsg + 1 := by rw [← hM]; exact insertM_nextMsg
  have hMc : M.current = m.current := by rw [← hM]; exact insertM_current.trans hc₂
  obtain ⟨hfM, hle, hend⟩ := fresh_push hl₂ hf₂ hL hid hMn hMs
  rw [← hid]
  refine ⟨?_, fun u hu => ?_, hfM.of_eq rfl (Nat.le_refl _)⟩
  · rw [ownPos_observe hL, ← hMc, ite_eq_left rfl, hend]; rfl
  · rw [ownPos_observe hL, ite_eq_right (by rw [hMc]; exact hu), ← ownPos_of_eq ha₂ hs₂ u]
    exact hle u

/-- Appending an RMW to the newest message preserves freshness and every thread's floor. -/
theorem rmwM_latest_seen {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hp : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.Fresh (rmwM m i pos ord rd new) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (rmwM m i pos ord rd new) u := by
  obtain ⟨ha, ho, hf'⟩ := rmwM_seen hl hf hp ord rd new
  refine ⟨hf', fun u => ?_⟩
  by_cases hu : u = m.current
  · subst u; rw [ha]; exact Nat.le_of_lt (ownPos_lt hl (by omega) _)
  · exact ho u hu

/-- A successful newest-message RMW leaves its caller's floor at the new last write. -/
theorem rmwM_seen_last {m : Mem} {i pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (hp : pos + 1 = l.msgs.size) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) :
    W.ownPos (rmwM m i pos ord rd new) m.current =
      (W.hist (rmwM m i pos ord rd new)).size - 1 := by
  have hs : (W.hist (rmwM m i pos ord rd new)).size = l.msgs.size + 1 := by
    unfold rmwM
    split
    · have hl' : W.Loc (acqM m rd.relClock) i l := hl
      change (W.hist (insertM (acqM m rd.relClock) i (pos + 1)
        (rmwMsg (acqM m rd.relClock) ord rd new))).size = l.msgs.size + 1
      rw [hist_size (loc_insert_last hl' hp _)]; simp
    · change (W.hist (insertM m i (pos + 1) (rmwMsg m ord rd new))).size = l.msgs.size + 1
      rw [hist_size (loc_insert_last hl hp _)]; simp
  rw [hs, Nat.add_sub_cancel]
  exact (rmwM_seen hl hf hp ord rd new).1

/-- An RMW's actual read choice in a chain selects its newest message. -/
theorem rmwM_read_seen {m : Mem} {i c pos : Nat} {l : ALoc} (hl : W.Loc m i l)
    (hf : W.Fresh m) (h0 : 0 < l.msgs.size) (hc : l.Chain)
    (hr : (readOpts m i true)[c]? = some pos) (ord : AtomicOrder) (new : BitVec n) :
    W.Fresh (rmwM m i pos ord (l.msgs[pos]!) new) ∧
      ∀ u, W.ownPos m u ≤ W.ownPos (rmwM m i pos ord (l.msgs[pos]!) new) u := by
  have hp : pos + 1 = l.msgs.size := by
    have := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
    rw [(loc_get hl).2.2] at this
    omega
  exact rmwM_latest_seen hl hf hp ord _ new

/-- Every completed RMW operation and signedness uses the same floor/freshness rule. -/
theorem atomicRmw_seen {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, h0, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rw [(loc_get hl).2.2]
  obtain ⟨hf', hm⟩ := rmwM_read_seen hl hf₁ h0 hchain hr ord (op.apply signed old v)
  refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
  · unfold rmwM
    split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
  · unfold rmwM
    split <;> exact insertM_current.trans hc

/-- Every completed RMW leaves its caller at the new last write, for every operation, order
and signedness. -/
theorem atomicRmw_write_seen {m m' : Mem} {c : Nat} {op : RmwOp} {signed : Bool} {ord : AtomicOrder}
    {v old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((atomicRmwAt c op signed ord nb W.ptr v).run m).run = some (.ok (old, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, _, hp, hr, _, rfl⟩ := atomicRmwAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, h0, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  have hp' := rmw_chain_pos (by rwa [(loc_get hl).2.2]) (by rwa [(loc_get hl).2.2]) hr
  rw [(loc_get hl).2.2] at hp' ⊢
  rw [← hc]
  exact rmwM_seen_last hl hf₁ (by omega) ord _ _

/-- Success of a CAS uses the newest message of a chain. Recording its write does not change
the floors or freshness before the RMW. -/
theorem casRmw_seen {m : Mem} {i c pos : Nat} {l : ALoc} {expected new : BitVec n}
    (hl : W.Loc m i l) (hf : W.Fresh m) (hc : l.Chain)
    (hr : (casOpts m i expected)[c]? = some pos)
    (hv : (intOfBytes n ((m.atomics[i]!).msgs[pos]!).bytes).run = some (.ok expected))
    (ord : AtomicOrder) :
    W.Fresh (rmwM (m.recordAt W.b W.o nb .atomicWrite) i pos ord (l.msgs[pos]!) new) ∧
      ∀ u, W.ownPos m u ≤
        W.ownPos (rmwM (m.recordAt W.b W.o nb .atomicWrite) i pos ord (l.msgs[pos]!) new) u := by
  have hp := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
  have hj := (casOpts_pos hr).1
  rw [(loc_get hl).2.2] at hp hj
  have hlr : W.Loc (m.recordAt W.b W.o nb .atomicWrite) i l := hl
  exact rmwM_latest_seen (pos := pos) hlr (hf.of_eq rfl (Nat.le_refl _)) (by omega) ord _ new

/-- Strong CAS preserves freshness and nondecreasing floors in both its successful RMW and
its failure-order read branch. -/
theorem cmpxchg_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [W.sz_eq, (loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := casRmw_seen hl hf₁ hchain hr hv succ
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
    · unfold rmwM
      split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
    · unfold rmwM
      split <;> exact insertM_current.trans hc
  · have hread : ∃ j : Nat, (readOpts m₁ li false)[j]? = some pos := by
      exact Array.mem_iff_getElem?.mp (Array.mem_filter.mp (Array.mem_of_getElem? hr)).1
    obtain ⟨j, hj⟩ := hread
    rw [(loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hj fail
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, (loadM_current _ _ _ _).trans hc⟩
    unfold loadM; split <;> exact Nat.le_refl _

/-- A failed strong CAS reads the message at its resulting floor, at its failure order. -/
theorem cmpxchg_read_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (some old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val old ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := cmpxchg_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, rd, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨_, he, _, _⟩ | ⟨_, he, rfl⟩
  · cases he
  · cases he
    have hj := (casOpts_pos hr).1
    rw [(loc_get hl).2.2] at hj hv ⊢
    refine ⟨pos, ?_⟩
    rw [← hc]
    exact loadM_seen_val hl hf₁ hj hv fail

/-- A successful strong CAS leaves the caller at its new last message. -/
theorem cmpxchg_write_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (none, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, _, _, rfl⟩ | ⟨_, he, _⟩
  · have hp' := cas_chain_pos (by rwa [(loc_get hl).2.2]) hr hv
    have hj := (casOpts_pos hr).1
    rw [(loc_get hl).2.2] at hp' hj
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    rw [W.sz_eq, (loc_get hl).2.2, ← hc]
    exact rmwM_seen_last hlr (hf₁.of_eq rfl (Nat.le_refl _)) (by omega) succ _ new
  · cases he

/-- Weak CAS includes every matching-value spurious failure. Each permitted branch uses the
same preparation, read and RMW facts as strong CAS. -/
theorem cmpxchgWeak_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} {r : Option (BitVec n)} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run = some (.ok (r, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      m.nextMsg ≤ m'.nextMsg ∧ m'.current = m.current := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, he, hn, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    rw [W.sz_eq, (loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := casRmw_seen hl hf₁ hchain hj hv succ
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, ?_⟩
    · unfold rmwM
      split <;> dsimp only [observeM] <;> rw [insertM_nextMsg] <;> exact Nat.le_succ _
    · unfold rmwM
      split <;> exact insertM_current.trans hc
  · obtain ⟨j, hj⟩ := weakCasOpts_read hr
    rw [(loc_get hl).2.2]
    obtain ⟨hf', hm⟩ := loadM_read_seen hl hf₁ hj fail
    refine ⟨hf', fun u => by rw [← he u]; exact hm u, Nat.le_trans hn ?_, (loadM_current _ _ _ _).trans hc⟩
    unfold loadM; split <;> exact Nat.le_refl _

/-- The same actual-message fact includes matching-value spurious weak-CAS failures. -/
theorem cmpxchgWeak_read_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new old : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (some old, m'))) :
    W.Fresh m' ∧ (∀ u, W.ownPos m u ≤ W.ownPos m' u) ∧
      ∃ j < (W.hist m').size, (W.hist m')[j]!.Val old ∧ W.ownPos m' m.current = j := by
  obtain ⟨hf', hm, _, _⟩ := cmpxchgWeak_seen hw hf h
  refine ⟨hf', hm, ?_⟩
  obtain ⟨b, blk, o, li, m₁, pos, spurious, rd, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, _, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨_, _, he, _, _⟩ | ⟨_, he, rfl⟩
  · cases he
  · cases he
    obtain ⟨j, hj⟩ := weakCasOpts_read hr
    have hpos := readOpts_lt hj
    rw [(loc_get hl).2.2] at hpos hv ⊢
    refine ⟨pos, ?_⟩
    rw [← hc]
    exact loadM_seen_val hl hf₁ hpos hv fail

/-- A successful weak CAS has the same newest-write floor as a successful strong CAS. -/
theorem cmpxchgWeak_write_seen {m m' : Mem} {c : Nat} {succ fail : AtomicOrder}
    {expected new : BitVec n} (hw : W.Ok m) (hf : W.Fresh m)
    (h : ((cmpxchgWeakAt c succ fail nb W.ptr expected new).run m).run =
      some (.ok (none, m'))) :
    W.ownPos m' m.current = (W.hist m').size - 1 := by
  obtain ⟨b, blk, o, li, m₁, pos, spurious, old, hacc, _, hp, hr, hv, hb⟩ := cmpxchgWeakAt_ok h
  obtain ⟨blk₀, _, _, _, _, ha⟩ := hw.access
  rw [W.sz_eq, ha] at hacc
  rw [W.sz_eq] at hp
  cases hacc
  obtain ⟨l, hl, _, _, hchain, hf₁, _, _, hc⟩ := prepare_seen hw hf rfl hp
  rcases hb with ⟨rfl, rfl, _, _, rfl⟩ | ⟨_, he, _⟩
  · obtain ⟨j, hj⟩ := weakCasOpts_strong hr
    have hp' := cas_chain_pos (by rwa [(loc_get hl).2.2]) hj hv
    have hpos := (casOpts_pos hj).1
    rw [(loc_get hl).2.2] at hp' hpos
    have hlr : W.Loc (m₁.recordAt W.b W.o nb .atomicWrite) li l := hl
    rw [W.sz_eq, (loc_get hl).2.2, ← hc]
    exact rmwM_seen_last hlr (hf₁.of_eq rfl (Nat.le_refl _)) (by omega) succ _ new
  · cases he

end Word
end Conc
end Zig
