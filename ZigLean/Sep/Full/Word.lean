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
- **A step of a thread on its own part keeps the word** (`Word.keepK_stepIn`): its frame has the
  word's cells, which stay up to `Cell.norm` (`FLock.Inv.cellsN`).
- **A futex wait at the word** by a thread out of the lock's code (`away`) keeps the lock's
  invariant (`FLock.Inv.waitOff`, `FLock.Inv.spuriousOff`); so does a futex wake at it
  (`FLock.Inv.wakeOff`).

A rest that has the word's cells of an older memory, the same up to `Cell.norm`, is the rest with
the word's cells of the new memory (`FLock.Inv.congrX`).
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
    fun b x hx => ?_, fun hwf => ?_, fun e he => ?_⟩
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
    · refine .inr ⟨fun x hx1 hx2 => ⟨h1, by omega, by rcases hx2 with h | h <;> omega⟩, by
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
  · have hne : W.b ≠ L.b ∨ W.o ≠ L.o := by
      rcases hap with h | h | h
      · exact .inl (Ne.symm h)
      · exact .inr (by omega)
      · exact .inr (by omega)
    exact hs.locs.same W.b W.o hne i l
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
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega

/-- **A step of a thread on its own part keeps the word**: its frame `hF` has the word's bytes,
and the word's cells stay up to `Cell.norm` (`FLock.Inv.cellsN`). -/
theorem keepK_stepIn {m m' : Mem} {hF : Heap}
    (hs : StepIn hF m m') (hwF : ∀ l, W.In l → hF l ≠ none)
    (hcells : ∀ l, W.In l → (m'.heap l).map Cell.norm = (m.heap l).map Cell.norm) :
    W.KeepK m m' := by
  have hcl : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true := hs.clock
  refine ⟨fun x h1 h2 => ?_, fun i l => by unfold Word.Loc; rw [hs.atomics],
    fun l hl => .inl (hs.atomics ▸ hl), fun e he => ?_,
    fun _ h u hu => VClock.le_trans (h u (hs.threads ▸ hu)) (hcl u),
    fun _ ⟨u, hu, hle⟩ => ⟨u, hs.threads ▸ hu, VClock.le_trans hle (hcl u)⟩⟩
  · have := congrArg (Option.map cellKey) (hcells (W.b, x) ⟨rfl, h1, h2⟩)
    simpa [Option.map_map, Function.comp_def, cellKey_norm] using this
  · rcases hs.fp e he with h | ⟨-, hnt, -⟩
    · exact .inl h
    · exact .inr fun hh => hnt (touches_of hh fun x h1 h2 => hwF _ ⟨rfl, h1, h2⟩)

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

/-- The word's cells of the rest are the memory's, up to `Cell.norm`. -/
theorem Inv.cellsN {G : ThreadId → γ} {rY : Res} {m₀ m : Mem}
    (hi : L.Inv G (rsum (W.cellsR m₀) rY) m) {l : Zig.Loc} (hl : W.In l)
    (h0 : m₀.heap l ≠ none) : (m.heap l).map Cell.norm = (m₀.heap l).map Cell.norm := by
  obtain ⟨rL, ho, -, hLX, -⟩ := hi.rest
  cases e : m₀.heap l with
  | none => exact absurd e h0
  | some c =>
    have hW : (W.cellsR m₀).heap l = some ⟨c, none⟩ := by simp [cellsAt_of hl, e]
    have hrL : rL.heap l = none := (hLX l).resolve_right (by simp [FHeap.union_apply, hW])
    have hwr : (L.wordR m).heap l = none := by
      by_cases hin : L.In l
      · have := LockWord.off_erase.mp hi.xoff l hin
        simp [FHeap.union_apply, hW] at this
      · exact cellsAt_none hin
    have := ho.rest_cell (l := l) (fc := ⟨c, none⟩) (by
      simp only [FHeap.union_apply, hW, hwr, hrL, Option.none_or, Option.some_or])
    rw [this]; rfl

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
  have hne : L.b ≠ W.b ∨ L.o ≠ W.o := by
    rcases hap with h | h | h
    · exact .inl h
    · exact .inr (by omega)
    · exact .inr (by omega)
  have hloc : ∀ i l, L.Loc m' i l ↔ L.Loc m i l := fun i l => hop.locs.same L.b L.o hne i l
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
      · rcases h2 with h2 | h2 <;> omega
      · rcases h2 with h2 | h2 <;> omega
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
          exact absurd (by simp [FHeap.erase, hLW (W.b, x) ⟨rfl, h1, by rcases h2 with h2 | h2 <;> omega⟩]) h3
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
  have hpL : W.ptr ≠ L.ptr := fun e => by
    simp only [Word.ptr, LockWord.ptr, Ptr.mk.injEq, Option.some.injEq, Int.natCast_inj] at e
    rcases hap with h | h | h
    · exact h e.1.symm
    · omega
    · omega
  have hoff : ∀ bid blk o, m.access W.ptr 4 4 = pure (bid, blk, o) →
      bid ≠ L.b ∨ o + 4 ≤ L.o ∨ L.o + 4 ≤ o := fun bid blk o ha => by
    rw [ha₀] at ha; cases ha
    rcases hap with h | h | h
    · exact .inl (Ne.symm h)
    · exact .inr (.inr h)
    · exact .inr (.inl h)
  have hw := hi.w.waitOff (t := t) (by exact hph) hpL hoff hq h
  have hupd : ∀ u, L.ph (upd G t (L.set (G t) .out rnil) u) = if u = t then .out else L.ph (G u) :=
    fun u => by unfold upd; split <;> simp [L.ph_set]
  have hpl : L.pl (upd G t (L.set (G t) .out rnil)) = upd (L.pl G) t .out := pl_upd_set G t _ _
  -- the relabel of `t` from `away` to `out`, at a memory with the same parts
  have hrel : ∀ M : Mem, L.Inv G rX M → M.current = t →
      L.WInv (upd (L.pl G) t .out) M → L.Inv (upd G t (L.set (G t) .out rnil)) rX M := by
    intro M hiM hc hwM
    have := hiM.requeue M.current M.waiters M.woken (G' := upd G t (L.set (G t) .out rnil))
      (by rw [hpl]; exact hwM)
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
    L.Inv (upd G t (L.set (G t) .out rnil)) rX { m with current := t } := by
  have hnh : L.ph (G t) ≠ .holds := by rw [hph]; decide
  have hupd : ∀ u, L.ph (upd G t (L.set (G t) .out rnil) u) = if u = t then .out else L.ph (G u) :=
    fun u => by unfold upd; split <;> simp [L.ph_set]
  have := hi.requeue t m.waiters m.woken (G' := upd G t (L.set (G t) .out rnil))
    (by rw [pl_upd_set]; exact (hi.w.spuriousOff (t := t) (by exact hph) hq).2)
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

/-- A futex wake by thread `t` at a shared word apart from the lock's: the lock's invariant
holds. -/
theorem Inv.wakeOff {W : Word 32 4} {G : ThreadId → γ} {rX : Res} {m m' : Mem} {t : ThreadId}
    {k : Nat} {cs : List Nat} (hi : L.Inv G rX m) (hap : W.ApartL L.toLockWord)
    (h : ((Thread.futexWake W.ptr k cs).run { m with current := t }).run = some (.ok ((), m'))) :
    L.Inv G rX m' := by
  have hpL : W.ptr ≠ L.ptr := fun e => by
    simp only [Word.ptr, LockWord.ptr, Ptr.mk.injEq, Option.some.injEq, Int.natCast_inj] at e
    rcases hap with h | h | h
    · exact h e.1.symm
    · omega
    · omega
  have hw := hi.w.wakeOff hpL h
  have hm' := Proto.modify_ok h
  subst hm'
  exact hi.requeue t _ _ hw (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl) (fun _ h => h)
    (fun _ => Iff.rfl)

end FLock

end Full
end Zig
