import ZigLean.Sep.Full.AtomicPtr
import ZigLean.Sep.Full.Conc
import ZigLean.Conc.WeakCas

/-!
# More sequential atomic rules (the translated `ArenaAllocator`)

The rules of `Atomic.lean` and `AtomicPtr.lean`, for the further atomic ops that the arena's
`free`, `resize` and `remap` reach (`tests/roadmap/alloc-arena`):

* `FTriple.atomicLoadPtr`: an atomic load (any order) of an owned pointer-valued word
  (`loadFirstNode`: `@atomicLoad(?*Node, &state.used_list, .acquire)`), choice `0`: the newest
  message, which holds the owned bytes;
* `FTriple.cmpxchgHit`: a strong `cmpxchg` of an owned 64-bit word that holds the expected value
  (choice `0`): it succeeds and the word holds the new value;
* `FTriple.atomicLoadAs`: an atomic load of a packed type over an owned 64-bit word
  (`Node.loadBuf`: `@atomicLoad(Node.Size, &node.size, .monotonic)`), decoded by `Packed.ofBits`.
* `wptsE`: an owned pointer-valued word with any tag constraint (`wpts` for `Enc` values);
  `FTriple.atomicXchgPtrW` (`stealFreeList`'s `.Xchg`: returns the old pointer, the word holds the
  new one), `FTriple.cmpxchgWeakPtrW` (`pushFreeList`'s weak `cmpxchg`: choice `0` is not a
  spurious failure, so it succeeds when the word holds the expected pointer);
* `FTriple.atomicLoadUnorderedW`, `FTriple.atomicLoadUnorderedAsW`: an `unordered` load of an
  owned 64-bit word, integer or packed (`Node.endResize`'s assert).

All are at the oracle's choice `0`. As in `Atomic.lean`, each op has one analysis of its run
(`cmpxchgHit_run`, …) that gives the thread rule of a word of any constraint (`FTTriple.…W`); the
`apts`/`aptsE` thread rules and all sequential rules follow from it.
-/

namespace Zig
namespace Full

open FAssn Conc Conc.Proto

theorem atomicLoadPtrAt_ok {α : Type} [Enc α] {c : Nat} {ord : AtomicOrder} {align : Nat} {p : Ptr}
    {v : α} {m m' : Mem} (h : ((atomicLoadPtrAt α c ord align p).run m).run = some (.ok (v, m'))) :
    ∃ b blk o li m₁ pos, m.access p (intSize 64) align = pure (b, blk, o) ∧
      ((locIdx b o (intSize 64)).run (m.recordAt b o (intSize 64) .atomicRead)).run =
        some (.ok (li, m₁)) ∧
      (readOpts m₁ li false)[c]? = some pos ∧
      (Enc.decode ((m₁.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok v) ∧
      m' = loadM m₁ li ord ((m₁.atomics[li]!).msgs[pos]!) := by
  unfold atomicLoadPtrAt at h
  obtain ⟨⟨li, opts⟩, m₁, hp, h₁⟩ := MemM.bind_ok h
  obtain ⟨b, blk, o, ha, -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha hl
  refine ⟨b, blk, o, li, m₁, ?_⟩
  dsimp only at h₁
  split at h₁
  · rename_i pos hpos
    refine ⟨pos, ha, hl, hpos, ?_⟩
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, ho, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok ho
    subst this
    unfold loadM
    cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h₃ ⊢
    · obtain ⟨hd, rfl⟩ := MemM.lift_ok h₃
      exact ⟨hd, rfl⟩
    · obtain ⟨_, m₄, hc, h₄⟩ := MemM.bind_ok h₃
      have := modify_ok hc
      subst this
      obtain ⟨hd, rfl⟩ := MemM.lift_ok h₄
      exact ⟨hd, rfl⟩
  · exact (MemM.throw_ok h₁).elim

theorem atomicLoadPtrAt_noErr {α : Type} [Enc α] {c : Nat} {ord : AtomicOrder} {align : Nat}
    {p : Ptr} {m : Mem}
    (hprep : ∀ e, ((loadPrep 64 ord align p false).run m).run ≠ some (.error e))
    (hpos : ∀ li opts m₁, ((loadPrep 64 ord align p false).run m).run =
        some (.ok ((li, opts), m₁)) →
      ∃ pos, opts[c]? = some pos ∧
        ∃ w, (Enc.decode ((m₁.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok w))
    (e : Error) : ((atomicLoadPtrAt α c ord align p).run m).run ≠ some (.error e) := by
  intro h
  unfold atomicLoadPtrAt at h
  rcases MemM.bind_err h with he1 | ⟨⟨li, opts⟩, m₁, hp, h1⟩
  · exact hprep e he1
  obtain ⟨pos, hpos, w, hw⟩ := hpos li opts m₁ hp
  simp only [hpos] at h1
  rcases MemM.bind_err h1 with he2 | ⟨a₂, m₂, hg, h2⟩
  · exact MemM.get_err he2
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h2 with he3 | ⟨_, m₃, ho, h3⟩
  · exact MemM.modify_err he3
  have := modify_ok ho; subst this
  have hw' : (Enc.decode ((m₂.atomics[li]!).msgs[pos]!).bytes : Result α).run = some (.ok w) := hw
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h3
  · have := MemM.lift_err h3
    rw [hw'] at this; cases this
  · rcases MemM.bind_err h3 with he4 | ⟨_, m₄, hc, h4⟩
    · exact MemM.modify_err he4
    have := modify_ok hc; subst this
    have := MemM.lift_err h4
    rw [hw'] at this; cases this

/-- **Atomic load** of an owned pointer-valued word in a thread (choice 0: the newest message),
any order. -/
theorem FTTriple.atomicLoadPtr {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    FTTriple (aptsE p v) (atomicLoadPtrAt α 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) := by
  refine FTTriple.of_step (fun _ _ _ hh hp => aptsE_fix hh hp)
    fun m r rF hh hxr hxF hp hc ho hwf hld => ?_
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hKb := (abytesAt_kind hxr hab hsz hpb hblk).1
  have hnr : NoRace m b p.off.toNat (intSize 64) .atomicRead := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have hacc8 : m.access p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; simpa using hacc
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hab hsz hc ho hpb .atomicRead
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  have hnewest : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      (readOpts m₁ li false)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, -, -, -, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hwf (by decide) (by rw [hcur, hsz]) hl
    exact ⟨readOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur], hupd, hwf, htag⟩
  refine ⟨fun e hrun => ?_, fun w m' hrun => ?_⟩
  · refine atomicLoadPtrAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun
    · exact loadPrep_noErr (by simpa using hacc8) hnr
        (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
      simp only [Bool.false_eq_true, ↓reduceIte] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
      obtain ⟨hz, hbytes, -⟩ := hnewest li m₁ hl
      exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
  ·
      obtain ⟨b', blk', o', li, m₁, pos, ha', hl, hpos, hw, hm'⟩ := atomicLoadPtrAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
      obtain ⟨hz, hbytes, ⟨a, sn, next, hm₁⟩, hwf, htag⟩ := hnewest li m₁ hl
      rw [hz] at hpos; cases hpos
      have hwv : w = v := by
        rw [hbytes, hdec] at hw
        cases hw; rfl
      subst hm'
      have hblocks : (loadM m₁ li ord ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!)).blocks
          = m.blocks := by
        unfold loadM acqM observeM; split <;> simp [hm₁, Mem.recordAt]
      have hshapes : shapes (loadM m₁ li ord
          ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!)) = shapes m₁ := by
        unfold loadM acqM observeM; split <;> rfl
      obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            exact hxr _ _ (abytesAt_cell hab hpb hin)
          · rfl)
        (fun b' x => by rw [hshapes, hsz]; exact htag b' x) (kmono_of_blocks hblocks)
      have hs0 := fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead
      have hs1 := FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
        (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicRead) rfl)
        (by rw [intSize_64] at hl; exact hl)
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, A, S, K, bs, hal, hK, hsz, hv, by rw [← hsz]; exact hab'⟩,
        by rw [hshapes]; exact hwf, LDMono.of_blocks hblocks hld,
        hs0.trans (hs1.trans (FStepIn.loadM ((hs0.trans hs1).cur hc) _ _ _)),
        Mem.NoRevive.of_blocks hblocks⟩

/-- **Atomic load** of an owned pointer-valued word (sequential: choice 0), any order. -/
theorem FTriple.atomicLoadPtr {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    FTriple (aptsE p v) (atomicLoadPtrAt α 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) :=
  (FTTriple.atomicLoadPtr p v ord).toFTriple

/-- **The run of a strong `cmpxchg`** of an owned 64-bit word that holds the expected value
(choice 0: the newest message): it succeeds, and the word holds the new value. -/
theorem cmpxchgHit_run (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wpts p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout) :
    (∀ e, ((cmpxchgAt 0 succ fail 8 p v new).run m).run ≠ some (.error e)) ∧
    ∀ res m', ((cmpxchgAt 0 succ fail 8 p v new).run m).run = some (.ok (res, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪res = none⟫ ⋆ apts p new) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  obtain ⟨hKb, hlo⟩ := abytesAt_kind hxr hab hsz hpb hblk
  have hmine : ∀ x, p.off.toNat ≤ x → x < p.off.toNat + intSize 64 → r.heap.erase (b, x) ≠ none :=
    fun x h1 h2 => abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hab hsz hc ho hpb .atomicRead
  have hdec : (intOfBytes 64 bs).run = some (.ok v) := by rw [hv]; rfl
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      (casOpts m₁ li v)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      (∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x) ∧
      0 < (m₁.atomics[li]!).msgs.size := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hwf (by decide) (by rw [hcur, hsz]) hl
    refine ⟨filter_head (readOpts_zero hpos) ?_, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
    simp [hasRmwAfter_last]
  -- the second access (the write mark) does not race: the thread still owns the word
  have hnr₀ : ∀ li m₀, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₀)) →
      NoRace m₀ b p.off.toNat (intSize 64) .atomicWrite := by
    intro li m₀ hl
    obtain ⟨-, -, -, -, -, ⟨a', sn, next, hm₀⟩, -⟩ := hpost li m₀ hl
    have ho₀ : m₀.Owns m₀.current r.heap.erase := by rw [hm₀]; exact ho.recordAt hc
    exact ho₀.noRace hmine
  refine ⟨fun e hrun => ?_, fun res m' hrun => ?_⟩
  · refine cmpxchgAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) (fun li opts m₁ hp e' => ?_)
      e hrun
    · exact casPrep_noErr haccW8 (ho.noRace hmine) hlocok e'
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casPrep_ok hp
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
      exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casPrep_ok hp
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨-, -, -, -, -, ⟨a', sn, next, hm₁⟩, -⟩ := hpost li m₁ hl
      rw [casMarkWrite_run (by rw [accessW_of_blocks (by rw [hm₁]; try rfl)]; exact haccW8)
        (hnr₀ li m₁ hl)]
      simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]
  ·
      obtain ⟨b', blk', o', li, m₀, pos, old, ha', -, hl, hpos, hold, hbr⟩ := cmpxchgAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos0⟩ := hpost li m₀ hl
      rw [hz] at hpos; cases hpos
      rw [hbytes, hdec] at hold; cases hold
      obtain ⟨-, hres, -, hm'⟩ := hbr.resolve_right fun ⟨hne, _⟩ => hne rfl
      subst hm' hres
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      -- the step: the read's record, the location, the write's record
      have hs₀ := (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead).trans
        (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
          (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicRead) rfl)
          (by rw [intSize_64] at hl; exact hl))
      have hs₃ := hs₀.trans (fstep_record hh.disj (hs₀.cur hc) hab hsz hpb
        (by rw [hblk₀]; exact hblk) hKb hK (k := .atomicWrite))
      have key := write_newest_apts hh hab hsz hal hK hpb hblk hlive hlo (by omega) hA hS hKb hli
        hb ho hwf htag hld hpos0 new
      unfold rmwM
      dsimp only
      simp only [intSize_64]
      cases hq : succ.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [Mem.recordAt]) (by simp [Mem.recordAt, hblk₀]) hs₃ _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0)) (.inl rfl)
            (rmw_relClock _ _ _)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [acqM, Mem.recordAt]) (by simp [acqM, Mem.recordAt, hblk₀])
            (hs₃.trans (FStepIn.acq (hs₃.cur hc) _)) _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0)) (.inr (acqM_clock (hs₃.cur hc) _))
            (rmw_relClock _ _ _)

/-- **Strong `cmpxchg`** of an owned 64-bit word, whatever its layout, that holds the expected
value, in a thread (choice 0): it succeeds, and the word holds the new value. -/
theorem FTTriple.cmpxchgHitW (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTTriple (wpts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) :=
  FTTriple.of_step (fun _ _ _ hh hp => wpts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    cmpxchgHit_run p v new succ fail hh hxr hxF hp hc ho hw hl

/-- **Strong `cmpxchg`** of an owned 64-bit word that holds the expected value (sequential). -/
theorem FTriple.cmpxchgHitW (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTriple (wpts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) :=
  (FTTriple.cmpxchgHitW p v new succ fail).toFTriple

/-- **Strong `cmpxchg`** of an `apts` word that holds the expected value, in a thread. -/
theorem FTTriple.cmpxchgHit (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTTriple (apts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) :=
  (FTTriple.cmpxchgHitW p v new succ fail).pre fun _ => apts_wpts

/-- **Strong `cmpxchg`** of an `apts` word that holds the expected value. -/
theorem FTriple.cmpxchgHit (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTriple (apts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) :=
  (FTTriple.cmpxchgHit p v new succ fail).toFTriple

theorem readOpts_zero_rmw {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    (readOpts m li true)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf := floorPos_lt h
  obtain ⟨k, hk⟩ : ∃ k, (m.atomics[li]!).msgs.size - floorPos m li = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  unfold readOpts
  rw [← Array.getElem?_toList]
  simp [hk, List.range_succ_eq_map, List.filter_cons, ALoc.hasRmwAfter_last]

/-- **The run of an atomic RMW** of an owned word (choice 0, the newest message): it returns the
old value `v`, and the word holds `op.apply signed v x`. -/
theorem atomicRmw_run (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wpts p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout) :
    (∀ e, ((atomicRmwAt 0 op signed ord 8 p x).run m).run ≠ some (.error e)) ∧
    ∀ res m', ((atomicRmwAt 0 op signed ord 8 p x).run m).run = some (.ok (res, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪res = v⟫ ⋆ apts p (op.apply signed v x)) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    have hr := abytesAt_cell hab hpb (l := (b, p.off.toNat)) ⟨rfl, Nat.le_refl _, by omega⟩
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (hxr _ _ hr)
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (hxr _ _ hr)
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have hnr : NoRace m b p.off.toNat (intSize 64) .atomicWrite := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hab hsz hc ho hpb .atomicWrite
  have hdec : (intOfBytes 64 bs).run = some (.ok v) := by rw [hv]; rfl
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicWrite)).run = some (.ok (li, m₁)) →
      (readOpts m₁ li true)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicWrite with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      (∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x) ∧
      0 < (m₁.atomics[li]!).msgs.size := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hwf (by decide) (by rw [hcur, hsz]) hl
    exact ⟨readOpts_zero_rmw hpos, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
  refine ⟨fun e hrun => ?_, fun old m' hrun => ?_⟩
  · refine atomicRmwAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun
    · exact loadPrep_noErr (rmw := true) (by simpa using haccW8) hnr
        (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
    · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
      simp only [↓reduceIte] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
      exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
  ·
      obtain ⟨b', blk', o', li, m₀, pos, ha', -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos0⟩ := hpost li m₀ hl
      rw [hz] at hpos; cases hpos
      rw [hbytes, hdec] at hold; cases hold
      subst hm'
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      have hs₀ := (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicWrite).trans
        (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
          (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicWrite) rfl)
          (by rw [intSize_64] at hl; exact hl))
      have key := write_newest_apts hh hab hsz hal hK hpb hblk hlive hlo (by omega) hA hS hKb hli
        hb ho hwf htag hld hpos0 (op.apply signed v x)
      have hfp : ∀ e ∈ (m.recordAt b p.off.toNat 8 .atomicWrite).footprint, e ∈ m₀.footprint :=
        fun e he => by rw [hm₀]; exact he
      have hcl : m₀.clocks[m₀.current]! = (m.recordAt b p.off.toNat 8 .atomicWrite).clocks[m.current]! := by
        rw [hm₀]; rfl
      unfold rmwM
      dsimp only
      cases hq : ord.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ rfl hblk₀ hs₀ _ rfl ?_)
        exact msgCovAt_recordAt hc (by decide) hfp hb ho
          (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0)) (.inl hcl)
          (rmw_relClock _ _ _)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [acqM]) (by simp [acqM, hblk₀]) (hs₀.trans (FStepIn.acq (hs₀.cur hc) _))
            _ rfl ?_)
        exact msgCovAt_recordAt hc (by decide) hfp hb ho
          (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0))
          (.inr (by simp only [rmwMsg]; rw [acqM_clock (hs₀.cur hc), hcl]; rfl))
          (rmw_relClock _ _ _)

/-- **Atomic RMW** of an owned word, whatever its layout, in a thread (choice 0, the newest
message): it returns the old value `v`, and the word holds `op.apply signed v x`. -/
theorem FTTriple.atomicRmwW (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) :
    FTTriple (wpts p v) (atomicRmwAt 0 op signed ord 8 p x)
      (fun r => ⟪r = v⟫ ⋆ apts p (op.apply signed v x)) :=
  FTTriple.of_step (fun _ _ _ hh hp => wpts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    atomicRmw_run p v x op signed ord hh hxr hxF hp hc ho hw hl

/-- **Atomic RMW** of an owned word, whatever its layout (sequential). -/
theorem FTriple.atomicRmwW (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) :
    FTriple (wpts p v) (atomicRmwAt 0 op signed ord 8 p x)
      (fun r => ⟪r = v⟫ ⋆ apts p (op.apply signed v x)) :=
  (FTTriple.atomicRmwW p v x op signed ord).toFTriple

/-- **Atomic RMW** of an `apts` word in a thread (choice 0, the newest message). -/
theorem FTTriple.atomicRmw (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) :
    FTTriple (apts p v) (atomicRmwAt 0 op signed ord 8 p x)
      (fun r => ⟪r = v⟫ ⋆ apts p (op.apply signed v x)) :=
  (FTTriple.atomicRmwW p v x op signed ord).pre fun _ => apts_wpts

/-- **Typed atomic load** of an owned word, whatever its layout, in a thread (`atomicLoadAs`, a
packed type of 64 bits whose bits `v` are `valid`), choice `0`: the integer load, decoded by
`Packed.ofBits`. -/
theorem FTTriple.atomicLoadAsW {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTTriple (wpts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) := by
  unfold Zig.atomicLoadAs
  refine FTTriple.bind (FTTriple.atomicLoadW p v ord) fun w => FTTriple.lift fun hw => ?_
  subst hw
  have e : (StateT.lift (Packed.ofBits? (α := α) w) : MemM α) = pure (Packed.ofBits w) := by
    simp only [Packed.ofBits?, hv, ↓reduceIte]; rfl
  rw [e]
  exact FTTriple.ret' _ fun _ h => sep_lift.mpr ⟨rfl, h⟩

/-- **Typed atomic load** of an owned word, whatever its layout (sequential). -/
theorem FTriple.atomicLoadAsW {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTriple (wpts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadAsW p v ord hv).toFTriple

/-- **Typed atomic RMW** of an owned word, whatever its layout, in a thread (`atomicRmwAs`, a
packed type of 64 bits; `Node.beginResize`'s `@atomicRmw(Size, &node.size, .Or, …)`), choice `0`:
the integer RMW on the bits; the old bits `w` are `valid`. -/
theorem FTTriple.atomicRmwAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (op : RmwOp)
    (ord : AtomicOrder) (v : α) (hw : Packed.valid (α := α) w = true) :
    FTTriple (wpts p w) (Zig.atomicRmwAs 0 op ord 8 p v)
      (fun r => ⟪r = Packed.ofBits w⟫ ⋆ apts p (op.apply false w (Packed.toBits v))) := by
  unfold Zig.atomicRmwAs
  refine FTTriple.bind (FTTriple.atomicRmwW p w (Packed.toBits v) op false ord) fun b =>
    FTTriple.lift fun hb => ?_
  subst hb
  have e : (StateT.lift (Packed.ofBits? (α := α) b) : MemM α) = pure (Packed.ofBits b) := by
    simp only [Packed.ofBits?, hw, ↓reduceIte]; rfl
  rw [e]
  exact FTTriple.ret' _ fun _ h => sep_lift.mpr ⟨rfl, h⟩

/-- **Typed atomic RMW** of an owned word, whatever its layout (sequential). -/
theorem FTriple.atomicRmwAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (op : RmwOp)
    (ord : AtomicOrder) (v : α) (hw : Packed.valid (α := α) w = true) :
    FTriple (wpts p w) (Zig.atomicRmwAs 0 op ord 8 p v)
      (fun r => ⟪r = Packed.ofBits w⟫ ⋆ apts p (op.apply false w (Packed.toBits v))) :=
  (FTTriple.atomicRmwAsW p w op ord v hw).toFTriple

/-- **Typed atomic store** to an owned word, whatever its layout, in a thread (`atomicStoreAs`;
`Node.endResize`): the integer store of the bits. -/
theorem FTTriple.atomicStoreAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (ord : AtomicOrder)
    (v : α) : FTTriple (wpts p w) (Zig.atomicStoreAs 0 ord 8 p v) (fun _ => apts p (Packed.toBits v)) :=
  FTTriple.atomicStoreW p w (Packed.toBits v) ord

/-- **Typed atomic store** to an owned word, whatever its layout (sequential). -/
theorem FTriple.atomicStoreAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (ord : AtomicOrder)
    (v : α) : FTriple (wpts p w) (Zig.atomicStoreAs 0 ord 8 p v) (fun _ => apts p (Packed.toBits v)) :=
  FTriple.atomicStoreW p w (Packed.toBits v) ord

/-! ## Pointer words and `unordered` loads, any tag constraint

The rest of the arena's `alloc` (`stealFreeList`, `pushFreeList`, `Node.endResize`). -/

/-- An owned 8-aligned pointer-valued word that holds `v`, with any tag constraint (`wpts` for
`Enc` values). -/
def wptsE {α : Type} [Enc α] (p : Ptr) (v : α) : FAssn := fun r => ∃ A S K bs tg,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ Enc.decode bs = pure v ∧
  abytesAt p A S K bs tg r
theorem wptsE_fix {α : Type} [Enc α] {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {v : α}
    (h : wptsE p v r) : wptsE p v (r.fix m) := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := h
  obtain ⟨S', K', hn, hab'⟩ := abytesAt_fix hh hab (by omega)
  exact ⟨A, S', K', bs, tg, hal, norm_ne_constGlobal hn hK, hsz, hv, hab'⟩


theorem aptsE_wptsE {α : Type} [Enc α] {p : Ptr} {v : α} {r : Res} (h : aptsE p v r) :
    wptsE p v r := by
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := h
  exact ⟨A, S, K, bs, _, hal, hK, hsz, hv, hab⟩

/-- **The run of a pointer `.Xchg`** of an owned pointer-valued word (choice 0, the newest
message): it returns the old pointer `v`, and the word holds `new`. -/
theorem atomicXchgPtr_run {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) (p : Ptr)
    (v new : α) (ord : AtomicOrder) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wptsE p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout) :
    (∀ e, ((atomicXchgPtrAt 0 ord 8 p new).run m).run ≠ some (.error e)) ∧
    ∀ res m', ((atomicXchgPtrAt 0 ord 8 p new).run m).run = some (.ok (res, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪res = v⟫ ⋆ aptsE p new) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  obtain ⟨hKb, hlo⟩ := abytesAt_kind hxr hab hsz hpb hblk
  have hnr : NoRace m b p.off.toNat (intSize 64) .atomicWrite := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hab hsz hc ho hpb .atomicWrite
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicWrite)).run = some (.ok (li, m₁)) →
      (readOpts m₁ li true)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicWrite with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      (∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x) ∧
      0 < (m₁.atomics[li]!).msgs.size := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hwf (by decide) (by rw [hcur, hsz]) hl
    exact ⟨readOpts_zero_rmw hpos, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
  unfold atomicXchgPtrAt
  refine ⟨fun e hrun => ?_, fun res m' hrun => ?_⟩
  ·
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · exact loadPrep_noErr (rmw := true) (by simpa using haccW8) hnr
          (fun e'' => by rw [intSize_64]; exact hlocok e'') e he
      obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp1
      simp only [↓reduceIte] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
      (try simp only at h1); rw [hz] at h1; simp only at h1
      rcases MemM.bind_err h1 with he | ⟨a₂, m₂, hg, h2⟩
      · exact MemM.get_err he
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      rcases MemM.bind_err h2 with he | ⟨old, m₃, hd, h3⟩
      · have := MemM.lift_err he; rw [hbytes, hdec] at this; cases this
      obtain ⟨-, rfl⟩ := MemM.lift_ok hd
      rcases MemM.bind_err h3 with he | ⟨_, m₄, hw, h4⟩
      · exact rmwWriteBytes_noErr e he
      exact MemM.pure_err h4
  ·
      obtain ⟨⟨li, opts⟩, m₀, hp1, h1⟩ := MemM.bind_ok hrun
      obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp1
      simp only [↓reduceIte] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos0⟩ := hpost li m₀ hl
      (try simp only at h1); rw [hz] at h1; simp only at h1
      obtain ⟨a₂, m₂, hg, h2⟩ := MemM.bind_ok h1
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      obtain ⟨old, m₃, hd, h3⟩ := MemM.bind_ok h2
      have hd2 := (MemM.lift_ok hd).1
      have e4 := (MemM.lift_ok hd).2
      subst m₃
      rw [hbytes, hdec] at hd2; cases hd2
      obtain ⟨_, m₇, hw, h7⟩ := MemM.bind_ok h3
      have hm₇ := rmwWriteBytes_ok hw
      obtain ⟨hres, e7⟩ := MemM.pure_ok h7
      subst m'
      subst m₇
      subst hres
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      have hs₀ := (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicWrite).trans
        (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
          (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicWrite) rfl)
          (by rw [intSize_64] at hl; exact hl))
      have key := write_newest_aptsE hα hh hab hsz hal hK hpb hblk hlive hlo (by omega) hA hS hKb
        hli hb ho hwf htag hld hpos0 new
      have hfp : ∀ e ∈ (m.recordAt b p.off.toNat 8 .atomicWrite).footprint, e ∈ m₀.footprint :=
        fun e he => by rw [hm₀]; exact he
      have hcl : m₀.clocks[m₀.current]! = (m.recordAt b p.off.toNat 8 .atomicWrite).clocks[m.current]! := by
        rw [hm₀]; rfl
      unfold rmwBM
      dsimp only
      cases hq : ord.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ rfl hblk₀ hs₀ _ rfl ?_)
        exact msgCovAt_recordAt hc (by decide) hfp hb ho
          (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0)) (.inl hcl) (rmw_relClock _ _ _)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [acqM]) (by simp [acqM, hblk₀]) (hs₀.trans (FStepIn.acq (hs₀.cur hc) _))
            _ rfl ?_)
        exact msgCovAt_recordAt hc (by decide) hfp hb ho
          (Mem.MsgCovAt.relClock_of_mem (last_mem hpos0))
          (.inr (by show (acqM m₀ _).clocks[(acqM m₀ _).current]! = _
                    rw [acqM_clock (hs₀.cur hc), hcl]; rfl))
          (rmw_relClock _ _ _)

/-- **Pointer `.Xchg`** of an owned pointer-valued word, whatever its layout, in a thread
(choice 0, the newest message): it returns the old pointer `v`, and the word holds `new`. -/
theorem FTTriple.atomicXchgPtrW {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) (p : Ptr)
    (v new : α) (ord : AtomicOrder) :
    FTTriple (wptsE p v) (atomicXchgPtrAt 0 ord 8 p new) (fun r => ⟪r = v⟫ ⋆ aptsE p new) :=
  FTTriple.of_step (fun _ _ _ hh hp => wptsE_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    atomicXchgPtr_run hα p v new ord hh hxr hxF hp hc ho hw hl

/-- **Pointer `.Xchg`** of an owned pointer-valued word, whatever its layout (sequential). -/
theorem FTriple.atomicXchgPtrW {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) (p : Ptr)
    (v new : α) (ord : AtomicOrder) :
    FTriple (wptsE p v) (atomicXchgPtrAt 0 ord 8 p new) (fun r => ⟪r = v⟫ ⋆ aptsE p new) :=
  (FTTriple.atomicXchgPtrW hα p v new ord).toFTriple

/-- **Pointer `.Xchg`** of an `aptsE` word in a thread (choice 0, the newest message). -/
theorem FTTriple.atomicXchgPtr {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) (p : Ptr)
    (v new : α) (ord : AtomicOrder) :
    FTTriple (aptsE p v) (atomicXchgPtrAt 0 ord 8 p new) (fun r => ⟪r = v⟫ ⋆ aptsE p new) :=
  (FTTriple.atomicXchgPtrW hα p v new ord).pre fun _ => aptsE_wptsE

theorem weak_head {xs : Array Nat} {ys : Array (Nat × Bool)} {x : Nat} (h : xs[0]? = some x) :
    (xs.map (·, false) ++ ys)[0]? = some (x, false) := by
  rw [← Array.getElem?_toList] at h ⊢
  cases hl : xs.toList with
  | nil => rw [hl] at h; simp at h
  | cons y ys' => rw [hl] at h; simp at h; subst h; simp [Array.toList_append, hl]

/-- **The run of a weak pointer `cmpxchg`** of an owned pointer-valued word that holds the
expected value (choice 0, which is not a spurious failure): it succeeds, and the word holds the
new value. -/
theorem cmpxchgWeakPtr_run {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wptsE p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout) :
    (∀ e, ((cmpxchgWeakPtrAt 0 succ fail 8 p v new).run m).run ≠ some (.error e)) ∧
    ∀ res m', ((cmpxchgWeakPtrAt 0 succ fail 8 p v new).run m).run = some (.ok (res, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪res = none⟫ ⋆ aptsE p new) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  obtain ⟨hKb, hlo⟩ := abytesAt_kind hxr hab hsz hpb hblk
  have hmine : ∀ x, p.off.toNat ≤ x → x < p.off.toNat + intSize 64 → r.heap.erase (b, x) ≠ none :=
    fun x h1 h2 => abytesAt_mine hab hpb x h1 (by rw [hsz]; rw [intSize_64] at h2; exact h2)
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := locIdx_noErr_word hab hsz hc ho hpb .atomicRead
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      ((casPtrStrongOpts m₁ li v (readOpts m₁ li false)).map (·, false) ++
        ((readOpts m₁ li false).filter fun pos => ptrMsgEq m₁ li pos v).map (·, true))[0]? =
        some ((m₁.atomics[li]!).msgs.size - 1, false) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      (∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x) ∧
      0 < (m₁.atomics[li]!).msgs.size := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hwf (by decide) (by rw [hcur, hsz]) hl
    refine ⟨weak_head (filter_head (readOpts_zero hpos) ?_), by rw [lastBytes_eq hpos, hlast, hcur],
      hli, hb, ho, hupd, hwf, htag, hpos⟩
    simp [hasRmwAfter_last]
  -- the second access (the write mark) does not race: the thread still owns the word
  have hnr₀ : ∀ li m₀, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₀)) →
      NoRace m₀ b p.off.toNat (intSize 64) .atomicWrite := by
    intro li m₀ hl
    obtain ⟨-, -, -, -, -, ⟨a', sn, next, hm₀⟩, -⟩ := hpost li m₀ hl
    have ho₀ : m₀.Owns m₀.current r.heap.erase := by rw [hm₀]; exact ho.recordAt hc
    exact ho₀.noRace hmine
  unfold cmpxchgWeakPtrAt
  refine ⟨fun e hrun => ?_, fun res m' hrun => ?_⟩
  ·
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · unfold weakCasPtrPrep at he
        rcases MemM.bind_err he with he | ⟨⟨li, rd⟩, m₁, hp1, h1⟩
        · exact casReadPrep_noErr haccW8 (ho.noRace hmine) hlocok e he
        rcases MemM.bind_err h1 with he | ⟨a, m₂, hg, h2⟩
        · exact MemM.get_err he
        exact MemM.pure_err h2
      · unfold weakCasPtrPrep at hp1
        obtain ⟨⟨li', rd⟩, m₀, hp0, hq⟩ := MemM.bind_ok hp1
        obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casReadPrep_ok hp0
        obtain ⟨a, m₂, hg, h2⟩ := MemM.bind_ok hq
        obtain ⟨e1, e2⟩ := MemM.get_ok hg
        rw [e1, e2] at h2
        obtain ⟨hpair, e3⟩ := MemM.pure_ok h2
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        subst m₁
        rw [haccW8] at ha'; simp [pure, ExceptT.pure, ExceptT.mk] at ha'
        obtain ⟨rfl, rfl, rfl⟩ := ha'
        obtain ⟨hz, hbytes, -, -, -, ⟨a', sn, next, hm₀⟩, -⟩ := hpost li m₀ hl
        (try simp only at h1); rw [hz] at h1; simp only at h1
        rcases MemM.bind_err h1 with he | ⟨a₂, m₂, hg, h2⟩
        · exact MemM.get_err he
        obtain ⟨e1, e2⟩ := MemM.get_ok hg
        rw [e1, e2] at h2
        rcases MemM.bind_err h2 with he | ⟨old, m₃, hd, h3⟩
        · have := MemM.lift_err he; rw [hbytes, hdec] at this; cases this
        have hd2 := (MemM.lift_ok hd).1
        have e4 := (MemM.lift_ok hd).2
        subst m₃
        rw [hbytes, hdec] at hd2; cases hd2
        rcases MemM.bind_err h3 with he | ⟨a₄, m₄, hg, h4⟩
        · exact MemM.get_err he
        obtain ⟨e1, e2⟩ := MemM.get_ok hg
        rw [e1, e2] at h4
        rcases MemM.bind_err h4 with he | ⟨eq, m₅, hq5, h5⟩
        · have := MemM.lift_err he; rw [ptrValEq_self] at this; cases this
        have hq6 := (MemM.lift_ok hq5).1
        have e5 := (MemM.lift_ok hq5).2
        subst m₅
        rw [ptrValEq_self] at hq6; cases hq6
        unfold casPtrFinish at h5
        simp only [↓reduceIte] at h5
        rcases MemM.bind_err h5 with he | ⟨_, m₆, hc', h6⟩
        · rw [casMarkWrite_run (by rw [accessW_of_blocks (by rw [hm₀]; try rfl)]; exact haccW8)
            (hnr₀ li m₀ hl)] at he
          simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he
        rcases MemM.bind_err h6 with he | ⟨_, m₇, hw, h7⟩
        · exact rmwWriteBytes_noErr e he
        exact MemM.pure_err h7
  ·
      obtain ⟨⟨li, opts⟩, m₁, hp1, h1⟩ := MemM.bind_ok hrun
      unfold weakCasPtrPrep at hp1
      obtain ⟨⟨li', rd⟩, m₀, hp0, hq⟩ := MemM.bind_ok hp1
      obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casReadPrep_ok hp0
      obtain ⟨a, m₂, hg, h2⟩ := MemM.bind_ok hq
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      obtain ⟨hpair, e3⟩ := MemM.pure_ok h2
      simp only [Prod.mk.injEq] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      subst m₁
      rw [haccW8] at ha'; simp [pure, ExceptT.pure, ExceptT.mk] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := ha'
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos⟩ := hpost li m₀ hl
      (try simp only at h1); rw [hz] at h1; simp only at h1
      obtain ⟨a₂, m₂, hg, h2⟩ := MemM.bind_ok h1
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      obtain ⟨old, m₃, hd, h3⟩ := MemM.bind_ok h2
      have hd2 := (MemM.lift_ok hd).1
      have e4 := (MemM.lift_ok hd).2
      subst m₃
      rw [hbytes, hdec] at hd2; cases hd2
      obtain ⟨a₄, m₄, hg, h4⟩ := MemM.bind_ok h3
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h4
      obtain ⟨eq, m₅, hq5, h5⟩ := MemM.bind_ok h4
      have hq6 := (MemM.lift_ok hq5).1
      have e5 := (MemM.lift_ok hq5).2
      subst m₅
      rw [ptrValEq_self] at hq6; cases hq6
      unfold casPtrFinish at h5
      simp only [↓reduceIte] at h5
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      obtain ⟨_, m₆, hc', h6⟩ := MemM.bind_ok h5
      rw [casMarkWrite_run (by rw [accessW_of_blocks hblk₀]; exact haccW8) (hnr₀ li m₀ hl)] at hc'
      simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, StateT.pure, Option.some.injEq,
        Except.ok.injEq, Prod.mk.injEq] at hc'
      obtain ⟨-, rfl⟩ := hc'
      obtain ⟨_, m₇, hw, h7⟩ := MemM.bind_ok h6
      have hm₇ := rmwWriteBytes_ok hw
      obtain ⟨hres, e7⟩ := MemM.pure_ok h7
      subst m'
      subst m₇
      rw [hres]
      -- the step: the read's record, the location, the write's record
      have hs₀ := (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead).trans
        (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
          (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicRead) rfl)
          (by rw [intSize_64] at hl; exact hl))
      have hs₃ := hs₀.trans (fstep_record hh.disj (hs₀.cur hc) hab hsz hpb
        (by rw [hblk₀]; exact hblk) hKb hK (k := .atomicWrite))
      have key := write_newest_aptsE hα hh hab hsz hal hK hpb hblk hlive hlo (by omega) hA hS hKb
        hli hb ho hwf htag hld hpos new
      unfold rmwBM
      dsimp only
      simp only [intSize_64]
      cases hq : succ.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [Mem.recordAt]) (by simp [Mem.recordAt, hblk₀]) hs₃ _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos)) (.inl rfl) (rmw_relClock _ _ _)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [acqM, Mem.recordAt]) (by simp [acqM, Mem.recordAt, hblk₀])
            (hs₃.trans (FStepIn.acq (hs₃.cur hc) _)) _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos)) (.inr (acqM_clock (hs₃.cur hc) _))
            (rmw_relClock _ _ _)

/-- **Weak pointer `cmpxchg`** of an owned pointer-valued word, with any tag constraint, that
holds the expected value, in a thread (choice 0, which is not a spurious failure): it succeeds,
and the word holds the new value. -/
theorem FTTriple.cmpxchgWeakPtrW {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTTriple (wptsE p v) (cmpxchgWeakPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) :=
  FTTriple.of_step (fun _ _ _ hh hp => wptsE_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    cmpxchgWeakPtr_run hα p v new succ fail hh hxr hxF hp hc ho hw hl

/-- **Weak pointer `cmpxchg`** of an owned pointer-valued word, with any tag constraint, that
holds the expected value (sequential). -/
theorem FTriple.cmpxchgWeakPtrW {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTriple (wptsE p v) (cmpxchgWeakPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) :=
  (FTTriple.cmpxchgWeakPtrW hα p v new succ fail).toFTriple

/-- **Weak pointer `cmpxchg`** of an `aptsE` word that holds the expected value, in a thread. -/
theorem FTTriple.cmpxchgWeakPtr {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTTriple (aptsE p v) (cmpxchgWeakPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) :=
  (FTTriple.cmpxchgWeakPtrW hα p v new succ fail).pre fun _ => aptsE_wptsE


/-- **The run of an `unordered` atomic load** of an owned 64-bit word (choice 0): it reads `v`,
and the word is then an `apts`. -/
theorem atomicLoadUnordered_run (p : Ptr) (v : BitVec 64) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hxr : Exact m r) (hxF : Exact m rF) (hp : wpts p v r)
    (hc : m.current < m.clocks.size) (ho : m.Owns m.current r.heap.erase)
    (hwf : ShapesWF (shapes m)) (hld : m.LiveLayout) :
    (∀ e, ((atomicLoadUnorderedAt (n := 64) 0 8 p).run m).run ≠ some (.error e)) ∧
    ∀ w m', ((atomicLoadUnorderedAt (n := 64) 0 8 p).run m).run = some (.ok (w, m')) →
      ∃ r', Holds m' r' rF ∧ (⟪w = v⟫ ⋆ apts p v) r' ∧
        ShapesWF (shapes m') ∧ m'.LiveLayout ∧ FStepIn rF.heap.erase m m' ∧ m.NoRevive m' := by
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hKb := (abytesAt_kind hxr hab hsz hpb hblk).1
  have hnr : NoRace m b p.off.toNat 8 .atomicRead := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; exact h2)
  have hacc8 : m.access p 8 8 = pure (b, blk, p.off.toNat) := by simpa using hacc
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat 8).run (m.recordAt b p.off.toNat 8 .atomicRead)).run
      = some (.ok (li, m₁)) →
      (unorderedOpts m₁ li)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      (∃ a sn next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, seen := sn, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₁) b' x = some (p.off.toNat, 8)
        else tagOf (shapes m₁) b' x = none ∨ tagOf (shapes m₁) b' x = tagOf (shapes m) b' x := by
    intro li m₁ hl
    obtain ⟨hupd, -, -, -, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hwf (by decide) (by rw [hcur, hsz]) hl
    exact ⟨unorderedOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur], hupd, hwf, htag⟩
  have hdec : (intOfBytes 64 bs).run = some (.ok v) := by rw [hv]; rfl
  have e : atomicLoadUnorderedAt (n := 64) 0 8 p = (do
      let (li, opts) ← unorderedPrep 8 8 p
      let some pos := opts[0]? | throw .illegal
      intOfBytes 64 ((← get).atomics[li]!.msgs[pos]!.bytes) : MemM (BitVec 64)) := by
    unfold atomicLoadUnorderedAt; rw [intSize_64]; rfl
  rw [e]
  refine ⟨fun e hrun => ?_, fun w m' hrun => ?_⟩
  ·
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · exact unorderedPrep_noErr hacc8 hnr (locIdx_noErr_word hab hsz hc ho hpb .atomicRead) e he
      · obtain ⟨b', blk', o', ha', hl, rfl⟩ := unorderedPrep_ok hp1
        rw [hacc8] at ha'; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha'
        obtain ⟨rfl, rfl, rfl⟩ := ha'
        obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
        (try simp only at h1); rw [hz] at h1; simp only at h1
        rcases MemM.bind_err h1 with he | ⟨a₂, m₂, hg, h2⟩
        · exact MemM.get_err he
        obtain ⟨e1, e2⟩ := MemM.get_ok hg
        rw [e1, e2] at h2
        have := MemM.lift_err h2
        rw [hbytes] at this
        change ExceptT.run (intOfBytes 64 bs) = _ at this
        rw [hdec] at this; cases this
  ·
      obtain ⟨⟨li, opts⟩, m₁, hp1, h1⟩ := MemM.bind_ok hrun
      obtain ⟨b', blk', o', ha', hl, rfl⟩ := unorderedPrep_ok hp1
      rw [hacc8] at ha'; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := ha'
      obtain ⟨hz, hbytes, ⟨a, sn, next, hm₁⟩, hwf, htag⟩ := hpost li m₁ hl
      (try simp only at h1); rw [hz] at h1; simp only at h1
      obtain ⟨a₂, m₂, hg, h2⟩ := MemM.bind_ok h1
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      obtain ⟨hw, e3⟩ := MemM.lift_ok h2
      subst m'
      rw [hbytes] at hw
      change ExceptT.run (intOfBytes 64 bs) = _ at hw
      rw [hdec] at hw
      have hwv : w = v := by cases hw; rfl
      have hblocks : m₁.blocks = m.blocks := by rw [hm₁]; rfl
      obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            exact hxr _ _ (abytesAt_cell hab hpb hin)
          · rfl)
        (fun b' x => by rw [hsz]; exact htag b' x) (kmono_of_blocks hblocks)
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, apts_of hal hK hsz hv hab'⟩, hwf,
        LDMono.of_blocks hblocks hld,
        (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead).trans
          (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
            (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicRead) rfl) hl),
        Mem.NoRevive.of_blocks hblocks⟩

/-- **`unordered` atomic load** of an owned 64-bit word with any tag constraint, in a thread
(choice 0): it reads `v`, and the word is then an `apts`. -/
theorem FTTriple.atomicLoadUnorderedW (p : Ptr) (v : BitVec 64) :
    FTTriple (wpts p v) (atomicLoadUnorderedAt (n := 64) 0 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  FTTriple.of_step (fun _ _ _ hh hp => wpts_fix hh hp) fun _ _ _ hh hxr hxF hp hc ho hw hl =>
    atomicLoadUnordered_run p v hh hxr hxF hp hc ho hw hl

/-- **`unordered` atomic load** of an owned 64-bit word with any tag constraint (sequential). -/
theorem FTriple.atomicLoadUnorderedW (p : Ptr) (v : BitVec 64) :
    FTriple (wpts p v) (atomicLoadUnorderedAt (n := 64) 0 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadUnorderedW p v).toFTriple

/-- **`unordered` atomic load** of an `apts` word in a thread (choice 0). -/
theorem FTTriple.atomicLoadUnordered (p : Ptr) (v : BitVec 64) :
    FTTriple (apts p v) (atomicLoadUnorderedAt (n := 64) 0 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadUnorderedW p v).pre fun _ => apts_wpts

/-- **Typed `unordered` atomic load** of an owned word, whatever its layout, in a thread
(`atomicLoadUnorderedAs`, a packed type of 64 bits whose bits `v` are `valid`; `Node.endResize`'s
assert), choice `0`. -/
theorem FTTriple.atomicLoadUnorderedAsW {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64)
    (hv : Packed.valid (α := α) v = true) :
    FTTriple (wpts p v) (atomicLoadUnorderedAsAt α 0 8 p)
      (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) := by
  unfold atomicLoadUnorderedAsAt
  refine FTTriple.bind (FTTriple.atomicLoadUnorderedW p v) fun w => FTTriple.lift fun hw => ?_
  subst hw
  have e : (StateT.lift (Packed.ofBits? (α := α) w) : MemM α) = pure (Packed.ofBits w) := by
    simp only [Packed.ofBits?, hv, ↓reduceIte]; rfl
  rw [e]
  exact FTTriple.ret' _ fun _ h => sep_lift.mpr ⟨rfl, h⟩

/-- **Typed `unordered` atomic load** of an owned word, whatever its layout (sequential). -/
theorem FTriple.atomicLoadUnorderedAsW {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64)
    (hv : Packed.valid (α := α) v = true) :
    FTriple (wpts p v) (atomicLoadUnorderedAsAt α 0 8 p)
      (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadUnorderedAsW p v hv).toFTriple

/-! ## Typed atomics in a thread, and the sequential `apts`/`aptsE` rules

Each op has one thread rule, for a word of any tag constraint (`…W`); the typed ones are the
integer thread rules with the decode (`FTTriple.bind`). The `apts`/`aptsE` thread rules are the
`W` rules with the stronger precondition (`FTTriple.pre`), and every sequential rule is its
thread rule read sequentially (`FTTriple.toFTriple`). -/

/-- **Typed atomic load** of an `apts` word in a thread. -/
theorem FTTriple.atomicLoadAs {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTTriple (apts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadAsW p v ord hv).pre fun _ => apts_wpts

/-- **Typed atomic RMW** of an `apts` word in a thread. -/
theorem FTTriple.atomicRmwAs {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (op : RmwOp)
    (ord : AtomicOrder) (v : α) (hw : Packed.valid (α := α) w = true) :
    FTTriple (apts p w) (Zig.atomicRmwAs 0 op ord 8 p v)
      (fun r => ⟪r = Packed.ofBits w⟫ ⋆ apts p (op.apply false w (Packed.toBits v))) :=
  (FTTriple.atomicRmwAsW p w op ord v hw).pre fun _ => apts_wpts

/-- **Typed atomic store** to an `apts` word in a thread. -/
theorem FTTriple.atomicStoreAs {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (ord : AtomicOrder)
    (v : α) : FTTriple (apts p w) (Zig.atomicStoreAs 0 ord 8 p v) (fun _ => apts p (Packed.toBits v)) :=
  FTTriple.atomicStore p w (Packed.toBits v) ord

/-- **Typed `unordered` atomic load** of an `apts` word in a thread. -/
theorem FTTriple.atomicLoadUnorderedAs {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64)
    (hv : Packed.valid (α := α) v = true) :
    FTTriple (apts p v) (atomicLoadUnorderedAsAt α 0 8 p)
      (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadUnorderedAsW p v hv).pre fun _ => apts_wpts

theorem FTriple.atomicLoadAs {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTriple (apts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadAs p v ord hv).toFTriple

theorem FTriple.atomicRmwAs {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (op : RmwOp)
    (ord : AtomicOrder) (v : α) (hw : Packed.valid (α := α) w = true) :
    FTriple (apts p w) (Zig.atomicRmwAs 0 op ord 8 p v)
      (fun r => ⟪r = Packed.ofBits w⟫ ⋆ apts p (op.apply false w (Packed.toBits v))) :=
  (FTTriple.atomicRmwAs p w op ord v hw).toFTriple

theorem FTriple.atomicRmw (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool) (ord : AtomicOrder) :
    FTriple (apts p v) (atomicRmwAt 0 op signed ord 8 p x)
      (fun r => ⟪r = v⟫ ⋆ apts p (op.apply signed v x)) :=
  (FTTriple.atomicRmw p v x op signed ord).toFTriple

theorem FTriple.atomicXchgPtr {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) (p : Ptr)
    (v new : α) (ord : AtomicOrder) :
    FTriple (aptsE p v) (atomicXchgPtrAt 0 ord 8 p new) (fun r => ⟪r = v⟫ ⋆ aptsE p new) :=
  (FTTriple.atomicXchgPtr hα p v new ord).toFTriple

theorem FTriple.cmpxchgWeakPtr {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTriple (aptsE p v) (cmpxchgWeakPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) :=
  (FTTriple.cmpxchgWeakPtr hα p v new succ fail).toFTriple

theorem FTriple.atomicLoadUnordered (p : Ptr) (v : BitVec 64) :
    FTriple (apts p v) (atomicLoadUnorderedAt (n := 64) 0 8 p) (fun w => ⟪w = v⟫ ⋆ apts p v) :=
  (FTTriple.atomicLoadUnordered p v).toFTriple

/-! ## The oracle's choice at an owned word (`CTriple`)

A call (`CTriple`) goes on at an atomic op's oracle pick in every memory in which the thread
still owns its part and whose messages are covered (`Mem.MsgCov`, the resumption of
`CTriple.Run`). At an owned word every message happened before the thread (`newest_before`), so
the op has one option, the newest message (`…Count_le`): the pick is the choice `0` of the
op's thread rule (`CTriple.pick_one`). A weak `cmpxchg` has two (a success and a spurious
failure, `weakCasPtrCount_le`, `weakCasCount_le`): its pick keeps both (`CTriple.pick_le`). -/

/-- The bytes of an owned 8-byte word (`apts`, `aptsE` and their `W` forms). -/
def OwnedWord (p : Ptr) (r : Res) : Prop :=
  ∃ A S K bs tg, bs.size = 8 ∧ abytesAt p A S K bs tg r

theorem apts_owned {p : Ptr} {v : BitVec 64} {r : Res} (h : apts p v r) : OwnedWord p r :=
  let ⟨A, S, K, bs, _, _, hsz, _, hab⟩ := h; ⟨A, S, K, bs, _, hsz, hab⟩

theorem aptsE_owned {α : Type} [Enc α] {p : Ptr} {v : α} {r : Res} (h : aptsE p v r) :
    OwnedWord p r :=
  let ⟨A, S, K, bs, _, _, hsz, _, hab⟩ := h; ⟨A, S, K, bs, _, hsz, hab⟩

theorem wpts_owned {p : Ptr} {v : BitVec 64} {r : Res} (h : wpts p v r) : OwnedWord p r :=
  let ⟨A, S, K, bs, tg, _, _, hsz, _, hab⟩ := h; ⟨A, S, K, bs, tg, hsz, hab⟩

theorem wptsE_owned {α : Type} [Enc α] {p : Ptr} {v : α} {r : Res} (h : wptsE p v r) :
    OwnedWord p r :=
  let ⟨A, S, K, bs, tg, _, _, hsz, _, hab⟩ := h; ⟨A, S, K, bs, tg, hsz, hab⟩

section Count

variable {m : Mem} {r rF : Res} {p : Ptr}

/-- `newest_before` at the access of a prepared atomic op (its `locIdx` after its record). -/
theorem newest_at (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) {b o : Nat} {blk : Block}
    (hacc : m.access p (intSize 64) 8 = pure (b, blk, o)) {k : AccessKind} {li : Nat} {m₁ : Mem}
    (hl : ((locIdx b o (intSize 64)).run (m.recordAt b o (intSize 64) k)).run = some (.ok (li, m₁))) :
    0 < (m₁.atomics[li]!).msgs.size ∧
      VClock.le ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).clock
        (m₁.clocks[m₁.current]!) = true := by
  obtain ⟨A, S, K, bs, tg, hsz, hab⟩ := hw
  obtain ⟨hpb, -, -, -, -, -, rfl⟩ := access_eq hacc
  rw [intSize_64] at hl
  exact newest_before hh hc.1 ho hmc hc.2.1 hab hsz hpb hl

theorem floor_at (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) {b o : Nat} {blk : Block}
    (hacc : m.access p (intSize 64) 8 = pure (b, blk, o)) {k : AccessKind} {li : Nat} {m₁ : Mem}
    (hl : ((locIdx b o (intSize 64)).run (m.recordAt b o (intSize 64) k)).run = some (.ok (li, m₁))) :
    floorPos m₁ li = (m₁.atomics[li]!).msgs.size - 1 := by
  obtain ⟨A, S, K, bs, tg, hsz, hab⟩ := hw
  obtain ⟨hpb, -, -, -, -, -, rfl⟩ := access_eq hacc
  rw [intSize_64] at hl
  exact floor_newest hh hc.1 ho hmc hc.2.1 hab hsz hpb hl

theorem access_of_accessW {n a : Nat} {x : BlockId × Block × Nat}
    (h : m.accessW p n a = pure x) : m.access p n a = pure x :=
  (accessW_pure (by rw [h]; rfl)).1

/-- An atomic load or RMW of an owned word has one option. -/
theorem loadPrep_count_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (ord : AtomicOrder) (rmw : Bool) :
    optCount ((·.2) <$> loadPrep 64 ord 8 p rmw) m ≤ 1 := by
  refine optCount_snd_le (Nat.le_refl 1) fun li opts m' hrun => ?_
  obtain ⟨b, blk, o, hacc, -, hl, rfl⟩ := loadPrep_ok hrun
  cases rmw <;> simp only [Bool.false_eq_true, ↓reduceIte] at hacc hl
  · exact readOpts_size_le (floor_at hh hc ho hmc hw hacc hl)
  · exact readOpts_size_le (floor_at hh hc ho hmc hw (access_of_accessW hacc) hl)

theorem loadCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (ord : AtomicOrder) : loadCount 64 ord 8 p m ≤ 1 :=
  loadPrep_count_le hh hc ho hmc hw ord false

theorem rmwCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (ord : AtomicOrder) : rmwCount 64 ord 8 p m ≤ 1 :=
  loadPrep_count_le hh hc ho hmc hw ord true

/-- An atomic store to an owned word has one place. -/
theorem storeCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (ord : AtomicOrder) : storeCount 64 ord 8 p m ≤ 1 := by
  refine optCount_snd_le (Nat.le_refl 1) fun li opts m' hrun => ?_
  obtain ⟨b, blk, o, hacc, -, hl, rfl⟩ := storePrep_ok hrun
  exact writeSlots_size_le (floor_at hh hc ho hmc hw (access_of_accessW hacc) hl)

/-- The readable messages of a `cmpxchg` at an owned word: one. -/
theorem casReadPrep_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) {li : Nat} {readable : Array Nat} {m' : Mem}
    (hrun : ((casReadPrep 64 8 p).run m).run = some (.ok ((li, readable), m'))) :
    readable.size ≤ 1 := by
  obtain ⟨b, blk, o, hacc, -, hl, rfl⟩ := casReadPrep_ok hrun
  exact readOpts_size_le (floor_at hh hc ho hmc hw (access_of_accessW hacc) hl)

/-- A strong `cmpxchg` of an owned word has one option. -/
theorem casCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (succ : AtomicOrder) (expected : BitVec 64) :
    casCount 64 succ 8 p expected m ≤ 1 := by
  refine optCount_snd_le (Nat.le_refl 1) fun li opts m' hrun => ?_
  obtain ⟨b, blk, o, hacc, -, hl, rfl⟩ := casPrep_ok hrun
  exact Nat.le_trans Array.size_filter_le
    (readOpts_size_le (floor_at hh hc ho hmc hw (access_of_accessW hacc) hl))

/-- A strong pointer `cmpxchg` of an owned word has one option. -/
theorem casPtrCount_le {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (hh : Holds m r rF)
    (hc : m.FConc) (ho : m.Owns m.current r.heap.erase) (hmc : m.MsgCov) (hw : OwnedWord p r)
    (expected : α) : casPtrCount 8 p expected m ≤ 1 := by
  refine optCount_snd_le (Nat.le_refl 1) fun li opts m' hrun => ?_
  unfold casPtrPrep at hrun
  obtain ⟨⟨li₁, readable⟩, m₁, hp, h₁⟩ := MemM.bind_ok hrun
  obtain ⟨a, m₂, hg, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₂
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact Nat.le_trans Array.size_filter_le (casReadPrep_le hh hc ho hmc hw hp)

/-- The options of a weak `cmpxchg`: the strong ones and the forced failures, two filters of one
readable message at most. -/
theorem two_filters {xs : Array Nat} (h : xs.size ≤ 1) {f g : Nat → Bool} {β : Type}
    {F G : Nat → β} :
    ((xs.filter f).map F ++ (xs.filter g).map G).size ≤ 2 := by
  simp only [Array.size_append, Array.size_map]
  have := Array.size_filter_le (p := f) (xs := xs)
  have := Array.size_filter_le (p := g) (xs := xs)
  omega

/-- A weak pointer `cmpxchg` of an owned word has two options at most: a success and a spurious
failure. -/
theorem weakCasPtrCount_le {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (hh : Holds m r rF)
    (hc : m.FConc) (ho : m.Owns m.current r.heap.erase) (hmc : m.MsgCov) (hw : OwnedWord p r)
    (expected : α) : weakCasPtrCount 8 p expected m ≤ 2 := by
  refine optCount_snd_le (by decide) fun li opts m' hrun => ?_
  unfold weakCasPtrPrep at hrun
  obtain ⟨⟨li₁, readable⟩, m₁, hp, h₁⟩ := MemM.bind_ok hrun
  obtain ⟨a, m₂, hg, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₂
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact two_filters (casReadPrep_le hh hc ho hmc hw hp)

/-- A weak `cmpxchg` of an owned word has two options at most. -/
theorem weakCasCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) (succ : AtomicOrder) (expected : BitVec 64) :
    weakCasCount 64 succ 8 p expected m ≤ 2 := by
  refine optCount_snd_le (by decide) fun li opts m' hrun => ?_
  obtain ⟨b, blk, o, hacc, -, hl, rfl⟩ := weakCasPrep_ok hrun
  rw [weakCasOpts_eq]
  exact two_filters (readOpts_size_le (floor_at hh hc ho hmc hw (access_of_accessW hacc) hl))

/-- An `unordered` load of an owned word has one option. -/
theorem unorderedCount_le (hh : Holds m r rF) (hc : m.FConc) (ho : m.Owns m.current r.heap.erase)
    (hmc : m.MsgCov) (hw : OwnedWord p r) : unorderedCount 8 8 p m ≤ 1 := by
  refine optCount_snd_le (Nat.le_refl 1) fun li opts m' hrun => ?_
  obtain ⟨b, blk, o, hacc, hl, rfl⟩ := unorderedPrep_ok hrun
  obtain ⟨hpos, hle⟩ := newest_at hh hc ho hmc hw (b := b) (o := o) (blk := blk) hacc
    (by rw [intSize_64]; exact hl)
  have hj : (m'.atomics[li]!).msgs.size - 1 < (m'.atomics[li]!).msgs.size := by omega
  rw [getElem!_pos (m'.atomics[li]!).msgs _ hj] at hle
  have hge : (m'.atomics[li]!).msgs.size - 1 ≤ hbFloorPos m' li := by
    unfold hbFloorPos
    rw [← Array.foldl_toList]
    refine foldl_max_ge (fun x : Msg => VClock.le x.clock (m'.clocks[m'.current]!)) _ 0 _
      (.inl ⟨(m'.atomics[li]!).msgs[(m'.atomics[li]!).msgs.size - 1], ?_, hle⟩)
    rw [Array.mem_toList_iff, Array.mem_zipIdx_iff_getElem?]
    exact Array.getElem?_eq_getElem hj
  unfold unorderedOpts
  simp only [Array.size_map, Array.size_range]
  omega

end Count

namespace CTriple

variable {Tgt : Type}

/-- **An atomic load or RMW's pick at an owned word**: the choice `0` (module section). -/
theorem pick_load (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (apts p v) (ConcM.sync (.pick (loadCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ apts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => loadCount_le hh hc ho hmc (apts_owned hp) ord

theorem pick_loadE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (aptsE p v) (ConcM.sync (.pick (loadCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ aptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => loadCount_le hh hc ho hmc (aptsE_owned hp) ord

theorem pick_rmw (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (apts p v) (ConcM.sync (.pick (rmwCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ apts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => rmwCount_le hh hc ho hmc (apts_owned hp) ord

theorem pick_rmwE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (aptsE p v) (ConcM.sync (.pick (rmwCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ aptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => rmwCount_le hh hc ho hmc (aptsE_owned hp) ord

theorem pick_store (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (apts p v) (ConcM.sync (.pick (storeCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ apts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => storeCount_le hh hc ho hmc (apts_owned hp) ord

theorem pick_storeE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (aptsE p v) (ConcM.sync (.pick (storeCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ aptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => storeCount_le hh hc ho hmc (aptsE_owned hp) ord

theorem pick_cas (p : Ptr) (v : BitVec 64) (succ : AtomicOrder) (expected : BitVec 64) :
    CTriple (apts p v) (ConcM.sync (.pick (casCount 64 succ 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ apts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => casCount_le hh hc ho hmc (apts_owned hp) succ expected

theorem pick_casPtr {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (p : Ptr) (v expected : α) :
    CTriple (aptsE p v) (ConcM.sync (.pick (casPtrCount 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ aptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => casPtrCount_le hh hc ho hmc (aptsE_owned hp) expected

/-- A weak `cmpxchg`'s pick at an owned word: a success (`0`) or a spurious failure (`1`). -/
theorem pick_weakCasPtr {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (p : Ptr)
    (v expected : α) :
    CTriple (aptsE p v) (ConcM.sync (.pick (weakCasPtrCount 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c ≤ 1⟫ ⋆ aptsE p v) :=
  pick_le fun _ _ _ hh hp hc ho hmc => weakCasPtrCount_le hh hc ho hmc (aptsE_owned hp) expected

theorem pick_weakCas (p : Ptr) (v : BitVec 64) (succ : AtomicOrder) (expected : BitVec 64) :
    CTriple (apts p v) (ConcM.sync (.pick (weakCasCount 64 succ 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c ≤ 1⟫ ⋆ apts p v) :=
  pick_le fun _ _ _ hh hp hc ho hmc => weakCasCount_le hh hc ho hmc (apts_owned hp) succ expected

theorem pick_unordered (p : Ptr) (v : BitVec 64) :
    CTriple (apts p v) (ConcM.sync (.pick (unorderedCount 8 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ apts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => unorderedCount_le hh hc ho hmc (apts_owned hp)

theorem pick_unorderedE {α : Type} [Enc α] (p : Ptr) (v : α) :
    CTriple (aptsE p v) (ConcM.sync (.pick (unorderedCount 8 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ aptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => unorderedCount_le hh hc ho hmc (aptsE_owned hp)

/-! The same picks at a word of any tag constraint (`wpts`, `wptsE`): the counts read only the
owned bytes (`OwnedWord`). -/

theorem pick_loadW (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (wpts p v) (ConcM.sync (.pick (loadCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wpts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => loadCount_le hh hc ho hmc (wpts_owned hp) ord

theorem pick_loadWE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (wptsE p v) (ConcM.sync (.pick (loadCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => loadCount_le hh hc ho hmc (wptsE_owned hp) ord

theorem pick_rmwW (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (wpts p v) (ConcM.sync (.pick (rmwCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wpts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => rmwCount_le hh hc ho hmc (wpts_owned hp) ord

theorem pick_rmwWE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (wptsE p v) (ConcM.sync (.pick (rmwCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => rmwCount_le hh hc ho hmc (wptsE_owned hp) ord

theorem pick_storeW (p : Ptr) (v : BitVec 64) (ord : AtomicOrder) :
    CTriple (wpts p v) (ConcM.sync (.pick (storeCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wpts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => storeCount_le hh hc ho hmc (wpts_owned hp) ord

theorem pick_storeWE {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    CTriple (wptsE p v) (ConcM.sync (.pick (storeCount 64 ord 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => storeCount_le hh hc ho hmc (wptsE_owned hp) ord

theorem pick_casW (p : Ptr) (v : BitVec 64) (succ : AtomicOrder) (expected : BitVec 64) :
    CTriple (wpts p v) (ConcM.sync (.pick (casCount 64 succ 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wpts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => casCount_le hh hc ho hmc (wpts_owned hp) succ expected

theorem pick_casPtrW {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (p : Ptr) (v expected : α) :
    CTriple (wptsE p v) (ConcM.sync (.pick (casPtrCount 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => casPtrCount_le hh hc ho hmc (wptsE_owned hp) expected

theorem pick_weakCasPtrW {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (p : Ptr)
    (v expected : α) :
    CTriple (wptsE p v) (ConcM.sync (.pick (weakCasPtrCount 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c ≤ 1⟫ ⋆ wptsE p v) :=
  pick_le fun _ _ _ hh hp hc ho hmc => weakCasPtrCount_le hh hc ho hmc (wptsE_owned hp) expected

theorem pick_weakCasW (p : Ptr) (v : BitVec 64) (succ : AtomicOrder) (expected : BitVec 64) :
    CTriple (wpts p v) (ConcM.sync (.pick (weakCasCount 64 succ 8 p expected)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c ≤ 1⟫ ⋆ wpts p v) :=
  pick_le fun _ _ _ hh hp hc ho hmc => weakCasCount_le hh hc ho hmc (wpts_owned hp) succ expected

theorem pick_unorderedW (p : Ptr) (v : BitVec 64) :
    CTriple (wpts p v) (ConcM.sync (.pick (unorderedCount 8 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wpts p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => unorderedCount_le hh hc ho hmc (wpts_owned hp)

theorem pick_unorderedWE {α : Type} [Enc α] (p : Ptr) (v : α) :
    CTriple (wptsE p v) (ConcM.sync (.pick (unorderedCount 8 8 p)) : ConcM Tgt Nat)
      (fun c : Nat => ⟪c = 0⟫ ⋆ wptsE p v) :=
  pick_one fun _ _ _ hh hp hc ho hmc => unorderedCount_le hh hc ho hmc (wptsE_owned hp)

end CTriple

end Full
end Zig
