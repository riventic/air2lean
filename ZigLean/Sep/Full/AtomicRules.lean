import ZigLean.Sep.Full.AtomicPtr

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

Both are sequential readings (one thread, the oracle's choice `0`), as the other rules here.
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

/-- **Atomic load** of an owned pointer-valued word (sequential: choice 0), any order. -/
theorem FTriple.atomicLoadPtr {α : Type} [Enc α] (p : Ptr) (v : α) (ord : AtomicOrder) :
    FTriple (aptsE p v) (atomicLoadPtrAt α 0 ord 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_erase
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hacc8 : m.access p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; simpa using hacc
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_single (m := m.recordAt b p.off.toNat 8 .atomicRead)
    (singleThread_recordAt hs.1.single _ _ _ _) b p.off.toNat 8 e
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
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2.1 (by decide) (by rw [hcur, hsz]) hl
    exact ⟨readOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur], hupd, hwf, htag⟩
  cases hrun : ((atomicLoadPtrAt α 0 ord 8 p).run m).run with
  | none => trivial
  | some x =>
    cases x with
    | error e =>
      refine (atomicLoadPtrAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun).elim
      · exact loadPrep_noErr (by simpa using hacc8) (noRace_of_singleThread hs.1.single _ _ _ _)
          (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
        simp only [Bool.false_eq_true, ↓reduceIte] at ha'
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (hacc8.symm.trans ha')
        obtain ⟨hz, hbytes, -⟩ := hnewest li m₁ hl
        exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
    | ok x =>
      obtain ⟨w, m'⟩ := x
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
            exact hh.cell (abytesAt_cell hab hpb hin)
          · rfl)
        (fun b' x => by rw [hshapes, hsz]; exact htag b' x) (kmono_of_blocks hblocks)
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, A, S, K, bs, hal, hK, hsz, hv, by rw [← hsz]; exact hab'⟩,
        ⟨⟨singleThread_loadM (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _) _ _ _⟩,
          by rw [hshapes]; exact hwf, LDMono.of_blocks hblocks hs.2.2⟩⟩

/-- **Strong `cmpxchg`** of an owned 64-bit word that holds the expected value (sequential:
choice 0): it succeeds, and the word holds the new value. -/
theorem FTriple.cmpxchgHitW (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTriple (wpts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_erase
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    obtain ⟨-, -, b0, hb0, -, hl0⟩ := id hab
    rw [hpb] at hb0; cases hb0
    have hr := hl0 (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at hr
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (hh.cell hr)
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (hh.cell hr)
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_single (m := m.recordAt b p.off.toNat 8 .atomicRead)
    (singleThread_recordAt hs.1.single _ _ _ _) b p.off.toNat 8 e
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
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2.1 (by decide) (by rw [hcur, hsz]) hl
    refine ⟨filter_head (readOpts_zero hpos) ?_, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
    simp [hasRmwAfter_last]
  cases hrun : ((cmpxchgAt 0 succ fail 8 p v new).run m).run with
  | none => trivial
  | some x =>
    cases x with
    | error e =>
      refine (cmpxchgAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) (fun li opts m₁ hp e' => ?_)
        e hrun).elim
      · exact casPrep_noErr haccW8 (noRace_of_singleThread hs.1.single _ _ _ _) hlocok e'
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casPrep_ok hp
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
        obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
        exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := casPrep_ok hp
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
        obtain ⟨-, -, -, -, -, ⟨a', sn, next, hm₁⟩, -⟩ := hpost li m₁ hl
        rw [casMarkWrite_run (by rw [accessW_of_blocks (by rw [hm₁]; try rfl)]; exact haccW8)
          (noRace_of_singleThread (by rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _)
            _ _ _ _)]
        simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]
    | ok x =>
      obtain ⟨res, m'⟩ := x
      obtain ⟨b', blk', o', li, m₀, pos, old, ha', -, hl, hpos, hold, hbr⟩ := cmpxchgAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos0⟩ := hpost li m₀ hl
      rw [hz] at hpos; cases hpos
      rw [hbytes, hdec] at hold; cases hold
      obtain ⟨-, hres, -, hm'⟩ := hbr.resolve_right fun ⟨hne, _⟩ => hne rfl
      subst hm' hres
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      have key : ∀ M₂ : Mem, M₂.atomics = m₀.atomics → M₂.blocks = m.blocks →
          M₂.SingleThread → ∀ msg : Msg, msg.bytes = Enc.encode new →
          ∃ r', Holds (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg) r' rF ∧ apts p new r' ∧
            (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg).FSeq := by
        intro M₂ hat hbl hst msg hmb
        have hn1 : (m₀.atomics[li]!).msgs.size - 1 + 1 = (M₂.atomics[li]!).msgs.size := by
          rw [hat]; omega
        rw [hn1]
        have hb₂ : M₂.blocks[(M₂.atomics[li]!).block]? = some blk := by
          rw [hat, hb, hbl]; exact hblk
        have hins := insertM_last (li := li) (msg := msg) hb₂
        have hblocks : (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li
            M₂.nextMsg).blocks =
            m.blocks.set! b { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode new) } := by
          unfold observeM; rw [hins, hat, hb, ho, hbl, hmb]
        have hshapes : shapes (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li
            M₂.nextMsg) = shapes m₀ := by
          show shapes (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) = _
          rw [shapes_insertM_last hb₂ (by rw [hat]; exact hli)]
          simp [shapes, hat]
        have henc : (Enc.encode new).size = 8 := LawfulEnc.size_encode new
        have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive (bs := Enc.encode new)
          (by rw [henc]; omega) hlo
        obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := Enc.encode new) (by rw [henc, hsz])
          hpb
          (fun l => by
            rw [heap_of_blocks (m := m.write b blk p.off.toNat (Enc.encode new)) hblocks, hwr, henc,
              hsz, hA, hS, hKb])
          (fun b' x => by rw [hshapes, hsz]; exact htag b' x)
          (KMono.set (blk' := { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode new) })
            hblk rfl hblocks)
        refine ⟨r', hh', apts_of hal hK henc (LawfulEnc.decode_encode new) (by rw [henc, ← hsz]; exact hab'), ⟨⟨?_⟩, by rw [hshapes]; exact hwf,
          ld_write hblk (by rw [henc]; omega) hblocks hs.2.2⟩⟩
        unfold observeM
        exact singleThread_insertM hst _ _ _
      have hst₀ : m₀.SingleThread := by
        rw [hm₀]; exact singleThread_recordAt hs.1.single _ _ _ _
      have hst₃ := singleThread_recordAt hst₀ b p.off.toNat (intSize 64) .atomicWrite
      unfold rmwM
      dsimp only
      cases hq : succ.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ (by simp [Mem.recordAt]) (by simp [Mem.recordAt, hblk₀]) hst₃ _ ?_)
        rfl
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ (by simp [acqM, Mem.recordAt]) (by simp [acqM, Mem.recordAt, hblk₀])
            (singleThread_acqM hst₃ _) _ ?_)
        rfl

/-- **Strong `cmpxchg`** of an `apts` word that holds the expected value. -/
theorem FTriple.cmpxchgHit (p : Ptr) (v new : BitVec 64) (succ fail : AtomicOrder) :
    FTriple (apts p v) (cmpxchgAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ apts p new) :=
  (FTriple.cmpxchgHitW p v new succ fail).pre fun _ => apts_wpts

theorem readOpts_zero_rmw {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    (readOpts m li true)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf := floorPos_lt h
  obtain ⟨k, hk⟩ : ∃ k, (m.atomics[li]!).msgs.size - floorPos m li = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  unfold readOpts
  rw [← Array.getElem?_toList]
  simp [hk, List.range_succ_eq_map, List.filter_cons, ALoc.hasRmwAfter_last]

/-- **Atomic RMW** of an owned word, whatever its layout (sequential: choice 0, the newest
message): it returns the old value `v`, and the word holds `op.apply signed v x`. -/
theorem FTriple.atomicRmwW (p : Ptr) (v x : BitVec 64) (op : RmwOp) (signed : Bool)
    (ord : AtomicOrder) :
    FTriple (wpts p v) (atomicRmwAt 0 op signed ord 8 p x)
      (fun r => ⟪r = v⟫ ⋆ apts p (op.apply signed v x)) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_erase
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    have hr := abytesAt_cell hab hpb (l := (b, p.off.toNat)) ⟨rfl, Nat.le_refl _, by omega⟩
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (hh.cell hr)
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (hh.cell hr)
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicWrite) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_single (m := m.recordAt b p.off.toNat 8 .atomicWrite)
    (singleThread_recordAt hs.1.single _ _ _ _) b p.off.toNat 8 e
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
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicWrite) hs.2.1 (by decide) (by rw [hcur, hsz]) hl
    exact ⟨readOpts_zero_rmw hpos, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
  cases hrun : ((atomicRmwAt 0 op signed ord 8 p x).run m).run with
  | none => trivial
  | some y =>
    cases y with
    | error e =>
      refine (atomicRmwAt_noErr (fun e' => ?_) (fun li opts m₁ hp => ?_) e hrun).elim
      · exact loadPrep_noErr (rmw := true) (by simpa using haccW8)
          (noRace_of_singleThread hs.1.single _ _ _ _) (fun e'' => by rw [intSize_64]; exact hlocok e'') e'
      · obtain ⟨b', blk', o', ha', -, hl, rfl⟩ := loadPrep_ok hp
        simp only [↓reduceIte] at ha'
        obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
        obtain ⟨hz, hbytes, -⟩ := hpost li m₁ hl
        exact ⟨_, hz, v, by rw [hbytes, hdec]⟩
    | ok y =>
      obtain ⟨old, m'⟩ := y
      obtain ⟨b', blk', o', li, m₀, pos, ha', -, hl, hpos, hold, hm'⟩ := atomicRmwAt_ok hrun
      obtain ⟨rfl, rfl, rfl⟩ := access_inj (haccW8.symm.trans ha')
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', sn, next, hm₀⟩, hwf, htag, hpos0⟩ := hpost li m₀ hl
      rw [hz] at hpos; cases hpos
      rw [hbytes, hdec] at hold; cases hold
      subst hm'
      have hblk₀ : m₀.blocks = m.blocks := by rw [hm₀]; try rfl
      have key : ∀ M₂ : Mem, M₂.atomics = m₀.atomics → M₂.blocks = m.blocks →
          M₂.SingleThread → ∀ msg : Msg, msg.bytes = Enc.encode (op.apply signed v x) →
          ∃ r', Holds (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg) r' rF ∧ apts p (op.apply signed v x) r' ∧
            (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg).FSeq := by
        intro M₂ hat hbl hst msg hmb
        have hn1 : (m₀.atomics[li]!).msgs.size - 1 + 1 = (M₂.atomics[li]!).msgs.size := by
          rw [hat]; omega
        rw [hn1]
        have hb₂ : M₂.blocks[(M₂.atomics[li]!).block]? = some blk := by
          rw [hat, hb, hbl]; exact hblk
        have hins := insertM_last (li := li) (msg := msg) hb₂
        have hblocks : (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li
            M₂.nextMsg).blocks = m.blocks.set! b
              { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode (op.apply signed v x)) } := by
          unfold observeM; rw [hins, hat, hb, ho, hbl, hmb]
        have hshapes : shapes (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li
            M₂.nextMsg) = shapes m₀ := by
          show shapes (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) = _
          rw [shapes_insertM_last hb₂ (by rw [hat]; exact hli)]
          simp [shapes, hat]
        have henc : (Enc.encode (op.apply signed v x)).size = 8 := LawfulEnc.size_encode _
        have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive
          (bs := Enc.encode (op.apply signed v x)) (by rw [henc]; omega) hlo
        obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := Enc.encode (op.apply signed v x))
          (by rw [henc, hsz]) hpb
          (fun l => by
            rw [heap_of_blocks (m := m.write b blk p.off.toNat (Enc.encode (op.apply signed v x)))
              hblocks, hwr, henc, hsz, hA, hS, hKb])
          (fun b' x => by rw [hshapes, hsz]; exact htag b' x)
          (KMono.set (blk' := { blk with
            bytes := writeBytes blk.bytes p.off.toNat (Enc.encode (op.apply signed v x)) })
            hblk rfl hblocks)
        refine ⟨r', hh', apts_of hal hK henc (LawfulEnc.decode_encode (op.apply signed v x))
          (by rw [henc, ← hsz]; exact hab'),
          ⟨⟨?_⟩, by rw [hshapes]; exact hwf, ld_write hblk (by rw [henc]; omega) hblocks hs.2.2⟩⟩
        unfold observeM
        exact singleThread_insertM hst _ _ _
      have hst₀ : m₀.SingleThread := by
        rw [hm₀]; exact singleThread_recordAt hs.1.single _ _ _ _
      unfold rmwM
      dsimp only
      cases hq : ord.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ rfl hblk₀ hst₀ _ rfl)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ (by simp [acqM]) (by simp [acqM, hblk₀]) (singleThread_acqM hst₀ _) _ rfl)

/-- **Typed atomic load** of an owned word (`atomicLoadAs`, a packed type of 64 bits whose bits
`v` are `valid`), choice `0`: the integer load, decoded by `Packed.ofBits`. -/
theorem FTriple.atomicLoadAsW {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTriple (wpts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) := by
  unfold Zig.atomicLoadAs
  refine FTriple.bind (FTriple.atomicLoadW p v ord) fun w => FTriple.lift fun hw => ?_
  subst hw
  have e : (StateT.lift (Packed.ofBits? (α := α) w) : MemM α) = pure (Packed.ofBits w) := by
    simp only [Packed.ofBits?, hv, ↓reduceIte]; rfl
  rw [e]
  exact FTriple.ret' _ fun _ h => sep_lift.mpr ⟨rfl, h⟩

theorem FTriple.atomicLoadAs {α : Type} [Packed α 64] (p : Ptr) (v : BitVec 64) (ord : AtomicOrder)
    (hv : Packed.valid (α := α) v = true) :
    FTriple (apts p v) (Zig.atomicLoadAs α 0 ord 8 p) (fun w => ⟪w = Packed.ofBits v⟫ ⋆ apts p v) :=
  (FTriple.atomicLoadAsW p v ord hv).pre fun _ => apts_wpts

/-- **Typed atomic RMW** of an owned word (`atomicRmwAs`, a packed type of 64 bits; `Node.beginResize`'s
`@atomicRmw(Size, &node.size, .Or, …)`), choice `0`: the integer RMW on the bits; the old bits
`w` are `valid`. -/
theorem FTriple.atomicRmwAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (op : RmwOp)
    (ord : AtomicOrder) (v : α) (hw : Packed.valid (α := α) w = true) :
    FTriple (wpts p w) (Zig.atomicRmwAs 0 op ord 8 p v)
      (fun r => ⟪r = Packed.ofBits w⟫ ⋆ apts p (op.apply false w (Packed.toBits v))) := by
  unfold Zig.atomicRmwAs
  refine FTriple.bind (FTriple.atomicRmwW p w (Packed.toBits v) op false ord) fun b =>
    FTriple.lift fun hb => ?_
  subst hb
  have e : (StateT.lift (Packed.ofBits? (α := α) b) : MemM α) = pure (Packed.ofBits b) := by
    simp only [Packed.ofBits?, hw, ↓reduceIte]; rfl
  rw [e]
  exact FTriple.ret' _ fun _ h => sep_lift.mpr ⟨rfl, h⟩

/-- **Typed atomic store** to an owned word (`atomicStoreAs`; `Node.endResize`): the integer
store of the bits. -/
theorem FTriple.atomicStoreAsW {α : Type} [Packed α 64] (p : Ptr) (w : BitVec 64) (ord : AtomicOrder)
    (v : α) : FTriple (wpts p w) (Zig.atomicStoreAs 0 ord 8 p v) (fun _ => apts p (Packed.toBits v)) :=
  FTriple.atomicStoreW p w (Packed.toBits v) ord

end Full
end Zig
