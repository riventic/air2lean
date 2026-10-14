import ZigLean.Sep.Full.Atomic
import ZigLean.Conc.AtomicWord
import ZigLean.Conc.PtrAtomicLemmas

/-!
# Pointer-valued atomic points-to (`docs/sep-full-state.md`)

`aptsE p v`: the 8 bytes at the 8-aligned `p` decode to `v` (`Enc`, for `Zig.Ptr` and
`Option Zig.Ptr` a pointer with its provenance), and their atomic tag is `none` or exactly
`(p.off, 8)`, as for the integer `apts` (`ZigLean/Sep/Full/Res.lean`). Rules at choice `0`,
proved as thread rules (`FTTriple`, `ZigLean/Sep/Full/Atomic.lean`) and read sequentially by
`toFTriple`:

* `FTriple.atomicLoadUnorderedEnc`: an `unordered` load (`Zig.atomicLoadUnorderedEncAt`,
  `std.heap.PageAllocator`'s read of `addr_hint`) reads `v`.
* `FTriple.cmpxchgPtr`: a strong pointer `cmpxchg` (`Zig.cmpxchgPtrAt`, the hint's update) whose
  expected value is the one the word holds succeeds, and the word then holds the new value. The
  compare is by identity (`ptrValEq_self`), so no block address is read.
-/

namespace Zig
namespace Full

open FAssn Conc Conc.Proto

/-- **Atomic points-to** of an 8-byte value of type `α` (module doc). -/
def aptsE {α : Type} [Enc α] (p : Ptr) (v : α) : FAssn := fun r => ∃ A S K bs,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ Enc.decode bs = pure v ∧
  abytesAt p A S K bs (some (p.off.toNat, 8)) r
theorem aptsE_fix {α : Type} [Enc α] {m : Mem} {r rF : Res} (hh : Holds m r rF) {p : Ptr} {v : α}
    (h : aptsE p v r) : aptsE p v (r.fix m) := by
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := h
  obtain ⟨S', K', hn, hab'⟩ := abytesAt_fix hh hab (by omega)
  exact ⟨A, S', K', bs, hal, norm_ne_constGlobal hn hK, hsz, hv, hab'⟩


theorem hbFloorPos_le (m : Mem) (li : Nat) :
    hbFloorPos m li = 0 ∨ hbFloorPos m li < (m.atomics[li]!).msgs.size := by
  unfold hbFloorPos
  generalize hl : m.atomics[li]! = l
  have key : ∀ (xs : List (Msg × Nat)) (a : Nat), (a = 0 ∨ a < l.msgs.size) →
      (∀ x ∈ xs, x.2 < l.msgs.size) →
      xs.foldl (fun a (x, i) => if VClock.le x.clock (m.clocks[m.current]!) then Nat.max a i
        else a) a = 0 ∨
      xs.foldl (fun a (x, i) => if VClock.le x.clock (m.clocks[m.current]!) then Nat.max a i
        else a) a < l.msgs.size := by
    intro xs
    induction xs with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hx
      simp only [List.foldl_cons]
      apply ih _ _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      have := hx x List.mem_cons_self
      split
      · rcases ha with ha | ha
        · right; subst ha; simp; omega
        · right; simp [Nat.max_def]; split <;> omega
      · exact ha
  rw [← Array.foldl_toList]
  apply key _ 0 (.inl rfl)
  intro x hx
  rw [Array.toList_zipIdx] at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  simp at hi ⊢; omega

/-- A sequential `unordered` read reads the newest message. -/
theorem unorderedOpts_zero {m : Mem} {li : Nat} (h : 0 < (m.atomics[li]!).msgs.size) :
    (unorderedOpts m li)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf : hbFloorPos m li < (m.atomics[li]!).msgs.size := by
    rcases hbFloorPos_le m li with e | e
    · omega
    · exact e
  obtain ⟨k, hk⟩ : ∃ k, (m.atomics[li]!).msgs.size - hbFloorPos m li = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  unfold unorderedOpts
  rw [← Array.getElem?_toList]
  simp [hk, List.range_succ_eq_map]

theorem unorderedPrep_ok {size align : Nat} {p : Ptr} {m m' : Mem} {li : Nat} {opts : Array Nat}
    (h : ((unorderedPrep size align p).run m).run = some (.ok ((li, opts), m'))) :
    ∃ b blk o, (m.access p size align).run = some (.ok (b, blk, o)) ∧
      ((locIdx b o size).run (m.recordAt b o size .atomicRead)).run = some (.ok (li, m')) ∧
      opts = unorderedOpts m' li := by
  unfold unorderedPrep at h
  obtain ⟨a₁, m₁, hg, h₁⟩ := MemM.bind_ok h
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨⟨b, blk, o⟩, m₂, ha, h₂⟩ := MemM.bind_ok h₁
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  obtain ⟨_, m₃, hr, h₃⟩ := MemM.bind_ok h₂
  obtain ⟨-, rfl⟩ := recordAccess_ok hr
  obtain ⟨li', m₄, hl, h₄⟩ := MemM.bind_ok h₃
  obtain ⟨a₅, m₅, hg, h₅⟩ := MemM.bind_ok h₄
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  obtain ⟨he, rfl⟩ := MemM.pure_ok h₅
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨b, blk, o, ha, hl, rfl⟩

theorem unorderedPrep_noErr {size align : Nat} {p : Ptr} {m : Mem} {b o : Nat} {blk : Block}
    (hacc : m.access p size align = pure (b, blk, o)) (hnr : NoRace m b o size .atomicRead)
    (hloc : ∀ e, ((locIdx b o size).run (m.recordAt b o size .atomicRead)).run ≠ some (.error e))
    (e : Error) : ((unorderedPrep size align p).run m).run ≠ some (.error e) := by
  intro h
  unfold unorderedPrep at h
  rcases MemM.bind_err h with he1 | ⟨a₁, m₁, hg, h1⟩
  · exact MemM.get_err he1
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  rcases MemM.bind_err h1 with he2 | ⟨r, m₂, ha, h2⟩
  · have := MemM.lift_err he2; rw [hacc] at this; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at this
  obtain ⟨ha, rfl⟩ := MemM.lift_ok ha
  rw [hacc] at ha; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha; subst ha
  rcases MemM.bind_err h2 with he3 | ⟨_, m₃, hr, h3⟩
  · rw [recordAccess_run hnr] at he3; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he3
  obtain ⟨-, rfl⟩ := recordAccess_ok hr
  rcases MemM.bind_err h3 with he4 | ⟨li, m₄, hl, h4⟩
  · exact hloc e he4
  rcases MemM.bind_err h4 with he5 | ⟨a₅, m₅, hg, h5⟩
  · exact MemM.get_err he5
  obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
  exact MemM.pure_err h5

/-- `write_newest_apts` for a pointer-valued word: an `aptsE` of the written value. -/
theorem write_newest_aptsE {α : Type} [Enc α] [LawfulEnc α] (hα : Enc.size α = 8) {m m₀ : Mem}
    {r rF : Res} (hh : Holds m r rF) {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}
    {tg : Option (Nat × Nat)} (hab : abytesAt p A S K bs tg r) (hsz : bs.size = 8)
    (hal : (A + p.off.toNat) % 8 = 0) (hK : K ≠ .constGlobal) {b : BlockId} {blk : Block}
    (hpb : p.block = some b) (hblk : m.blocks[b]? = some blk) (hlive : blk.live = true)
    (hlo : blk.kind.mappedLo ≤ p.off.toNat) (hfit : p.off.toNat + 8 ≤ blk.bytes.size)
    (hA : blk.addr = A) (hS : blk.bytes.size = S) (hKb : blk.kind = K)
    {li : Nat} (hli : li < m₀.atomics.size) (hb : (m₀.atomics[li]!).block = b)
    (ho : (m₀.atomics[li]!).off = p.off.toNat) (hwf : ShapesWF (shapes m₀))
    (htag : ∀ b' x, if Covers b' x (b, p.off.toNat, 8) then tagOf (shapes m₀) b' x = some (p.off.toNat, 8)
      else tagOf (shapes m₀) b' x = none ∨ tagOf (shapes m₀) b' x = tagOf (shapes m) b' x)
    (hld : m.LiveLayout) (hpos : 0 < (m₀.atomics[li]!).msgs.size) (new : α) :
    ∀ M₂ : Mem, M₂.atomics = m₀.atomics → M₂.blocks = m.blocks → m.Aux M₂ →
      FStepIn rF.heap.erase m M₂ →
      ∀ msg : Msg, msg.bytes = Enc.encode new → M₂.MsgCovAt li msg →
      ∃ r', Holds (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
          M₂.nextMsg) r' rF ∧ aptsE p new r' ∧
        ShapesWF (shapes (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
          M₂.nextMsg)) ∧
        (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li M₂.nextMsg).LiveLayout ∧
        FStepIn rF.heap.erase m
          (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li M₂.nextMsg) ∧
        m.NoRevive (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li M₂.nextMsg) := by
  intro M₂ hat hbl hax hs₂ msg hmb hmc
  have hn1 : (m₀.atomics[li]!).msgs.size - 1 + 1 = (M₂.atomics[li]!).msgs.size := by
    rw [hat]; omega
  rw [hn1]
  have henc : (Enc.encode new).size = 8 := by rw [LawfulEnc.size_encode, hα]
  obtain ⟨r', hh', hab', h3⟩ := write_newest hh hab hsz hK hpb hblk hlive hlo hfit hA
    hS hKb hli hb ho hwf htag hld hat hbl hax hs₂ msg (by rw [hmb, henc]) hmc
  exact ⟨r', hh', ⟨A, S, K, Enc.encode new, hal, hK, henc, LawfulEnc.decode_encode new,
    by rw [← hmb]; exact hab'⟩, h3⟩

/-- **`unordered` atomic load** of an owned pointer-valued word in a thread (choice 0: the
newest message, which the owner reads). -/
theorem FTTriple.atomicLoadUnorderedEnc {α : Type} [Enc α] (p : Ptr) (v : α) :
    FTTriple (aptsE p v) (atomicLoadUnorderedEncAt α 0 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) := by
  refine FTTriple.of_step (fun _ _ _ hh hp => aptsE_fix hh hp)
    fun m r rF hh hxr hxF hp hc ho hwf hld => ?_
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := hp
  have hm := hh.heap_exact hxr hxF
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hKb := (abytesAt_kind hxr hab hsz hpb hblk).1
  have hacc8 : m.access p 8 8 = pure (b, blk, p.off.toNat) := by simpa using hacc
  have hnr : NoRace m b p.off.toNat 8 .atomicRead := ho.noRace fun x h1 h2 =>
    abytesAt_mine hab hpb x h1 (by rw [hsz]; exact h2)
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
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  have e : atomicLoadUnorderedEncAt α 0 8 p = (do
      let (li, opts) ← unorderedPrep 8 8 p
      let some pos := opts[0]? | throw .illegal
      StateT.lift (Enc.decode ((← get).atomics[li]!.msgs[pos]!.bytes)) : MemM α) := rfl
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
        rw [hbytes, hdec] at this; cases this
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
      rw [hbytes, hdec] at hw
      have hwv : w = v := by cases hw; rfl
      have hblocks : m₁.blocks = m.blocks := by rw [hm₁]; rfl
      obtain ⟨r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            exact hxr _ _ (abytesAt_cell hab hpb hin)
          · rfl)
        (fun b' x => by rw [hsz]; exact htag b' x)
        (kmono_of_blocks hblocks (by rw [hm₁]; exact ⟨rfl, rfl, rfl⟩))
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, A, S, K, bs, hal, hK, hsz, hv, by rw [← hsz]; exact hab'⟩,
        hwf, LDMono.of_blocks hblocks hld,
        (fstep_record hh.disj hc hab hsz hpb hblk hKb hK .atomicRead).trans
          (FStepIn.locIdx (by decide) (frame_off hh hab hsz hpb)
            (word_inBlock hh hab hsz hpb (m.recordAt b p.off.toNat 8 .atomicRead) rfl) hl),
        Mem.NoRevive.of_blocks hblocks⟩

/-- **`unordered` atomic load** of an owned pointer-valued word (sequential: choice 0). -/
theorem FTriple.atomicLoadUnorderedEnc {α : Type} [Enc α] (p : Ptr) (v : α) :
    FTriple (aptsE p v) (atomicLoadUnorderedEncAt α 0 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) :=
  (FTTriple.atomicLoadUnorderedEnc p v).toFTriple

/-! ## Pointer `cmpxchg` -/

/-- `rmwWriteBytes li pos ord rd bytes` on `m`. -/
def rmwBM (m : Mem) (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (bytes : Array Byte) : Mem :=
  let m₂ := if ord.isAcq then acqM m rd.relClock else m
  let cl := m₂.clocks[m₂.current]!
  observeM (insertM m₂ li (pos + 1)
    { id := m₂.nextMsg, bytes, clock := cl,
      relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock),
      rmwOf := some rd.id }) li m₂.nextMsg

theorem rmwWriteBytes_ok {li pos : Nat} {ord : AtomicOrder} {rd : Msg} {bytes : Array Byte}
    {m m' : Mem} {x : Unit} (h : ((rmwWriteBytes li pos ord rd bytes).run m).run = some (.ok (x, m'))) :
    m' = rmwBM m li pos ord rd bytes := by
  unfold rmwWriteBytes at h
  unfold rmwBM
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, hi, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok hi
    subst this
    exact modify_ok h₃
  · obtain ⟨_, m₁, ha, h₁⟩ := MemM.bind_ok h
    have := modify_ok ha
    subst this
    obtain ⟨a₂, m₂, hg, h₂⟩ := MemM.bind_ok h₁
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    obtain ⟨_, m₃, hi, h₃⟩ := MemM.bind_ok h₂
    have := modify_ok hi
    subst this
    exact modify_ok h₃

theorem rmwWriteBytes_noErr {li pos : Nat} {ord : AtomicOrder} {rd : Msg} {bytes : Array Byte}
    {m : Mem} (e : Error) : ((rmwWriteBytes li pos ord rd bytes).run m).run ≠ some (.error e) := by
  intro h
  unfold rmwWriteBytes at h
  have tail : ∀ m₀, ((do
      let m ← (get : MemM Mem)
      let cl := m.clocks[m.current]!
      let id := m.nextMsg
      insertMsg li (pos + 1)
        { id, bytes, clock := cl,
          relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock),
          rmwOf := some rd.id }
      observe li id : MemM Unit).run m₀).run ≠ some (.error e) := by
    intro m₀ h
    rcases MemM.bind_err h with he | ⟨a, m₁, hg, h1⟩
    · exact MemM.get_err he
    obtain ⟨rfl, rfl⟩ := MemM.get_ok hg
    rcases MemM.bind_err h1 with he | ⟨_, m₂, hi, h2⟩
    · exact MemM.modify_err he
    exact MemM.modify_err h2
  cases hq : ord.isAcq <;> simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
  · exact tail m h
  · rcases MemM.bind_err h with he | ⟨_, m₁, ha, h1⟩
    · exact MemM.modify_err he
    exact tail m₁ h1

theorem filter_head {xs : Array Nat} {f : Nat → Bool} {x : Nat} (h : xs[0]? = some x)
    (hf : f x = true) : (xs.filter f)[0]? = some x := by
  rw [← Array.getElem?_toList] at h ⊢
  rw [Array.toList_filter]
  cases hl : xs.toList with
  | nil => rw [hl] at h; simp at h
  | cons y ys => rw [hl] at h; simp at h; subst h; simp [List.filter_cons, hf]

theorem hasRmwAfter_last {l : ALoc} : l.hasRmwAfter (l.msgs.size - 1) = false := by
  unfold ALoc.hasRmwAfter
  rw [Array.getElem?_eq_none (by omega)]

theorem access_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) (p : Ptr) (n a : Nat) :
    m'.access p n a = m.access p n a := by
  unfold Mem.access; rw [h]

theorem accessW_of_blocks {m m' : Mem} (h : m'.blocks = m.blocks) (p : Ptr) (n a : Nat) :
    m'.accessW p n a = m.accessW p n a := by
  unfold Mem.accessW; rw [access_of_blocks h]

/-- **Strong pointer `cmpxchg`** of an owned pointer-valued word that holds the expected value,
in a thread (choice 0: the newest message): it succeeds, and the word holds the new value. -/
theorem FTTriple.cmpxchgPtr {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTTriple (aptsE p v) (cmpxchgPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) := by
  refine FTTriple.of_step (fun _ _ _ hh hp => aptsE_fix hh hp)
    fun m r rF hh hxr hxF hp hc ho hwf hld => ?_
  obtain ⟨A, S, K, bs, hal, hK, hsz, hv, hab⟩ := hp
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
      (casPtrStrongOpts m₁ li v (readOpts m₁ li false))[0]? =
        some ((m₁.atomics[li]!).msgs.size - 1) ∧
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
  ·
      unfold cmpxchgPtrAt at hrun
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · unfold casPtrPrep at he
        rcases MemM.bind_err he with he | ⟨⟨li, rd⟩, m₁, hp1, h1⟩
        · exact casReadPrep_noErr haccW8 (ho.noRace hmine) hlocok e he
        rcases MemM.bind_err h1 with he | ⟨a, m₂, hg, h2⟩
        · exact MemM.get_err he
        exact MemM.pure_err h2
      · unfold casPtrPrep at hp1
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
        rcases MemM.bind_err h5 with he | ⟨_, m₆, hc, h6⟩
        · rw [casMarkWrite_run (by rw [accessW_of_blocks (by rw [hm₀]; try rfl)]; exact haccW8)
            (hnr₀ li m₀ hl)] at he
          simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he
        rcases MemM.bind_err h6 with he | ⟨_, m₇, hw, h7⟩
        · exact rmwWriteBytes_noErr e he
        exact MemM.pure_err h7
  ·
      unfold cmpxchgPtrAt at hrun
      obtain ⟨⟨li, opts⟩, m₁, hp1, h1⟩ := MemM.bind_ok hrun
      unfold casPtrPrep at hp1
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
      have hax₀ : m.Aux m₀ := by rw [hm₀]; exact ⟨rfl, rfl, rfl⟩
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
          (key _ (by simp [Mem.recordAt]) (by simp [Mem.recordAt, hblk₀])
            (by exact hax₀.trans ⟨rfl, rfl, rfl⟩) hs₃ _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos)) (.inl rfl) (rmw_relClock _ _ _)
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, h3⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, h3⟩)
          (key _ (by simp [acqM, Mem.recordAt]) (by simp [acqM, Mem.recordAt, hblk₀])
            (by exact hax₀.trans ⟨rfl, rfl, rfl⟩)
            (hs₃.trans (FStepIn.acq (hs₃.cur hc) _)) _ ?_ ?_)
        · rfl
        · exact msgCovAt_recordAt (m := m₀) (hs₀.cur hc) (by decide) (fun _ he => he) hb ho
            (Mem.MsgCovAt.relClock_of_mem (last_mem hpos)) (.inr (acqM_clock (hs₃.cur hc) _))
            (rmw_relClock _ _ _)

/-- **Strong pointer `cmpxchg`** of an owned pointer-valued word that holds the expected value
(sequential: choice 0): it succeeds, and the word holds the new value. -/
theorem FTriple.cmpxchgPtr {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTriple (aptsE p v) (cmpxchgPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) :=
  (FTTriple.cmpxchgPtr hα p v new succ fail).toFTriple

end Full
end Zig
