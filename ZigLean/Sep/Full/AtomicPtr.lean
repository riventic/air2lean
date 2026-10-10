import ZigLean.Sep.Full.Atomic
import ZigLean.Conc.AtomicWord
import ZigLean.Conc.PtrAtomicLemmas

/-!
# Pointer-valued atomic points-to (`docs/sep-full-state.md`)

`aptsE p v`: the 8 bytes at the 8-aligned `p` decode to `v` (`Enc`, for `Zig.Ptr` and
`Option Zig.Ptr` a pointer with its provenance), and their atomic tag is `none` or exactly
`(p.off, 8)`, as for the integer `apts` (`ZigLean/Sep/Full/Res.lean`). Rules, in a sequential run
(choice `0`):

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
def aptsE {α : Type} [Enc α] (p : Ptr) (v : α) : FAssn := fun r => ∃ A S K bs tg,
  (A + p.off.toNat) % 8 = 0 ∧ K ≠ .constGlobal ∧ bs.size = 8 ∧ Enc.decode bs = pure v ∧
  (tg = none ∨ tg = some (p.off.toNat, 8)) ∧ abytesAt p A S K bs tg r

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

/-- **`unordered` atomic load** of an owned pointer-valued word (sequential: choice 0). -/
theorem FTriple.atomicLoadUnorderedEnc {α : Type} [Enc α] (p : Ptr) (v : α) :
    FTriple (aptsE p v) (atomicLoadUnorderedEncAt α 0 8 p) (fun w => ⟪w = v⟫ ⋆ aptsE p v) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, htg, hab⟩ := hp
  have hm : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union]
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  have hpb := (access_eq hacc).1
  have hacc8 : m.access p 8 8 = pure (b, blk, p.off.toNat) := by simpa using hacc
  have htok := tagOk_of_own hh hab hsz htg hpb
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat 8).run (m.recordAt b p.off.toNat 8 .atomicRead)).run
      = some (.ok (li, m₁)) →
      (unorderedOpts m₁ li)[0]? = some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      (∃ a next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      ∀ b' x, tagOf (shapes m₁) b' x =
        if Covers b' x (b, p.off.toNat, 8) then some (p.off.toNat, 8) else tagOf (shapes m) b' x := by
    intro li m₁ hl
    obtain ⟨hupd, -, -, -, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2 (by decide) htok
        (by rw [hcur, hsz]) hl
    exact ⟨unorderedOpts_zero hpos, by rw [lastBytes_eq hpos, hlast, hcur], hupd, hwf, htag⟩
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  unfold atomicLoadUnorderedEncAt
  cases hrun : ((do
      let (li, opts) ← unorderedPrep 8 8 p
      let some pos := opts[0]? | throw .illegal
      StateT.lift (Enc.decode ((← get).atomics[li]!.msgs[pos]!.bytes)) : MemM α).run m).run with
  | none => trivial
  | some x =>
    cases x with
    | error e =>
      exfalso
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · exact unorderedPrep_noErr hacc8 (noRace_of_singleThread hs.1.single _ _ _ _)
          (fun e' => locIdx_noErr_tag (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2 (by decide)
            htok e') e he
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
    | ok x =>
      obtain ⟨w, m'⟩ := x
      obtain ⟨⟨li, opts⟩, m₁, hp1, h1⟩ := MemM.bind_ok hrun
      obtain ⟨b', blk', o', ha', hl, rfl⟩ := unorderedPrep_ok hp1
      rw [hacc8] at ha'; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at ha'
      obtain ⟨rfl, rfl, rfl⟩ := ha'
      obtain ⟨hz, hbytes, ⟨a, next, hm₁⟩, hwf, htag⟩ := hpost li m₁ hl
      (try simp only at h1); rw [hz] at h1; simp only at h1
      obtain ⟨a₂, m₂, hg, h2⟩ := MemM.bind_ok h1
      obtain ⟨e1, e2⟩ := MemM.get_ok hg
      rw [e1, e2] at h2
      obtain ⟨hw, e3⟩ := MemM.lift_ok h2
      subst m'
      rw [hbytes, hdec] at hw
      have hwv : w = v := by cases hw; rfl
      have hblocks : m₁.blocks = m.blocks := by rw [hm₁]; rfl
      have hnext : m₁.nextAddr = m.nextAddr := by rw [hm₁]; rfl
      obtain ⟨hAB, r', hh', hab'⟩ := holds_after hh hab (bs' := bs) rfl hpb
        (fun l => by
          rw [heap_of_blocks hblocks]
          split
          · rename_i hin
            obtain ⟨-, b0, hb0, -, hl0⟩ := hab
            rw [hpb] at hb0; cases hb0
            have hr := hl0 l
            rw [if_pos hin] at hr
            exact (fheap_tag (hh.own hr)).2
          · rfl)
        (fun b' x => by rw [htag, hsz]) (kmono_of_blocks hblocks) hs.1.addr hnext
      refine ⟨r', hh', sep_lift.mpr ⟨hwv, A, S, K, bs, _, hal, hK, hsz, hv, .inr (by rw [hsz]), hab'⟩,
        ⟨⟨?_, hAB⟩, hwf⟩⟩
      rw [hm₁]; exact singleThread_recordAt hs.1.single _ _ _ _

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

/-- **Strong pointer `cmpxchg`** of an owned pointer-valued word that holds the expected value
(sequential: choice 0): it succeeds, and the word holds the new value. -/
theorem FTriple.cmpxchgPtr {α : Type} [Enc α] [LawfulEnc α] [DecidableEq α] [AtomicPtrVal α]
    (hα : Enc.size α = 8) (p : Ptr) (v new : α) (succ fail : AtomicOrder) :
    FTriple (aptsE p v) (cmpxchgPtrAt 0 succ fail 8 p v new) (fun r => ⟪r = none⟫ ⋆ aptsE p new) := by
  intro m r rF hh hp hs
  obtain ⟨A, S, K, bs, tg, hal, hK, hsz, hv, htg, hab⟩ := hp
  have hm : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union]
  obtain ⟨b, blk, hacc, hblk, hA, hS, hx⟩ := bytesAt_access (q := p) (k := 0) (n := 8) (a := 8)
    (abytesAt_bytesAt hab) hm (by simp [Ptr.add]) (by decide) (by omega) (by simpa using hal)
  obtain ⟨hpb, -, hlive, h0, hfit, -, -⟩ := access_eq hacc
  have hKb : blk.kind = K ∧ blk.kind.mappedLo ≤ p.off.toNat := by
    obtain ⟨-, b0, hb0, -, hl0⟩ := id hab
    rw [hpb] at hb0; cases hb0
    have hr := hl0 (b, p.off.toNat)
    rw [if_pos ⟨rfl, Nat.le_refl _, by omega⟩] at hr
    obtain ⟨blk', hblk', _, _, hc⟩ := Mem.heap_some (fheap_tag (hh.own hr)).2
    obtain ⟨blk'', hblk'', hlo⟩ := Mem.heap_some_lo (fheap_tag (hh.own hr)).2
    rw [hblk] at hblk' hblk''; cases hblk'; cases hblk''
    simp only [Cell.mk.injEq] at hc
    exact ⟨hc.2.2.2.symm, hlo⟩
  obtain ⟨hKb, hlo⟩ := hKb
  have haccW8 : m.accessW p (intSize 64) 8 = pure (b, blk, p.off.toNat) := by
    rw [intSize_64]; unfold Mem.accessW; rw [show m.access p 8 8 = pure (b, blk, p.off.toNat) by
      simpa using hacc]
    simp [hKb, hK, pure_bind]
  have htok := tagOk_of_own hh hab hsz htg hpb
  have hcur : curBytes (m.recordAt b p.off.toNat 8 .atomicRead) b p.off.toNat 8 = bs := by
    simp only [curBytes, Mem.recordAt, hblk, Option.map_some, Option.getD_some]
    have : bs.extract 0 8 = bs := by rw [← hsz]; simp
    simpa [this] using hx
  have hlocok := fun e => locIdx_noErr_tag (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2
    (by decide) htok e
  have hdec : (Enc.decode bs : Result α).run = some (.ok v) := by rw [hv]; rfl
  have hpost : ∀ li m₁, ((locIdx b p.off.toNat (intSize 64)).run
      (m.recordAt b p.off.toNat (intSize 64) .atomicRead)).run = some (.ok (li, m₁)) →
      (casPtrStrongOpts m₁ li v (readOpts m₁ li false))[0]? =
        some ((m₁.atomics[li]!).msgs.size - 1) ∧
      ((m₁.atomics[li]!).msgs[(m₁.atomics[li]!).msgs.size - 1]!).bytes = bs ∧
      li < m₁.atomics.size ∧ (m₁.atomics[li]!).block = b ∧ (m₁.atomics[li]!).off = p.off.toNat ∧
      (∃ a next, m₁ = { m.recordAt b p.off.toNat 8 .atomicRead with atomics := a, nextMsg := next }) ∧
      ShapesWF (shapes m₁) ∧
      (∀ b' x, tagOf (shapes m₁) b' x =
        if Covers b' x (b, p.off.toNat, 8) then some (p.off.toNat, 8) else tagOf (shapes m) b' x) ∧
      0 < (m₁.atomics[li]!).msgs.size := by
    intro li m₁ hl
    rw [intSize_64] at hl
    obtain ⟨hupd, hli, hb, ho, hpos, hlast, hwf, htag⟩ :=
      locIdx_post (m := m.recordAt b p.off.toNat 8 .atomicRead) hs.2 (by decide) htok
        (by rw [hcur, hsz]) hl
    refine ⟨filter_head (readOpts_zero hpos) ?_, by rw [lastBytes_eq hpos, hlast, hcur], hli, hb, ho,
      hupd, hwf, htag, hpos⟩
    simp [hasRmwAfter_last]
  cases hrun : ((cmpxchgPtrAt 0 succ fail 8 p v new).run m).run with
  | none => trivial
  | some x =>
    unfold cmpxchgPtrAt at hrun
    cases x with
    | error e =>
      exfalso
      rcases MemM.bind_err hrun with he | ⟨⟨li, opts⟩, m₁, hp1, h1⟩
      · unfold casPtrPrep at he
        rcases MemM.bind_err he with he | ⟨⟨li, rd⟩, m₁, hp1, h1⟩
        · exact casReadPrep_noErr haccW8 (noRace_of_singleThread hs.1.single _ _ _ _) hlocok e he
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
        obtain ⟨hz, hbytes, -, -, -, ⟨a', next, hm₀⟩, -⟩ := hpost li m₀ hl
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
            (noRace_of_singleThread (by rw [hm₀]; exact singleThread_recordAt hs.1.single _ _ _ _)
              _ _ _ _)] at he
          simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at he
        rcases MemM.bind_err h6 with he | ⟨_, m₇, hw, h7⟩
        · exact rmwWriteBytes_noErr e he
        exact MemM.pure_err h7
    | ok x =>
      obtain ⟨res, m'⟩ := x
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
      obtain ⟨hz, hbytes, hli, hb, ho, ⟨a', next, hm₀⟩, hwf, htag, hpos⟩ := hpost li m₀ hl
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
      obtain ⟨_, m₆, hc, h6⟩ := MemM.bind_ok h5
      rw [casMarkWrite_run (by rw [accessW_of_blocks hblk₀]; exact haccW8)
        (noRace_of_singleThread (by rw [hm₀]; exact singleThread_recordAt hs.1.single _ _ _ _)
          _ _ _ _)] at hc
      simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, StateT.pure, Option.some.injEq,
        Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, rfl⟩ := hc
      obtain ⟨_, m₇, hw, h7⟩ := MemM.bind_ok h6
      have hm₇ := rmwWriteBytes_ok hw
      obtain ⟨hres, e7⟩ := MemM.pure_ok h7
      subst m'
      subst m₇
      rw [hres]
      have key : ∀ M₂ : Mem, M₂.atomics = m₀.atomics → M₂.blocks = m.blocks →
          M₂.nextAddr = m.nextAddr → M₂.SingleThread → ∀ msg : Msg, msg.bytes = Enc.encode new →
          ∃ r', Holds (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg) r' rF ∧ aptsE p new r' ∧
            (observeM (insertM M₂ li ((m₀.atomics[li]!).msgs.size - 1 + 1) msg) li
              M₂.nextMsg).FSeq := by
        intro M₂ hat hbl hna hst msg hmb
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
        have hnext : (observeM (insertM M₂ li (M₂.atomics[li]!).msgs.size msg) li
            M₂.nextMsg).nextAddr = m.nextAddr := by
          unfold observeM; rw [hins]; exact hna
        have henc : (Enc.encode new).size = 8 := by rw [LawfulEnc.size_encode, hα]
        have hwr := Mem.heap_write (m := m) (o := p.off.toNat) hblk hlive (bs := Enc.encode new)
          (by rw [henc]; omega) hlo
        obtain ⟨hAB, r', hh', hab'⟩ := holds_after hh hab (bs' := Enc.encode new) (by rw [henc, hsz])
          hpb
          (fun l => by
            rw [heap_of_blocks (m := m.write b blk p.off.toNat (Enc.encode new)) hblocks, hwr, henc,
              hsz, hA, hS, hKb])
          (fun b' x => by rw [hshapes, htag, hsz])
          (KMono.set (blk' := { blk with bytes := writeBytes blk.bytes p.off.toNat (Enc.encode new) })
            hblk rfl hblocks) hs.1.addr hnext
        refine ⟨r', hh', ⟨A, S, K, Enc.encode new, _, hal, hK, henc, LawfulEnc.decode_encode new,
          .inr (by rw [hsz]), hab'⟩, ⟨⟨?_, hAB⟩, by rw [hshapes]; exact hwf⟩⟩
        unfold observeM
        exact singleThread_insertM hst _ _ _
      have hst₀ : m₀.SingleThread := by
        rw [hm₀]; exact singleThread_recordAt hs.1.single _ _ _ _
      have hst₃ := singleThread_recordAt hst₀ b p.off.toNat (intSize 64) .atomicWrite
      unfold rmwBM
      dsimp only
      cases hq : succ.isAcq
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ (by simp [Mem.recordAt]) (by simp [Mem.recordAt, hblk₀])
            (by simp [Mem.recordAt, hm₀]) hst₃ _ ?_)
        rfl
      · simp only [↓reduceIte]
        refine (fun ⟨r', hh', hap, hfs⟩ => ⟨r', hh', sep_lift.mpr ⟨by first | rfl | trivial, hap⟩, hfs⟩)
          (key _ (by simp [acqM, Mem.recordAt]) (by simp [acqM, Mem.recordAt, hblk₀])
            (by simp [acqM, Mem.recordAt, hm₀]) (singleThread_acqM hst₃ _) _ ?_)
        rfl

end Full
end Zig
