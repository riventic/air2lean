import IdleLoop.Total

/-!
# The memory of the client between two turns

`Inv stored m` holds at every scheduler stop after `main`'s spawn turn. `stored` says whether
`main` has made its release store to `flag`.

- `data` holds 42 (`main` wrote it in its spawn turn, before any worker access).
- `flag`'s atomic location holds the first message (0), and after the store also `main`'s
  message (1), whose release clock is above every write to `data`.
- Each footprint entry is `main`'s write of `data`, a worker read of `data` after the store,
  or an atomic access to `flag`; its clock is below its thread's clock.

The step lemmas are the turns' memory parts: the worker's acquire load of `flag`
(`step_load`, `load_noErr`), `main`'s release store (`step_store`, `store_noErr`) and the
worker's read of `data` (`read_run`). They follow `Proofs/Atomics/MessagePassing.lean`, with
the roles of the two threads exchanged and the blocks as globals.
-/

namespace IdleLoop.Client

open Zig Zig.Conc Zig.Conc.Proto

/-- The bytes `0..4` of block `b` hold the `u32` `v`. -/
def U32At (m : Mem) (b : Nat) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m b 0 4)).run = some (.ok v)

/-- Message `msg` holds the `u32` `v`. -/
def Val (msg : Msg) (v : BitVec 32) : Prop := (intOfBytes 32 msg.bytes).run = some (.ok v)

/-- Every write to `data` happened before `c`. -/
def DataLe (m : Mem) (c : VClock) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.kind = .write → VClock.le e.clock c = true

/-- Block `b` is a live, 4-byte, 4-aligned global. -/
def GBlk (m : Mem) (b : Nat) : Prop :=
  ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = 4 ∧ blk.kind = .global ∧
    blk.addr % 4 = 0

/-- `main` and the worker, which `main` has not joined yet. -/
def thr0 : Array ThreadRec := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }]

/-- `flag`'s atomic location: the first message (0); after the store also `main`'s message (1),
whose release clock is above every write to `data`. -/
def FlagLoc (stored : Bool) (m : Mem) (l : ALoc) : Prop :=
  l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 1 0 4 ∧
  ((stored = false ∧ ∃ m0, l.msgs = #[m0] ∧ Val m0 0) ∨
   (stored = true ∧ ∃ m0 m1, l.msgs = #[m0, m1] ∧ Val m0 0 ∧ Val m1 1 ∧ DataLe m m1.relClock))

/-- No atomic location yet (before the store, `flag` holds 0), or `flag`'s. -/
def FlagOk (stored : Bool) (m : Mem) : Prop :=
  (stored = false ∧ m.atomics = #[] ∧ U32At m 1 0) ∨ ∃ l, m.atomics = #[l] ∧ FlagLoc stored m l

/-- A footprint entry: `main`'s write of `data`, a worker read of `data` after the store, or an
atomic access to `flag`. -/
def FpOk (stored : Bool) (e : FootprintEntry) : Prop :=
  (e.block = 0 ∧ e.kind = .write ∧ e.tid = 0) ∨
  (e.block = 0 ∧ e.kind = .read ∧ e.tid = 1 ∧ stored = true) ∨
  (e.block = 1 ∧ e.kind.isAtomic = true)

/-- The memory between two turns (module doc). -/
structure Inv (stored : Bool) (m : Mem) : Prop where
  thr : m.threads = thr0
  csize : m.clocks.size = 2
  b0 : GBlk m 0
  b1 : GBlk m 1
  data : U32At m 0 42
  flag : FlagOk stored m
  fp : ∀ e ∈ m.footprint, FpOk stored e
  own : ∀ e ∈ m.footprint, e.tid < 2 ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-! ## Blocks -/

theorem GBlk.congr {m m' : Mem} (h : m'.blocks = m.blocks) {b : Nat} (hb : GBlk m b) : GBlk m' b := by
  unfold GBlk; rw [h]; exact hb

theorem GBlk.write {m : Mem} {b o : Nat} {blk : Block} {bs : Array Byte}
    (hb : m.blocks[b]? = some blk) (hfit : o + bs.size ≤ blk.bytes.size) {b' : Nat}
    (h : GBlk m b') : GBlk (m.write b blk o bs) b' := by
  obtain ⟨blk', hb', hl, hs, hkd, ha⟩ := h
  have hlt : b < m.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  simp only [GBlk, Mem.write, Array.set!_eq_setIfInBounds]
  by_cases hbb : b = b'
  · subst hbb
    rw [hb] at hb'; cases hb'
    rw [Array.getElem?_setIfInBounds_self_of_lt hlt]
    exact ⟨_, rfl, hl, by rw [writeBytes_size _ _ _ hfit]; exact hs, hkd, ha⟩
  · rw [Array.getElem?_setIfInBounds_ne hbb]
    exact ⟨blk', hb', hl, hs, hkd, ha⟩

/-- An access of at most 4 bytes at offset 0 of a global of `GBlk`. -/
theorem acc_g {m : Mem} {b : Nat} (h : GBlk m b) {len : Nat} (hl : len ≤ 4) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.kind = .global ∧ blk.bytes.size = 4 ∧
      m.access ⟨some b, 0⟩ len 4 = pure (b, blk, 0) := by
  obtain ⟨blk, hb, hlv, hs, hk, ha⟩ := h
  refine ⟨blk, hb, hk, hs, ?_⟩
  have := access_of (m := m) (p := ⟨some b, 0⟩) (n := len) (a := 4) rfl hb hlv (by simp)
    (by simp only [hs]; omega) (by simpa using ha)
  simpa using this

theorem accW_g {m : Mem} {b : Nat} (h : GBlk m b) {len : Nat} (hl : len ≤ 4) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.bytes.size = 4 ∧
      m.accessW ⟨some b, 0⟩ len 4 = pure (b, blk, 0) := by
  obtain ⟨blk, hb, hk, hs, ha⟩ := acc_g h hl
  exact ⟨blk, hb, hs, by simp [Mem.accessW, ha, hk]⟩

/-! ## Frames -/

theorem Inv.grow {s : Bool} {m m' : Mem} (hi : Inv s m) (hg : Grows m m') : Inv s m' where
  thr := by rw [hg.threads]; exact hi.thr
  csize := by rw [hg.csize]; exact hi.csize
  b0 := hi.b0.congr hg.blocks
  b1 := hi.b1.congr hg.blocks
  data := by unfold U32At; rw [curBytes_congr hg.blocks]; exact hi.data
  flag := by
    unfold FlagOk FlagLoc U32At DataLe
    rw [hg.atomics, curBytes_congr hg.blocks, hg.footprint]
    exact hi.flag
  fp := by intro e he; rw [hg.footprint] at he; exact hi.fp e he
  own := by
    intro e he
    rw [hg.footprint] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨h1, VClock.le_trans h2 (hg.cle _)⟩

theorem Inv.cur {s : Bool} {m : Mem} (hi : Inv s m) (t : ThreadId) : Inv s { m with current := t } :=
  hi.grow (grows_current m t)

/-- A race-free access by the current thread, which is not a write of `data`. -/
theorem Inv.record {s : Bool} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv s m)
    (ht : m.current < 2) (hnw : ¬ (b = 0 ∧ k = .write))
    (hf : FpOk s
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current, block := b,
        off := o, len := len, kind := k : FootprintEntry }) :
    Inv s (m.recordAt b o len k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.csize]; exact ht
  let m₁ : Mem := { m with clocks := m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current) }
  have hg : Grows m m₁ := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [m₁], fun u => ?_⟩
    simp only [m₁]
    rw [getElem!_set!_ite]
    split
    · rename_i h; rw [h.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _
  have hi₁ := hi.grow hg
  have hcur : (m.recordAt b o len k).clocks[m.current]! = VClock.bump (m.clocks[m.current]!) m.current := by
    simp only [Mem.recordAt]; rw [getElem!_set!_ite]; simp [hcs]
  exact {
    thr := hi₁.thr, csize := hi₁.csize, b0 := hi₁.b0, b1 := hi₁.b1, data := hi₁.data
    flag := by
      rcases hi₁.flag with h | ⟨l, ha, hb, ho, hl, hlast, h1 | ⟨hs, m0, m1, hms, h0, h1, hle⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hb, ho, hl, hlast, .inl h1⟩
      · refine .inr ⟨l, ha, hb, ho, hl, hlast, .inr ⟨hs, m0, m1, hms, h0, h1, fun e he hb0 hkw => ?_⟩⟩
        simp only [Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact hle e he hb0 hkw
        · exact absurd ⟨hb0, hkw⟩ hnw
    fp := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.fp e he
      · exact hf
    own := by
      intro e he
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi₁.own e he
      · exact ⟨ht, by rw [hcur]; exact VClock.le_refl _⟩ }

/-! ## `flag` -/

/-- The flag's location at an atomic op (`locIdx 1 0 4`): location 0. -/
theorem loc_flag {s : Bool} {m m₁ : Mem} {li : Nat} (hf : FlagOk s m)
    (h : ((locIdx 1 0 4).run m).run = some (.ok (li, m₁))) :
    li = 0 ∧ ∃ l k, FlagLoc s m l ∧ m₁ = { m with atomics := #[l], nextMsg := k } := by
  have h0 : m.atomics = #[] ∨ ∃ l, m.atomics = #[l] ∧ l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧
      ALoc.lastBytes l = curBytes m 1 0 4 := by
    rcases hf with ⟨-, ha, -⟩ | ⟨l, ha, hlb, hlo, hll, hlast, -⟩
    · exact .inl ha
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast⟩
  obtain ⟨rfl, l, k, rfl, ⟨ha, rfl⟩ | ha⟩ := locIdx_single h0 h
  · rcases hf with ⟨hs, -, hu⟩ | ⟨l, ha', -⟩
    · exact ⟨rfl, firstLoc m 1 0 4, k, ⟨rfl, rfl, rfl, rfl, .inl ⟨hs, firstMsg m 1 0 4, rfl, hu⟩⟩, rfl⟩
    · rw [ha] at ha'; simp at ha'
  · rcases hf with ⟨-, ha', -⟩ | ⟨l', ha', hfl⟩
    · rw [ha] at ha'; simp at ha'
    · rw [ha] at ha'
      have : l = l' := by simpa using ha'
      subst this
      exact ⟨rfl, l, k, hfl, rfl⟩

theorem flag_locIdx_noErr {s : Bool} {m : Mem} (hf : FlagOk s m) (e : Error) :
    ((locIdx 1 0 4).run m).run ≠ some (.error e) := by
  refine locIdx_noErr (fun i hi => ?_) (fun hn l hl => ?_) e
  · rcases hf with ⟨-, ha, -⟩ | ⟨l, ha, -, -, hll, -⟩
    · rw [ha] at hi; simp at hi
    · have := (Array.findIdx?_eq_some_iff_getElem.mp hi).1
      rw [ha] at this hi ⊢
      have : i = 0 := by simp at this; omega
      subst this; exact hll
  · rcases hf with ⟨-, ha, -⟩ | ⟨l', ha, hlb, hlo, -, -⟩
    · rw [ha] at hl; simp at hl
    · rw [ha] at hn; simp [hlb, hlo] at hn

theorem Inv.setLoc {s : Bool} {m : Mem} {l : ALoc} (hi : Inv s m) (hl : FlagLoc s m l) (k : Nat) :
    Inv s { m with atomics := #[l], nextMsg := k } :=
  { hi with flag := .inr ⟨l, rfl, hl⟩ }

theorem FlagLoc.pos {s : Bool} {m : Mem} {l : ALoc} (h : FlagLoc s m l) : 0 < l.msgs.size := by
  obtain ⟨-, -, -, -, ⟨-, m0, hms, -⟩ | ⟨-, m0, m1, hms, -⟩⟩ := h <;> rw [hms] <;> simp

/-- An atomic access to `flag` does not race. -/
theorem noRace_flag {s : Bool} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true) (hi : Inv s m) :
    NoRace m 1 0 (intSize 32) k :=
  noRace_of fun e he hb _ _ => by
    rcases hi.fp e he with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ha⟩
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
    · exact .inr (racePair_atomic ha hk)

/-- The first position that a read offers is the newest message. -/
theorem readOpts_zero {m : Mem} {li : Nat} (h0 : 0 < (m.atomics[li]!).msgs.size) :
    (readOpts m li false)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf := floorPos_lt h0
  unfold readOpts
  simp only [Bool.not_false, Bool.true_or]
  have h1 : ∀ xs : Array Nat, Array.filter (fun _ => true) xs 0 xs.size = xs := by
    intro xs
    apply Array.ext'
    simp
  rw [h1]
  simp only [Array.getElem?_map, Option.map_eq_some_iff]
  refine ⟨0, ?_, by omega⟩
  simp [show 0 < (m.atomics[li]!).msgs.size - floorPos m li by omega]

/-! ## The worker's acquire load of `flag` -/

/-- The worker's acquire load: 0, or 1 after the store, and then every write of `data` happened
before the worker. After the store, option 0 reads the store's message. -/
theorem step_load {s : Bool} {m m' : Mem} {c : Nat} {v : BitVec 32} (hi : Inv s m)
    (hc : m.current = 1)
    (h : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run = some (.ok (v, m'))) :
    m'.current = 1 ∧ m'.threads = m.threads ∧ Inv s m' ∧
      (v = 0 ∨ (v = 1 ∧ s = true ∧ DataLe m' (m'.clocks[1]!))) ∧ (s = true → c = 0 → v = 1) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨blk₁, hb₁, -, -, hacc₁⟩ := acc_g hi.b1 (len := intSize 32) (by decide)
  rw [show fPtr = ⟨some 1, 0⟩ from rfl, hacc₁] at hacc
  cases hacc
  have ht : m.current < 2 := by rw [hc]; decide
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicRead) ht
    (fun h => by cases h.2) (.inr (.inr ⟨rfl, rfl⟩))
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicRead).current = 1 := hc
  have hcs : 1 < (m.recordAt 1 0 (intSize 32) .atomicRead).clocks.size := by
    show 1 < (m.clocks.set! _ _).size; simp [hi.csize]
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  generalize m.recordAt 1 0 (intSize 32) .atomicRead = mr at hir hl hcur hcs hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM := hir.setLoc hfl k
  have hg' := grows_loadM { mr with atomics := #[l], nextMsg := k } 0 .acquire
    ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!)
  refine ⟨by rw [loadM_current]; exact hcur, hg'.threads.trans hthr, hiM.grow hg', ?_⟩
  have hlt := readOpts_lt hpos
  have hpos0 : c = 0 → pos = l.msgs.size - 1 := by
    rintro rfl
    rw [readOpts_zero (by rw [hl0]; exact hfl.pos), hl0] at hpos
    exact (Option.some.inj hpos).symm
  rw [hl0] at hlt hv
  obtain ⟨-, -, -, -, ⟨hs, m0, hms, h0⟩ | ⟨hs, m0, m1, hms, h0, h1, hle⟩⟩ := hfl
  · rw [hms] at hlt hv
    have : pos = 0 := by simp at hlt; omega
    subst this
    have hv0 : v = 0 := by have := hv.symm.trans h0; simpa using this
    exact ⟨.inl hv0, fun h => by rw [hs] at h; cases h⟩
  · rw [hms] at hlt hv hpos0
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    refine ⟨?_, fun _ hc0 => ?_⟩
    · rcases this with rfl | rfl
      · left
        have := hv.symm.trans h0
        simpa using this
      · right
        refine ⟨by have := hv.symm.trans h1; simpa using this, hs, fun e he hb0 hkw => ?_⟩
        have hmsg : (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[1]! = m1 := by
          rw [hl0, hms]; rfl
        rw [hmsg]
        rw [← hcur]
        exact VClock.le_trans (hle e he hb0 hkw) (loadM_acq_le _ _ _ rfl (by rw [hcur]; exact hcs))
    · have hp := hpos0 hc0
      simp at hp
      subst hp
      have := hv.symm.trans h1
      simpa using this

theorem load_noErr {s : Bool} {m : Mem} {c : Nat} (hi : Inv s m) (ht : m.current < 2)
    (hcr : c < loadCnt m ∨ loadCnt m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₁, -, -, -, hacc₁⟩ := acc_g hi.b1 (len := intSize 32) (by decide)
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicRead) ht
    (fun h => by cases h.2) (.inr (.inr ⟨rfl, rfl⟩))
  refine atomicLoadAt_noErr (loadPrep_noErr (rmw := false) (by simpa [fPtr] using hacc₁)
    (by simpa using noRace_flag (k := .atomicRead) rfl hi)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact flag_locIdx_noErr hir.flag))
    (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hacc' hl
  rw [show fPtr = ⟨some 1, 0⟩ from rfl, hacc₁] at hacc'
  cases hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hl0 : ({ m.recordAt 1 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hcount : loadCnt m = (readOpts { m.recordAt 1 0 (intSize 32) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := optCount_eq hp
  have hne : 0 < (readOpts { m.recordAt 1 0 (intSize 32) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false).size := by
    exact readOpts_ne (by rw [hl0]; exact hfl.pos)
  rw [hcount] at hcr
  have hc : c < (readOpts { m.recordAt 1 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } 0 false).size := by
    rcases hcr with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)
  obtain ⟨pos, hpos⟩ : ∃ pos, (readOpts { m.recordAt 1 0 (intSize 32) .atomicRead with
      atomics := #[l], nextMsg := k } 0 false)[c]? = some pos := ⟨_, Array.getElem?_eq_getElem hc⟩
  refine ⟨pos, hpos, ?_⟩
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt ⊢
  obtain ⟨-, -, -, -, ⟨-, m0, hms, h0⟩ | ⟨-, m0, m1, hms, h0, h1, -⟩⟩ := hfl
  · rw [hms] at hlt ⊢
    have : pos = 0 := by simp at hlt; omega
    subst this; exact ⟨0, h0⟩
  · rw [hms] at hlt ⊢
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    rcases this with rfl | rfl
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩

/-! ## `main`'s release store of 1 -/

/-- The invariant depends only on the threads, clocks, blocks, atomic locations and footprint. -/
theorem Inv.congr {s : Bool} {m m' : Mem} (hi : Inv s m) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) (hw : m'.waiters = m.waiters) : Inv s m' :=
  hi.grow ⟨ht, hb, ha, hf, hw, by rw [hc], fun _ => by rw [hc]; exact VClock.le_refl _⟩

/-- `main`'s message (1) after the first one: the store has happened. -/
theorem Inv.pushFlag {M : Mem} {l : ALoc} {m0 msg : Msg} {blk : Block}
    (hi : Inv false M) (ha : M.atomics = #[l]) (hms : l.msgs = #[m0])
    (hb : M.blocks[1]? = some blk) (hbs : msg.bytes.size = 4) (hv : Val msg 1)
    (hrel : DataLe M msg.relClock) (k : Nat) :
    Inv true
      { M.write 1 blk 0 msg.bytes with
        atomics := #[{ l with msgs := #[m0, msg] }], nextMsg := k } := by
  obtain ⟨l', ha', hlb, hlo, hll, -, h1⟩ : ∃ l', M.atomics = #[l'] ∧ FlagLoc false M l' := by
    rcases hi.flag with ⟨-, ha', -⟩ | h
    · rw [ha] at ha'; simp at ha'
    · exact h
  rw [ha] at ha'
  have hl : l = l' := by simpa using ha'
  subst hl
  have h0 : Val m0 0 := by
    rcases h1 with ⟨-, m0', hm, hv0⟩ | ⟨h, -⟩
    · rw [hms] at hm
      have : m0 = m0' := by simpa using hm
      subst this; exact hv0
    · cases h
  have hfit : 0 + msg.bytes.size ≤ blk.bytes.size := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b1
    rw [hb] at hb'; cases hb'; omega
  have hcN : ∀ b o len, curBytes { M.write 1 blk 0 msg.bytes with
      atomics := #[{ l with msgs := #[m0, msg] }], nextMsg := k } b o len =
      curBytes (M.write 1 blk 0 msg.bytes) b o len := fun _ _ _ => rfl
  have hlast : ALoc.lastBytes { l with msgs := #[m0, msg] } =
      curBytes (M.write 1 blk 0 msg.bytes) 1 0 4 := by
    have := curBytes_write_same hb hfit
    rw [hbs] at this
    rw [this]; rfl
  exact {
    thr := hi.thr
    csize := hi.csize
    b0 := GBlk.write hb hfit hi.b0
    b1 := GBlk.write hb hfit hi.b1
    data := by
      unfold U32At; rw [hcN, curBytes_write_other hb hfit (.inl (by decide))]; exact hi.data
    flag := .inr ⟨_, rfl, hlb, hlo, hll, by rw [hcN]; exact hlast,
      .inr ⟨rfl, m0, msg, rfl, h0, hv, hrel⟩⟩
    fp := by
      intro e he
      rcases hi.fp e he with h | ⟨-, -, -, h⟩ | h
      · exact .inl h
      · cases h
      · exact .inr (.inr h)
    own := hi.own }

/-- `main`'s release store of 1 to `flag`: its message is the newest, with a release clock above
`main`'s write of `data`. -/
theorem step_store {m m' : Mem} {c : Nat} (hi : Inv false m) (hc : m.current = 0)
    (h : ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    m'.current = 0 ∧ m'.threads = m.threads ∧ Inv true m' := by
  obtain ⟨b, blk, o, li, m₁, slot, hacc, -, hl, hs, rfl⟩ := atomicStoreAt_ok h
  obtain ⟨blk₁, hb₁, -, hacc₁⟩ := accW_g hi.b1 (len := intSize 32) (by decide)
  rw [show fPtr = ⟨some 1, 0⟩ from rfl, hacc₁] at hacc
  cases hacc
  have ht : m.current < 2 := by rw [hc]; decide
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicWrite) ht
    (fun h => by cases h.2) (.inr (.inr ⟨rfl, rfl⟩))
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicWrite).current = 0 := hc
  have hbr : (m.recordAt 1 0 (intSize 32) .atomicWrite).blocks[1]? = some blk := hb₁
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads = m.threads := rfl
  generalize m.recordAt 1 0 (intSize 32) .atomicWrite = mr at hir hl hcur hbr hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  obtain ⟨hlb, hlo, hll, hlast, ⟨-, m0, hms, h0⟩ | ⟨hs', -⟩⟩ := hfl
  · have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    obtain ⟨hf1, hs1⟩ := writeSlots_bounds hs
    rw [hl0, hms] at hs1
    have hslot : slot = (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size := by
      rw [hl0, hms]; simp at hs1 ⊢; omega
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hlb]; exact hbr
    have hiM := hir.setLoc ⟨hlb, hlo, hll, hlast, .inl ⟨rfl, m0, hms, h0⟩⟩ k
    have hrel : DataLe { mr with atomics := #[l], nextMsg := k }
        (storeMsg { mr with atomics := #[l], nextMsg := k } .release (1 : BitVec 32)).relClock := by
      intro e he hb0 hkw
      show VClock.le e.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      rcases hir.fp e he with ⟨-, -, htid⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩
      · have := (hir.own e he).2; rw [htid] at this; exact this
      · rw [hkw] at hk; cases hk
      · exact (blk_ne h hb0 (by decide)).elim
    have hiN := hiM.pushFlag rfl hms hbr (msg := storeMsg { mr with atomics := #[l], nextMsg := k }
      .release (1 : BitVec 32)) (LawfulEnc.size_encode (α := BitVec 32) 1) (intOfBytes_rmw 1) hrel
      (k + 1)
    unfold storeM
    rw [hslot, insertM_last hbM]
    refine ⟨hcur, hthr, hiN.congr rfl rfl ?_ ?_ rfl rfl⟩
    · show mr.blocks.set! _ _ = mr.blocks.set! _ _
      rw [hl0, hlb, hlo]
    · show (#[l] : Array ALoc).set! 0 _ = _
      rw [hl0, hms]; rfl
  · cases hs'

theorem store_noErr {m : Mem} {c : Nat} (hi : Inv false m) (ht : m.current < 2)
    (hcr : c < storeCnt m ∨ storeCnt m = 0 ∧ c = 0)
    (e : Error) : ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m).run ≠ some (.error e) := by
  obtain ⟨blk₁, -, -, hacc₁⟩ := accW_g hi.b1 (len := intSize 32) (by decide)
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicWrite) ht
    (fun h => by cases h.2) (.inr (.inr ⟨rfl, rfl⟩))
  refine atomicStoreAt_noErr (storePrep_noErr hacc₁ (noRace_flag rfl hi)
    (flag_locIdx_noErr hir.flag)) (fun li slots m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := storePrep_ok hp
  rw [hacc₁] at hacc'
  cases hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hne := writeSlots_ne (m := { m.recordAt 1 0 (intSize 32) .atomicWrite with atomics := #[l], nextMsg := k })
    (li := 0) (by show 0 < l.msgs.size; exact hfl.pos)
  have hcount : storeCnt m = (writeSlots { m.recordAt 1 0 (intSize 32) .atomicWrite with
      atomics := #[l], nextMsg := k } 0).size := optCount_eq hp
  rw [hcount] at hcr
  rcases hcr with h | ⟨h0, -⟩
  · exact h
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)

/-! ## The worker's read of `data` -/

/-- After the store, a worker whose clock is above every write of `data` reads 42 without a
race. -/
theorem read_run {m : Mem} (hi : Inv true m) (hc : m.current = 1)
    (hle : DataLe m (m.clocks[1]!)) :
    (load (BitVec 32) 4 dPtr).run m = pure (42, m.recordAt 0 0 4 .read) ∧
      Inv true (m.recordAt 0 0 4 .read) := by
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := acc_g hi.b0 (len := Enc.size (BitVec 32)) (by decide)
  have h42 := hi.data
  unfold U32At curBytes at h42
  rw [hb₀] at h42
  have hdec : (Enc.decode (blk₀.bytes.extract 0 (0 + Enc.size (BitVec 32))) : Result (BitVec 32)) =
      pure 42 := h42
  have hnr : NoRace m 0 0 (Enc.size (BitVec 32)) .read := noRace_of fun e he hb _ _ => by
    rcases hi.fp e he with ⟨-, hk, -⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩
    · exact .inl (by rw [hc]; exact hle e he hb hk)
    · exact .inr (by rw [hk]; rfl)
    · exact (blk_ne h hb (by decide)).elim
  refine ⟨load_run (p := dPtr) hacc₀ hdec hnr, ?_⟩
  exact hi.record (b := 0) (o := 0) (len := 4) (k := .read) (by rw [hc]; decide)
    (fun h => by cases h.2) (.inr (.inl ⟨rfl, rfl, hc, rfl⟩))

end IdleLoop.Client
