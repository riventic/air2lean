import Proofs.Atomics.Gen
import ZigLean.Conc.Lemmas

/-!
# `mpRelAcq` over all schedules: message passing

`mpRelAcq` spawns a writer. The writer writes 42 to `data` (a plain write), then stores 1 to
`flag` with `.release`. `main` loads `flag` with `.acquire`; if it reads 1, it reads `data`. The
result is 0 or 42 under every schedule (`mpRelAcq_spec`), and no schedule gives an error
(`mpRelAcq_safe`): the read of `data` does not race with the write.

**Why.** The release store puts the writer's clock in its message (`Msg.relClock`). The acquire
load of that message joins it into `main`'s clock. So the write of `data` happened before the
read. The invariant (`Inv`) has this as an assertion on the flag's messages (`FlagLoc`): each
message holds 0, or holds 1, and then the writer has ended and every write to `data` happened
before the message's release clock.
-/

open Zig Zig.Conc Zig.Conc.Proto Atomics

namespace Atomics.MP

/-- A thread's ghost value. -/
inductive Gh where
  | none
  /-- `main` before its spawn. -/
  | pre
  /-- `main` at the load of `flag`. -/
  | run
  /-- `main` at its join. -/
  | joins
  /-- The writer before its write of `data`. -/
  | start
  /-- The writer after its write of `data`, at the store of `flag`. -/
  | wrote
  /-- The writer has ended. -/
  | fin
  deriving DecidableEq

/-- `data` (block 0). -/
def dPtr : Ptr := ⟨some 0, 0⟩
/-- `flag` (block 1). -/
def fPtr : Ptr := ⟨some 1, 0⟩
/-- The `MpCtx` (block 2). -/
def cPtr : Ptr := ⟨some 2, 0⟩

/-- The bytes `0..4` of block `b` hold the `u32` `v`. -/
def U32At (m : Mem) (b : Nat) (v : BitVec 32) : Prop :=
  (intOfBytes 32 (curBytes m b 0 4)).run = some (.ok v)

/-- Message `msg` holds the `u32` `v`. -/
def Val (msg : Msg) (v : BitVec 32) : Prop := (intOfBytes 32 msg.bytes).run = some (.ok v)

/-- The clock `c` happened before every thread. -/
def Before (m : Mem) (c : VClock) : Prop :=
  ∀ u < m.threads.size, VClock.le c (m.clocks[u]!) = true

/-- Every write to `data` happened before `c`. -/
def DataLe (m : Mem) (c : VClock) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.kind = .write → VClock.le e.clock c = true

/-- The flag's atomic location. Its newest message has the block's bytes. It has the first
message (0), and then the writer's message (1): the writer has ended, and every write to `data`
happened before the release clock of the message. -/
def FlagLoc (G : ThreadId → Gh) (m : Mem) (l : ALoc) : Prop :=
  l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 1 0 4 ∧
  ((∃ m0, l.msgs = #[m0] ∧ Val m0 0) ∨
   (∃ m0 m1, l.msgs = #[m0, m1] ∧ Val m0 0 ∧ Val m1 1 ∧ G 1 = .fin ∧ DataLe m m1.relClock))

/-- No atomic location yet (the flag holds 0), or the flag's. -/
def FlagOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  (m.atomics = #[] ∧ U32At m 1 0) ∨ ∃ l, m.atomics = #[l] ∧ FlagLoc G m l

/-- A footprint entry: a write that happened before every thread; the writer's write to `data`;
`main`'s read of `data` after the writer ended; an atomic access to `flag`; a read of the
`MpCtx`. -/
def FpOk (G : ThreadId → Gh) (m : Mem) (e : FootprintEntry) : Prop :=
  (e.kind = .write ∧ Before m e.clock) ∨
  (e.block = 0 ∧ e.kind = .write ∧ e.tid = 1) ∨
  (e.block = 0 ∧ e.kind = .read ∧ G 1 = .fin) ∨
  (e.block = 1 ∧ e.kind.isAtomic = true) ∨
  (e.block = 2 ∧ e.kind = .read)

/-- The threads: `main` alone before its spawn; then `main` and the writer, which `main` did not
join yet. -/
def ThrOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  m.threads[0]? = some { spawner := 0, joined := true } ∧ m.clocks.size = m.threads.size ∧
  ((m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none) ∨
   (m.threads.size = 2 ∧ (∃ r, m.threads[1]? = some r ∧ r.spawner = 0 ∧ r.joined = false) ∧
    (G 0 = .run ∨ G 0 = .joins) ∧ (G 1 = .start ∨ G 1 = .wrote ∨ G 1 = .fin) ∧
    ∀ u, 2 ≤ u → G u = .none))

/-- The invariant (see the module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  thr : ThrOk G m
  b0 : BlkAt m 0 4 4
  b1 : BlkAt m 1 4 4
  b2 : BlkAt m 2 16 8
  ctx : curBytes m 2 0 8 = Enc.encode dPtr ∧ curBytes m 2 8 8 = Enc.encode fPtr
  data : (G 1 = .wrote ∨ G 1 = .fin) → U32At m 0 42
  flag : FlagOk G m
  fp : ∀ e ∈ m.footprint, FpOk G m e
  own : ∀ e ∈ m.footprint, e.tid < m.threads.size ∧ VClock.le e.clock (m.clocks[e.tid]!) = true

/-- The protocol, in strict mode. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init
    | .mpWriter p => if p = cPtr then some .start else none
    | _ => none
  fin g := g = .fin
  strict := true
  joins g := g = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (v = .ok 0 ∨ v = .ok 42) ∧ joinedAll 0 m

/-! ## Frame: steps that keep the invariant -/

theorem before_grow {m m' : Mem} (hg : Grows m m') {c : VClock} (h : Before m c) : Before m' c :=
  fun u hu => VClock.le_trans (h u (hg.threads ▸ hu)) (hg.cle u)

theorem Inv.grow {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : Grows m m') : Inv G m' where
  thr := by unfold ThrOk; rw [hg.threads, hg.csize]; exact hi.thr
  b0 := hi.b0.congr hg.blocks
  b1 := hi.b1.congr hg.blocks
  b2 := hi.b2.congr hg.blocks
  ctx := by rw [curBytes_congr hg.blocks, curBytes_congr hg.blocks]; exact hi.ctx
  data := by unfold U32At; rw [curBytes_congr hg.blocks]; exact hi.data
  flag := by
    unfold FlagOk FlagLoc U32At DataLe
    rw [hg.atomics, curBytes_congr hg.blocks, hg.footprint]
    exact hi.flag
  fp := by
    intro e he
    rw [hg.footprint] at he
    rcases hi.fp e he with ⟨hk, hb⟩ | h | h | h | h
    · exact .inl ⟨hk, before_grow hg hb⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  own := by
    intro e he
    rw [hg.footprint] at he
    obtain ⟨h1, h2⟩ := hi.own e he
    exact ⟨hg.threads ▸ h1, VClock.le_trans h2 (hg.cle _)⟩

/-- A race-free access by the current thread: its clock is bumped and the entry recorded. The
invariant holds if the entry is one of `FpOk`, and it is not a write to `data` after the writer
ended. -/
theorem Inv.record {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size) (hnd : b = 0 → k = .write → G 1 ≠ .fin)
    (hf : FpOk G (m.recordAt b o len k)
      { tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current, block := b,
        off := o, len := len, kind := k }) :
    Inv G (m.recordAt b o len k) := by
  have hcs : m.current < m.clocks.size := by rw [hi.thr.2.1]; exact ht
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
    thr := hi₁.thr, b0 := hi₁.b0, b1 := hi₁.b1, b2 := hi₁.b2, ctx := hi₁.ctx, data := hi₁.data
    flag := by
      rcases hi₁.flag with h | ⟨l, ha, hb, ho, hl, hlast, h1 | ⟨m0, m1, hms, h0, h1, hfin, hle⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hb, ho, hl, hlast, .inl h1⟩
      · refine .inr ⟨l, ha, hb, ho, hl, hlast, .inr ⟨m0, m1, hms, h0, h1, hfin, fun e he hb0 hkw => ?_⟩⟩
        simp only [Mem.recordAt, Array.mem_push] at he
        rcases he with he | rfl
        · exact hle e he hb0 hkw
        · exact absurd hfin (hnd hb0 hkw)
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

/-- The race check of an access by the current thread to block `b`: each entry of `b` is a write
before every thread, happened before the thread, or does not race by its kind. -/
theorem noRace_inv {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (h : ∀ e ∈ m.footprint, e.block = b → FpOk G m e →
      (e.kind = .write ∧ Before m e.clock) ∨ VClock.le e.clock (m.clocks[m.current]!) = true ∨
        racePair e.kind k = none) :
    NoRace m b o len k :=
  noRace_of fun e he hb _ _ => by
    rcases h e he hb (hi.fp e he) with ⟨-, hle⟩ | h | h
    · exact .inl (hle _ ht)
    · exact .inl h
    · exact .inr h

theorem racePair_atomic {a b : AccessKind} (ha : a.isAtomic = true) (hb : b.isAtomic = true) :
    racePair a b = none := by
  unfold racePair; rw [ha, hb]; simp

/-- `u`'s ghost value is `main`'s or the writer's: `u` is thread 0 or 1. -/
theorem thr_of {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : ThrOk G m)
    (hg : G u = .run ∨ G u = .joins ∨ G u = .start ∨ G u = .wrote ∨ G u = .fin) :
    m.threads.size = 2 ∧ u < 2 := by
  obtain ⟨-, -, ⟨-, h0, hn⟩ | ⟨hs, -, -, -, hn⟩⟩ := h
  · by_cases hu : u = 0
    · subst hu; rw [h0] at hg; simp at hg
    · rw [hn u (by unfold ThreadId at *; omega)] at hg; simp at hg
  · refine ⟨hs, ?_⟩
    by_cases hu : 2 ≤ u
    · rw [hn u hu] at hg; simp at hg
    · unfold ThreadId at *; omega

/-- A `u32` store gives 4 bytes. -/
theorem enc4 (v : BitVec 32) : (Enc.encode v).size = 4 :=
  LawfulEnc.size_encode (α := BitVec 32) v

/-- The clocks after a record are not smaller. -/
theorem record_cle (m : Mem) (b o len : Nat) (k : AccessKind) (u : Nat) :
    VClock.le (m.clocks[u]!) ((m.recordAt b o len k).clocks[u]!) = true := by
  simp only [Mem.recordAt]
  rw [getElem!_set!_ite]
  split
  · rename_i h; rw [h.1]; exact VClock.le_bump _ _
  · exact VClock.le_refl _

theorem before_record {m : Mem} {b o len : Nat} {k : AccessKind} {c : VClock} (h : Before m c) :
    Before (m.recordAt b o len k) c :=
  fun u hu => VClock.le_trans (h u hu) (record_cle m b o len k u)

/-- The invariant depends only on the threads, the clocks, the blocks, the atomic locations and
the footprint. -/
theorem Inv.congr {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : m'.footprint = m.footprint) : Inv G m' where
  thr := by unfold ThrOk; rw [ht, hc]; exact hi.thr
  b0 := hi.b0.congr hb
  b1 := hi.b1.congr hb
  b2 := hi.b2.congr hb
  ctx := by rw [curBytes_congr hb, curBytes_congr hb]; exact hi.ctx
  data := by unfold U32At; rw [curBytes_congr hb]; exact hi.data
  flag := by unfold FlagOk FlagLoc U32At DataLe; rw [ha, curBytes_congr hb, hf]; exact hi.flag
  fp := by
    intro e he
    rw [hf] at he
    have := hi.fp e he
    unfold FpOk Before at this ⊢
    rw [ht, hc]
    exact this
  own := by intro e he; rw [hf] at he; rw [ht, hc]; exact hi.own e he

/-- Two block numbers that differ. -/
theorem blk_ne {x : BlockId} {a b : Nat} (ha : x = a) (hb : x = b) (hab : a ≠ b) : False :=
  hab (ha.symm.trans hb)

/-! ## The writer -/

/-- A read of a pointer of the `MpCtx` (block 2, bytes `o..o+8`). -/
theorem step_ctx {G : ThreadId → Gh} {m m' : Mem} {o : Nat} {q q₀ : Ptr} (hi : Inv G m)
    (ho : o + 8 ≤ 16) (hoa : o % 8 = 0) (hq : curBytes m 2 o 8 = Enc.encode q₀)
    (h : ((load Ptr 8 ⟨some 2, (o : Int)⟩).run m).run = some (.ok (q, m'))) (ht : m.current < m.threads.size) :
    q = q₀ ∧ m' = m.recordAt 2 o 8 .read ∧ Inv G m' := by
  obtain ⟨b, blk, o', hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨blk₂, hb₂, -, -, hacc₂⟩ := access_blk (a := 8) (len := Enc.size Ptr) (o := o) hi.b2
    (by show o + 8 ≤ 16; omega) (fun A hA => by omega) rfl
  rw [hacc₂] at hacc
  cases hacc
  have hx : blk.bytes.extract o (o + Enc.size Ptr) = Enc.encode q₀ := by
    have := hq; unfold curBytes at this; rw [hb₂] at this; exact this
  rw [hx, LawfulEnc.decode_encode] at hdec
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht (fun h => by cases h) (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩

theorem ctx_noErr {G : ThreadId → Gh} {m : Mem} {o : Nat} {q₀ : Ptr} (hi : Inv G m)
    (ht : m.current < m.threads.size) (ho : o + 8 ≤ 16) (hoa : o % 8 = 0)
    (hq : curBytes m 2 o 8 = Enc.encode q₀) (e : Error) :
    ((load Ptr 8 ⟨some 2, (o : Int)⟩).run m).run ≠ some (.error e) := by
  obtain ⟨blk₂, hb₂, -, -, hacc₂⟩ := access_blk (a := 8) (len := Enc.size Ptr) (o := o) hi.b2
    (by show o + 8 ≤ 16; omega) (fun A hA => by omega) rfl
  have hx : blk₂.bytes.extract o (o + Enc.size Ptr) = Enc.encode q₀ := by
    have := hq; unfold curBytes at this; rw [hb₂] at this; exact this
  have hnr : NoRace m 2 o (Enc.size Ptr) .read := noRace_inv hi ht fun e _ hb hf => by
    rcases hf with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hk⟩
    · exact .inl h
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
    · exact .inr (.inr (by rw [hk]; rfl))
  exact MemM.noErr_of_run (load_run hacc₂ (by rw [hx]; exact LawfulEnc.decode_encode q₀) hnr) e

/-- A change of the ghost value of `main` (`run`, `joins`) or of the writer (`start`, `wrote`,
`fin`) keeps `ThrOk`. -/
theorem thr_upd {G : ThreadId → Gh} {m m' : Mem} {u : ThreadId} {g : Gh} (h : ThrOk G m)
    (ht : m'.threads = m.threads) (hc : m'.clocks.size = m.clocks.size)
    (hu : (u = 0 ∧ (G 0 = .run ∨ G 0 = .joins) ∧ (g = .run ∨ g = .joins)) ∨
      (u = 1 ∧ (G 1 = .start ∨ G 1 = .wrote ∨ G 1 = .fin) ∧ (g = .start ∨ g = .wrote ∨ g = .fin))) :
    ThrOk (upd G u g) m' := by
  obtain ⟨h0, hcs, ⟨-, hp, hn⟩ | ⟨hs2, hr, g0, g1, g2⟩⟩ := h
  · exfalso
    rcases hu with ⟨rfl, hg, -⟩ | ⟨rfl, hg, -⟩
    · rw [hp] at hg; simp at hg
    · rw [hn 1 (by decide)] at hg; simp at hg
  refine ⟨ht ▸ h0, by rw [hc, ht]; exact hcs, .inr ⟨ht ▸ hs2, ht ▸ hr, ?_, ?_, fun v hv => ?_⟩⟩
  · rcases hu with ⟨rfl, -, hg⟩ | ⟨rfl, -, -⟩
    · rw [upd_self]; exact hg
    · rw [upd_ne _ _ (by decide)]; exact g0
  · rcases hu with ⟨rfl, -, -⟩ | ⟨rfl, -, hg⟩
    · rw [upd_ne _ _ (by decide)]; exact g1
    · rw [upd_self]; exact hg
  · rw [upd_ne _ _ (by rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> unfold ThreadId at * <;> omega)]
    exact g2 v hv

/-- A write of 4 bytes to `data` (block 0) while the writer is at `start`. -/
theorem Inv.write0 {G : ThreadId → Gh} {m : Mem} {blk : Block} {bs : Array Byte} (hi : Inv G m)
    (hg : G 1 = .start) (hb : m.blocks[0]? = some blk) (hbs : bs.size = 4) :
    Inv G (m.write 0 blk 0 bs) := by
  have hfit : 0 + bs.size ≤ blk.bytes.size := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b0
    rw [hb] at hb'; cases hb'; omega
  exact {
    thr := hi.thr
    b0 := BlkAt.write hb hfit hi.b0
    b1 := BlkAt.write hb hfit hi.b1
    b2 := BlkAt.write hb hfit hi.b2
    ctx := by
      rw [curBytes_write_other hb hfit (.inl (by decide)), curBytes_write_other hb hfit (.inl (by decide))]
      exact hi.ctx
    data := fun h => by rw [hg] at h; simp at h
    flag := by
      rcases hi.flag with ⟨ha, hu⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hms⟩
      · exact .inl ⟨ha, by unfold U32At; rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hu⟩
      · exact .inr ⟨l, ha, hlb, hlo, hll, by
          rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hlast, hms⟩
    fp := hi.fp
    own := hi.own }

/-- The writer goes from `start` to `wrote`, when `data` holds 42. -/
theorem Inv.wrote {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (h42 : U32At m 0 42) : Inv (upd G 1 .wrote) m where
  thr := thr_upd hi.thr rfl rfl (.inr ⟨rfl, .inl hg, .inr (.inl rfl)⟩)
  b0 := hi.b0
  b1 := hi.b1
  b2 := hi.b2
  ctx := hi.ctx
  data := fun _ => h42
  flag := by
    rcases hi.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, .inl h1⟩
    · rw [hg] at hfin; cases hfin
  fp := by
    intro e he
    rcases hi.fp e he with h | h | ⟨-, -, h⟩ | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · rw [hg] at h; cases h
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  own := hi.own

/-- The writer's write of 42 to `data`: the writer goes from `start` to `wrote`. -/
theorem step_data {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (hc : m.current = 1)
    (h : ((store (α := BitVec 32) 4 dPtr (42 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    m'.current = 1 ∧ m'.threads = m.threads ∧ Inv (upd G 1 .wrote) m' := by
  obtain ⟨b, blk, o, hacc, -, rfl⟩ := store_ok h
  obtain ⟨blk₀, hb₀, -, hs₀, hacc₀⟩ := access_blk (p := dPtr) (a := 4)
    (len := (Enc.encode (42 : BitVec 32)).size) (o := 0) hi.b0 (by rw [enc4]; omega)
    (fun A hA => by omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  have ht : m.current < m.threads.size := by
    rw [hc, (thr_of hi.thr (.inr (.inr (.inl hg)))).1]; decide
  have hfit : 0 + (Enc.encode (42 : BitVec 32)).size ≤ blk.bytes.size := by rw [enc4, hs₀]; omega
  have hir := hi.record (b := 0) (o := 0) (len := (Enc.encode (42 : BitVec 32)).size) (k := .write)
    ht (fun _ _ => by rw [hg]; decide) (.inr (.inl ⟨rfl, rfl, hc⟩))
  have hb : (m.recordAt 0 0 (Enc.encode (42 : BitVec 32)).size .write).blocks[0]? = some blk := hb₀
  refine ⟨hc, rfl, (hir.write0 hg hb (enc4 42)).wrote hg ?_⟩
  unfold U32At
  have := curBytes_write_same hb hfit
  rw (occs := .pos [2]) [enc4] at this
  rw [this]
  exact intOfBytes_rmw 42

theorem data_noErr {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (hc : m.current = 1) (e : Error) :
    ((store (α := BitVec 32) 4 dPtr (42 : BitVec 32)).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, hk, -, hacc₀⟩ := access_blk (p := dPtr) (a := 4)
    (len := Enc.size (BitVec 32)) (o := 0) hi.b0 (by decide) (fun A hA => by omega) rfl
  have ht : m.current < m.threads.size := by
    rw [hc, (thr_of hi.thr (.inr (.inr (.inl hg)))).1]; decide
  have hnr : NoRace m 0 0 (Enc.size (BitVec 32)) .write := noRace_inv hi ht fun e he hb hf => by
    rcases hf with h | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · refine .inr (.inl ?_)
      have := (hi.own e he).2
      rw [h, ← hc] at this
      exact this
    · rw [hg] at h; cases h
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
  exact MemM.noErr_of_run (store_run (42 : BitVec 32) hacc₀ hk hnr) e

/-! ## The flag's atomic location -/

/-- The flag's location at an atomic op (`locIdx 1 0 4`): location 0, with the flag's messages.
The op changes only `atomics` and `nextMsg`. -/
theorem loc_flag {G : ThreadId → Gh} {m m₁ : Mem} {li : Nat} (hf : FlagOk G m)
    (h : ((locIdx 1 0 4).run m).run = some (.ok (li, m₁))) :
    li = 0 ∧ ∃ l k, FlagLoc G m l ∧ m₁ = { m with atomics := #[l], nextMsg := k } := by
  rcases hf with ⟨ha, hu⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hms⟩
  · obtain ⟨rfl, rfl⟩ := locIdx_new (by rw [ha]; simp) h
    let m0 : Msg := { id := m.nextMsg, bytes := curBytes m 1 0 4, clock := plainClock m 1 0 4, relClock := #[] }
    let l : ALoc := { block := 1, off := 0, len := 4, msgs := #[m0] }
    refine ⟨by rw [ha]; rfl, l, m.nextMsg + 1, ⟨rfl, rfl, rfl, rfl, .inl ⟨_, rfl, hu⟩⟩, ?_⟩
    rw [ha]
    rfl
  · have hfind : m.atomics.findIdx? (fun l => l.block == 1 && l.off == 0) = some 0 := by
      rw [ha]; simp [hlb, hlo]
    have hl0 : m.atomics[0]! = l := by rw [ha]; rfl
    obtain ⟨rfl, hm⟩ := locIdx_found hfind (by rw [hl0]; exact hll) (by rw [hl0]; exact hlast) h
    refine ⟨rfl, l, m.nextMsg, ⟨hlb, hlo, hll, hlast, hms⟩, ?_⟩
    rw [hm]
    cases m
    simp only at ha
    subst ha
    rfl

theorem flag_locIdx_noErr {G : ThreadId → Gh} {m : Mem} (hf : FlagOk G m) (e : Error) :
    ((locIdx 1 0 4).run m).run ≠ some (.error e) := by
  refine locIdx_noErr (fun i hi => ?_) (fun hn l hl => ?_) e
  · rcases hf with ⟨ha, -⟩ | ⟨l, ha, -, -, hll, -⟩
    · rw [ha] at hi; simp at hi
    · have := (Array.findIdx?_eq_some_iff_getElem.mp hi).1
      rw [ha] at this hi ⊢
      have : i = 0 := by simp at this; omega
      subst this; exact hll
  · rcases hf with ⟨ha, -⟩ | ⟨l', ha, hlb, hlo, -, -⟩
    · rw [ha] at hl; simp at hl
    · rw [ha] at hn; simp [hlb, hlo] at hn

/-- A new flag location for the invariant. -/
theorem Inv.setLoc {G : ThreadId → Gh} {m : Mem} {l : ALoc} (hi : Inv G m) (hl : FlagLoc G m l)
    (k : Nat) : Inv G { m with atomics := #[l], nextMsg := k } :=
  { hi with flag := .inr ⟨l, rfl, hl⟩ }

/-- The flag's location has at least one message. -/
theorem FlagLoc.pos {G : ThreadId → Gh} {m : Mem} {l : ALoc} (h : FlagLoc G m l) :
    0 < l.msgs.size := by
  obtain ⟨-, -, -, -, ⟨m0, hms, -⟩ | ⟨m0, m1, hms, -⟩⟩ := h <;> rw [hms] <;> simp

/-- An atomic access to the flag: block 1, offset 0. -/
theorem accW_flag {m : Mem} {b : BlockId} {blk : Block} {o : Nat} (hb1 : BlkAt m 1 4 4)
    (h : m.accessW fPtr (intSize 32) 4 = pure (b, blk, o)) :
    b = 1 ∧ o = 0 ∧ m.blocks[1]? = some blk := by
  obtain ⟨blk₁, hb₁, -, -, he⟩ := access_blk (p := fPtr) (a := 4) (len := intSize 32) (o := 0) hb1
    (by decide) (fun A hA => by omega) rfl
  have ha := (accessW_pure h).1
  rw [he] at ha
  cases ha
  exact ⟨rfl, rfl, hb₁⟩

theorem acc_flag {m : Mem} {b : BlockId} {blk : Block} {o : Nat} (hb1 : BlkAt m 1 4 4)
    (h : m.access fPtr (intSize 32) 4 = pure (b, blk, o)) :
    b = 1 ∧ o = 0 ∧ m.blocks[1]? = some blk := by
  obtain ⟨blk₁, hb₁, -, -, he⟩ := access_blk (p := fPtr) (a := 4) (len := intSize 32) (o := 0) hb1
    (by decide) (fun A hA => by omega) rfl
  rw [he] at h
  cases h
  exact ⟨rfl, rfl, hb₁⟩

/-- An atomic access to the flag does not race. -/
theorem noRace_flag {G : ThreadId → Gh} {m : Mem} {k : AccessKind} (hk : k.isAtomic = true)
    (hi : Inv G m) (ht : m.current < m.threads.size) : NoRace m 1 0 (intSize 32) k :=
  noRace_inv hi ht fun e _ hb hf => by
    rcases hf with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ha⟩ | ⟨h, -⟩
    · exact .inl h
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
    · exact .inr (.inr (racePair_atomic ha hk))
    · exact (blk_ne h hb (by decide)).elim

/-- The writer's message at the flag (1, after the first message): the writer ends. -/
theorem Inv.pushFlag {G : ThreadId → Gh} {M : Mem} {l : ALoc} {m0 msg : Msg} {blk : Block}
    (hi : Inv G M) (hg : G 1 = .wrote) (ha : M.atomics = #[l]) (hms : l.msgs = #[m0])
    (hb : M.blocks[1]? = some blk) (hbs : msg.bytes.size = 4) (hv : Val msg 1)
    (hrel : DataLe M msg.relClock) :
    Inv (upd G 1 .fin) { M.write 1 blk 0 msg.bytes with atomics := #[{ l with msgs := #[m0, msg] }] } := by
  obtain ⟨l', ha', hlb, hlo, hll, -, h1⟩ : ∃ l', M.atomics = #[l'] ∧ FlagLoc G M l' := by
    rcases hi.flag with ⟨ha', -⟩ | h
    · rw [ha] at ha'; simp at ha'
    · exact h
  rw [ha] at ha'
  have hl : l = l' := by simpa using ha'
  subst hl
  have h0 : Val m0 0 := by
    rcases h1 with ⟨m0', hm, hv0⟩ | ⟨-, -, -, -, -, hfin, -⟩
    · rw [hms] at hm
      have : m0 = m0' := by simpa using hm
      subst this; exact hv0
    · rw [hg] at hfin; cases hfin
  have hfit : 0 + msg.bytes.size ≤ blk.bytes.size := by
    obtain ⟨blk', hb', -, hs, -⟩ := hi.b1
    rw [hb] at hb'; cases hb'; omega
  have hcN : ∀ b o len, curBytes { M.write 1 blk 0 msg.bytes with
      atomics := #[{ l with msgs := #[m0, msg] }] } b o len = curBytes (M.write 1 blk 0 msg.bytes) b o len :=
    fun _ _ _ => rfl
  have hlast : ALoc.lastBytes { l with msgs := #[m0, msg] } = curBytes (M.write 1 blk 0 msg.bytes) 1 0 4 := by
    have := curBytes_write_same hb hfit
    rw [hbs] at this
    rw [this]; rfl
  exact {
    thr := thr_upd hi.thr rfl rfl (.inr ⟨rfl, .inr (.inl hg), .inr (.inr rfl)⟩)
    b0 := BlkAt.write hb hfit hi.b0
    b1 := BlkAt.write hb hfit hi.b1
    b2 := BlkAt.write hb hfit hi.b2
    ctx := by
      rw [hcN, hcN, curBytes_write_other hb hfit (.inl (by decide)),
        curBytes_write_other hb hfit (.inl (by decide))]
      exact hi.ctx
    data := fun _ => by
      unfold U32At; rw [hcN, curBytes_write_other hb hfit (.inl (by decide))]; exact hi.data (.inl hg)
    flag := .inr ⟨_, rfl, hlb, hlo, hll, by rw [hcN]; exact hlast,
      .inr ⟨m0, msg, rfl, h0, hv, upd_self _ _ _, hrel⟩⟩
    fp := by
      intro e he
      rcases hi.fp e he with h | h | ⟨h1, h2, -⟩ | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨h1, h2, upd_self _ _ _⟩))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr h)))
    own := hi.own }

/-- The writer's release store of 1 to the flag: the writer ends. -/
theorem step_flag {G : ThreadId → Gh} {m m' : Mem} {c : Nat} (hi : Inv G m) (hg : G 1 = .wrote)
    (hc : m.current = 1)
    (h : ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    m'.threads = m.threads ∧ Inv (upd G 1 .fin) m' := by
  obtain ⟨b, blk, o, li, m₁, slot, hacc, -, hl, hs, rfl⟩ := atomicStoreAt_ok h
  obtain ⟨rfl, rfl, hb₁⟩ := accW_flag hi.b1 hacc
  have hsz := (thr_of hi.thr (.inr (.inr (.inr (.inl hg))))).1
  have ht : m.current < m.threads.size := by rw [hc, hsz]; decide
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicWrite) ht
    (fun h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicWrite).current = 1 := hc
  have hszr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads.size = 2 := hsz
  have hbr : (m.recordAt 1 0 (intSize 32) .atomicWrite).blocks[1]? = some blk := hb₁
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads = m.threads := rfl
  generalize m.recordAt 1 0 (intSize 32) .atomicWrite = mr at hir hl hcur hszr hbr hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  obtain ⟨hlb, hlo, hll, hlast, ⟨m0, hms, h0⟩ | ⟨-, -, -, -, -, hfin, -⟩⟩ := hfl
  · have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    obtain ⟨hf1, hs1⟩ := writeSlots_bounds hs
    rw [hl0, hms] at hs1
    have hslot : slot = (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size := by
      rw [hl0, hms]; simp at hs1 ⊢; omega
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hlb]; exact hbr
    have hiM := hir.setLoc ⟨hlb, hlo, hll, hlast, .inl ⟨m0, hms, h0⟩⟩ k
    have hrel : DataLe { mr with atomics := #[l], nextMsg := k }
        (storeMsg { mr with atomics := #[l], nextMsg := k } .release (1 : BitVec 32)).relClock := by
      intro e he hb0 hkw
      show VClock.le e.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      rcases hir.fp e he with ⟨-, hbf⟩ | ⟨-, -, htid⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hbf 1 (by rw [hszr]; decide)
      · have := (hir.own e he).2; rw [htid] at this; exact this
      · rw [hkw] at hk; cases hk
      · exact (blk_ne h hb0 (by decide)).elim
      · exact (blk_ne h hb0 (by decide)).elim
    have hiN := hiM.pushFlag hg rfl hms hbr (msg := storeMsg { mr with atomics := #[l], nextMsg := k }
      .release (1 : BitVec 32)) (LawfulEnc.size_encode (α := BitVec 32) 1) (intOfBytes_rmw 1) hrel
    unfold storeM
    rw [hslot, insertM_last hbM]
    refine ⟨hthr, hiN.congr rfl rfl ?_ ?_ rfl⟩
    · show mr.blocks.set! _ _ = mr.blocks.set! _ _
      rw [hl0, hlb, hlo]
    · show (#[l] : Array ALoc).set! 0 _ = _
      rw [hl0, hms]; rfl
  · rw [hg] at hfin; cases hfin

theorem flagStore_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (hcr : c < storeCount 32 .release 4 fPtr m ∨ storeCount 32 .release 4 fPtr m = 0 ∧ c = 0)
    (e : Error) : ((atomicStoreAt c .release 4 fPtr (1 : BitVec 32)).run m).run ≠ some (.error e) := by
  obtain ⟨blk₁, hb₁, hk₁, -, hacc₁⟩ := access_blk (p := fPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b1 (by decide) (fun A hA => by omega) rfl
  have hacc : m.accessW fPtr (intSize 32) 4 = pure (1, blk₁, 0) := by simp [Mem.accessW, hacc₁, hk₁]
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicWrite) ht
    (fun h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  refine atomicStoreAt_noErr (storePrep_noErr hacc (noRace_flag rfl hi ht)
    (flag_locIdx_noErr hir.flag)) (fun li slots m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := storePrep_ok hp
  obtain ⟨rfl, rfl, -⟩ := accW_flag hi.b1 hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hne := writeSlots_ne (m := { m.recordAt 1 0 (intSize 32) .atomicWrite with atomics := #[l], nextMsg := k })
    (li := 0) (by show 0 < l.msgs.size; exact hfl.pos)
  have hcount : storeCount 32 .release 4 fPtr m = (writeSlots { m.recordAt 1 0 (intSize 32) .atomicWrite with
      atomics := #[l], nextMsg := k } 0).size := optCount_eq hp
  rw [hcount] at hcr
  rcases hcr with h | ⟨h0, -⟩
  · exact h
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp hne)

/-! ## `main` -/

/-- `main`'s acquire load of the flag: 0, or 1, and then the writer has ended and every write to
`data` happened before `main`. -/
theorem step_load {G : ThreadId → Gh} {m m' : Mem} {c : Nat} {v : BitVec 32} (hi : Inv G m)
    (hg : G 0 = .run) (hc : m.current = 0)
    (h : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run = some (.ok (v, m'))) :
    m'.current = 0 ∧ m'.threads = m.threads ∧ Inv G m' ∧
      (v = 0 ∨ (v = 1 ∧ G 1 = .fin ∧ DataLe m' (m'.clocks[0]!))) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨rfl, rfl, -⟩ := acc_flag hi.b1 hacc
  have hsz := (thr_of hi.thr (.inl hg)).1
  have ht : m.current < m.threads.size := by rw [hc, hsz]; decide
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicRead) ht
    (fun h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicRead).current = 0 := hc
  have hcs : 0 < (m.recordAt 1 0 (intSize 32) .atomicRead).clocks.size := by
    show 0 < (m.clocks.set! _ _).size; simp [hi.thr.2.1, hsz]
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  generalize m.recordAt 1 0 (intSize 32) .atomicRead = mr at hir hl hcur hcs hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM := hir.setLoc hfl k
  have hg' := grows_loadM { mr with atomics := #[l], nextMsg := k } 0 .acquire
    ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!)
  refine ⟨by rw [loadM_current]; exact hcur, hg'.threads.trans hthr, hiM.grow hg', ?_⟩
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  obtain ⟨-, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, hfin, hle⟩⟩ := hfl
  · rw [hms] at hlt hv
    have : pos = 0 := by simp at hlt; omega
    subst this
    left
    have := hv.symm.trans h0
    simpa using this
  · rw [hms] at hlt hv
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    rcases this with rfl | rfl
    · left
      have := hv.symm.trans h0
      simpa using this
    · right
      refine ⟨by have := hv.symm.trans h1; simpa using this, hfin, fun e he hb0 hkw => ?_⟩
      have hmsg : (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[1]! = m1 := by
        rw [hl0, hms]; rfl
      rw [hmsg]
      exact VClock.le_trans (hle e he hb0 hkw) (loadM_acq_le _ _ _ hcur hcs)

theorem load_noErr {G : ThreadId → Gh} {m : Mem} {c : Nat} (hi : Inv G m)
    (ht : m.current < m.threads.size)
    (hcr : c < loadCount 32 .acquire 4 fPtr m ∨ loadCount 32 .acquire 4 fPtr m = 0 ∧ c = 0)
    (e : Error) : ((atomicLoadAt (n := 32) c .acquire 4 fPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₁, hb₁, -, -, hacc₁⟩ := access_blk (p := fPtr) (a := 4) (len := intSize 32) (o := 0)
    hi.b1 (by decide) (fun A hA => by omega) rfl
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicRead) ht
    (fun h => by cases h) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  refine atomicLoadAt_noErr (loadPrep_noErr (rmw := false) (by simpa using hacc₁)
    (by simpa using noRace_flag (k := .atomicRead) rfl hi ht)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact flag_locIdx_noErr hir.flag))
    (fun li opts m₁ hp => ?_) e
  obtain ⟨b, blk, o, hacc', -, hl, rfl⟩ := loadPrep_ok hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hacc' hl
  obtain ⟨rfl, rfl, -⟩ := acc_flag hi.b1 hacc'
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hl0 : ({ m.recordAt 1 0 (intSize 32) .atomicRead with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hcount : loadCount 32 .acquire 4 fPtr m = (readOpts { m.recordAt 1 0 (intSize 32) .atomicRead with
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
  obtain ⟨-, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, -⟩⟩ := hfl
  · rw [hms] at hlt ⊢
    have : pos = 0 := by simp at hlt; omega
    subst this; exact ⟨0, h0⟩
  · rw [hms] at hlt ⊢
    have : pos = 0 ∨ pos = 1 := by simp at hlt; omega
    rcases this with rfl | rfl
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩

/-- `main`'s read of `data` after it read 1 at the flag: 42, no race. -/
theorem step_read {G : ThreadId → Gh} {m m' : Mem} {v : BitVec 32} (hi : Inv G m)
    (hfin : G 1 = .fin) (h : ((load (BitVec 32) 4 dPtr).run m).run = some (.ok (v, m')))
    (ht : m.current < m.threads.size) :
    v = 42 ∧ m' = m.recordAt 0 0 4 .read ∧ Inv G m' := by
  obtain ⟨b, blk, o, hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (p := dPtr) (a := 4) (len := Enc.size (BitVec 32))
    (o := 0) hi.b0 (by decide) (fun A hA => by omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  have h42 := hi.data (.inr hfin)
  unfold U32At curBytes at h42
  rw [hb₀] at h42
  have : (Enc.decode (blk.bytes.extract 0 (0 + Enc.size (BitVec 32))) : Result (BitVec 32)).run =
      some (.ok 42) := h42
  rw [this] at hdec
  simp only [Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht (fun _ h => by cases h) (.inr (.inr (.inl ⟨rfl, rfl, hfin⟩)))⟩

theorem read_noErr {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hfin : G 1 = .fin)
    (hle : DataLe m (m.clocks[m.current]!)) (ht : m.current < m.threads.size) (e : Error) :
    ((load (BitVec 32) 4 dPtr).run m).run ≠ some (.error e) := by
  obtain ⟨blk₀, hb₀, -, -, hacc₀⟩ := access_blk (p := dPtr) (a := 4) (len := Enc.size (BitVec 32))
    (o := 0) hi.b0 (by decide) (fun A hA => by omega) rfl
  have h42 := hi.data (.inr hfin)
  unfold U32At curBytes at h42
  rw [hb₀] at h42
  have hnr : NoRace m 0 0 (Enc.size (BitVec 32)) .read := noRace_inv hi ht fun e he hb hf => by
    rcases hf with h | ⟨-, hk, -⟩ | ⟨-, hk, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr (.inl (hle e he hb hk))
    · exact .inr (.inr (by rw [hk]; rfl))
    · exact (blk_ne h hb (by decide)).elim
    · exact (blk_ne h hb (by decide)).elim
  exact MemM.noErr_of_run (load_run hacc₀ h42 hnr) e

/-- A change of `main`'s ghost value between `run` and `joins`. -/
theorem Inv.retag0 {G : ThreadId → Gh} {m : Mem} {g : Gh} (hi : Inv G m)
    (hg : G 0 = .run ∨ G 0 = .joins) (hg' : g = .run ∨ g = .joins) : Inv (upd G 0 g) m := by
  have h1 : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)
  exact {
    thr := thr_upd hi.thr rfl rfl (.inl ⟨rfl, hg, hg'⟩)
    b0 := hi.b0, b1 := hi.b1, b2 := hi.b2, ctx := hi.ctx
    data := by rw [h1]; exact hi.data
    flag := by unfold FlagOk FlagLoc; rw [h1]; exact hi.flag
    fp := by intro e he; unfold FpOk; rw [h1]; exact hi.fp e he
    own := hi.own }

/-- Every thread was spawned by `main`: the writer joined its own threads (none). -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (hi : Inv G m) (hu : 0 < u) :
    joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, -, h⟩ := hi.thr
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hr
  have h0' : ∀ h : 0 < m.threads.size, (m.threads[0]'h).spawner = 0 := by
    intro h
    rw [Array.getElem?_eq_getElem h] at h0
    rw [Option.some.inj h0]
  rcases h with ⟨h1, -, -⟩ | ⟨h2, ⟨r₁, hr₁, hsp, -⟩, -⟩
  · have : i = 0 := by omega
    subst this
    rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [h0' hi'] at hs; exact absurd hs (Nat.ne_of_lt hu)
    · rw [Array.getElem?_eq_getElem hi'] at hr₁
      rw [Option.some.inj hr₁, hsp] at hs; exact absurd hs (Nat.ne_of_lt hu)

/-- The writer (thread 1): the read of `data`'s pointer, the write of 42, the read of `flag`'s
pointer, the release store of 1 (a stop), its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt = some g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | mpWriter p =>
    simp only [proto] at hg
    split at hg
    · rename_i hp
      subst hp
      cases hg
      have hi₀ : Inv G { m with current := u } := (hi : Inv G m).grow (grows_current m u)
      obtain ⟨hs2, hu2⟩ := thr_of hi₀.thr (.inr (.inr (.inl hgu)))
      have hu1 : u = 1 := by unfold ThreadId at *; omega
      subst hu1
      show proto.WP 1 ((fun _ => ()) <$> mpWriter cPtr) _ G _ d
      refine WP.map ?_
      unfold mpWriter
      refine WP.bind ?_
      rw [StateT.run'_eq]
      refine WP.map ?_
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      rw [show cPtr.add 0 = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl]
      have ht₀ : ({ m with current := 1 } : Mem).current < ({ m with current := 1 } : Mem).threads.size := by
        show 1 < _; rw [hs2]; decide
      -- the pointer to `data`
      refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₀ ht₀ (by decide) (by decide) hi₀.ctx.1 e he).elim)
        fun q m₁ hl => ?_)
      obtain ⟨rfl, rfl, hi₁⟩ := step_ctx hi₀ (by decide) (by decide) hi₀.ctx.1 hl ht₀
      refine ⟨rfl, ?_⟩
      -- the write of 42
      refine WP.bind (WP.liftM (fun e he => (data_noErr hi₁ hgu rfl e he).elim) fun _ m₂ hs => ?_)
      obtain ⟨hc₂, hth₂, hi₂⟩ := step_data hi₁ hgu rfl hs
      refine ⟨by rw [hth₂], ?_⟩
      rw [show cPtr.add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
      have ht₂ : m₂.current < m₂.threads.size := by rw [hc₂, hth₂]; exact ht₀
      -- the pointer to `flag`
      refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₂ ht₂ (by decide) (by decide) hi₂.ctx.2 e he).elim)
        fun q m₃ hl => ?_)
      obtain ⟨rfl, rfl, hi₃⟩ := step_ctx hi₂ (by decide) (by decide) hi₂.ctx.2 hl ht₂
      refine ⟨rfl, ?_⟩
      -- the release store of 1
      simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc, atomicStoreC]
      rw [show fPtr.add 0 = fPtr from rfl]
      refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.wrote, hi₃, fun G₁ m₄ hg₁ hi₄ c hcr => ?_⟩)
      have hi₄' : Inv G₁ { m₄ with current := 1 } := (hi₄ : Inv G₁ m₄).grow (grows_current _ _)
      have ht₄ : ({ m₄ with current := 1 } : Mem).current < ({ m₄ with current := 1 } : Mem).threads.size := by
        show 1 < _; rw [(thr_of hi₄'.thr (.inr (.inr (.inr (.inl hg₁))))).1]; decide
      refine WP.bind (WP.callMC (fun e he => (flagStore_noErr hi₄' ht₄ hcr e he).elim) fun _ m₅ hs₅ => ?_)
      obtain ⟨hth₅, hi₅⟩ := step_flag hi₄' hg₁ rfl hs₅
      refine ⟨by rw [hth₅], ?_⟩
      refine WP.pure' (WP.pure' ?_)
      exact ⟨.fin, hi₅, rfl, fun _ => joinedAll_kid hi₅ (by decide)⟩
    · cases hg
  | mpWriterRelaxed p => cases hg
  | sb p => cases hg
  | push p => cases hg
  | ww p => cases hg

end Atomics.MP
