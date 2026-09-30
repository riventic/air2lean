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

end Atomics.MP
