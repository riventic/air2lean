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

/-- Every write to `data` happened before `c`. -/
def DataLe (m : Mem) (c : VClock) : Prop :=
  ∀ e ∈ m.footprint, e.block = 0 → e.kind = .write → VClock.le e.clock c = true

/-- The flag's atomic location. Its newest message has the block's bytes, and each plain write
to the flag happened before it. It has the first message (0), and then the writer's message (1):
the writer has ended, and every write to `data` happened before the release clock of the
message. -/
def FlagLoc (G : ThreadId → Gh) (m : Mem) (l : ALoc) : Prop :=
  l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 1 0 4 ∧
  PlainLe m 1 0 4 l.lastClock ∧
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
  init tgt g := (match tgt with
      | .mpWriter p => if p = cPtr then some .start else none
      | _ => none) = some g
  fin g := g = .fin
  strict := true
  joins g := g = .joins

/-- `main`'s post: the result. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop :=
  fun v _ m _ => (v = .ok 0 ∨ v = .ok 42) ∧ joinedAll 0 m

/-! ## Frame: steps that keep the invariant -/

theorem Inv.grow {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : Grows m m') : Inv G m' where
  thr := by unfold ThrOk; rw [hg.threads, hg.csize]; exact hi.thr
  b0 := hi.b0.congr hg.blocks
  b1 := hi.b1.congr hg.blocks
  b2 := hi.b2.congr hg.blocks
  ctx := by rw [curBytes_congr hg.blocks, curBytes_congr hg.blocks]; exact hi.ctx
  data := by unfold U32At; rw [curBytes_congr hg.blocks]; exact hi.data
  flag := by
    unfold FlagOk FlagLoc U32At DataLe PlainLe
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
    (hn1 : b = 1 → k ≠ .write)
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
  have hpf : ∀ e ∈ (m.recordAt b o len k).footprint, e ∈ m₁.footprint ∨ plainHit 1 0 4 e = false := by
    intro e he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr (plainHit_false_of hn1)
  exact {
    thr := hi₁.thr, b0 := hi₁.b0, b1 := hi₁.b1, b2 := hi₁.b2, ctx := hi₁.ctx, data := hi₁.data
    flag := by
      rcases hi₁.flag with h | ⟨l, ha, hb, ho, hl, hlast, hpl, h1 | ⟨m0, m1, hms, h0, h1, hfin, hle⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hb, ho, hl, hlast, hpl.of_fp hpf, .inl h1⟩
      · refine .inr ⟨l, ha, hb, ho, hl, hlast, hpl.of_fp hpf,
          .inr ⟨m0, m1, hms, h0, h1, hfin, fun e he hb0 hkw => ?_⟩⟩
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
  flag := by unfold FlagOk FlagLoc U32At DataLe PlainLe; rw [ha, curBytes_congr hb, hf]; exact hi.flag
  fp := by
    intro e he
    rw [hf] at he
    have := hi.fp e he
    unfold FpOk Before at this ⊢
    rw [ht, hc]
    exact this
  own := by intro e he; rw [hf] at he; rw [ht, hc]; exact hi.own e he

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
  rw [hx, decodeLoad_of_decode (LawfulEnc.decode_encode _)] at hdec
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht (fun h => by cases h) (by decide) (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))⟩

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
      rcases hi.flag with ⟨ha, hu⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hms⟩
      · exact .inl ⟨ha, by unfold U32At; rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hu⟩
      · exact .inr ⟨l, ha, hlb, hlo, hll, by
          rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hlast, hpl, hms⟩
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
    rcases hi.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl, .inl h1⟩
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
    (len := (Enc.encode (42 : BitVec 32)).size) (o := 0) hi.b0 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) rfl
  rw [hacc₀] at hacc
  cases hacc
  have ht : m.current < m.threads.size := by
    rw [hc, (thr_of hi.thr (.inr (.inr (.inl hg)))).1]; decide
  have hfit : 0 + (Enc.encode (42 : BitVec 32)).size ≤ blk.bytes.size := by rw [size_encode_u32, hs₀]; omega
  have hir := hi.record (b := 0) (o := 0) (len := (Enc.encode (42 : BitVec 32)).size) (k := .write)
    ht (fun _ _ => by rw [hg]; decide) (by decide) (.inr (.inl ⟨rfl, rfl, hc⟩))
  have hb : (m.recordAt 0 0 (Enc.encode (42 : BitVec 32)).size .write).blocks[0]? = some blk := hb₀
  refine ⟨hc, rfl, (hir.write0 hg hb (size_encode_u32 42)).wrote hg ?_⟩
  unfold U32At
  have := curBytes_write_same hb hfit
  rw (occs := .pos [2]) [size_encode_u32] at this
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
  have h0 : m.atomics = #[] ∨ ∃ l, m.atomics = #[l] ∧ l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧
      ALoc.lastBytes l = curBytes m 1 0 4 ∧ PlainLe m 1 0 4 l.lastClock := by
    rcases hf with ⟨ha, -⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, -⟩
    · exact .inl ha
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl⟩
  obtain ⟨rfl, l, k, rfl, ⟨ha, rfl⟩ | ha⟩ := locIdx_single h0 h
  · rcases hf with ⟨-, hu⟩ | ⟨l, ha', -⟩
    · refine ⟨rfl, firstLoc m 1 0 4, k, ⟨rfl, rfl, rfl, rfl, fun e he hh => ?_,
        .inl ⟨firstMsg m 1 0 4, rfl, hu⟩⟩, rfl⟩
      simpa [ALoc.lastClock, firstLoc, firstMsg] using plainLe_plainClock m 1 0 4 e he hh
    · rw [ha] at ha'; simp at ha'
  · rcases hf with ⟨ha', -⟩ | ⟨l', ha', hfl⟩
    · rw [ha] at ha'; simp at ha'
    · rw [ha] at ha'
      have : l = l' := by simpa using ha'
      subst this
      exact ⟨rfl, l, k, hfl, rfl⟩

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
  obtain ⟨-, -, -, -, -, ⟨m0, hms, -⟩ | ⟨m0, m1, hms, -⟩⟩ := h <;> rw [hms] <;> simp

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
    (hrel : DataLe M msg.relClock) (hpl : PlainLe M 1 0 4 msg.clock) :
    Inv (upd G 1 .fin) { M.write 1 blk 0 msg.bytes with atomics := #[{ l with msgs := #[m0, msg] }] } := by
  obtain ⟨l', ha', hlb, hlo, hll, -, -, h1⟩ : ∃ l', M.atomics = #[l'] ∧ FlagLoc G M l' := by
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
      fun e he hh => by simpa [ALoc.lastClock] using hpl e he hh,
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
    (fun h => by cases h) (by decide) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicWrite).current = 1 := hc
  have hszr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads.size = 2 := hsz
  have hbr : (m.recordAt 1 0 (intSize 32) .atomicWrite).blocks[1]? = some blk := hb₁
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads = m.threads := rfl
  generalize m.recordAt 1 0 (intSize 32) .atomicWrite = mr at hir hl hcur hszr hbr hthr
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  obtain ⟨hlb, hlo, hll, hlast, hpl, ⟨m0, hms, h0⟩ | ⟨-, -, -, -, -, hfin, -⟩⟩ := hfl
  · have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    obtain ⟨hf1, hs1⟩ := writeSlots_bounds hs
    rw [hl0, hms] at hs1
    have hslot : slot = (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size := by
      rw [hl0, hms]; simp at hs1 ⊢; omega
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hlb]; exact hbr
    have hiM := hir.setLoc ⟨hlb, hlo, hll, hlast, hpl, .inl ⟨m0, hms, h0⟩⟩ k
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
    have hplM : PlainLe { mr with atomics := #[l], nextMsg := k } 1 0 4
        (storeMsg { mr with atomics := #[l], nextMsg := k } .release (1 : BitVec 32)).clock := by
      intro e he hh
      show VClock.le e.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      have hb1 := plainHit_block hh
      have hkw := plainHit_kind hh
      rcases hir.fp e he with ⟨-, hbf⟩ | ⟨h, -⟩ | ⟨-, hk, -⟩ | ⟨-, ha⟩ | ⟨h, -⟩
      · exact hbf 1 (by rw [hszr]; decide)
      · exact (blk_ne h hb1 (by decide)).elim
      · rw [hkw] at hk; cases hk
      · rw [hkw] at ha; cases ha
      · exact (blk_ne h hb1 (by decide)).elim
    have hiN := hiM.pushFlag hg rfl hms hbr (msg := storeMsg { mr with atomics := #[l], nextMsg := k }
      .release (1 : BitVec 32)) (LawfulEnc.size_encode (α := BitVec 32) 1) (intOfBytes_rmw 1) hrel hplM
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
    (fun h => by cases h) (by decide) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
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
    (fun h => by cases h) (by decide) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
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
  obtain ⟨-, -, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, hfin, hle⟩⟩ := hfl
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
    (fun h => by cases h) (by decide) (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
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
  obtain ⟨-, -, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, -⟩⟩ := hfl
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
  rw [decodeLoad_run_of_decode this] at hdec
  simp only [Option.some.injEq, Except.ok.injEq] at hdec
  exact ⟨hdec.symm, rfl, hi.record ht (fun _ h => by cases h) (by decide) (.inr (.inr (.inl ⟨rfl, rfl, hfin⟩)))⟩

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
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
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
      rw [show cPtr = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl]
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
      -- the pointer to `flag`'s field (`ptrProject`: in bounds of the 16-byte context)
      refine WP.bind (WP.callMC_ptrProject (hi₂.b2.ptrProject_run (o := 0) (k := 8) (by decide)) ?_)
      rw [show (⟨some 2, ((0 : Nat) : Int)⟩ : Ptr).add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
      have ht₂ : m₂.current < m₂.threads.size := by rw [hc₂, hth₂]; exact ht₀
      -- the pointer to `flag`
      refine WP.bind (WP.liftM (fun e he => (ctx_noErr hi₂ ht₂ (by decide) (by decide) hi₂.ctx.2 e he).elim)
        fun q m₃ hl => ?_)
      obtain ⟨rfl, rfl, hi₃⟩ := step_ctx hi₂ (by decide) (by decide) hi₂.ctx.2 hl ht₂
      refine ⟨rfl, ?_⟩
      -- the release store of 1
      simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc, atomicStoreC]
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

/-! ## `main` before its spawn -/

/-- `main` before its spawn: `Solo`, with the three blocks. -/
structure Pre (m : Mem) : Prop extends Solo m where
  b0 : BlkAt m 0 4 4
  b1 : BlkAt m 1 4 4
  b2 : BlkAt m 2 16 8

/-- `main`'s store before its spawn, to block `b` at `o` (`solo_store`). -/
theorem pre_store {α : Type} [Enc α] {m m' : Mem} {b sz al o a : Nat} {v : α} (h : Pre m)
    (hb : BlkAt m b sz al) (hfit : o + (Enc.encode v).size ≤ sz)
    (hal : ∀ A : Nat, A % al = 0 → (A + o) % a = 0)
    (hs : ((store a ⟨some b, (o : Int)⟩ v).run m).run = some (.ok ((), m'))) :
    Pre m' ∧ curBytes m' b o (Enc.encode v).size = Enc.encode v ∧
      ∀ b' o' len, (b ≠ b' ∨ b' = b ∧ o' + len ≤ sz ∧ (o + (Enc.encode v).size ≤ o' ∨ o' + len ≤ o)) →
        curBytes m' b' o' len = curBytes m b' o' len := by
  obtain ⟨hs', hk, -, h1, h2⟩ := solo_store h.toSolo hb hfit hal hs
  exact ⟨{ toSolo := hs', b0 := hk _ _ _ h.b0, b1 := hk _ _ _ h.b1, b2 := hk _ _ _ h.b2 }, h1, h2⟩

theorem pre_store_noErr {α : Type} [Enc α] {m : Mem} {b sz al o a : Nat} {v : α} (h : Pre m)
    (hb : BlkAt m b sz al) (hfit : o + (Enc.encode v).size ≤ sz)
    (hal : ∀ A : Nat, A % al = 0 → (A + o) % a = 0) (e : Error) :
    ((store a ⟨some b, (o : Int)⟩ v).run m).run ≠ some (.error e) :=
  solo_store_noErr h.toSolo hb hfit hal e

/-- The start: before its spawn, `main` holds the invariant with the ghost value `pre`. -/
def G0 : ThreadId → Gh := fun u => if u = 0 then .pre else .none

theorem pre_inv {m : Mem} (h : Pre m) (h1 : U32At m 1 0)
    (hctx : curBytes m 2 0 8 = Enc.encode dPtr ∧ curBytes m 2 8 8 = Enc.encode fPtr) : Inv G0 m where
  thr := by
    refine ⟨by rw [h.thr]; rfl, by rw [h.clk, h.thr]; rfl, .inl ⟨by rw [h.thr]; rfl, rfl, fun u hu => ?_⟩⟩
    unfold G0; split
    · rename_i h; unfold ThreadId at *; omega
    · rfl
  b0 := h.b0
  b1 := h.b1
  b2 := h.b2
  ctx := hctx
  data := fun hg => by simp [G0] at hg
  flag := .inl ⟨h.at0, h1⟩
  fp := fun e he => .inl ⟨(h.fp e he).1, fun u hu => by
    have : u = 0 := by rw [h.thr] at hu; simp at hu; omega
    rw [this]; exact (h.fp e he).2.2⟩
  own := fun e he => by
    obtain ⟨-, h2, h3⟩ := h.fp e he
    rw [h2]; exact ⟨by rw [h.thr]; decide, h3⟩

/-- `main`'s spawn, for the threads: the writer is thread 1; `main` goes to `run`, the writer
starts. -/
theorem thr_fork {G : ThreadId → Gh} {m : Mem} (h : ThrOk G m) (hg : G 0 = .pre)
    (hc : m.current = 0) :
    m.threads.size = 1 ∧ (∀ u, 1 ≤ u → G u = .none) ∧ m.clocks.size = 1 ∧
    ThrOk (upd (upd G 1 .start) 0 .run) { m with
      clocks := (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
        (VClock.bump (m.clocks[m.current]!) m.current),
      threads := m.threads.push { spawner := m.current, joined := false } } := by
  obtain ⟨h0, hcs, hthr⟩ := h
  obtain ⟨hs1, -, hnone⟩ : m.threads.size = 1 ∧ G 0 = .pre ∧ ∀ u, 1 ≤ u → G u = .none := by
    rcases hthr with h | ⟨-, -, g0, -, -⟩
    · exact h
    · rcases g0 with g0 | g0 <;> rw [hg] at g0 <;> cases g0
  have hG1 : (upd (upd G 1 .start) 0 .run) 1 = .start := by rw [upd_ne _ _ (by decide), upd_self]
  refine ⟨hs1, hnone, by rw [hcs, hs1], ⟨by
      rw [Array.getElem?_push_lt (by omega), ← Array.getElem?_eq_getElem (by omega)]; exact h0,
    by simp [hcs], .inr ⟨by simp [hs1], ⟨{ spawner := m.current, joined := false },
      by simp [Array.getElem_push, hs1], hc, rfl⟩, .inl (upd_self _ _ _), .inl hG1, fun u hu => ?_⟩⟩⟩
  rw [upd_ne _ _ (by unfold ThreadId at *; omega), upd_ne _ _ (by unfold ThreadId at *; omega)]
  exact hnone u (by unfold ThreadId at *; omega)

/-- `main`'s spawn: the writer is thread 1. The writer's clock is a copy of `main`'s bumped
clock, so each write before the spawn happened before both threads. -/
theorem inv_fork {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : Inv G m) (hg : G 0 = .pre)
    (hc : m.current = 0) (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ Inv (upd (upd G 1 .start) 0 .run) m' := by
  rw [fork_run] at h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hs1, hnone, hcs, hthr⟩ := thr_fork hi.thr hg hc
  refine ⟨hs1, hc, ?_⟩
  have hG1 : (upd (upd G 1 .start) 0 .run) 1 = .start := by rw [upd_ne _ _ (by decide), upd_self]
  have hcl : ∀ u < 2, VClock.le (m.clocks[0]!) (((m.clocks.set! m.current
      (VClock.bump (m.clocks[m.current]!) m.current)).push
      (VClock.bump (m.clocks[m.current]!) m.current))[u]!) = true := by
    intro u hu
    rw [hc, fork_clocks_one hcs u hu]
    exact VClock.le_bump _ _
  refine {
    thr := hthr
    b0 := hi.b0
    b1 := hi.b1
    b2 := hi.b2
    ctx := hi.ctx
    data := fun h => by rw [hG1] at h; simp at h
    flag := ?_
    fp := ?_
    own := ?_ }
  · rcases hi.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, h1 | ⟨-, -, -, -, -, hfin, -⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl, .inl h1⟩
    · rw [hnone 1 (by decide)] at hfin; cases hfin
  · intro e he
    rcases hi.fp e he with ⟨hk, hb⟩ | h | ⟨-, -, hfin⟩ | h | h
    · refine .inl ⟨hk, fun u hu => VClock.le_trans (hb 0 (by rw [hs1]; decide)) (hcl u ?_)⟩
      simpa [hs1] using hu
    · exact .inr (.inl h)
    · rw [hnone 1 (by decide)] at hfin; cases hfin
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · intro e he
    obtain ⟨h1, h2⟩ := hi.own e he
    have ht0 : e.tid = 0 := by unfold ThreadId at *; omega
    refine ⟨by rw [ht0, Array.size_push, hs1]; decide, ?_⟩
    rw [ht0] at h2 ⊢
    exact VClock.le_trans h2 (hcl 0 (by decide))

/-- `main`'s join of the writer is possible: thread 1, spawned by `main`, not joined. -/
theorem join_ok {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (h0 : G 0 = .joins) :
    ∃ m', ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m')) := by
  obtain ⟨-, -, ⟨-, hp, -⟩ | ⟨-, ⟨r, hr, hs, hj⟩, -⟩⟩ := hi.thr
  · rw [h0] at hp; cases hp
  · exact join_run (m := { m with current := 0 }) hr hs hj

/-- After the join: `main` joined every thread; the blocks are the same. -/
theorem join_final {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (h0 : G 0 = .joins)
    (hj : ((Thread.join 1).run { m with current := 0 }).run = some (.ok ((), m'))) :
    joinedAll 0 m' ∧ m'.threads.size = 2 ∧ m'.blocks = m.blocks := by
  obtain ⟨rec, hr, hjf, rfl⟩ := join_eq hj
  obtain ⟨h00, hcs, ⟨-, hp, -⟩ | ⟨hs2, -, -, -, -⟩⟩ := hi.thr
  · rw [h0] at hp; cases hp
  refine ⟨?_, by simp [hs2], rfl⟩
  intro r hrm hsp
  obtain ⟨i, hi', rfl⟩ := Array.mem_iff_getElem.mp hrm
  simp only [Array.size_set!] at hi'
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hi'] at hsp ⊢
  split
  · rfl
  · rename_i hne
    have : i = 0 := by omega
    subst this
    rw [Array.getElem?_eq_getElem (by omega)] at h00
    rw [Option.some.inj h00]

theorem init_run : (atomic_Value_u32_init 0).run = some (.ok ⟨0⟩) := rfl

theorem enc_av : Enc.encode ({ raw := 0 } : atomic_Value_u32) = Enc.encode (0 : BitVec 32) := by
  decide +kernel

theorem enc_av4 : (Enc.encode ({ raw := 0 } : atomic_Value_u32)).size = 4 := by
  rw [enc_av]; exact size_encode_u32 0

/-- `main`: three blocks, four stores, the spawn, the acquire load of the flag (a stop), the read
of `data` if the flag is 1, the join (a stop), three frees. -/
theorem main_spec (σ : Placement) (d : Nat) :
    proto.WP 0 mpRelAcq QM G0 { mem0 σ with current := 0 } d := by
  unfold mpRelAcq
  -- the blocks: `data`, `flag`, the `MpCtx`
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s0 m₁ ha₁ => ?_)
  obtain ⟨hq₁, hm₁⟩ := alloc_ok ha₁
  have e0 : s0 = dPtr := by rw [hq₁]; rfl
  subst e0 hm₁
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s2 m₂ ha₂ => ?_)
  obtain ⟨hq₂, hm₂⟩ := alloc_ok ha₂
  have e2 : s2 = fPtr := by rw [hq₂]; rfl
  subst e2 hm₂
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e h => (alloc_noErr e h).elim) fun s5 m₃ ha₃ => ?_)
  obtain ⟨hq₃, hm₃⟩ := alloc_ok ha₃
  have e5 : s5 = cPtr := by rw [hq₃]; rfl
  subst e5
  refine ⟨by rw [hm₃] <;> rfl, ?_⟩
  have hp₃ : Pre m₃ := by
    rw [hm₃]
    exact { toSolo := ⟨rfl, rfl, rfl, rfl, fun e he => by simp [mem0, Mem.ofGlobals, Mem.afterAlloc] at he⟩
            b0 := by blkat_alloc
            b1 := by blkat_alloc
            b2 := by blkat_alloc }
  clear hm₃ ha₃ hq₃
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [show dPtr = ⟨some 0, ((0 : Nat) : Int)⟩ from rfl, show fPtr = ⟨some 1, ((0 : Nat) : Int)⟩ from rfl]
  -- `data = 0`
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₃ hp₃.b0 (by rw [size_encode_u32]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₄ hs₄ => ?_)
  obtain ⟨hp₄, -, -⟩ := pre_store hp₃ hp₃.b0 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₄
  refine ⟨by rw [hp₄.thr, hp₃.thr], ?_⟩
  -- `flag = .init(0)`
  refine WP.bind (WP.callRC (fun e he => by rw [init_run] at he; cases he) fun a ha => ?_)
  rw [init_run] at ha
  cases ha
  dsimp only
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₄ hp₄.b1 (by rw [enc_av4]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₅ hs₅ => ?_)
  obtain ⟨hp₅, h1₅, hk₅⟩ := pre_store hp₄ hp₄.b1 (by rw [enc_av4]; omega) (fun A hA => by omega) hs₅
  refine ⟨by rw [hp₅.thr, hp₄.thr], ?_⟩
  -- the `MpCtx`
  dsimp only
  rw [show cPtr = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl]
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₅ hp₅.b2 (by rw [size_encode_ptr]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₆ hs₆ => ?_)
  obtain ⟨hp₆, h2₆, hk₆⟩ := pre_store hp₅ hp₅.b2 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₆
  refine ⟨by rw [hp₆.thr, hp₅.thr], ?_⟩
  dsimp only
  refine WP.bind (WP.callMC_ptrProject (hp₆.b2.ptrProject_run (o := 0) (k := 8) (by decide)) ?_)
  rw [show (⟨some 2, ((0 : Nat) : Int)⟩ : Ptr).add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
  dsimp only
  refine WP.bind (WP.liftM (fun e he => (pre_store_noErr hp₆ hp₆.b2 (by rw [size_encode_ptr]; omega)
    (fun A hA => by omega) e he).elim) fun _ m₇ hs₇ => ?_)
  obtain ⟨hp₇, h3₇, hk₇⟩ := pre_store hp₆ hp₆.b2 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₇
  refine ⟨by rw [hp₇.thr, hp₆.thr], ?_⟩
  have hi₇ : Inv G0 m₇ := by
    refine pre_inv hp₇ ?_ ⟨?_, ?_⟩
    · unfold U32At
      rw [hk₇ 1 0 4 (.inl (by decide)), hk₆ 1 0 4 (.inl (by decide))]
      rw [enc_av4] at h1₅
      rw [h1₅, enc_av]
      exact intOfBytes_rmw 0
    · rw [hk₇ 2 0 8 (.inr ⟨rfl, by decide, .inr (by decide)⟩)]
      rw [size_encode_ptr] at h2₆
      exact h2₆
    · rw [size_encode_ptr] at h3₇
      exact h3₇
  have hG0 : upd G0 0 .pre = G0 := by
    funext u; unfold upd G0; split <;> simp_all
  -- the spawn
  refine WP.bind (WP.spawnC fun k hk => ⟨.pre, by rw [hG0]; exact hi₇, fun G₁ m₈ hg₁ hi₈ =>
    ⟨.start, by simp [proto, cPtr], fun child m₉ hf => ?_⟩⟩)
  obtain ⟨rfl, hc₉, hi₉⟩ := inv_fork ((hi₈ : Inv G₁ m₈).grow (grows_current m₈ 0)) hg₁ rfl hf
  dsimp only
  simp only [StateT.run_bind, pure_bind, bind_assoc, atomicLoadC]
  -- the acquire load of the flag
  refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.run, hi₉, fun G₂ m₁₀ hg₂ hi₁₀ c hcr => ?_⟩)
  have hi₁₀' : Inv G₂ { m₁₀ with current := 0 } := (hi₁₀ : Inv G₂ m₁₀).grow (grows_current _ _)
  have ht₁₀ : ({ m₁₀ with current := 0 } : Mem).current <
      ({ m₁₀ with current := 0 } : Mem).threads.size := by
    show 0 < _; rw [(thr_of hi₁₀'.thr (.inl hg₂)).1]; decide
  refine WP.bind (WP.callMC (fun e he => (load_noErr hi₁₀' ht₁₀ hcr e he).elim) fun v m₁₁ hl => ?_)
  obtain ⟨hc₁₁, hth₁₁, hi₁₁, hv⟩ := step_load hi₁₀' hg₂ rfl hl
  refine ⟨by rw [hth₁₁], ?_⟩
  dsimp only
  have ht₁₁ : m₁₁.current < m₁₁.threads.size := by rw [hc₁₁, hth₁₁]; exact ht₁₀
  have hs₁₁ : m₁₁.threads.size = 2 := by rw [hth₁₁]; exact (thr_of hi₁₀'.thr (.inl hg₂)).1
  -- the read of `data` if the flag is 1: the result is 0 or 42
  refine WP.bind (WP.mono (Q := fun (p : mpRelAcqExit × mpRelAcqLocals) G m _ =>
      ∃ r, p.1 = .br17 r ∧ (r = 0 ∨ r = 42) ∧ m.current = 0 ∧ Inv G m ∧ G 0 = .run) ?_ ?_)
  rotate_left
  · rcases hv with rfl | ⟨rfl, hfin, hle⟩
    · simp only [beq_iff_eq, BitVec.reduceEq, ↓reduceIte, StateT.run_pure]
      exact WP.pure' ⟨0, rfl, .inl rfl, hc₁₁, hi₁₁, hg₂⟩
    · simp only [beq_self_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure]
      refine WP.bind (WP.liftM (fun e he => (read_noErr hi₁₁ hfin (by rw [hc₁₁]; exact hle) ht₁₁ e he).elim)
        fun v' m₁₂ hl' => ?_)
      obtain ⟨rfl, rfl, hi₁₂⟩ := step_read hi₁₁ hfin hl' ht₁₁
      refine ⟨rfl, ?_⟩
      exact WP.pure' ⟨42, rfl, .inr rfl, hc₁₁, hi₁₂, hg₂⟩
  rintro ⟨e, sl⟩ G₃ m₁₂ d₃ ⟨r, rfl, hr, hc₁₂, hi₁₂, hg₃⟩
  dsimp only
  -- the join
  simp only [StateT.run_bind]
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨.joins, hi₁₂.retag0 (.inl hg₃) (.inr rfl), fun G₄ m₁₃ hg₄ hi₁₃ =>
    ⟨fun _ => ⟨by decide, by rw [(thr_of hi₁₃.thr (.inr (.inl hg₄))).1]; decide, rfl, by
      obtain ⟨m', hj⟩ := join_ok hi₁₃ hg₄
      exact Proto.join_valid hj⟩, fun _ =>
      ⟨fun _ => join_ok hi₁₃ hg₄, fun m₁₄ hj => ?_⟩⟩⟩)
  obtain ⟨hja, -, hjb⟩ := join_final hi₁₃ hg₄ hj
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the frees
  obtain ⟨blk₀, hb₀, hl₀, -⟩ := hi₁₃.b0
  obtain ⟨blk₁, hb₁, hl₁, -⟩ := hi₁₃.b1
  obtain ⟨blk₂, hb₂, hl₂, -⟩ := hi₁₃.b2
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (m := m₁₄) (by rw [hjb]; exact hb₀) hl₀ e he).elim)
    fun _ m₁₅ hf₁ => ?_)
  obtain ⟨b, blk, hb, -, rfl⟩ := free_ok hf₁
  cases hb
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 1) (by
      simp only [Array.set!_eq_setIfInBounds]; rw [Array.getElem?_setIfInBounds_ne (by decide), hjb]
      exact hb₁) hl₁ e he).elim) fun _ m₁₆ hf₂ => ?_)
  obtain ⟨b, blk', hb, -, rfl⟩ := free_ok hf₂
  cases hb
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun e he => (free_noErr (b := 2) (by
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem?_setIfInBounds_ne (by decide), Array.getElem?_setIfInBounds_ne (by decide), hjb]
      exact hb₂) hl₂ e he).elim) fun _ m₁₇ hf₃ => ?_)
  obtain ⟨b, blk'', hb, -, rfl⟩ := free_ok hf₃
  cases hb
  refine ⟨rfl, WP.pure' ⟨?_, hja⟩⟩
  rcases hr with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

/-! ## The results -/

/-- **`mpRelAcq` gives 0 or 42 under every schedule** (every oracle `o`, every `fuel`): after
the acquire load reads the writer's release store, the read of `data` sees 42. -/
theorem mpRelAcq_spec {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run dispatch fuel o mpRelAcq (mem0 σ)).run = some (.ok (v, m))) :
    v = .ok 0 ∨ v = .ok 42 := by
  obtain ⟨_, _, hv, -⟩ := proto.run_sound dispatch G0 dispatch_spec
    (fun _ _ _ _ _ hq => hq.2) rfl (main_spec σ) h
  exact hv

/-- **No run of `mpRelAcq` gives an error**: the read of `data` does not race with the write,
under every schedule. -/
theorem mpRelAcq_safe {σ : Placement} {fuel : Nat} {o : Nat → Nat} {e : Error} :
    (Sched.run dispatch fuel o mpRelAcq (mem0 σ)).run ≠ some (.error e) :=
  proto.run_safe dispatch G0 rfl dispatch_spec (fun _ _ _ _ hq => hq.2) rfl (main_spec σ)

end Atomics.MP
