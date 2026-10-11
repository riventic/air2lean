import Proofs.Atomics.MessagePassing

/-!
# `mpRelaxed` over all schedules: a relaxed flag passes no message

`mpRelaxed` is `mpRelAcq` (`Proofs/Atomics/MessagePassing.lean`) with `.monotonic` (relaxed)
atomics. A relaxed load does not join the writer's clock into `main`'s clock. So when `main`
reads 1 and then reads `data`, the writer's write of `data` is concurrent with the read: a data
race (`.illegal`). Every run that gives a result gives 0 (`mpRelaxed_spec`). The proof is in
partial correctness (`Proto.strict` is `false`): a run with the race gives an error.

**Why** (`Inv`): until the join, `main`'s clock has 0 at the writer's component (no acquire),
and the writer's clock at `main`'s component is not above `main`'s own (`view`). Each entry of
the writer has at least 1 at its own component (`wr`). A read of 1 means that the writer has
written `data` (`WrEntry`).
-/

open Zig Zig.Conc Zig.Conc.Proto Atomics Atomics.MP

namespace Atomics.MPR

/-- The writer's write of `data` is in the footprint. -/
def WrEntry (m : Mem) : Prop :=
  ∃ e ∈ m.footprint, e.tid = 1 ∧ e.block = 0 ∧ e.off = 0 ∧ e.len = 4 ∧ e.kind = .write

/-- The flag's atomic location: its newest message has the block's bytes, and each plain write
to the flag happened before it; the first message (0), then the writer's message (1). -/
def FlagLoc (G : ThreadId → Gh) (m : Mem) (l : ALoc) : Prop :=
  l.block = 1 ∧ l.off = 0 ∧ l.len = 4 ∧ ALoc.lastBytes l = curBytes m 1 0 4 ∧
  PlainLe m 1 0 4 l.lastClock ∧
  ((∃ m0, l.msgs = #[m0] ∧ Val m0 0) ∨ (∃ m0 m1, l.msgs = #[m0, m1] ∧ Val m0 0 ∧ Val m1 1 ∧ G 1 = .fin))

/-- No atomic location yet (the flag holds 0), or the flag's. -/
def FlagOk (G : ThreadId → Gh) (m : Mem) : Prop :=
  (m.atomics = #[] ∧ U32At m 1 0) ∨ ∃ l, m.atomics = #[l] ∧ FlagLoc G m l

/-- The invariant (see the module doc). -/
structure Inv (G : ThreadId → Gh) (m : Mem) : Prop where
  thr : ThrOk G m
  ctx : curBytes m 2 0 8 = Enc.encode dPtr ∧ curBytes m 2 8 8 = Enc.encode fPtr
  flag : FlagOk G m
  wrote : (G 1 = .wrote ∨ G 1 = .fin) → WrEntry m
  view : (m.clocks[0]!).get 1 = 0 ∧ (m.threads.size = 2 → (m.clocks[1]!).get 0 ≤ (m.clocks[0]!).get 0)
  wr : ∀ e ∈ m.footprint, e.tid = 1 → 1 ≤ e.clock.get 1 ∧ e.clock.get 0 ≤ (m.clocks[1]!).get 0
  /-- Each plain write to the flag happened before every thread. -/
  pw : ∀ e ∈ m.footprint, plainHit 1 0 4 e = true → ∀ u < m.threads.size,
    VClock.le e.clock (m.clocks[u]!) = true

/-- The protocol, in partial correctness. -/
def proto : Proto Tgt Gh where
  inv := Inv
  init tgt g := (match tgt with
      | .mpWriterRelaxed p => if p = cPtr then some .start else none
      | _ => none) = some g
  fin g := g = .fin
  joins g := g = .joins

/-- `main`'s post: the result is 0. -/
def QM : Except ErrName (BitVec 32) → (ThreadId → Gh) → Mem → Nat → Prop := fun v _ _ _ => v = .ok 0

/-! ## Frame -/

/-- The invariant depends only on the threads, the clocks, the blocks, the atomic locations and
the footprint (it grows). -/
theorem Inv.congr {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (ht : m'.threads = m.threads)
    (hc : m'.clocks = m.clocks) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (hf : ∀ e ∈ m.footprint, e ∈ m'.footprint)
    (hf' : ∀ e ∈ m'.footprint, e.tid = 1 → e ∈ m.footprint)
    (hf1 : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨ plainHit 1 0 4 e = false) : Inv G m' where
  thr := by unfold ThrOk; rw [ht, hc]; exact hi.thr
  ctx := by rw [curBytes_congr hb, curBytes_congr hb]; exact hi.ctx
  flag := by
    rcases hi.flag with ⟨ha', hu⟩ | ⟨l, ha', hlb, hlo, hll, hlast, hpl, hms⟩
    · exact .inl ⟨by rw [ha]; exact ha', by unfold U32At; rw [curBytes_congr hb]; exact hu⟩
    · exact .inr ⟨l, by rw [ha]; exact ha', hlb, hlo, hll, by rw [curBytes_congr hb]; exact hlast,
        hpl.of_fp hf1, hms⟩
  wrote := fun h => by
    obtain ⟨e, he, h1⟩ := hi.wrote h
    exact ⟨e, hf e he, h1⟩
  view := by rw [ht, hc]; exact hi.view
  wr := fun e he ht1 => by rw [hc]; exact hi.wr e (hf' e he ht1) ht1
  pw := fun e he hh u hu => by
    rcases hf1 e he with he | hn
    · rw [hc]; exact hi.pw e he hh u (by rw [← ht]; exact hu)
    · rw [hn] at hh; cases hh

/-- The clock of thread `u` after a record by the current thread. -/
theorem record_clock (m : Mem) (b o len : Nat) (k : AccessKind) (u : Nat)
    (hcs : m.current < m.clocks.size) :
    (m.recordAt b o len k).clocks[u]! =
      if u = m.current then VClock.bump (m.clocks[m.current]!) m.current else m.clocks[u]! := by
  simp only [Mem.recordAt]
  rw [getElem!_set!_ite]
  by_cases h : u = m.current <;> simp [h, hcs]

/-- An access by `main` (thread 0) or the writer (thread 1). -/
theorem Inv.record {G : ThreadId → Gh} {m : Mem} {b o len : Nat} {k : AccessKind} (hi : Inv G m)
    (ht : m.current = 0 ∨ m.current = 1) (hcs : m.current < m.clocks.size)
    (hn1 : b = 1 → k ≠ .write) :
    Inv G (m.recordAt b o len k) := by
  have hle : ∀ (c : VClock) (t i : ThreadId), c.get i ≤ (VClock.bump c t).get i :=
    fun c t i => VClock.le_iff.mp (VClock.le_bump c t) i
  have hfp : ∀ e ∈ (m.recordAt b o len k).footprint, e ∈ m.footprint ∨ e.tid = m.current := by
    intro e he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr rfl
  have hthr : ThrOk G (m.recordAt b o len k) := by
    unfold ThrOk; simp only [Mem.recordAt, Array.size_set!]; exact hi.thr
  have hwr : (G 1 = .wrote ∨ G 1 = .fin) → WrEntry (m.recordAt b o len k) := fun h => by
    obtain ⟨e, he, h1⟩ := hi.wrote h
    exact ⟨e, by simp [Mem.recordAt, he], h1⟩
  have hpf : ∀ e ∈ (m.recordAt b o len k).footprint, e ∈ m.footprint ∨ plainHit 1 0 4 e = false := by
    intro e he
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr (plainHit_false_of hn1)
  have hflag : FlagOk G (m.recordAt b o len k) := by
    rcases hi.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hms⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl.of_fp hpf, hms⟩
  have hpw : ∀ e ∈ (m.recordAt b o len k).footprint, plainHit 1 0 4 e = true →
      ∀ u < (m.recordAt b o len k).threads.size,
        VClock.le e.clock ((m.recordAt b o len k).clocks[u]!) = true := by
    intro e he hh u hu
    rcases hpf e he with he | hn
    · refine VClock.le_trans (hi.pw e he hh u hu) ?_
      rw [record_clock _ _ _ _ _ _ hcs]
      split
      · rename_i h; rw [h]; exact VClock.le_bump _ _
      · exact VClock.le_refl _
    · rw [hn] at hh; cases hh
  rcases ht with ht | ht
  · have h0 : (m.recordAt b o len k).clocks[0]! = VClock.bump (m.clocks[0]!) 0 := by
      rw [record_clock _ _ _ _ _ _ hcs, ht]; simp
    have h1 : (m.recordAt b o len k).clocks[1]! = m.clocks[1]! := by
      rw [record_clock _ _ _ _ _ _ hcs, ht]; simp
    refine {
      thr := hthr, ctx := hi.ctx, flag := hflag, wrote := hwr, view := ⟨?_, fun hs => ?_⟩
      wr := fun e he ht1 => ?_, pw := hpw }
    · rw [h0, VClock.get_bump_ne _ _ _ (by decide)]; exact hi.view.1
    · rw [h0, h1]; exact Nat.le_trans (hi.view.2 hs) (hle _ _ _)
    · rw [h1]
      rcases hfp e he with he | he
      · exact hi.wr e he ht1
      · rw [ht] at he; rw [he] at ht1; cases ht1
  · have h0 : (m.recordAt b o len k).clocks[0]! = m.clocks[0]! := by
      rw [record_clock _ _ _ _ _ _ hcs, ht]; simp
    have h1 : (m.recordAt b o len k).clocks[1]! = VClock.bump (m.clocks[1]!) 1 := by
      rw [record_clock _ _ _ _ _ _ hcs, ht]; simp
    refine {
      thr := hthr, ctx := hi.ctx, flag := hflag, wrote := hwr, view := ⟨?_, fun hs => ?_⟩
      wr := fun e he ht1 => ?_, pw := hpw }
    · rw [h0]; exact hi.view.1
    · rw [h0, h1, VClock.get_bump_ne _ _ _ (by decide)]; exact hi.view.2 hs
    · rw [h1, VClock.get_bump_ne _ _ _ (by decide)]
      simp only [Mem.recordAt, Array.mem_push] at he
      rcases he with he | rfl
      · exact hi.wr e he ht1
      · refine ⟨?_, ?_⟩
        · show 1 ≤ (VClock.bump (m.clocks[m.current]!) m.current).get 1
          rw [ht, VClock.get_bump_self]; exact Nat.le_add_left _ _
        · show (VClock.bump (m.clocks[m.current]!) m.current).get 0 ≤ _
          rw [ht, VClock.get_bump_ne _ _ _ (by decide)]
          exact Nat.le_refl _

/-- A write of `bs` to block 0 keeps the invariant (while the writer is not at `fin`). -/
theorem Inv.write0 {G : ThreadId → Gh} {m : Mem} {blk : Block} {o : Nat} {bs : Array Byte}
    (hi : Inv G m) (hb : m.blocks[0]? = some blk) (hfit : o + bs.size ≤ blk.bytes.size) :
    Inv G (m.write 0 blk o bs) where
  thr := hi.thr
  ctx := by
    rw [curBytes_write_other hb hfit (.inl (by decide)), curBytes_write_other hb hfit (.inl (by decide))]
    exact hi.ctx
  flag := by
    rcases hi.flag with ⟨ha, hu⟩ | ⟨l, ha, hlb, hlo, hll, hlast, hpl, hms⟩
    · exact .inl ⟨ha, by unfold U32At; rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hu⟩
    · exact .inr ⟨l, ha, hlb, hlo, hll, by
        rw [curBytes_write_other hb hfit (.inl (by decide))]; exact hlast, hpl, hms⟩
  wrote := hi.wrote
  view := hi.view
  wr := hi.wr
  pw := hi.pw

/-! ## The writer -/

/-- A read of a pointer of the `MpCtx` (block 2, bytes `o..o+8`). -/
theorem step_ctx {G : ThreadId → Gh} {m m' : Mem} {o : Nat} {q q₀ : Ptr} (hi : Inv G m)
    (ht : m.current = 0 ∨ m.current = 1) (hcs : m.current < m.clocks.size)
    (hq : curBytes m 2 o 8 = Enc.encode q₀)
    (h : ((load Ptr 8 ⟨some 2, (o : Int)⟩).run m).run = some (.ok (q, m'))) :
    q = q₀ ∧ m' = m.recordAt 2 o 8 .read ∧ Inv G m' := by
  obtain ⟨b, blk, o', hacc, -, hdec, rfl⟩ := load_ok h
  obtain ⟨hpb, hblk, -, -, -, -, ho⟩ := access_eq hacc
  cases hpb
  simp only [Int.toNat_natCast] at ho
  rw [ho] at hdec
  have hx : blk.bytes.extract o (o + Enc.size Ptr) = Enc.encode q₀ := by
    have := hq; unfold curBytes at this; rw [hblk] at this; exact this
  rw [hx, decodeLoad_of_decode (LawfulEnc.decode_encode _)] at hdec
  simp only [pure, ExceptT.pure, ExceptT.mk, ExceptT.run, Option.some.injEq, Except.ok.injEq] at hdec
  rw [ho]
  exact ⟨hdec.symm, rfl, hi.record ht hcs (by decide)⟩

/-- The writer's write of 42 to `data`: the writer goes from `start` to `wrote`. -/
theorem step_data {G : ThreadId → Gh} {m m' : Mem} (hi : Inv G m) (hg : G 1 = .start)
    (hc : m.current = 1) (hcs : m.current < m.clocks.size)
    (h : ((store (α := BitVec 32) 4 dPtr (42 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    m'.current = 1 ∧ m'.threads = m.threads ∧ m'.clocks.size = m.clocks.size ∧
      Inv (upd G 1 .wrote) m' := by
  obtain ⟨b, blk, o, hacc, -, rfl⟩ := store_ok h
  obtain ⟨hpb, hblk, -, -, hfit, -, ho⟩ := access_eq hacc
  cases hpb
  simp only [dPtr, Int.toNat_zero] at ho hfit
  subst ho
  have hir := hi.record (b := 0) (o := 0) (len := (Enc.encode (42 : BitVec 32)).size) (k := .write)
    (.inr hc) hcs (by decide)
  have hb : (m.recordAt 0 0 (Enc.encode (42 : BitVec 32)).size .write).blocks[0]? = some blk := hblk
  have hiw := hir.write0 hb (o := 0) (bs := Enc.encode (42 : BitVec 32)) (by omega)
  refine ⟨hc, rfl, by simp [Mem.write, Mem.recordAt], ?_⟩
  exact {
    thr := thr_upd hiw.thr rfl rfl (.inr ⟨rfl, .inl hg, .inr (.inl rfl)⟩)
    ctx := hiw.ctx
    flag := by
      rcases hiw.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, h1 | ⟨-, -, -, -, -, hfin⟩⟩
      · exact .inl h
      · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl, .inl h1⟩
      · rw [hg] at hfin; cases hfin
    wrote := fun _ => ⟨{
        tid := m.current, clock := VClock.bump (m.clocks[m.current]!) m.current
        block := 0, off := 0, len := (Enc.encode (42 : BitVec 32)).size, kind := .write },
      by simp [Mem.write, Mem.recordAt], hc, rfl, rfl, size_encode_u32 _, rfl⟩
    view := hiw.view
    wr := hiw.wr
    pw := hiw.pw }

/-- The writer's message at the flag (1, after the first message): the writer ends. -/
theorem Inv.pushFlag {G : ThreadId → Gh} {M : Mem} {l : ALoc} {m0 msg : Msg} {blk : Block}
    (hi : Inv G M) (hg : G 1 = .wrote) (ha : M.atomics = #[l]) (hms : l.msgs = #[m0])
    (hb : M.blocks[1]? = some blk) (hfit : 0 + msg.bytes.size ≤ blk.bytes.size)
    (hbs : msg.bytes.size = 4) (hv : Val msg 1) (hpl : PlainLe M 1 0 4 msg.clock) :
    Inv (upd G 1 .fin) { M.write 1 blk 0 msg.bytes with atomics := #[{ l with msgs := #[m0, msg] }] } := by
  obtain ⟨l', ha', hlb, hlo, hll, -, -, h1⟩ : ∃ l', M.atomics = #[l'] ∧ FlagLoc G M l' := by
    rcases hi.flag with ⟨ha', -⟩ | h
    · rw [ha] at ha'; simp at ha'
    · exact h
  rw [ha] at ha'
  have hl : l = l' := by simpa using ha'
  subst hl
  have h0 : Val m0 0 := by
    rcases h1 with ⟨m0', hm, hv0⟩ | ⟨-, -, -, -, -, hfin⟩
    · rw [hms] at hm
      have : m0 = m0' := by simpa using hm
      subst this; exact hv0
    · rw [hg] at hfin; cases hfin
  have hcN : ∀ b o len, curBytes { M.write 1 blk 0 msg.bytes with
      atomics := #[{ l with msgs := #[m0, msg] }] } b o len = curBytes (M.write 1 blk 0 msg.bytes) b o len :=
    fun _ _ _ => rfl
  have hlast : ALoc.lastBytes { l with msgs := #[m0, msg] } = curBytes (M.write 1 blk 0 msg.bytes) 1 0 4 := by
    have := curBytes_write_same hb hfit
    rw [hbs] at this
    rw [this]; rfl
  exact {
    thr := thr_upd hi.thr rfl rfl (.inr ⟨rfl, .inr (.inl hg), .inr (.inr rfl)⟩)
    ctx := by
      rw [hcN, hcN, curBytes_write_other hb hfit (.inl (by decide)),
        curBytes_write_other hb hfit (.inl (by decide))]
      exact hi.ctx
    flag := .inr ⟨_, rfl, hlb, hlo, hll, by rw [hcN]; exact hlast,
      fun e he hh => by simpa [ALoc.lastClock] using hpl e he hh,
      .inr ⟨m0, msg, rfl, h0, hv, upd_self _ _ _⟩⟩
    wrote := fun _ => hi.wrote (.inl hg)
    view := hi.view
    wr := hi.wr
    pw := hi.pw }

/-- The flag's location at an atomic op (`locIdx 1 0 4`): location 0, with the flag's messages;
the op changes only `atomics` and `nextMsg`. -/
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

/-- The writer's relaxed store of 1 to the flag: the writer ends. -/
theorem step_flag {G : ThreadId → Gh} {m m' : Mem} {c : Nat} (hi : Inv G m) (hg : G 1 = .wrote)
    (hc : m.current = 1) (hcs : m.current < m.clocks.size)
    (h : ((atomicStoreAt c .relaxed 4 fPtr (1 : BitVec 32)).run m).run = some (.ok ((), m'))) :
    m'.threads = m.threads ∧ Inv (upd G 1 .fin) m' := by
  obtain ⟨b, blk, o, li, m₁, slot, hacc, -, hl, hs, rfl⟩ := atomicStoreAt_ok h
  obtain ⟨hpb, hblk, -, -, hfit, -, ho⟩ := access_eq (accessW_pure hacc).1
  cases hpb
  simp only [fPtr, Int.toNat_zero] at ho hfit
  subst ho
  have h4 : intSize 32 = 4 := by decide
  rw [h4] at hfit
  have hfit' : 0 + (padTo (intSize 32) (intBytes (1 : BitVec 32))).size ≤ blk.bytes.size := by
    have hbs : (padTo (intSize 32) (intBytes (1 : BitVec 32))).size = 4 :=
      LawfulEnc.size_encode (α := BitVec 32) 1
    rw [hbs]; omega
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicWrite) (.inr hc) hcs
    (by decide)
  have hbr : (m.recordAt 1 0 (intSize 32) .atomicWrite).blocks[1]? = some blk := hblk
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicWrite).threads = m.threads := rfl
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicWrite).current = 1 := hc
  generalize m.recordAt 1 0 (intSize 32) .atomicWrite = mr at hir hl hbr hthr hcur
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  obtain ⟨hlb, hlo, hll, hlast, hpl, ⟨m0, hms, h0⟩ | ⟨-, -, -, -, -, hfin⟩⟩ := hfl
  · have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
    obtain ⟨hf1, hs1⟩ := writeSlots_bounds hs
    rw [hl0, hms] at hs1
    have hslot : slot = (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs.size := by
      rw [hl0, hms]; simp at hs1 ⊢; omega
    have hbM : ({ mr with atomics := #[l], nextMsg := k } : Mem).blocks[
        (({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).block]? = some blk := by
      rw [hl0, hlb]; exact hbr
    have hiM : Inv G { mr with atomics := #[l], nextMsg := k } :=
      { hir with flag := .inr ⟨l, rfl, hlb, hlo, hll, hlast, hpl, .inl ⟨m0, hms, h0⟩⟩ }
    have hplM : PlainLe { mr with atomics := #[l], nextMsg := k } 1 0 4
        (storeMsg { mr with atomics := #[l], nextMsg := k } .relaxed (1 : BitVec 32)).clock := by
      intro e he hh
      show VClock.le e.clock (mr.clocks[mr.current]!) = true
      rw [hcur]
      exact hir.pw e he hh 1 (by rw [(thr_of hir.thr (.inr (.inr (.inr (.inl hg))))).1]; decide)
    have hiN := hiM.pushFlag hg rfl hms hbr (msg := storeMsg { mr with atomics := #[l], nextMsg := k }
      .relaxed (1 : BitVec 32)) hfit' (LawfulEnc.size_encode (α := BitVec 32) 1) (intOfBytes_rmw 1) hplM
    unfold storeM
    rw [hslot, insertM_last hbM]
    refine ⟨hthr, hiN.congr rfl rfl ?_ ?_ (fun e he => he) (fun e he _ => he) (fun e he => .inl he)⟩
    · show mr.blocks.set! _ _ = mr.blocks.set! _ _
      rw [hl0, hlb, hlo]
    · show (#[l] : Array ALoc).set! 0 _ = _
      rw [hl0, hms]; rfl
  · rw [hg] at hfin; cases hfin

/-- Every thread was spawned by `main`: the writer joined its own threads (none). -/
theorem joinedAll_kid {G : ThreadId → Gh} {m : Mem} {u : ThreadId} (h : ThrOk G m) (hu : 0 < u) :
    joinedAll u m := by
  intro r hr hs
  obtain ⟨h0, -, h⟩ := h
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
pointer, the relaxed store of 1 (a stop), its end. -/
theorem dispatch_spec (tgt : Tgt) (g : Gh) (hg : proto.init tgt g) (u : ThreadId)
    (G : ThreadId → Gh) (m : Mem) (d : Nat) (hu : 0 < u) (hgu : G u = g) (hi : proto.inv G m) :
    proto.WP u (dispatch tgt) (proto.QKid u) G { m with current := u } d := by
  cases tgt with
  | mpWriterRelaxed p =>
    simp only [proto] at hg
    split at hg
    · rename_i hp
      subst hp
      cases hg
      have hi₀ : Inv G { m with current := u } := (hi : Inv G m).congr rfl rfl rfl rfl
        (fun e he => he) (fun e he _ => he) (fun e he => .inl he)
      obtain ⟨hs2, hu2⟩ := thr_of hi₀.thr (.inr (.inr (.inl hgu)))
      have hu1 : u = 1 := by unfold ThreadId at *; omega
      subst hu1
      have hcs₀ : ({ m with current := 1 } : Mem).current < ({ m with current := 1 } : Mem).clocks.size := by
        show 1 < _; rw [hi₀.thr.2.1, hs2]; decide
      show proto.WP 1 ((fun _ => ()) <$> mpWriterRelaxed cPtr) _ G _ d
      refine WP.map ?_
      unfold mpWriterRelaxed
      refine WP.bind ?_
      rw [StateT.run'_eq]
      refine WP.map ?_
      simp only [StateT.run_bind, StateT.run_pure, pure_bind]
      rw [show cPtr = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl]
      -- the pointer to `data`
      refine WP.bind (WP.liftM (fun _ _ => rfl) fun q m₁ hl => ?_)
      obtain ⟨rfl, rfl, hi₁⟩ := step_ctx hi₀ (.inr rfl) hcs₀ hi₀.ctx.1 hl
      refine ⟨rfl, ?_⟩
      -- the write of 42
      refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₂ hs => ?_)
      obtain ⟨hc₂, hth₂, hcs₂, hi₂⟩ := step_data hi₁ hgu rfl
        (by show 1 < (Array.set! _ _ _).size; simp only [Array.size_set!]; exact hcs₀) hs
      refine ⟨by rw [hth₂], ?_⟩
      -- `&ctx.flag` (`ptrProject`; partial correctness: an error satisfies every post)
      refine WP.bind (WP.callMC_ptrProject_partial rfl ?_)
      dsimp only
      rw [show (⟨some 2, ((0 : Nat) : Int)⟩ : Ptr).add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
      have hcs₂' : m₂.current < m₂.clocks.size := by
        rw [hc₂, hcs₂]; show 1 < (Array.set! _ _ _).size; simp only [Array.size_set!]; exact hcs₀
      -- the pointer to `flag`
      refine WP.bind (WP.liftM (fun _ _ => rfl) fun q m₃ hl => ?_)
      obtain ⟨rfl, rfl, hi₃⟩ := step_ctx hi₂ (.inr hc₂) hcs₂' hi₂.ctx.2 hl
      refine ⟨rfl, ?_⟩
      -- the relaxed store of 1
      simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc, atomicStoreC]
      refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.wrote, hi₃, fun G₁ m₄ hg₁ hi₄ c hcr => ?_⟩)
      have hi₄' : Inv G₁ { m₄ with current := 1 } := (hi₄ : Inv G₁ m₄).congr rfl rfl rfl rfl
        (fun e he => he) (fun e he _ => he) (fun e he => .inl he)
      have hcs₄ : ({ m₄ with current := 1 } : Mem).current < ({ m₄ with current := 1 } : Mem).clocks.size := by
        show 1 < _; rw [hi₄'.thr.2.1, (thr_of hi₄'.thr (.inr (.inr (.inr (.inl hg₁))))).1]; decide
      refine WP.bind (WP.callMC (fun _ _ => rfl) fun _ m₅ hs₅ => ?_)
      obtain ⟨hth₅, hi₅⟩ := step_flag hi₄' hg₁ rfl hcs₄ hs₅
      refine ⟨by rw [hth₅], ?_⟩
      refine WP.pure' (WP.pure' ?_)
      exact ⟨.fin, hi₅, rfl, fun _ => joinedAll_kid hi₅.thr (by decide)⟩
    · cases hg
  | mpWriter p => cases hg
  | sb p => cases hg
  | push p => cases hg
  | ww p => cases hg

/-! ## `main` -/

/-- `main`'s relaxed load of the flag: 0, or 1 when the writer has ended. -/
theorem step_load {G : ThreadId → Gh} {m m' : Mem} {c : Nat} {v : BitVec 32} (hi : Inv G m)
    (hc : m.current = 0) (hcs : m.current < m.clocks.size)
    (h : ((atomicLoadAt (n := 32) c .relaxed 4 fPtr).run m).run = some (.ok (v, m'))) :
    m'.current = 0 ∧ m'.threads = m.threads ∧ m'.clocks.size = m.clocks.size ∧ Inv G m' ∧
      (v = 0 ∨ (v = 1 ∧ G 1 = .fin)) := by
  obtain ⟨b, blk, o, li, m₁, pos, hacc, -, hl, hpos, hv, rfl⟩ := atomicLoadAt_ok h
  obtain ⟨hpb, -, -, -, -, -, ho⟩ := access_eq hacc
  cases hpb
  simp only [fPtr, Int.toNat_zero] at ho
  subst ho
  have hir := hi.record (b := 1) (o := 0) (len := intSize 32) (k := .atomicRead) (.inl hc) hcs
    (by decide)
  have hcur : (m.recordAt 1 0 (intSize 32) .atomicRead).current = 0 := hc
  have hthr : (m.recordAt 1 0 (intSize 32) .atomicRead).threads = m.threads := rfl
  have hcsz : (m.recordAt 1 0 (intSize 32) .atomicRead).clocks.size = m.clocks.size := by
    simp [Mem.recordAt]
  generalize m.recordAt 1 0 (intSize 32) .atomicRead = mr at hir hl hcur hthr hcsz
  obtain ⟨rfl, l, k, hfl, rfl⟩ := loc_flag hir.flag hl
  have hl0 : ({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]! = l := rfl
  have hiM : Inv G { mr with atomics := #[l], nextMsg := k } :=
    { hir with flag := .inr ⟨l, rfl, hfl⟩ }
  have hload : loadM { mr with atomics := #[l], nextMsg := k } 0 .relaxed
      ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!) =
      observeM { mr with atomics := #[l], nextMsg := k } 0
        ((({ mr with atomics := #[l], nextMsg := k } : Mem).atomics[0]!).msgs[pos]!).id := by
    unfold loadM; simp [AtomicOrder.isAcq]
  rw [hload]
  refine ⟨hcur, hthr, hcsz, hiM.congr rfl rfl rfl rfl (fun e he => he) (fun e he _ => he) (fun e he => .inl he), ?_⟩
  have hlt := readOpts_lt hpos
  rw [hl0] at hlt hv
  obtain ⟨-, -, -, -, -, ⟨m0, hms, h0⟩ | ⟨m0, m1, hms, h0, h1, hfin⟩⟩ := hfl
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
      exact ⟨by have := hv.symm.trans h1; simpa using this, hfin⟩

/-- **The race.** After the writer ended (a read of 1), `main`'s read of `data` races with the
writer's write: the write is not below `main`'s clock (no acquire), and `main`'s clock is not
below the write. -/
theorem read_race {G : ThreadId → Gh} {m : Mem} (hi : Inv G m) (hc : m.current = 0)
    (hs : m.threads.size = 2) (hfin : G 1 = .fin) :
    ¬ NoRace m 0 0 (Enc.size (BitVec 32)) .read := by
  obtain ⟨e, he, ht, hb, ho, hl, hk⟩ := hi.wrote (.inr hfin)
  obtain ⟨hw1, hw0⟩ := hi.wr e he ht
  have hsolo : m.solo = false := by
    rcases hi.thr with ⟨-, -, ⟨h1, -⟩ | ⟨-, ⟨r, hr, -, hj⟩, -⟩⟩
    · omega
    · exact solo_false_of hr hj.1
  refine race_of he hb (by rw [ho, hl]; decide) (by rw [ho]; decide) ?_ (err := .illegal)
    (by rw [hk]; rfl) hsolo
  rw [hc]
  simp only [VClock.concurrent, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨VClock.le_eq_false (i := 1) ?_, VClock.le_eq_false (i := 0) ?_⟩
  · rw [VClock.get_bump_ne _ _ _ (by decide), hi.view.1]; omega
  · rw [VClock.get_bump_self]; have := hi.view.2 hs; omega

/-- A change of `main`'s ghost value between `run` and `joins`. -/
theorem Inv.retag0 {G : ThreadId → Gh} {m : Mem} {g : Gh} (hi : Inv G m)
    (hg : G 0 = .run ∨ G 0 = .joins) (hg' : g = .run ∨ g = .joins) : Inv (upd G 0 g) m := by
  have h1 : upd G 0 g 1 = G 1 := upd_ne _ _ (by decide)
  exact {
    thr := thr_upd hi.thr rfl rfl (.inl ⟨rfl, hg, hg'⟩)
    ctx := hi.ctx
    flag := by unfold FlagOk FlagLoc; rw [h1]; exact hi.flag
    wrote := by rw [h1]; exact hi.wrote
    view := hi.view
    wr := hi.wr
    pw := hi.pw }

/-- The start: before its spawn, `main` holds the invariant with the ghost value `pre`. -/
theorem pre_inv {m : Mem} (h : Pre m) (h1 : U32At m 1 0)
    (hctx : curBytes m 2 0 8 = Enc.encode dPtr ∧ curBytes m 2 8 8 = Enc.encode fPtr)
    (hv : (m.clocks[0]!).get 1 = 0) : Inv G0 m where
  thr := (MP.pre_inv h h1 hctx).thr
  ctx := hctx
  flag := .inl ⟨h.at0, h1⟩
  wrote := fun hg => by simp [G0] at hg
  view := ⟨hv, fun hs => by rw [h.thr] at hs; simp at hs⟩
  wr := fun e he ht => by rw [(h.fp e he).2.1] at ht; cases ht
  pw := fun e he _ u hu => by
    have : u = 0 := by rw [h.thr] at hu; simp at hu; omega
    rw [this]; exact (h.fp e he).2.2

/-- `main`'s store before its spawn keeps `main`'s clock at the writer's component. -/
theorem pre_view {α : Type} [Enc α] {m m' : Mem} {a : Nat} {p : Ptr} {v : α} (h : Pre m)
    (hs : ((store a p v).run m).run = some (.ok ((), m'))) :
    (m'.clocks[0]!).get 1 = (m.clocks[0]!).get 1 := by
  obtain ⟨b, blk, o, -, -, rfl⟩ := store_ok hs
  show ((m.recordAt b o (Enc.encode v).size .write).clocks[0]!).get 1 = _
  rw [record_clock _ _ _ _ _ _ (by rw [h.cur, h.clk]; decide), h.cur]
  simp only [↓reduceIte]
  exact VClock.get_bump_ne _ _ _ (by decide)

/-- `main`'s spawn: the writer is thread 1, with a copy of `main`'s bumped clock. -/
theorem inv_fork {G : ThreadId → Gh} {m m' : Mem} {c : ThreadId} (hi : Inv G m) (hg : G 0 = .pre)
    (hc : m.current = 0) (h : (Thread.fork.run m).run = some (.ok (c, m'))) :
    c = 1 ∧ m'.current = 0 ∧ Inv (upd (upd G 1 .start) 0 .run) m' := by
  rw [fork_run] at h
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hs1, hnone, hcs, hthr⟩ := thr_fork hi.thr hg hc
  refine ⟨hs1, hc, ?_⟩
  have hG1 : (upd (upd G 1 .start) 0 .run) 1 = .start := by rw [upd_ne _ _ (by decide), upd_self]
  have hcl : ∀ u < 2, ((m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current)).push
      (VClock.bump (m.clocks[m.current]!) m.current))[u]! = VClock.bump (m.clocks[0]!) 0 := by
    intro u hu
    rw [hc, fork_clocks_one hcs u hu]
  have hc1 : m.clocks[1]! = (default : VClock) := getElem!_neg _ _ (by omega)
  refine {
    thr := hthr
    ctx := hi.ctx
    flag := ?_
    wrote := fun h => by rw [hG1] at h; simp at h
    view := ⟨?_, fun _ => ?_⟩
    wr := fun e he ht => ?_
    pw := fun e he hh u hu => ?_ }
  · rcases hi.flag with h | ⟨l, ha, hlb, hlo, hll, hlast, hpl, h1 | ⟨-, -, -, -, -, hfin⟩⟩
    · exact .inl h
    · exact .inr ⟨l, ha, hlb, hlo, hll, hlast, hpl, .inl h1⟩
    · rw [hnone 1 (by decide)] at hfin; cases hfin
  · show (_ : VClock).get 1 = 0
    rw [hcl 0 (by decide), VClock.get_bump_ne _ _ _ (by decide)]; exact hi.view.1
  · show (_ : VClock).get 0 ≤ (_ : VClock).get 0
    rw [hcl 0 (by decide), hcl 1 (by decide)]
    exact Nat.le_refl _
  · obtain ⟨hw1, hw0⟩ := hi.wr e he ht
    refine ⟨hw1, ?_⟩
    rw [hc1] at hw0
    have : (default : VClock).get 0 = 0 := rfl
    omega
  · rw [hcl u (by simp at hu; omega)]
    exact VClock.le_trans (hi.pw e he hh 0 (by rw [hs1]; decide)) (VClock.le_bump _ _)

theorem main_spec (σ : Placement) (d : Nat) :
    proto.WP 0 mpRelaxed QM G0 { mem0 σ with current := 0 } d := by
  unfold mpRelaxed
  -- the blocks: `data`, `flag`, the `MpCtx`
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s0 m₁ ha₁ => ?_)
  obtain ⟨hq₁, hm₁⟩ := alloc_ok ha₁
  have e0 : s0 = dPtr := by rw [hq₁]; rfl
  subst e0 hm₁
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s2 m₂ ha₂ => ?_)
  obtain ⟨hq₂, hm₂⟩ := alloc_ok ha₂
  have e2 : s2 = fPtr := by rw [hq₂]; rfl
  subst e2 hm₂
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun s5 m₃ ha₃ => ?_)
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
  have hv₃ : (m₃.clocks[0]!).get 1 = 0 := by rw [hm₃]; rfl
  clear hm₃ ha₃ hq₃
  refine WP.bind ?_
  rw [StateT.run'_eq]
  refine WP.map ?_
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [show dPtr = ⟨some 0, ((0 : Nat) : Int)⟩ from rfl, show fPtr = ⟨some 1, ((0 : Nat) : Int)⟩ from rfl]
  -- `data = 0`
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₄ hs₄ => ?_)
  obtain ⟨hp₄, -, -⟩ := pre_store hp₃ hp₃.b0 (by rw [size_encode_u32]; omega) (fun A hA => by omega) hs₄
  have hv₄ := (pre_view hp₃ hs₄).trans hv₃
  refine ⟨by rw [hp₄.thr, hp₃.thr], ?_⟩
  -- `flag = .init(0)`
  refine WP.bind (WP.callRC (fun _ _ => rfl) fun a ha => ?_)
  rw [init_run] at ha
  cases ha
  dsimp only
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₅ hs₅ => ?_)
  obtain ⟨hp₅, h1₅, hk₅⟩ := pre_store hp₄ hp₄.b1 (by rw [enc_av4]; omega) (fun A hA => by omega) hs₅
  have hv₅ := (pre_view hp₄ hs₅).trans hv₄
  refine ⟨by rw [hp₅.thr, hp₄.thr], ?_⟩
  -- the `MpCtx`
  dsimp only
  rw [show cPtr = ⟨some 2, ((0 : Nat) : Int)⟩ from rfl]
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₆ hs₆ => ?_)
  obtain ⟨hp₆, h2₆, hk₆⟩ := pre_store hp₅ hp₅.b2 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₆
  have hv₆ := (pre_view hp₅ hs₆).trans hv₅
  refine ⟨by rw [hp₆.thr, hp₅.thr], ?_⟩
  dsimp only
  -- `&ctx.flag` is formed (in bounds of the 16-byte `MpCtx`, block 2)
  refine WP.bind (WP.callMC_ptrProject (hp₆.b2.ptrProject_run (o := 0) (k := 8) (by decide)) ?_)
  dsimp only
  rw [show (⟨some 2, ((0 : Nat) : Int)⟩ : Ptr).add 8 = ⟨some 2, ((8 : Nat) : Int)⟩ from rfl]
  refine WP.bind (WP.liftM (fun _ _ => rfl) fun _ m₇ hs₇ => ?_)
  obtain ⟨hp₇, h3₇, hk₇⟩ := pre_store hp₆ hp₆.b2 (by rw [size_encode_ptr]; omega) (fun A hA => by omega) hs₇
  have hv₇ := (pre_view hp₆ hs₇).trans hv₆
  refine ⟨by rw [hp₇.thr, hp₆.thr], ?_⟩
  have hi₇ : Inv G0 m₇ := by
    refine pre_inv hp₇ ?_ ⟨?_, ?_⟩ hv₇
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
  obtain ⟨rfl, hc₉, hi₉⟩ := inv_fork ((hi₈ : Inv G₁ m₈).congr rfl rfl rfl rfl (fun e he => he)
    (fun e he _ => he) (fun e he => .inl he) (m' := { m₈ with current := 0 })) hg₁ rfl hf
  dsimp only
  simp only [StateT.run_bind, pure_bind, bind_assoc, atomicLoadC]
  rw [show (⟨some 1, ((0 : Nat) : Int)⟩ : Ptr) = fPtr from rfl]
  -- the relaxed load of the flag
  refine WP.bind (WP.pickC fun k₁ hk₁ => ⟨.run, hi₉, fun G₂ m₁₀ hg₂ hi₁₀ c hcr => ?_⟩)
  have hi₁₀' : Inv G₂ { m₁₀ with current := 0 } := (hi₁₀ : Inv G₂ m₁₀).congr rfl rfl rfl rfl
    (fun e he => he) (fun e he _ => he) (fun e he => .inl he)
  have hs₁₀ := (thr_of hi₁₀'.thr (.inl hg₂)).1
  have hcs₁₀ : ({ m₁₀ with current := 0 } : Mem).current < ({ m₁₀ with current := 0 } : Mem).clocks.size := by
    show 0 < _; rw [hi₁₀'.thr.2.1, hs₁₀]; decide
  refine WP.bind (WP.callMC (fun _ _ => rfl) fun v m₁₁ hl => ?_)
  obtain ⟨hc₁₁, hth₁₁, -, hi₁₁, hv⟩ := step_load hi₁₀' rfl hcs₁₀ hl
  refine ⟨by rw [hth₁₁], ?_⟩
  dsimp only
  have hs₁₁ : m₁₁.threads.size = 2 := by rw [hth₁₁]; exact hs₁₀
  -- the read of `data` if the flag is 1: it races, so only 0 goes on
  refine WP.bind (WP.mono (Q := fun (p : mpRelaxedExit × mpRelaxedLocals) G m _ =>
      p.1 = .br17 0 ∧ m.current = 0 ∧ Inv G m ∧ G 0 = .run) ?_ ?_)
  rotate_left
  · rcases hv with rfl | ⟨rfl, hfin⟩
    · simp only [beq_iff_eq, BitVec.reduceEq, ↓reduceIte, StateT.run_pure]
      exact WP.pure' ⟨rfl, hc₁₁, hi₁₁, hg₂⟩
    · simp only [beq_self_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure]
      refine WP.bind (WP.liftM (fun _ _ => rfl) fun v' m₁₂ hl' => ?_)
      obtain ⟨b, blk, o, hacc, hnr, -, -⟩ := load_ok hl'
      obtain ⟨hpb, -, -, -, -, -, ho⟩ := access_eq hacc
      cases hpb
      simp only [Int.toNat_natCast] at ho
      subst ho
      exact (read_race hi₁₁ hc₁₁ hs₁₁ hfin hnr).elim
  rintro ⟨e, sl⟩ G₃ m₁₂ d₃ ⟨rfl, hc₁₂, hi₁₂, hg₃⟩
  dsimp only
  -- the join
  simp only [StateT.run_bind]
  refine WP.bind (WP.joinC fun k₂ hk₂ => ⟨.joins, hi₁₂.retag0 (.inl hg₃) (.inr rfl), fun G₄ m₁₃ hg₄ hi₁₃ =>
    ⟨fun h => absurd h (by decide), fun _ => ⟨fun h => absurd h (by decide), fun m₁₄ hj => ?_⟩⟩⟩)
  simp only [StateT.run_pure]
  refine WP.pure' ?_
  -- the frees
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₁₅ hf₁ => ?_)
  obtain ⟨b, blk, hb, -, rfl⟩ := free_ok hf₁
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₁₆ hf₂ => ?_)
  obtain ⟨b, blk', hb, -, rfl⟩ := free_ok hf₂
  refine ⟨rfl, ?_⟩
  refine WP.bind (WP.liftMem (fun _ _ => rfl) fun _ m₁₇ hf₃ => ?_)
  obtain ⟨b, blk'', hb, -, rfl⟩ := free_ok hf₃
  exact ⟨rfl, WP.pure' rfl⟩

/-! ## The result -/

/-- **Every result of `mpRelaxed` is 0** (every oracle `o`, every `fuel`): a run where `main`
reads 1 at the relaxed flag races at `data` and gives no result. -/
theorem mpRelaxed_spec (env : Env) (henv : env.spawn = .available) {σ : Placement} {fuel : Nat} {o : Nat → Nat} {v : Except ErrName (BitVec 32)} {m : Mem}
    (h : (Sched.run env dispatch fuel o mpRelaxed (mem0 σ)).run = some (.ok (v, m))) : v = .ok 0 := by
  obtain ⟨_, _, hv⟩ := proto.run_sound env (Proto.of_available henv) dispatch G0 dispatch_spec
    (fun h => absurd h (by decide)) rfl (main_spec σ) h
  exact hv

end Atomics.MPR
