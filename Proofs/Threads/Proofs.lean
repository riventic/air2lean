import Proofs.Threads.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Mem.Thread
import ZigLean.Simp

/-!
# Proofs about `examples/threads/threads.zig`

`parallelCounter`: 4 threads each add `n` to one shared `u32` counter with `fetchAdd(1, .seq_cst)`
in a loop, discarding the result (a commuting `addSub` RMW, `RmwOp.group`), then the main thread
joins all 4 and reads the counter once. The final value is `4 * n` — this file's minimum-scope
proof requirement (`docs/std-models.md` §Thread model, the task's own fallback clause: "at least
counter = N·k").

Two race arguments, matching `racePair`'s two ways an access pair does not race:
* Every RMW is `atomicWrite (some .addSub)`: two of them never race (`racePair`), independent of
  whether they are concurrent. `CounterInv` below carries this for the whole run.
* The single non-atomic store before any thread spawns, and the single atomic read after every
  thread is joined, both race with nothing because they are not concurrent with anything: the
  store happens-before every spawn (`VClock.le_bump`/`le_trans`, chained through 4 sequential
  spawns), and every RMW happens-before the final read (chained through 4 sequential joins,
  `VClock.le_merge_right`).

**Proved**: `bump_step` (one `fetchAdd` iteration is race-free and keeps the invariant) and
`bump_spec` (one thread's whole `bump`: the loop over its context's `n`, through
`loop_spec_mm`, `ZigLean/Mem/Lemmas.lean`; the counter goes from `v0` to `v0 + n`, and the
thread's reads of its context never race, `CtxInv`). **Not yet proved**: the composition in
`parallelCounter` — the 3 loops over the 4 contexts and handles, `Thread.spawn`/`.join`, and
that every `fetchAdd` happens before the final `atomicLoad`. The diff test checks it against
the compiled Zig (`tests/diff/threads/`).
-/

open Zig Threads

namespace Zig

/-- A pointer's `Enc` round-trips: `decode_encode`'s match on the first byte's `ptrFrag` always
takes the same pointer the whole 8 bytes encode, and the byte-array comparison is then
reflexive. -/
instance : LawfulEnc Ptr where
  size_encode p := by simp [Enc.encode, Enc.size]
  decode_encode p := by simp [Enc.decode, Enc.encode]

/-- Every footprint entry that touches the counter's block (`cb`) is the whole 4-byte value at
offset 0, and either a commuting `addSub` RMW, or a clock dominated by `S` (the fixed baseline:
the clock right after the one plain store, before any thread is spawned). `S` never changes
through the whole proof — a later fact about a bigger clock is reached through `VClock.le_trans`,
not by re-deriving `CounterInv` with a new bound. -/
def CounterInv (cb : BlockId) (S : VClock) (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = cb →
    e.off = 0 ∧ e.len = 4 ∧
      (e.kind = AccessKind.atomicWrite (some RmwGroup.addSub) ∨ VClock.le e.clock S = true)

/-- `NoRace` for the next `addSub` RMW at `(cb, 0, 4)`: `CounterInv`'s two disjuncts match
`racePair`'s two ways two accesses do not race. -/
theorem noRace_addSub {cb : BlockId} {S : VClock} {m : Mem}
    (hinv : CounterInv cb S m)
    (hS : VClock.le S (VClock.bump (m.clocks[m.current]!) m.current) = true) :
    NoRace m cb 0 4 (.atomicWrite (some .addSub)) := by
  unfold NoRace raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  by_cases hbeq : e.block = cb
  · obtain ⟨ho, hl, hk⟩ := hinv e he hbeq
    rcases hk with hk | hk
    · simp only [hbeq, ho, hl, hk, racePair]
      split
      · decide
      · rfl
    · have hle := VClock.le_trans hk hS
      simp [hbeq, VClock.concurrent, hle]
  · have hb : (e.block == cb) = false := by simpa using hbeq
    simp [hb]

/-- `VClock.merge` is a genuine upper bound: `a`'s own component is never lost. -/
theorem VClock.get_merge (a b : VClock) (i : ThreadId) :
    (VClock.merge a b).get i = Nat.max (a.get i) (b.get i) := by
  unfold VClock.merge VClock.get
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases hi : i < Nat.max a.size b.size
  · simp only [hi, ite_true, Option.map_some, Option.getD_some]
  · simp only [hi, ite_false, Option.map_none, Option.getD_none]
    have hmax : Nat.max a.size b.size ≤ i := Nat.not_lt.mp hi
    have ha : a.size ≤ i := Nat.le_trans (Nat.le_max_left _ _) hmax
    have hb : b.size ≤ i := Nat.le_trans (Nat.le_max_right _ _) hmax
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hb]
    rfl

theorem VClock.le_merge_left (a b : VClock) : VClock.le a (VClock.merge a b) = true :=
  VClock.le_iff.mpr fun i => by rw [VClock.get_merge]; exact Nat.le_max_left _ _

theorem VClock.le_merge_right (a b : VClock) : VClock.le b (VClock.merge a b) = true :=
  VClock.le_iff.mpr fun i => by rw [VClock.get_merge]; exact Nat.le_max_right _ _

/-- `atomicRmw`'s effect, given the access and the pointee's current value: the memory after is
the input with the RMW recorded (`Mem.recordAt`) and the new value written (`Mem.write`); the
result is the old value. Mirrors `store_run`'s shape (`ZigLean/Mem/Lemmas.lean`), for the one
primitive that combines a read, a race check and a write into one atomic step. -/
theorem atomicRmw_run {n : Nat} {m : Mem} {op : RmwOp} {signed : Bool} {align : Nat} {p : Ptr}
    {v : BitVec n} {commute : Option RmwGroup} {b : BlockId} {blk : Block} {o : Nat} {old : BitVec n}
    (h : m.access p (intSize n) align = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hold : intOfBytes n (blk.bytes.extract o (o + intSize n)) = pure old)
    (hnr : NoRace m b o (intSize n) (.atomicWrite commute)) :
    (atomicRmw op signed align p v commute).run m =
      pure (old, (m.recordAt b o (intSize n) (.atomicWrite commute)).write b blk o
        (padTo (intSize n) (intBytes (op.apply signed old v)))) := by
  have hrec := recordAccess_run (block := b) (off := o) (len := intSize n)
    (kind := AccessKind.atomicWrite commute) hnr
  have hw : m.accessW p (intSize n) align = pure (b, blk, o) := by simp [Mem.accessW, h, hK]
  simp only [atomicRmw, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    hw, liftM, monadLift, MonadLift.monadLift, StateT.lift, pure, StateT.pure, ExceptT.pure,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind_some, hold]
  rw [show recordAccess b o (intSize n) (AccessKind.atomicWrite commute) m =
    pure ((), m.recordAt b o (intSize n) (AccessKind.atomicWrite commute)) from hrec]
  simp only [ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Option.bind_some, set, StateT.set,
    MonadStateOf.set, pure, Mem.write, Mem.recordAt]

/-- A `u32` written by an `atomicRmw` (`padTo (intSize 32) (intBytes v)` is `Enc.encode v` for
`BitVec 32`, definitionally) reads back as itself, matching `decode_writeBytes32`
(`Proofs/Pointers/Proofs.lean`) for the raw `intBytes`/`intOfBytes` layer that `atomicRmw` uses
directly instead of going through `Enc`/`load`/`store`. -/
theorem decode_writeBytes32' (a : Array Byte) (o : Nat) (v : BitVec 32) (h : o + 4 ≤ a.size) :
    intOfBytes 32 ((writeBytes a o (padTo (intSize 32) (intBytes v))).extract o (o + 4)) =
      pure v := by
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  have hx := extract_writeBytes a o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v, hsz] at hx
  show Enc.decode ((writeBytes a o (Enc.encode v)).extract o (o + 4)) = pure v
  rw [hx]; exact LawfulEnc.decode_encode v

/-- One `bump.loop4` iteration's RMW: `fetchAdd(1, .seq_cst)` on the shared counter, at `cp`, an
`addSub`-commuting RMW discarding its result. Given `CounterInv` and that `S` is dominated by the
running thread's own clock, the RMW succeeds, the counter's value goes from `v` to `v + 1`, and
both facts are preserved for the next step. -/
theorem bump_step {S : VClock} {cb : BlockId} {t : ThreadId} {m : Mem} {blk : Block} {v : BitVec 32}
    {cp : Ptr} (ht : m.current = t) (hbound : t < m.clocks.size)
    (hacc : m.access cp 4 4 = pure (cb, blk, 0)) (hK : blk.kind ≠ .constGlobal)
    (hval : intOfBytes 32 (blk.bytes.extract 0 4) = pure v)
    (hinv : CounterInv cb S m) (hSle : VClock.le S (m.clocks[t]!) = true) :
    ∃ blk', (atomicRmw RmwOp.add false 4 cp (1 : BitVec 32) (some .addSub)).run m =
        pure (v, (m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
          (padTo (intSize 32) (intBytes (v + 1)))) ∧
      ((m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
        (padTo (intSize 32) (intBytes (v + 1)))).access cp 4 4 = pure (cb, blk', 0) ∧
      blk'.kind = blk.kind ∧ intOfBytes 32 (blk'.bytes.extract 0 4) = pure (v + 1) ∧
      ((m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
        (padTo (intSize 32) (intBytes (v + 1)))).current = t ∧
      CounterInv cb S ((m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
        (padTo (intSize 32) (intBytes (v + 1)))) ∧
      VClock.le S (((m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
        (padTo (intSize 32) (intBytes (v + 1)))).clocks[t]!) = true := by
  have hnr : NoRace m cb 0 4 (.atomicWrite (some .addSub)) := by
    apply noRace_addSub hinv
    rw [ht]; exact VClock.le_trans hSle (VClock.le_bump _ _)
  have hrun := atomicRmw_run (n := 32) (m := m) (op := .add) (signed := false) (align := 4)
    (p := cp) (v := (1 : BitVec 32)) (commute := some .addSub) hacc hK hval hnr
  have h0 := (access_eq hacc).2.2.2.1
  have hn := (access_eq hacc).2.2.2.2.1
  refine ⟨{ blk with bytes := writeBytes blk.bytes 0 (padTo (intSize 32) (intBytes (v + 1))) },
    hrun, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have hbsize : (padTo (intSize 32) (intBytes (v + 1))).size = 4 := by
      simp [padTo, intBytes, intSize, intAlign, alignUp]
    have hacc1 : (m.recordAt cb 0 4 (.atomicWrite (some .addSub))).access cp 4 4 =
        pure (cb, blk, 0) := access_recordAt.trans hacc
    have hacc1' : (m.recordAt cb 0 4 (.atomicWrite (some .addSub))).access cp
        (padTo (intSize 32) (intBytes (v + 1))).size 4 = pure (cb, blk, 0) := by
      rw [hbsize]; exact hacc1
    exact access_write_same hacc1' hacc1
  · exact decode_writeBytes32' blk.bytes 0 (v + 1) (by omega)
  · show m.current = t
    exact ht
  · intro e he hbeq
    simp only [Mem.write, Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact hinv e he hbeq
    · exact ⟨rfl, rfl, Or.inl rfl⟩
  · show VClock.le S (m.clocks.set! m.current (VClock.bump (m.clocks[m.current]!) m.current))[t]! = true
    rw [ht]
    rw [Array.getElem!_set!_self m.clocks t _ hbound]
    exact VClock.le_trans hSle (VClock.le_bump _ _)

/-! ## One thread: `bump`

`bump.loop4` reads its context (`n` and the counter pointer) and does one `fetchAdd` per
iteration. `CtxInv`: every write to the context block happened before the thread started, so
the reads never race. `bump_spec`: from `v0`, the counter ends at `v0 + n`. -/

theorem bump_exit (p : Ptr) (s : bumpLocals) (m : Mem) (n : BitVec 32) (m1 : Mem)
    (h1 : Zig.load (BitVec 32) 4 (p.add 8) m = pure (n, m1)) (hlt : ¬ s.i.toNat < n.toNat) :
    ((bump.loop4 p).run s).run m = pure ((.br3, s), m1) := by
  unfold bump.loop4
  simp only [pure, ExceptT.pure, ExceptT.mk] at h1
  have hu : s.i.ult n = false := by simp [BitVec.ult, hlt]
  simp [zig_unfold, h1, hu, Zig.lt]

theorem bump_iter (p cp : Ptr) (s : bumpLocals) (m m1 m2 m3 : Mem) (n v : BitVec 32)
    (h1 : Zig.load (BitVec 32) 4 (p.add 8) m = pure (n, m1)) (hlt : s.i.toNat < n.toNat)
    (h2 : Zig.load Ptr 8 (p.add 0) m1 = pure (cp, m2))
    (h3 : Zig.atomicRmw RmwOp.add false 4 (cp.add 0) (1#32) (RmwOp.group .add false true) m2
      = pure (v, m3)) :
    ((bump.loop4 p).run s).run m = pure ((.rep4, { i := s.i + 1 }), m3) := by
  unfold bump.loop4
  simp only [pure, ExceptT.pure, ExceptT.mk] at h1 h2 h3
  have hno : ¬ (4294967295 ≤ s.i.toNat) := by have := n.isLt; omega
  have hu : s.i.ult n = true := by simp [BitVec.ult, hlt]
  simp [zig_unfold, h1, h2, h3, hu, Zig.lt, hno]


/-- Every write to the context block `xb` happened before `S` (the thread's start): a thread's
reads of its context never race. -/
def CtxInv (xb : BlockId) (S : VClock) (m : Mem) : Prop :=
  ∀ e ∈ m.footprint, e.block = xb → e.kind.isWrite = false ∨ VClock.le e.clock S = true

theorem noRace_ctxRead {xb : BlockId} {S : VClock} {m : Mem} {o n : Nat} (hinv : CtxInv xb S m)
    (hS : VClock.le S (VClock.bump (m.clocks[m.current]!) m.current) = true) :
    NoRace m xb o n .read := by
  unfold NoRace raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  by_cases hbeq : e.block = xb
  · rcases hinv e he hbeq with hk | hk
    · cases hek : e.kind with
      | read => split <;> rfl
      | atomicRead => split <;> rfl
      | write => simp [hek, AccessKind.isWrite] at hk
      | atomicWrite c => simp [hek, AccessKind.isWrite] at hk
    · have hle := VClock.le_trans hk hS
      simp [hbeq, VClock.concurrent, hle]
  · have hb : (e.block == xb) = false := by simpa using hbeq
    simp [hb]

theorem ctxInv_recordAt {xb b : BlockId} {S : VClock} {m : Mem} {o n : Nat} {k : AccessKind}
    (hinv : CtxInv xb S m) (hk : b ≠ xb ∨ k.isWrite = false) :
    CtxInv xb S (m.recordAt b o n k) := by
  intro e he hbeq
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact hinv e he hbeq
  · rcases hk with hk | hk
    · exact absurd hbeq hk
    · exact Or.inl hk

theorem counterInv_recordAt_read {cb b : BlockId} {S : VClock} {m : Mem} {o n : Nat}
    (hinv : CounterInv cb S m) (hb : b ≠ cb) : CounterInv cb S (m.recordAt b o n .read) := by
  intro e he hbeq
  simp only [Mem.recordAt, Array.mem_push] at he
  rcases he with he | rfl
  · exact hinv e he hbeq
  · exact absurd hbeq hb

theorem clocks_recordAt {m : Mem} {t : ThreadId} {b : BlockId} {o n : Nat} {k : AccessKind}
    (ht : m.current = t) (hb : t < m.clocks.size) :
    (m.recordAt b o n k).clocks[t]! = VClock.bump (m.clocks[t]!) t ∧
      (m.recordAt b o n k).clocks.size = m.clocks.size ∧ (m.recordAt b o n k).current = t := by
  subst ht
  refine ⟨Array.getElem!_set!_self m.clocks _ _ hb, by simp [Mem.recordAt], rfl⟩



/-- The state of `bump.loop4` after `i` iterations: `i ≤ n`; the context (at `p`: the counter
pointer `cp` at 0, `n` at 8) reads race-free; the counter holds `v0 + i`. -/
def BumpInv (p cp : Ptr) (n : BitVec 32) (xb cb : BlockId) (xblk : Block) (o8 o0 : Nat)
    (S : VClock) (t : ThreadId) (v0 : BitVec 32) (s : bumpLocals) (m : Mem) : Prop :=
  s.i.toNat ≤ n.toNat ∧ m.current = t ∧ t < m.clocks.size ∧ VClock.le S (m.clocks[t]!) = true ∧
  m.access (p.add 8) 4 4 = pure (xb, xblk, o8) ∧
  Enc.decode (xblk.bytes.extract o8 (o8 + 4)) = (pure n : Result (BitVec 32)) ∧
  m.access (p.add 0) 8 8 = pure (xb, xblk, o0) ∧
  Enc.decode (xblk.bytes.extract o0 (o0 + 8)) = (pure cp : Result Ptr) ∧
  CtxInv xb S m ∧ CounterInv cb S m ∧
  ∃ cblk, m.access (cp.add 0) 4 4 = pure (cb, cblk, 0) ∧ cblk.kind ≠ .constGlobal ∧
    intOfBytes 32 (cblk.bytes.extract 0 4) = pure (v0 + s.i)

theorem bump_loop_step {p cp : Ptr} {n : BitVec 32} {xb cb : BlockId} {xblk : Block} {o8 o0 : Nat}
    {S : VClock} {t : ThreadId} {v0 : BitVec 32} (hxc : xb ≠ cb) (s : bumpLocals) (m : Mem)
    (hinv : BumpInv p cp n xb cb xblk o8 o0 S t v0 s m) :
    ∃ e s' m', ((bump.loop4 p).run s).run m = pure ((e, s'), m') ∧
      (if bump.again4 e then BumpInv p cp n xb cb xblk o8 o0 S t v0 s' m' ∧
          n.toNat - s'.i.toNat < n.toNat - s.i.toNat
        else e = .br3 ∧ s'.i = n ∧ BumpInv p cp n xb cb xblk o8 o0 S t v0 s' m') := by
  obtain ⟨hle, ht, hsz, hS, ha8, hd8, ha0, hd0, hctx, hcnt, cblk, hac, hK, hval⟩ := hinv
  -- The read of `n`.
  have hS' : VClock.le S (VClock.bump (m.clocks[m.current]!) m.current) = true := by
    rw [ht]; exact VClock.le_trans hS (VClock.le_bump _ _)
  have h1 : StateT.run (load (BitVec 32) 4 (p.add 8)) m = pure (n, m.recordAt xb o8 4 .read) :=
    load_run (α := BitVec 32) ha8 hd8 (noRace_ctxRead hctx hS')
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.recordAt xb o8 4 .read := ⟨_, rfl⟩
  rw [← hm1] at h1
  obtain ⟨hc1, hsz1, ht1⟩ := clocks_recordAt (b := xb) (o := o8) (n := 4) (k := .read) ht hsz
  rw [← hm1] at hc1 hsz1 ht1
  by_cases hlt : s.i.toNat < n.toNat
  · -- One more iteration.
    have hS1 : VClock.le S (VClock.bump (m1.clocks[m1.current]!) m1.current) = true := by
      rw [ht1, hc1]; exact VClock.le_trans (VClock.le_trans hS (VClock.le_bump _ _)) (VClock.le_bump _ _)
    have hctx1 : CtxInv xb S m1 := hm1 ▸ ctxInv_recordAt hctx (Or.inr rfl)
    have ha0' : m1.access (p.add 0) 8 8 = pure (xb, xblk, o0) := hm1 ▸ access_recordAt.trans ha0
    have h2 : StateT.run (load Ptr 8 (p.add 0)) m1 = pure (cp, m1.recordAt xb o0 8 .read) :=
      load_run (α := Ptr) (m := m1) ha0' hd0 (noRace_ctxRead hctx1 hS1)
    obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.recordAt xb o0 8 .read := ⟨_, rfl⟩
    rw [← hm2] at h2
    obtain ⟨hc2, hsz2, ht2⟩ := clocks_recordAt (m := m1) (b := xb) (o := o0) (n := 8) (k := .read) ht1
      (by rw [hsz1]; exact hsz)
    rw [← hm2] at hc2 hsz2 ht2
    have hcnt2 : CounterInv cb S m2 := by
      rw [hm2, hm1]; exact counterInv_recordAt_read (counterInv_recordAt_read hcnt hxc) hxc
    have hac2 : m2.access (cp.add 0) 4 4 = pure (cb, cblk, 0) := by
      rw [hm2, hm1]; exact access_recordAt.trans (access_recordAt.trans hac)
    have hS2 : VClock.le S (m2.clocks[t]!) = true := by
      rw [hc2, hc1]
      exact VClock.le_trans (VClock.le_trans hS (VClock.le_bump _ _)) (VClock.le_bump _ _)
    obtain ⟨blk', hrmw, hac3, hk3, hval3, ht3, hcnt3, hS3⟩ :=
      bump_step ht2 (by rw [hsz2, hsz1]; exact hsz) hac2 hK hval hcnt2 hS2
    have hiter := bump_iter p cp s m m1 m2 _ n (v0 + s.i) h1 hlt h2 hrmw
    refine ⟨.rep4, { i := s.i + 1 }, _, hiter, ?_⟩
    simp only [bump.again4, ↓reduceIte]
    have hi1 : (s.i + 1).toNat = s.i.toNat + 1 := by
      rw [BitVec.toNat_add]; have := n.isLt; simp; omega
    refine ⟨⟨show (s.i + 1).toNat ≤ n.toNat by omega, ht3, ?_, hS3, ?_, hd8, ?_, hd0, ?_, hcnt3,
      blk', hac3, ?_, ?_⟩, show n.toNat - (s.i + 1).toNat < n.toNat - s.i.toNat by omega⟩
    · simp [Mem.write, Mem.recordAt, hsz2, hsz1, hsz]
    · rw [hm2, hm1]
      exact access_write_other (access_recordAt.trans (access_recordAt.trans (access_recordAt.trans ha8))) (Ne.symm hxc)
    · rw [hm2]
      exact access_write_other (access_recordAt.trans (access_recordAt.trans ha0')) (Ne.symm hxc)
    · intro e he hbeq
      rw [hm2] at he
      exact ctxInv_recordAt (ctxInv_recordAt hctx1 (Or.inr rfl)) (Or.inl (Ne.symm hxc)) e he hbeq
    · rw [hk3]; exact hK
    · simpa [BitVec.add_assoc] using hval3
  · -- The loop ends: `i = n`.
    have hiN : s.i = n := BitVec.eq_of_toNat_eq (by omega)
    refine ⟨.br3, s, m1, bump_exit p s m n m1 h1 hlt, ?_⟩
    simp only [bump.again4, Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, hiN, hle, ht1, by rw [hsz1]; exact hsz, ?_, ?_, hd8, ?_, hd0, ?_, ?_, cblk, ?_, hK, hval⟩
    · rw [hc1]; exact VClock.le_trans hS (VClock.le_bump _ _)
    · rw [hm1]; exact access_recordAt.trans ha8
    · rw [hm1]; exact access_recordAt.trans ha0
    · rw [hm1]; exact ctxInv_recordAt hctx (Or.inr rfl)
    · rw [hm1]; exact counterInv_recordAt_read hcnt hxc
    · rw [hm1]; exact access_recordAt.trans hac



/-- `bump p` adds `n` (the context's `n`) to the counter, `fetchAdd` by `fetchAdd`: from `v0`
to `v0 + n` (wrapping). Its accesses do not race, and the invariants hold after it. -/
theorem bump_spec {p cp : Ptr} {n : BitVec 32} {xb cb : BlockId} {xblk : Block} {o8 o0 : Nat}
    {S : VClock} {t : ThreadId} {v0 : BitVec 32} (hxc : xb ≠ cb) (m : Mem)
    (hinv : BumpInv p cp n xb cb xblk o8 o0 S t v0 { i := 0 } m) :
    ∃ m', (bump p).run m = pure ((), m') ∧
      BumpInv p cp n xb cb xblk o8 o0 S t v0 { i := n } m' := by
  obtain ⟨e, s', m', hloop, he, hi, hinv'⟩ :=
    loop_spec_mm (bump.loop4 p) bump.again4
      (fun s m => BumpInv p cp n xb cb xblk o8 o0 S t v0 s m)
      (fun s _ => n.toNat - s.i.toNat)
      (fun e s m => e = .br3 ∧ s.i = n ∧ BumpInv p cp n xb cb xblk o8 o0 S t v0 s m)
      (fun s m h => bump_loop_step hxc s m h) { i := 0 } m hinv
  subst he
  refine ⟨m', ?_, ?_⟩
  · unfold bump
    have hloop' : loop (bump.loop4 p) bump.again4 { i := 0#32 } m =
        some (Except.ok ((bumpExit.br3, s'), m')) := hloop
    simp [zig_unfold, hloop']
  · have hs' : s' = { i := n } := by cases s'; simp_all
    exact hs' ▸ hinv'

/-! Two RMWs of one group commute only on the same bytes, and a signed and an unsigned `Min`
are two groups (`racePair`, `RmwOp.group`). -/
example : racePair (.atomicWrite (some .addSub)) (.atomicWrite (some .addSub)) true = none := rfl
example : racePair (.atomicWrite (some .addSub)) (.atomicWrite (some .addSub)) false =
    some .nondet := rfl
example : (RmwOp.group .min true true == RmwOp.group .min false true) = false := rfl

end Zig
