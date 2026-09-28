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

**Scope cut**: `bump_step` proves one `fetchAdd` iteration race-free and invariant-preserving —
the mechanism the "counter = 4·n" result needs. The two steps that compose it into that result
are not done: the induction over `bump.loop4`'s variable iteration count `n`, and the 4-thread
`spawn`/`join` composition. Both need `Zig.loop`'s `partial_fixpoint` unfold (`loop.eq_1`) driven
over `Zig.MM`'s two-layer `StateT` (locals, then `Mem`) — no existing proof in this repo reasons
about a variable-bound loop over locals, and building that induction is a bigger proof-engineering
task than the rest of M22's scope (`docs/std-models.md` §Thread model, `PLAN.md`'s M22 entry). The
model itself is not affected: `bump`/`parallelCounter` run and race-check like any other example,
checked by the diff test against the real compiled/executed Zig code (`tests/diff/threads/`).
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
    (h : m.access p (intSize n) align = pure (b, blk, o))
    (hold : intOfBytes n (blk.bytes.extract o (o + intSize n)) = pure old)
    (hnr : NoRace m b o (intSize n) (.atomicWrite commute)) :
    (atomicRmw op signed align p v commute).run m =
      pure (old, (m.recordAt b o (intSize n) (.atomicWrite commute)).write b blk o
        (padTo (intSize n) (intBytes (op.apply signed old v)))) := by
  have hrec := recordAccess_run (block := b) (off := o) (len := intSize n)
    (kind := AccessKind.atomicWrite commute) hnr
  simp only [atomicRmw, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    h, liftM, monadLift, MonadLift.monadLift, StateT.lift, pure, StateT.pure, ExceptT.pure,
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
    (hacc : m.access cp 4 4 = pure (cb, blk, 0))
    (hval : intOfBytes 32 (blk.bytes.extract 0 4) = pure v)
    (hinv : CounterInv cb S m) (hSle : VClock.le S (m.clocks[t]!) = true) :
    ∃ blk', (atomicRmw RmwOp.add false 4 cp (1 : BitVec 32) (some .addSub)).run m =
        pure (v, (m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
          (padTo (intSize 32) (intBytes (v + 1)))) ∧
      ((m.recordAt cb 0 4 (.atomicWrite (some .addSub))).write cb blk 0
        (padTo (intSize 32) (intBytes (v + 1)))).access cp 4 4 = pure (cb, blk', 0) ∧
      intOfBytes 32 (blk'.bytes.extract 0 4) = pure (v + 1) ∧
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
    (p := cp) (v := (1 : BitVec 32)) (commute := some .addSub) hacc hval hnr
  have h0 := (access_eq hacc).2.2.2.1
  have hn := (access_eq hacc).2.2.2.2.1
  refine ⟨{ blk with bytes := writeBytes blk.bytes 0 (padTo (intSize 32) (intBytes (v + 1))) },
    hrun, ?_, ?_, ?_, ?_, ?_⟩
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

/-! Two RMWs of one group commute only on the same bytes, and a signed and an unsigned `Min`
are two groups (`racePair`, `RmwOp.group`). -/
example : racePair (.atomicWrite (some .addSub)) (.atomicWrite (some .addSub)) true = none := rfl
example : racePair (.atomicWrite (some .addSub)) (.atomicWrite (some .addSub)) false =
    some .nondet := rfl
example : (RmwOp.group .min true true == RmwOp.group .min false true) = false := rfl

end Zig
