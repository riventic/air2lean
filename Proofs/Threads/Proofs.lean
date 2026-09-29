import Proofs.Threads.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Mem.Thread
import ZigLean.Simp

/-!
# Proofs about `examples/threads/threads.zig`

The threads take turns at sync ops (`ZigLean/Conc/Sched.lean`), and `bump`, `parallelCounter`
and `xchgRace` are concurrent functions (`Zig.ConcM`). A spec of such a function holds for every
schedule; the program logic for it is milestone T4 (`PLAN.md`). This file has the facts of one
atomic step, which T4 builds on:

- Two atomic accesses never race (`racePair_atomic`), so an atomic access races only with a
  plain one (`noRace_of_atomic`).
- One `atomicRmw` step: it gives the old value and writes the new one (`atomicRmw_run`), and a
  `u32` written that way reads back (`decode_writeBytes32'`).
- An atomic op on an enum is the op on its tag (`Phase.ofBits_toBits`, `Phase.valid_toBits`).

The diff test checks the concurrent functions against the compiled Zig over the schedules
(`tests/diff/Diff.lean`'s `searchSchedules`).
-/

open Zig Threads

namespace Zig

/-- Two atomic accesses never race: the scheduler orders them. -/
theorem racePair_atomic {a b : AccessKind} (ha : a.isAtomic = true) (hb : b.isAtomic = true) :
    racePair a b = none := by
  simp [racePair, ha, hb]

/-- A data race: a plain write against any access. -/
example : racePair .write .atomicRead = some .illegal := rfl
example : racePair .read .atomicWrite = some .illegal := rfl
example : racePair .read .read = none := rfl

/-- An atomic access at `(b, o, n)` does not race if every earlier access to block `b` is
atomic. -/
theorem noRace_of_atomic {m : Mem} {b : BlockId} {o n : Nat} {k : AccessKind}
    (hk : k.isAtomic = true) (hall : ∀ e ∈ m.footprint, e.block = b → e.kind.isAtomic = true) :
    NoRace m b o n k := by
  unfold NoRace raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  by_cases hbeq : e.block = b
  · have := racePair_atomic (hall e he hbeq) hk
    simp [this]
  · have hb : (e.block == b) = false := by simpa using hbeq
    simp [hb]

/-- `atomicRmw`'s effect, given the access and the pointee's current value: the result is the
old value, and the block holds the new value after it. The other changes (the footprint, the
thread's clock and the location's release clock) are the race state. -/
theorem atomicRmw_run {n : Nat} {m : Mem} {op : RmwOp} {signed : Bool} {align : Nat} {p : Ptr}
    {v : BitVec n} {b : BlockId} {blk : Block} {o : Nat} {old : BitVec n}
    (h : m.access p (intSize n) align = pure (b, blk, o)) (hK : blk.kind ≠ .constGlobal)
    (hold : intOfBytes n (blk.bytes.extract o (o + intSize n)) = pure old)
    (hnr : NoRace m b o (intSize n) .atomicWrite) :
    ∃ m', (atomicRmw op signed align p v).run m = pure (old, m') ∧
      m'.blocks = m.blocks.set! b
        { blk with bytes := writeBytes blk.bytes o (padTo (intSize n) (intBytes (op.apply signed old v))) } ∧
      m'.current = m.current := by
  have hrec := recordAccess_run (block := b) (off := o) (len := intSize n)
    (kind := AccessKind.atomicWrite) hnr
  have hw : m.accessW p (intSize n) align = pure (b, blk, o) := by simp [Mem.accessW, h, hK]
  simp only [atomicRmw, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    hw, liftM, monadLift, MonadLift.monadLift, StateT.lift, pure, StateT.pure, ExceptT.pure,
    ExceptT.mk, ExceptT.bind, ExceptT.bindCont, Option.bind_some, hold]
  rw [show recordAccess b o (intSize n) AccessKind.atomicWrite m =
    pure ((), m.recordAt b o (intSize n) AccessKind.atomicWrite) from hrec]
  simp only [ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Option.bind_some, set, StateT.set,
    MonadStateOf.set, pure, Mem.recordAt, acquireAt, releaseAt, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  refine ⟨_, rfl, ?_, ?_⟩ <;> split <;> rfl

/-- An atomic op on an enum is the integer op on its tag (`Zig.Packed`): every `Phase` value
round-trips through its bits, and its bits are valid, so `cmpxchgAs` on `Phase` compares and
writes exactly the tags. -/
theorem Phase.ofBits_toBits (x : Phase) : (Packed.ofBits (Packed.toBits x) : Phase) = x := by
  cases x <;> rfl

theorem Phase.valid_toBits (x : Phase) : Packed.valid (α := Phase) (Packed.toBits x) = true := by
  cases x <;> rfl

/-- A `u32` written by an `atomicRmw` (`padTo (intSize 32) (intBytes v)` is `Enc.encode v` for
`BitVec 32`, definitionally) reads back as itself. -/
theorem decode_writeBytes32' (a : Array Byte) (o : Nat) (v : BitVec 32) (h : o + 4 ≤ a.size) :
    intOfBytes 32 ((writeBytes a o (padTo (intSize 32) (intBytes v))).extract o (o + 4)) =
      pure v := by
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  have hx := extract_writeBytes a o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v, hsz] at hx
  show Enc.decode ((writeBytes a o (Enc.encode v)).extract o (o + 4)) = pure v
  rw [hx]; exact LawfulEnc.decode_encode v

end Zig
