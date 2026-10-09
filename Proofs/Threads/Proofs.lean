import Proofs.Threads.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Mem.Thread
import ZigLean.Simp
import ZigLean.Witness

/-!
# Proofs about `examples/threads/threads.zig`

The threads take turns at sync ops (`ZigLean/Conc/Sched.lean`), and `bump`, `parallelCounter`
and `xchgRace` are concurrent functions (`Zig.ConcM`). A spec of such a function holds for every
schedule: `Proofs/Threads/Counter.lean` proves `parallelCounter n = 4 * n` over all schedules
with the program logic of `ZigLean/Conc/Logic.lean`. This file has facts of one atomic step:

- Two atomic accesses never race (`racePair_atomic`), so an atomic access races only with a
  plain one (`noRace_of_atomic`).
- RC11: option 0 of a read is the newest message (`readOpts_zero`); a `u32` written by an atomic
  op reads back (`decode_writeBytes32'`).
- An atomic op on an enum is the op on its tag (`Phase.ofBits_toBits`, `Phase.valid_toBits`).

The diff test checks the concurrent functions against the compiled Zig over the schedules
(`tests/diff/Diff.lean`'s `searchSchedules`).
-/

open Zig Threads

namespace Zig

/-- A data race: a plain write against any access. -/
example : racePair .write .atomicRead = some .illegal := rfl
example : racePair .read .atomicWrite = some .illegal := rfl
example : racePair .read .read = none := rfl

/-- An atomic access at `(b, o, n)` does not race if every earlier access to block `b` is
atomic. -/
theorem noRace_of_atomic {m : Mem} {b : BlockId} {o n : Nat} {k : AccessKind}
    (hk : k.isAtomic = true) (hall : ∀ e ∈ m.footprint, e.block = b → e.kind.isAtomic = true) :
    NoRace m b o n k := by
  apply noRace_of_raceAt
  unfold raceAt
  rw [Array.findSome?_eq_none_iff]
  intro e he
  by_cases hbeq : e.block = b
  · have := racePair_atomic (hall e he hbeq) hk
    simp [this]
  · have hb : (e.block == b) = false := by simpa using hbeq
    simp [hb]

/-- Option 0 of a read is the newest message: the first schedule of a search is the sequentially
consistent one. -/
theorem readOpts_zero (m : Mem) (li : Nat) (h : floorPos m li < (m.atomics[li]!).msgs.size) :
    (readOpts m li false)[0]? = some ((m.atomics[li]!).msgs.size - 1) := by
  have hf : ∀ (a : Array Nat), a.filter (fun _ => true) = a := fun a => by
    rw [Array.filter_eq_self]; intros; rfl
  simp only [readOpts, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or, hf]
  rw [Array.getElem?_map, Array.getElem?_range]
  simp; omega

/-- An atomic op on an enum is the integer op on its tag (`Zig.Packed`): every `Phase` value
round-trips through its bits, and its bits are valid, so `cmpxchgAs` on `Phase` compares and
writes exactly the tags. -/
theorem Phase.ofBits_toBits (x : Phase) : (Packed.ofBits (Packed.toBits x) : Phase) = x := by
  cases x <;> rfl

theorem Phase.valid_toBits (x : Phase) : Packed.valid (α := Phase) (Packed.toBits x) = true := by
  cases x <;> rfl

/-- A `u32` written by an atomic op (`padTo (intSize 32) (intBytes v)` is `Enc.encode v` for
`BitVec 32`, definitionally) reads back as itself. -/
theorem decode_writeBytes32' (a : Array Byte) (o : Nat) (v : BitVec 32) (h : o + 4 ≤ a.size) :
    intOfBytes 32 ((writeBytes a o (padTo (intSize 32) (intBytes v))).extract o (o + 4)) =
      pure v := by
  have hsz : Enc.size (BitVec 32) = 4 := rfl
  have hx := extract_writeBytes a o (Enc.encode v) (by rw [LawfulEnc.size_encode v]; omega)
  rw [LawfulEnc.size_encode v, hsz] at hx
  show Enc.decode ((writeBytes a o (Enc.encode v)).extract o (o + 4)) = pure v
  rw [hx]; exact LawfulEnc.decode_encode v

nonvacuity_witness decode_writeBytes32' := ⟨Array.replicate 4 .undef, 0, 0, by decide, trivial⟩

end Zig
