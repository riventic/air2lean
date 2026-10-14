import ZigLean.Os.Mmap
import ZigLean.Mem.Lemmas
import ZigLean.Mem.Thread

/-!
# Ended bytes lose their atomic locations: regression (`docs/sep-threads.md`, S1)

The counterexample to the old model (coordinator ruling (b), S1): a step that ended the bytes of
an atomic location kept the location and its messages, so after the bytes came alive again (a
shrink, then a growth in place, which maps fresh zero pages) an atomic read could read a message
from before they ended.

Mapping block 0 has 2 bytes; offset 1 is an atomic location with two messages: `5` (from before
every thread) and then `0`, written by thread 1. Thread 0 shrinks the mapping to 1 byte and grows
it back to 2 (`Mem.mremapShrunk`, `Mem.mremapGrown`): the grown byte is `0`. Thread 2 has not
synchronized with thread 1, so the message `0` did not happen before it.

* **Before the fix** (`stale`: the grown memory with the old location kept): thread 2's relaxed
  atomic load of offset 1 can read `5` (option 1, `stale_reads_old`), a value that the fresh page
  never held.
* **After the fix** the shrink retires the location (`Mem.retire`): the load starts a new location
  with the byte's value, has one option (`fresh_one_option`) and reads `0` (`fresh_reads_zero`).
  The same `Mem.retire` runs in `Os.munmap` and in a byte remap that shrinks
  (`Mem.afterByteRemap`).

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.RetireCX

open Zig

/-- The mapping: 2 zero bytes, live from offset 0. -/
def blk : Block := { bytes := #[.int 0, .int 0], align := 1, kind := .mapped 0, live := true, addr := 4096 }

/-- The atomic location at offset 1: `5` (from before every thread), then `0` by thread 1. -/
def loc : ALoc :=
  { block := 0, off := 1, len := 1,
    msgs := #[{ id := 0, bytes := #[.int 5], clock := #[], relClock := #[] },
              { id := 1, bytes := #[.int 0], clock := #[0, 1], relClock := #[], writer := some 1 }] }

/-- Thread 0 runs; threads 1 and 2 are not joined and know nothing of each other. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1], #[0, 0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false },
      { spawner := 0, joined := false }],
    atomics := #[loc], nextMsg := 2 }

/-- Thread 0's shrink to 1 byte (its recorded write of the cut byte, then the shrink). -/
def m₁ : Mem := (m.recordAt 0 1 1 .write).mremapShrunk 0 blk 0 1

/-- The mapping after the shrink. -/
def blk₁ : Block := { blk with bytes := #[.int 0] }

/-- The growth in place back to 2 bytes; then thread 2 runs. -/
def m₂ : Mem := { m₁.mremapGrown 1 0 blk₁ 0 2 with current := 2 }

/-- The old model: the same memory, with the location of the ended byte kept. -/
def stale : Mem := { m₂ with atomics := m.atomics, seen := m.seen }

/-- Offset 1 of block 0. -/
def p : Ptr := ⟨some 0, 1⟩

/-- **Before the fix**: thread 2's atomic load of the revived byte can read `5`. -/
theorem stale_reads_old :
    (match ((atomicLoadAt (n := 8) 1 .relaxed 1 p).run stale).run with
      | some (.ok (v, _)) => v == 5
      | _ => false) = true := by
  decide +kernel

/-- **After the fix**: the revived byte has no location; the load has one option. -/
theorem fresh_one_option : m₂.atomics = #[] ∧ loadCount 8 .relaxed 1 p m₂ = 1 := by
  decide +kernel

/-- **After the fix**: the load reads the byte's value. -/
theorem fresh_reads_zero :
    (match ((atomicLoadAt (n := 8) 0 .relaxed 1 p).run m₂).run with
      | some (.ok (v, _)) => v == 0
      | _ => false) = true := by
  decide +kernel

end Zig.RetireCX

#print axioms Zig.RetireCX.stale_reads_old
#print axioms Zig.RetireCX.fresh_one_option
#print axioms Zig.RetireCX.fresh_reads_zero
