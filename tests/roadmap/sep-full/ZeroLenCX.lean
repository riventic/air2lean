import ZigLean.Mem.Lemmas

/-!
# Zero-length accesses race with nothing: regression (`docs/sep-threads.md`, S2)

A zero-length access touches no byte. Before the model fix, `raceAt` counted a zero-length access
at an offset strictly inside a concurrent entry as overlapping it (and a zero-length entry inside a
later access), and `Mem.freeRaces` counted a zero-length entry at a nonzero offset. So the
zero-length write of an `mremap` shrink to the whole live length (`Os.mremapLive`, empty cut)
raced with a stale entry of another thread across the mapping's end, which made the shrink's
thread rule false for an empty cut. Natively nothing is accessed.

* `zero_write_noRace`: thread 0's zero-length write at offset 1 does not race with thread 1's
  concurrent write of `[0, 2)` (it did before the fix);
* `byte_write_races`: a one-byte write there still races (the check is unchanged otherwise);
* `zero_entry_noRace`: a later one-byte write over a concurrent zero-length entry does not race;
* `zero_entry_free`: the end of the block does not race with a concurrent zero-length entry.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.ZeroLenCX

open Zig

def blk : Block := { bytes := #[.int 0, .int 0], align := 1, kind := .heap, live := true, addr := 4096 }

/-- Thread 0 runs (clock `[1]`); thread 1 (clock `[0, 1]`) is not joined, and its access `e` is
concurrent with thread 0. -/
def mem (e : FootprintEntry) : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[e] }

/-- Thread 1's write of `[0, 2)`. -/
def wide : FootprintEntry := { tid := 1, clock := #[0, 1], block := 0, off := 0, len := 2, kind := .write }

/-- Thread 1's zero-length write at offset 1. -/
def empty : FootprintEntry := { tid := 1, clock := #[0, 1], block := 0, off := 1, len := 0, kind := .write }

theorem zero_write_noRace : NoRace (mem wide) 0 1 0 .write := by
  unfold NoRace; decide +kernel

theorem byte_write_races : ¬ NoRace (mem wide) 0 1 1 .write := by
  unfold NoRace; decide +kernel

theorem zero_entry_noRace : NoRace (mem empty) 0 0 2 .write := by
  unfold NoRace; decide +kernel

theorem zero_entry_free : (mem empty).freeRaces 0 2 = false := by
  decide +kernel

end Zig.ZeroLenCX

#print axioms Zig.ZeroLenCX.zero_write_noRace
#print axioms Zig.ZeroLenCX.byte_write_races
#print axioms Zig.ZeroLenCX.zero_entry_noRace
#print axioms Zig.ZeroLenCX.zero_entry_free
