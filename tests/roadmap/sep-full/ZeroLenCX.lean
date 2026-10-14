import ZigLean.Conc.Clock
import ZigLean.Mem.Noalias

/-!
# Zero-length accesses touch nothing: regression (`docs/sep-threads.md`, S2)

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

The same holds at every other place where the model asks whether an access meets bytes (one
mechanism: a zero-length access touches nothing anywhere):

* `zero_write_not_plainSince` / `byte_write_plainSince`: a concurrent zero-length plain write
  inside an atomic location is no write event since the location's newest message (`plainSince`:
  the next atomic op makes no message of it; it did before the fix); a one-byte write is one;
* `zero_entry_over` / `byte_entry_not_over`: a concurrent zero-length access inside a location
  does not keep the location from being retired (`ALoc.over`; it did before the fix); a one-byte
  access does;
* `zero_noalias_ok` / `byte_noalias_conflicts`: a zero-length access is no `noalias` violation
  (`NaEntry.conflicts`); a one-byte one is;
* `empty_touches_nothing`, `zero_entry_owned`: a zero-length entry touches no heap
  (`FootprintEntry.Touches`; before, it touched its first byte), so thread 0 owns every heap
  although thread 1's zero-length write is concurrent with it (`Mem.OwnsC`).

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

/-- Thread 1's one-byte write at offset 1. -/
def byte : FootprintEntry := { empty with len := 1 }

theorem zero_write_noRace : NoRace (mem wide) 0 1 0 .write := by
  unfold NoRace; decide +kernel

theorem byte_write_races : ¬ NoRace (mem wide) 0 1 1 .write := by
  unfold NoRace; decide +kernel

theorem zero_entry_noRace : NoRace (mem empty) 0 0 2 .write := by
  unfold NoRace; decide +kernel

theorem zero_entry_free : (mem empty).freeRaces 0 2 = false := by
  decide +kernel

/-! ## Atomic locations: message creation and retirement -/

/-- The atomic location over `[0, 2)` of block 0, whose newest message has thread 0's clock. -/
def loc : ALoc :=
  { block := 0, off := 0, len := 2, msgs := #[{ id := 0, bytes := #[.int 0, .int 0], clock := #[1], relClock := #[] }] }

theorem zero_write_not_plainSince : plainSince (mem empty) 0 0 2 loc.lastClock = false := by
  decide +kernel

theorem byte_write_plainSince : plainSince (mem byte) 0 0 2 loc.lastClock = true := by
  decide +kernel

theorem zero_entry_over : loc.over (mem empty) #[1] = true := by
  decide +kernel

theorem byte_entry_not_over : loc.over (mem byte) #[1] = false := by
  decide +kernel

/-! ## `noalias` -/

/-- A read of `[0, 2)` based on parameter 0. -/
def naRead : NaEntry := { block := 0, off := 0, len := 2, write := false, root := some 0 }

theorem zero_noalias_ok :
    NaEntry.conflicts { block := 0, off := 1, len := 0, write := true, root := none } naRead = false := by
  decide +kernel

theorem byte_noalias_conflicts :
    NaEntry.conflicts { block := 0, off := 1, len := 1, write := true, root := none } naRead = true := by
  decide +kernel

/-! ## Ownership -/

theorem empty_touches_nothing (h : Heap) : ¬ empty.Touches h := by
  rintro ⟨x, h1, h2, -⟩
  simp only [empty] at h1 h2
  omega

/-- Thread 0 owns every heap, although thread 1's zero-length write is concurrent with it. -/
theorem zero_entry_owned (h : Heap) : (mem empty).Owns 0 h := by
  intro e he ht
  simp only [mem, List.mem_toArray, List.mem_singleton] at he
  subst he
  rcases ht with ht | ht
  · exact absurd ht (empty_touches_nothing h)
  · exact absurd ht (by decide)

end Zig.ZeroLenCX

#print axioms Zig.ZeroLenCX.zero_write_noRace
#print axioms Zig.ZeroLenCX.byte_write_races
#print axioms Zig.ZeroLenCX.zero_entry_noRace
#print axioms Zig.ZeroLenCX.zero_entry_free
#print axioms Zig.ZeroLenCX.zero_write_not_plainSince
#print axioms Zig.ZeroLenCX.byte_write_plainSince
#print axioms Zig.ZeroLenCX.zero_entry_over
#print axioms Zig.ZeroLenCX.byte_entry_not_over
#print axioms Zig.ZeroLenCX.zero_noalias_ok
#print axioms Zig.ZeroLenCX.byte_noalias_conflicts
#print axioms Zig.ZeroLenCX.empty_touches_nothing
#print axioms Zig.ZeroLenCX.zero_entry_owned
