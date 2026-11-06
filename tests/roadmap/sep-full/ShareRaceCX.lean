import ZigLean.Conc.Clock

/-!
# Read shares and the race clocks: regressions (`ZigLean/Conc/Clock.lean` §Read ownership)

The memory `twoReaders`: threads `0` and `1` run with concurrent clocks, and thread `0` has read
byte `0` of block `0`. Both may hold a read share of that byte.

1. `reader_not_owns`: thread `1` does not own the byte (`Mem.Owns`): thread `0`'s read is not
   before its clock. So the ownership that F2 asks of every part (`FOwned.owns` over
   `Res.owned`, shares included) cannot hold for two concurrent readers, and a thread load rule on
   a share could not re-establish it for the other reader. For the same reason a whole share
   gathered by thread `1` after thread `0` read cannot become an exclusive cell without a
   happens-before edge from thread `0`'s read: the conversion needs `Mem.Owns`, which a protocol
   provides (`Mem.OwnsRC.owns`).
2. `readers_ownsR`: both threads may read the byte (`Mem.OwnsR`): no recorded write to it.
3. `reader_noRace`: so thread `1`'s read of the byte does not race (`Mem.OwnsR.noRace`), as
   natively two reads never race.
4. `writer_races`: but thread `1`'s write to the byte races with thread `0`'s read: a share
   gives no write.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.ShareRaceCX

open Zig

/-- Thread `0`'s read of byte `0` of block `0`. -/
def readEntry : FootprintEntry :=
  { tid := 0, clock := #[1, 0], block := 0, off := 0, len := 1, kind := .read }

/-- Two running threads with concurrent clocks; thread `0` has read byte `0` of block `0`;
thread `1` runs. -/
def twoReaders : Mem :=
  { blocks := #[{ bytes := #[], align := 1, kind := .heap, live := true, addr := 0 }], current := 1, clocks := #[#[1, 0], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[readEntry] }

/-- The heap of the byte. -/
def byte (c : Cell) : Heap := fun l => if l = (0, 0) then some c else none

theorem readEntry_touches (c : Cell) : readEntry.Touches (byte c) :=
  ⟨0, Nat.le_refl _, by decide, by simp [byte, readEntry]⟩

/-- **The second reader does not own the byte.** -/
theorem reader_not_owns (c : Cell) : ¬ (twoReaders).Owns 1 (byte c) := by
  intro ho
  have := ho readEntry (by simp [twoReaders]) (.inl (readEntry_touches c))
  revert this; decide +kernel

/-- **Both readers may read the byte.** -/
theorem readers_ownsR (c : Cell) :
    (twoReaders).OwnsR 0 (byte c) ∧ (twoReaders).OwnsR 1 (byte c) := by
  refine ⟨?_, ?_⟩ <;>
  · intro e he hw _
    simp only [twoReaders, Array.mem_singleton] at he
    subst he; revert hw; decide

/-- **The second reader's read does not race.** -/
theorem reader_noRace (c : Cell) : NoRace (twoReaders) 0 0 1 .read :=
  Mem.OwnsR.noRace (h := byte c) (readers_ownsR c).2 rfl fun x h1 h2 => by
    have : x = 0 := by omega
    subst this; simp [byte]

/-- **A write to the shared byte races.** -/
theorem writer_races : ¬ NoRace (twoReaders) 0 0 1 .write := by
  unfold NoRace raceCheck
  decide +kernel

#print axioms reader_not_owns
#print axioms readers_ownsR
#print axioms reader_noRace
#print axioms writer_races

end Zig.ShareRaceCX
