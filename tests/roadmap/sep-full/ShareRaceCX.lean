import ZigLean.Sep.Full.Share

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
5. `readers_ownsRes`: under option R (`Mem.OwnsRes`: full ownership of the exclusive bytes, read
   ownership of the partial shares) each reader owns its half share of the byte.
6. `gather_not_ownsRes`: but thread `1` does not own the whole share gathered from both halves,
   which is exclusive: the gathering rules fail closed (`FOwned.join`, `FLock.NoGather`).

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

/-! ## The ownership of a resource (option R, `Mem.OwnsRes`) -/

open Zig.Full

/-- The heap of the byte as one cell. -/
def cellH (c : Cell) : FHeap := fun l => if l = (0, 0) then some ⟨c, none⟩ else none

/-- The fraction `1/2`. -/
def half : Frac := ⟨1 / 2, by grind⟩

/-- A share `q` of the byte: no cell, the share as ghost state (`sheap`). -/
noncomputable def shareRes (c : Cell) (q : Frac) : Res :=
  ⟨FHeap.empty, Know.none, Ghost.sharesOf (cellH c) q⟩

/-- A half share is not exclusive: it holds no cell and no whole share (`Res.excl`). -/
theorem half_excl (c : Cell) (l : Loc) : (shareRes c half).excl l = none := by
  refine Classical.byContradiction fun h => ?_
  rcases Res.excl_ne.mp h with h | ⟨c', hc'⟩
  · exact h rfl
  · simp only [shareRes, Ghost.sharesOf_share, cellH] at hc'
    split at hc'
    · simp only [Option.elim_some, SCell.of] at hc'
      split at hc'
      · simp only [half] at hc'; grind
      · simp only [Frac.zero] at hc'; grind
    · simp only [Option.elim_none, SCell.zero, Frac.zero] at hc'; grind

/-- The whole share of the byte is exclusive (`Res.excl`). -/
theorem whole_excl (c : Cell) : (shareRes c Frac.one).excl (0, 0) ≠ none :=
  Res.excl_ne.mpr (.inr ⟨⟨c, none⟩, by
    simp only [shareRes, Ghost.sharesOf_share, cellH, ite_true, Option.elim_some, SCell.of_self,
      Frac.one]
    exact Rat.le_refl⟩)

/-- **Each of the two readers owns its half share** (`Mem.OwnsRes`): nothing is exclusive and no
write is recorded. -/
theorem readers_ownsRes (c : Cell) (t : ThreadId) : (twoReaders).OwnsRes t (shareRes c half) := by
  refine ⟨fun e he htc => ?_, fun e he hw _ => ?_⟩
  · simp only [twoReaders, Array.mem_singleton] at he
    subst he
    rcases htc with ⟨x, -, -, hx⟩ | hb
    · exact absurd (half_excl c _) hx
    · exact absurd hb (by decide)
  · simp only [twoReaders, Array.mem_singleton] at he
    subst he; exact absurd hw (by decide)

/-- **The second reader does not own the gathered whole share** (`Mem.OwnsRes`): the first
reader's read is not before its clock. So gathering the two halves at a join or an acquire fails
closed (`FOwned.join`'s `hg`, `FLock.NoGather`; engine ledger #share-gather). -/
theorem gather_not_ownsRes (c : Cell) : ¬ (twoReaders).OwnsRes 1 (shareRes c Frac.one) := by
  intro ho
  have := ho.1 readEntry (by simp [twoReaders]) (.inl ⟨0, Nat.le_refl _, by decide, whole_excl c⟩)
  revert this; decide +kernel

#print axioms reader_not_owns
#print axioms readers_ownsR
#print axioms reader_noRace
#print axioms writer_races
#print axioms readers_ownsRes
#print axioms gather_not_ownsRes

end Zig.ShareRaceCX
