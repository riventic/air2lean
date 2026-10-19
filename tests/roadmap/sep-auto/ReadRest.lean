import ZigLean.Sep.Full.LockSteps

/-!
# Admission can justify a rest read without admitting every live thread

These memory-level clock witnesses exercise the `NoRace` premise of `FLock.Inv.loadRest`.
They are not complete RwLock executions: the load's byte/encoding/invariant obligations remain
in the general library theorem. Reader 1 has the publication's clock; unrelated thread 2 does
not. The first read is race-free, the second races, and all-reader `ReadShared` fails.
-/

open Zig Zig.Conc

namespace SepAuto.ReadRest

private def publication : FootprintEntry :=
  { tid := 0, clock := #[1, 0, 0], block := 0, off := 0, len := 4, kind := .write }

private def readerMemory (t : ThreadId) : Mem :=
  { current := t
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false },
      { spawner := 0, joined := false }]
    clocks := #[#[1, 0, 0], #[1, 1, 0], #[0, 0, 1]]
    footprint := #[publication] }

/-- The admitted reader's clock covers the publication and its read is race-free. -/
theorem admitted_read_noRace : NoRace (readerMemory 1) 0 0 4 .read := by
  unfold NoRace
  decide +kernel

/-- An unrelated live thread did not acquire the publication; admitting it would permit a race. -/
theorem unadmitted_read_races : ¬ NoRace (readerMemory 2) 0 0 4 .read := by
  unfold NoRace
  decide +kernel

/-- Race-free admission of one reader does not imply admission of every live thread. -/
theorem admitted_is_not_readShared : ¬ ReadShared (fun e => e.block = 0) (readerMemory 1) := by
  intro hs
  have hs2 : ReadShared (fun e => e.block = 0) (readerMemory 2) := hs
  exact unadmitted_read_races
    (hs2.noRace_read (by decide) (fun _ hb _ _ _ => hb))

end SepAuto.ReadRest
