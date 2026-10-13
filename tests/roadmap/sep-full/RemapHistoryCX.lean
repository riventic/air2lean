import ZigLean.Os.Mmap
import ZigLean.Conc.Clock

/-!
# Revived bytes start with no access history: regression (`docs/sep-threads.md`, S2)

The counterexample to a thread rule for `mremap` growth in place (S2, "`mremap` growth in place")
before the model fix: thread 1 unmapped the tail of mapping block 0 (a recorded write of offset
`1`), concurrently with thread 0; thread 0 then grows the mapping in place to 2 bytes and owns the
grown byte `1` (it holds the mapping's authority, so the growth hands it the new bytes). With the
old record kept, thread 0's write of its own new byte races with thread 1's unmap (`stale_races`),
so no thread rule could give thread 0 the grown bytes.

The model now forgets the recorded accesses to the grown offsets (`Mem.forgetFrom` in
`Mem.mremapGrown` and `Mem.afterByteRemap`): they start with no access history, as the bytes of a
new block do. So the same write does not race (`grown_noRace`), and in general every clock owns
the grown bytes (`grown_owned`, from `Mem.OwnsC.forgotten`).

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound` at most.
-/

namespace Zig.RemapHistoryCX

open Zig

/-- Mapping block 0 after thread 1 unmapped its tail: one live byte (`S = 1`). -/
def blk : Block := { bytes := #[.int 0], align := 4096, kind := .mapped 0, live := true, addr := 4096 }

/-- Thread 1's unmap of offset `1` (clock `[0, 1]`), concurrent with thread 0 (clock `[1]`). -/
def unmapEntry : FootprintEntry :=
  { tid := 1, clock := #[0, 1], block := 0, off := 1, len := 1, kind := .write }

/-- The memory before the growth: thread 0 runs, thread 1 is not joined. -/
def m : Mem :=
  { blocks := #[blk], current := 0, clocks := #[#[1], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    footprint := #[unmapEntry] }

/-- The memory after the growth in place to 2 bytes. -/
def m' : Mem := m.mremapGrown 4096 0 blk 0 2

/-- **Before the fix**: the grown memory with the old record kept; thread 0's write of the grown
byte races with thread 1's unmap. -/
theorem stale_races : ¬ NoRace { m' with footprint := m.footprint } 0 1 1 .write := by
  unfold NoRace; decide +kernel

/-- **After the fix**: the same write does not race. -/
theorem grown_noRace : NoRace m' 0 1 1 .write := by
  unfold NoRace; decide +kernel

/-- **Every clock owns the grown bytes** (the bytes of block 0 at offsets `≥ 1`). -/
theorem grown_owned (c : VClock) :
    m'.OwnsC c (fun l => if l.1 = 0 ∧ 1 ≤ l.2 then m'.heap l else none) :=
  Mem.OwnsC.forgotten (m := m) (b := 0) (S := 1) rfl
    (fun l hl => by
      by_cases h : l.1 = 0 ∧ 1 ≤ l.2
      · exact h
      · simp [h] at hl)
    (fun e he hb => by
      have : e = unmapEntry.forgetFrom 0 1 := by
        simpa [m', Mem.mremapGrown, Mem.forgetFrom, m, blk] using he
      subst this; exfalso; revert hb; decide +kernel)

end Zig.RemapHistoryCX

#print axioms Zig.RemapHistoryCX.stale_races
#print axioms Zig.RemapHistoryCX.grown_noRace
#print axioms Zig.RemapHistoryCX.grown_owned
