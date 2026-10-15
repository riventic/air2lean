import ZigLean.Conc.Clock

/-!
# The current frame relation does not preserve a reader's seen floor

This is an obstruction to strengthening `AMap` while retaining the statements of
`FStepIn.observe` and `FStepIn.loadM`. It is not a counterexample to a current program
correctness theorem: an arbitrary `observeM` transition need not be a permitted atomic read.
-/

namespace Zig.SeenFrameCX

open Conc.Proto

def loc : ALoc :=
  { block := 0, off := 0, len := 4,
    msgs := #[{ id := 0, bytes := Array.replicate 4 (.int 0), clock := #[], relClock := #[] },
      { id := 1, bytes := Array.replicate 4 (.int 1), clock := #[0, 1], relClock := #[] }] }

def before : Mem :=
  { atomics := #[loc], seen := #[(0, 0, 1)], nextMsg := 2 }

def frame : Heap := fun _ => some ⟨.int 1, 4096, 4, .heap⟩

def after : Mem := observeM before 0 0

/-- The location is in the frame, so the proposed `hnot` premise is false. -/
theorem in_frame : loc.In frame := by
  intro x h1 h2
  simp [frame]

/-- Nevertheless, current main's unconditional rule admits this transition. -/
theorem admitted : FStepIn frame before after := FStepIn.observe 0 0

/-- `loadM`'s only premise (a valid current clock index) holds in the same example. -/
theorem admitted_load :
    FStepIn frame before (loadM before 0 .relaxed loc.msgs[0]!) :=
  FStepIn.loadM (by decide) 0 .relaxed loc.msgs[0]!

theorem same_location : after.atomics[0]? = some loc := rfl

/-- The message id in the current thread's view changes from `1` to `0`. -/
theorem view_changes : before.seen = #[(0, 0, 1)] ∧ after.seen = #[(0, 0, 0)] := by
  decide +kernel

/-- The read floor strictly decreases, although the framed location stays unchanged. -/
theorem floor_decreases : floorPos before 0 = 1 ∧ floorPos after 0 = 0 := by
  decide +kernel

/-- Before the raw observation, the model's permitted reads exclude the older message. -/
theorem read_options : readOpts before 0 false = #[1] ∧ readOpts after 0 false = #[1, 0] := by
  decide +kernel

/-- Therefore preservation, even as a nondecreasing floor, cannot follow from `FStepIn`. -/
theorem no_floor_preservation :
    ¬ (∀ (hF : Heap) (m m' : Mem), FStepIn hF m m' →
      (m.atomics[0]!).In hF → floorPos m 0 ≤ floorPos m' 0) := by
  intro h
  have hc := h frame before after admitted (by simpa [before] using in_frame)
  rw [floor_decreases.1, floor_decreases.2] at hc
  omega

end Zig.SeenFrameCX
