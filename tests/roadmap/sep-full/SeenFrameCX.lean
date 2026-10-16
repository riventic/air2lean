import ZigLean.Conc.Clock

/-!
# The observation premise is necessary for a reader's framed seen floor

The old unconditional `FStepIn.observe` and `FStepIn.loadM` admitted this backwards
observation. The strengthened relation excludes it. An arbitrary `observeM` transition
need not be a permitted atomic read; the actual `readOpts` already excluded this one.
Coherence also permits a reader to advance: equality at a framed location comes from
separation, not coherence alone.
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

/-- The corrected raw rule's extra premise is false. Its old index premise still holds. -/
theorem missing_premise : (before.atomics[0]!).In frame ∧ before.current < before.clocks.size :=
  ⟨in_frame, by decide⟩

/-- The stronger frame relation rejects the transition admitted by the old raw rule. -/
theorem not_admitted : ¬ FStepIn frame before after := by
  intro hs
  obtain ⟨σ, ha⟩ := hs.atomics
  obtain ⟨j, hij, hj⟩ := ha.frame 0 loc rfl in_frame
  have hj0 : j = 0 := by
    have := (Array.getElem?_eq_some_iff.mp hj).1
    change j < 1 at this
    omega
  subst j
  have h := ha.own 0 loc 0 rfl in_frame hij
  change some 0 = some 1 at h
  cases h

theorem not_admitted_load :
    ¬ FStepIn frame before (loadM before 0 .relaxed loc.msgs[0]!) := not_admitted

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

/-- The old unconditional statement contradicts the stronger relation. -/
theorem no_unconditional_observe :
    ¬ (∀ (hF : Heap) (m : Mem) (li id : Nat), FStepIn hF m (observeM m li id)) := by
  intro h
  exact not_admitted (h frame before 0 0)

def earlier : Mem := { before with seen := #[(0, 0, 0)] }

/-- Coherence allows advancing to a newer message. It does not imply view equality. -/
theorem permitted_advance :
    (readOpts earlier 0 false)[0]? = some 1 ∧
      earlier.seenAt 0 0 = some 0 ∧ (observeM earlier 0 1).seenAt 0 0 = some 1 := by
  decide +kernel

#print axioms not_admitted
#print axioms permitted_advance

end Zig.SeenFrameCX
