import AllocFba.Fba
import ZigLean.Sep.Full.Tame
import ZigLean.Sep.Full.AllocSpec

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the legacy total specification `FBA.allocSpec` (`Fba.lean`) lifts to the
full-state specification (`ZigLean/Sep/Full/AllocSpec.lean`, `docs/sep-full-state.md` stage 2),
with the invariant `(FBA.inv ctx B).toFull` (its assertions under `up`). The lifting needs only
that the four translated entries are `Tame`: they keep the atomic layout and every block's
address. `tame` proves that from the generated code, after `fba_norm`.
-/

namespace AllocFba

open Zig Zig.Full Gen

namespace FBA

theorem tame_alignPointerOffset (p : Ptr) (a : BitVec 64) :
    Tame (mem_alignPointerOffset__anon_1 p a) := by
  unfold mem_alignPointerOffset__anon_1; fba_norm; tame

theorem tame_sliceContainsSlice (a b : Slice) :
    Tame (heap_FixedBufferAllocator_sliceContainsSlice a b) := by
  unfold heap_FixedBufferAllocator_sliceContainsSlice; fba_norm; tame

theorem tame_ownsSlice (c : Ptr) (s : Slice) : Tame (heap_FixedBufferAllocator_ownsSlice c s) := by
  have := tame_sliceContainsSlice
  unfold heap_FixedBufferAllocator_ownsSlice; fba_norm; tame

theorem tame_isLastAllocation (c : Ptr) (s : Slice) :
    Tame (heap_FixedBufferAllocator_isLastAllocation c s) := by
  unfold heap_FixedBufferAllocator_isLastAllocation; fba_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_alloc (c : Ptr) (n : BitVec 64) (k : Nat) (ra : BitVec 64) :
    Tame (impl.alloc c n k ra) := by
  have := tame_alignPointerOffset
  unfold impl; simp only [heap_FixedBufferAllocator_alloc]; fba_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_resize (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) :
    Tame (impl.resize c s k n ra) := by
  have := tame_ownsSlice; have := tame_isLastAllocation
  unfold impl; simp only [heap_FixedBufferAllocator_resize]; fba_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_remap (c : Ptr) (s : Slice) (k : Nat) (n ra : BitVec 64) :
    Tame (impl.remap c s k n ra) := by
  have := fun c s k n ra => tame_resize c s k n ra
  unfold impl at this ⊢; simp only [heap_FixedBufferAllocator_remap]; fba_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_free (c : Ptr) (s : Slice) (k : Nat) (ra : BitVec 64) :
    Tame (impl.free c s k ra) := by
  have := tame_ownsSlice; have := tame_isLastAllocation
  unfold impl; simp only [heap_FixedBufferAllocator_free]; fba_norm; tame

theorem vtame (ctx : Ptr) : VTame impl ctx :=
  ⟨tame_alloc ctx, tame_resize ctx, tame_remap ctx, tame_free ctx⟩

/-- **The translated `FixedBufferAllocator` satisfies the full-state allocator specification.** -/
theorem fallocSpec (ctx : Ptr) (B : Buf) : FAllocSpec FLogic.total impl ctx (inv ctx B).toFull :=
  FAllocSpec.ofTotal (allocSpec ctx B) (vtame ctx)

end FBA

end AllocFba
