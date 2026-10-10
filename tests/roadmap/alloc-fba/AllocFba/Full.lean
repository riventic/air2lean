import AllocFba.Fba
import ZigLean.Sep.Full.Tame
import ZigLean.Sep.Full.AllocSpec

/-!
# The translated `FixedBufferAllocator` satisfies the full-state `FAllocSpec`

`FBA.fallocSpec`: the legacy total specification `FBA.allocSpec` (`Fba.lean`) lifts to the
full-state specification (`ZigLean/Sep/Full/AllocSpec.lean`, `docs/sep-full-state.md` stage 2),
with the invariant `(FBA.inv ctx B).toFull` (its assertions under `up`). The lifting needs only
that the four translated entries are `Tame`: they keep the atomic layout and every block's
address. `tame` proves that from the generated code, after `gen_norm`.
-/

namespace AllocFba

open Zig Zig.Full Gen

namespace FBA

theorem tame_alignPointerOffset (p : Ptr) (a : BitVec 64) :
    Tame (mem_alignPointerOffset__anon_1 p a) := by
  unfold mem_alignPointerOffset__anon_1; gen_norm; tame

theorem tame_sliceContainsSlice (a b : Slice) :
    Tame (heap_FixedBufferAllocator_sliceContainsSlice a b) := by
  unfold heap_FixedBufferAllocator_sliceContainsSlice; gen_norm; tame

theorem tame_ownsSlice (c : Ptr) (s : Slice) : Tame (heap_FixedBufferAllocator_ownsSlice c s) := by
  have := tame_sliceContainsSlice
  unfold heap_FixedBufferAllocator_ownsSlice; gen_norm; tame

theorem tame_isLastAllocation (c : Ptr) (s : Slice) :
    Tame (heap_FixedBufferAllocator_isLastAllocation c s) := by
  unfold heap_FixedBufferAllocator_isLastAllocation; gen_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_alloc (c : Ptr) (n : BitVec 64) (a : mem_Alignment) (ra : BitVec 64) :
    Tame (heap_FixedBufferAllocator_alloc c n a ra) := by
  have := tame_alignPointerOffset
  simp only [heap_FixedBufferAllocator_alloc]; gen_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_resize (c : Ptr) (s : Slice) (a : mem_Alignment) (n ra : BitVec 64) :
    Tame (heap_FixedBufferAllocator_resize c s a n ra) := by
  have := tame_ownsSlice; have := tame_isLastAllocation
  simp only [heap_FixedBufferAllocator_resize]; gen_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_remap (c : Ptr) (s : Slice) (a : mem_Alignment) (n ra : BitVec 64) :
    Tame (heap_FixedBufferAllocator_remap c s a n ra) := by
  have := tame_resize
  simp only [heap_FixedBufferAllocator_remap]; gen_norm; tame

set_option maxHeartbeats 2000000 in
theorem tame_free (c : Ptr) (s : Slice) (a : mem_Alignment) (ra : BitVec 64) :
    Tame (heap_FixedBufferAllocator_free c s a ra) := by
  have := tame_ownsSlice; have := tame_isLastAllocation
  simp only [heap_FixedBufferAllocator_free]; gen_norm; tame

theorem vtame (ctx : Ptr) : VTame impl ctx :=
  ⟨fun n k ra => tame_alloc ctx n ⟨BitVec.ofNat 6 k⟩ ra,
    fun s k n ra => tame_resize ctx s ⟨BitVec.ofNat 6 k⟩ n ra,
    fun s k n ra => tame_remap ctx s ⟨BitVec.ofNat 6 k⟩ n ra,
    fun s k ra => tame_free ctx s ⟨BitVec.ofNat 6 k⟩ ra⟩

/-- **The translated `FixedBufferAllocator` satisfies the full-state allocator specification.** -/
theorem fallocSpec (ctx : Ptr) (B : Buf) : FAllocSpec FLogic.total impl ctx (inv ctx B).toFull :=
  FAllocSpec.ofTotal (allocSpec ctx B) (vtame ctx)

end FBA

end AllocFba
