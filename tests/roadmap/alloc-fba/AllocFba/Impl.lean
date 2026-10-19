import AllocFba.Gen
import ZigLean.Sep.Base.Alloc

/-!
# The translated `FixedBufferAllocator` as a raw vtable

The four entries of the translated `FixedBufferAllocator` (`Gen.lean`) as a `RawVTable`, with the
alignment as a `Nat` log2, and the function pointers in the generated vtable constant. The
full-state contract `FBA.fallocSpec` (`Full.lean`) and the wrapper contracts (`Wrappers.lean`)
are stated over them.
-/

namespace AllocFba

open Zig Gen

/-- The translated `FixedBufferAllocator` entries, with the alignment as a `Nat` log2. -/
def impl : RawVTable where
  alloc c n k ra := heap_FixedBufferAllocator_alloc c n ⟨BitVec.ofNat 6 k⟩ ra
  resize c s k n ra := heap_FixedBufferAllocator_resize c s ⟨BitVec.ofNat 6 k⟩ n ra
  remap c s k n ra := heap_FixedBufferAllocator_remap c s ⟨BitVec.ofNat 6 k⟩ n ra
  free c s k ra := heap_FixedBufferAllocator_free c s ⟨BitVec.ofNat 6 k⟩ ra

/-- The function pointers in the generated vtable constant (globals 1 to 4 of `mem0`). -/
abbrev fns : VTableFns := ⟨⟨some 1, 0⟩, ⟨some 2, 0⟩, ⟨some 3, 0⟩, ⟨some 4, 0⟩⟩

end AllocFba
