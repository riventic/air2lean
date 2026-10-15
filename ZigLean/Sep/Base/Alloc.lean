import ZigLean.Sep.Base.Pts

/-!
# The `std.mem.Allocator` vtable

`RawVTable`: the semantics of the four entries of a `std.mem.Allocator.VTable`; `VTableFns`: the
function pointers of one allocator's `VTable`; `keepsPrefix`: what `resize`/`remap` keep of a
region's bytes. Vocabulary of the allocator specifications (`FAllocSpec`, `CAllocSpec`:
`ZigLean/Sep/Full/AllocSpec.lean`, `ZigLean/Sep/Full/Dispatch.lean`, `docs/alloc-spec.md`); no
program judgment is defined here (`docs/proof-framework.md`).
-/

namespace Zig

/-- The semantics of the four entries of a `std.mem.Allocator.VTable`, each called with the
context pointer (`Allocator.ptr`). The alignment is the log2 value `k` of `mem.Alignment`
(byte alignment `2 ^ k`); the last argument is `ret_addr`. A translated allocator instantiates
this with its generated functions (the generated `Alignment` value `⟨BitVec.ofNat 6 k⟩`). -/
structure RawVTable where
  alloc : Ptr → BitVec 64 → Nat → BitVec 64 → MemM (Option Ptr)
  resize : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM Bool
  remap : Ptr → Slice → Nat → BitVec 64 → BitVec 64 → MemM (Option Ptr)
  free : Ptr → Slice → Nat → BitVec 64 → MemM Unit

/-- The function pointers of the four entries of one allocator's `VTable`. -/
structure VTableFns where
  alloc : Ptr
  resize : Ptr
  remap : Ptr
  free : Ptr

/-- `new` keeps the common prefix of `old` (both read up to the shorter length). -/
def keepsPrefix (old new : Array Byte) : Prop := new.extract 0 old.size = old.extract 0 new.size

theorem keepsPrefix_refl (bs : Array Byte) : keepsPrefix bs bs := rfl

end Zig
