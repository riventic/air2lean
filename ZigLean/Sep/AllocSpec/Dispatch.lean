import ZigLean.Sep.AllocSpec

/-!
# The vtable dispatch of a translated `std.mem.Allocator`

A translated wrapper calls a vtable entry the way the compiler does: it loads the function
pointer from the `VTable` (a `const` global) at `vtable + 8 * i` and calls it. The translator
emits the indirect call as a test against each function the program can reach, and `.illegal`
for any other pointer. `dispatch impl fns vtp` is that: the `RawVTable` whose entries load the
pointer at `vtp` and, if it is the function `fns.*` of the allocator `impl`, run `impl`.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

/-- The function pointers of the four entries of one allocator's `VTable`. -/
structure VTableFns where
  alloc : Ptr
  resize : Ptr
  remap : Ptr
  free : Ptr

/-- The entries of the vtable at `vtp`, dispatched to `impl` (module doc). -/
def dispatch (impl : RawVTable) (fns : VTableFns) (vtp : Ptr) : RawVTable where
  alloc ctx len k ra := load Ptr 8 (vtp.add 0) >>= fun f =>
    if f = fns.alloc then impl.alloc ctx len k ra else throw .illegal
  resize ctx s k n ra := load Ptr 8 (vtp.add 8) >>= fun f =>
    if f = fns.resize then impl.resize ctx s k n ra else throw .illegal
  remap ctx s k n ra := load Ptr 8 (vtp.add 16) >>= fun f =>
    if f = fns.remap then impl.remap ctx s k n ra else throw .illegal
  free ctx s k ra := load Ptr 8 (vtp.add 24) >>= fun f =>
    if f = fns.free then impl.free ctx s k ra else throw .illegal

end Zig
