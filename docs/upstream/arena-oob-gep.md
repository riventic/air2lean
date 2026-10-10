# Draft upstream note: `ArenaAllocator.free`/`resize` form an out-of-bounds `inbounds` pointer after a failed `alloc`

Status: draft, **not filed**. Found by the translated-allocator work (`docs/alloc-arena.md`,
obstruction O-E). Zig 0.16.0 and 0.17.0 (`lib/std/heap/ArenaAllocator.zig`: the same code).

## Summary

`alloc` reserves space by an atomic `end_index += n + alignment - 1` before it checks that the
request fits the first node. When it does not fit, `end_index` keeps a value larger than the
node's buffer (`aligned_index + n > buf.len`). If the arena then gets no new node (the child
allocator is out of memory), `alloc` returns `null` and leaves that node first. A later `free`
or `resize` on the arena computes

```zig
const buf_ptr = @as([*]u8, @ptrCast(node)) + @sizeOf(Node);
const cur_end_index = @atomicLoad(usize, &node.end_index, .monotonic);
if (buf_ptr + cur_end_index != memory.ptr + memory.len) { ... }
```

`buf_ptr + cur_end_index` lies past the end of the node's allocation. The LLVM backend lowers
the many-pointer addition to `getelementptr inbounds`, whose result is `poison` out of bounds.
It is compared and branched on:

```llvm
%12 = load atomic i64, ptr %11 monotonic, align 8              ; cur_end_index
%13 = getelementptr inbounds [1 x i8], ptr %10, i64 %12        ; buf_ptr + cur_end_index
%14 = getelementptr inbounds [1 x i8], ptr %1, i64 %2          ; memory.ptr + memory.len
%.not7 = icmp eq ptr %13, %14
br i1 %.not7, label %Else2, label %common.ret
```

(`heap.ArenaAllocator.free`, `-OReleaseSafe`, aarch64-macos; `resize` has the same pattern.)
Branching on `poison` is undefined behaviour. In Zig terms, pointer arithmetic outside the
allocation is illegal behaviour that is not safety-checked.

## Reproducer

[`tests/roadmap/alloc-arena/upstream/oob_gep.zig`](../../tests/roadmap/alloc-arena/upstream/oob_gep.zig):
an arena over a 256-byte `FixedBufferAllocator`, an allocation that succeeds, one of 4096
bytes that fails, and then `free` of the first allocation. It prints `true` natively: the UB has
no visible effect in this build, but the IR above is the code that runs.

```sh
zig build-exe -OReleaseSafe -femit-llvm-ir=oob_gep.ll oob_gep.zig && ./oob_gep
```

## Possible fixes

* Compare integers, not pointers: `@intFromPtr(buf_ptr) + cur_end_index` (wrapping) against
  `@intFromPtr(memory.ptr) + memory.len`.
* Or, before forming the pointer, check that `cur_end_index <= buf.len`. The size is already
  loaded in `resize` (`loadBuf`); `free` would need the same load.
* Or have the failing `alloc` restore `end_index` (a `cmpxchg` back to the old value), so that
  `end_index <= buf.len` is an invariant of the first node. Concurrent `alloc`s that bump past
  the end make that harder.

## In the model

After the memory-model hardening (MM-3: `Zig.ptrProject` throws `.illegal` for an out-of-bounds
projection), the translated `free` and `resize` are `.illegal` in this state. So
`Arena ⊨ FAllocSpec` cannot hold for an invariant that admits the state that a failed `alloc`
leaves (`docs/alloc-arena.md`, O-E).
