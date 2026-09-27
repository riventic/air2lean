# Std functions: translated or modelled

A std function that an example calls is one of these:

| Kind | How | Where |
|---|---|---|
| Translated | Its AIR is written and translated like user code, so the diff test checks it too. | its name prefix in `examples/<ex>/filter` |
| Modelled | Not translated. A call to it is a call to a Lean model. | `Air2Lean/Memory.lean` (`allocFn?`), `ZigLean/Mem/Alloc.lean` |
| Panic handler | A noreturn call: a `Zig.Error` constructor. | `panicErrorFor?` (`docs/generated-code.md` §Panics) |

`Check.lean` rejects a call to a function that has no AIR file and no model.

## `examples/<ex>/filter`

One name prefix per line. `scripts/check.sh` writes the AIR of every function whose name starts with `<ex>.` or with one of these prefixes (`ZIG_AIR_JSON_FILTER`, a comma list). A prefix names the instance: `array_list.Aligned(u32,null).` translates the `ArrayListUnmanaged(u32)` methods, and not the instances that std's own debug code uses.

## Allocator model

`std.mem.Allocator` is `Zig.Allocator` (a structure without fields; 16 bytes in memory). The model is one allocator, with its state in `Zig.Mem`:

| Rule | |
|---|---|
| Blocks | Each allocation is a new block of kind `.heap`, with undefined bytes. |
| Failure | Allocation number `Mem.failAt` (from 0, counted in `Mem.allocs`) fails, and so does an allocation of more than `Zig.maxAllocBytes` (1 MiB). The function returns `error.OutOfMemory`. An allocation of 0 bytes is no allocation: its pointer has no block (`Zig.zeroAllocPtr`). |
| `resize`, `remap` | Always fail. So `realloc` and a growing `ArrayListUnmanaged` always allocate, copy and free, and the number of allocations does not depend on the allocator. |
| Free | The pointer is the start of a live `.heap` block, and the length is the length of the block. Anything else (a double free, a free of a global or of a stack block) throws `.illegal`. |

| Zig (`mem.Allocator.<fn>__anon_<n>`) | Lean |
|---|---|
| `create(T)` | `Zig.Allocator.create a size align` |
| `destroy(p)` | `Zig.Allocator.destroy a size p` |
| `alloc(T, n)`, `alignedAlloc(T, a, n)` | `Zig.Allocator.alloc a size align n` |
| `free(s)` | `Zig.Allocator.free a size s` |
| `dupe(T, s)` | `Zig.Allocator.dupe a size align srcAlign s` |
| `remap(s, n)` | `Zig.Allocator.remap a size s n` |

`size` and `align` come from the call's result or argument type. Every other function of `std.mem.Allocator` is outside the subset. A free of a slice with a sentinel is outside the subset.

The diff test runs each function with `TestAllocator` (`tests/diff/common.zig`), which has the same rules. Its first argument is the allocation that fails; each result line has the number of live allocations after the call (`docs/generated-code.md` §Protocol).

## Versions

The std code differs between Zig versions: 0.15.2's `growCapacity` has a loop, 0.16.0's does not. So an example with translated std code has a translation per version (`tests/golden/<version>/<ex>/Gen.lean`), and the proofs are about the 0.16.0 translation. 0.14.1 does not run `lists`: its `ArrayListUnmanaged` is a different type (`ArrayListAlignedUnmanaged`).
