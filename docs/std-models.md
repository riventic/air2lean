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

## Thread model

`std.Thread.spawn`/`.join` are modelled, like the allocator, in `Zig.Mem` (`ZigLean/Mem/Thread.lean`). Fork-join only: `Thread.detach`, `.yield`, `.spinLoopHint`, `std.Thread.Futex`, `.Mutex`, `.Condition` are outside the subset and rejected at translation time (`Air2Lean/Memory.lean`'s `rejectedThreadFn?`), with the reason in the error message.

| Rule | |
|---|---|
| `spawn(config, f, args)` | Runs `f args` eagerly, as a new thread forked from the caller. Never fails: the `SpawnConfig`'s stack size and allocator have no observable effect. `args` (the `.{...}` tuple) must have exactly 1 field (`Check.lean`) — one argument only. |
| `join(handle)` | Runs to completion (it already did, at `spawn`). Requires `handle` to be joined by the same thread that spawned it, and not already joined; anything else throws `.illegal`. A thread that returns with a handle it did not join throws `.illegal`: `spawn` checks this for a spawned thread, the diff test's runner (`renderThread`) for the main thread when the top-level function returns. |
| Happens-before | A Lamport vector clock per thread (`Zig.VClock`), bumped at every `spawn`/`join`. `spawn` bumps the parent's clock and gives the child a copy; `join` merges the joined thread's clock into the caller's. Two accesses are concurrent when neither clock is `≤` the other. |
| Footprint | Every access (`Mem.footprint`) is a byte range, a kind (plain read/write, atomic read/write, with the atomic write's commuting group if any), and the clock at the time. |
| Race check | Two concurrent accesses to the same bytes, at least one a non-atomic write, is `.illegal`. A concurrent atomic access with a write is `.nondet`, except two atomic RMWs of the same op group (`docs/generated-code.md` §Atomics and threads) on the same bytes (so the same width), `Min`/`Max` also with the same signedness, both with an unused result — those commute, so they never race. |

`Thread.spawn`'s eager run does not change which accesses are concurrent: concurrency is a property of the vector clocks, not of physical execution order.

**Known limit**: a spin-wait on a flag that no thread the model has run yet has set does not terminate — `Zig.loop`'s recursion returns `none` for it, the same as any other loop whose condition never becomes true.

Every atomic op and RMW is sequentially consistent within one thread: the model does not weaken `unordered`/`monotonic`/`acquire`/`release`/`acq_rel` orderings — it decodes the ordering argument and otherwise ignores it. `cmpxchg_weak` never fails spuriously: both it and `cmpxchg_strong` compile to the same model. The subset restricts an atomic op's pointee to an integer type: no float, `bool`, enum or pointer atomic (M20 territory: pointer atomics need the memory model to track a `Zig.Ptr`'s bytes atomically, and float/`bool` atomics have no test coverage yet).

## Versions

The std code differs between Zig versions: 0.15.2's `growCapacity` has a loop, 0.16.0's does not. So an example with translated std code has a translation per version (`tests/golden/<version>/<ex>/Gen.lean`), and the proofs hold for each of them (CI builds `Proofs/` after `check.sh` writes that version's translation). 0.14.1 does not run `lists`: its `ArrayListUnmanaged` is a different type (`ArrayListAlignedUnmanaged`).
