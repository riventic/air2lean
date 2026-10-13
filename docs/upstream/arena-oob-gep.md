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
  `@intFromPtr(memory.ptr) + memory.len`. **Not enough on its own**: with `end_index` past the
  buffer, a slice of another allocation whose end address happens to equal `buf_ptr +
  end_index` (for example the start of the next block) passes the test, `free` moves
  `end_index` back by its length, and a later `alloc` hands out bytes of the node that are
  still granted.
* Or, before forming the pointer, check that `cur_end_index <= buf.len`. The size is already
  loaded in `resize` (`loadBuf`); `free` would need the same load.
* Or have `alloc` give the reservation back when the request does not fit (a `cmpxchg` back to
  the old value), so that `end_index <= buf.len` stays an invariant of the first node. **Not
  enough under concurrency**: between another thread's bump and its rollback, `end_index` is past
  the buffer, and a rollback that loses its `cmpxchg` (a third thread bumped in between) leaves a
  value past it.

## Proposed patch

[`tests/roadmap/alloc-arena/upstream/arena-fix.patch`](../../tests/roadmap/alloc-arena/upstream/arena-fix.patch)
(against Zig 0.16.0 `lib/std/heap/ArenaAllocator.zig`; 0.17.0 has the same code) takes the
second and the third fix and, since the same proof obligation needs it, makes `alloc` return
`null` where a size overflows `usize` instead of panicking (O-B in
[alloc-arena.md](../alloc-arena.md)):

* `free` and `resize` load the node's size (`loadBuf`) and return before forming `buf_ptr +
  cur_end_index` when `cur_end_index` is past the buffer (`resize` then reports what a slice
  that is not the last allocation gets: `new_len <= memory.len`). Sizes only grow, so a size
  loaded after `end_index` bounds the node's allocation when the pointer is formed. A racing
  `alloc` (a reservation not yet given back, or a lost rollback) can therefore no longer make
  the pointer out of bounds, and the comparison is one of in-bounds addresses: a slice of
  another block cannot end inside the node past its header (live blocks are disjoint), so the
  test also stays sound if it is written on integers;
* the fast path does not reserve at all when `n + alignment - 1` exceeds the buffer (adding it
  to `end_index` could wrap around). The aligned request may still fit: the resize path then
  finds that the node need not grow, and instead of retrying (which would come back to the same
  place forever) it takes the place by a `cmpxchg` of `end_index`, or retries if `end_index`
  moved;
* the fast path checks the fit *before* the overshoot `cmpxchg`; when the request does not fit
  it gives the reservation back (`@cmpxchgStrong(&node.end_index, end_index +% alignable,
  end_index, …)`) and goes on to the resize, free-list and new-node paths, so a failure of the
  child leaves `end_index` within the buffer;
* `n + alignment - 1`, the sizes of the in-place growth and of a free-list node
  (`nodeSizeFor`), and the size of a new node are computed with overflow checks that fail the
  request (or skip that path) instead of panicking.

Consequences visible in the fixture: `arena_oom_free` (an allocation the child cannot serve
after one it could, then the `free` of the first) frees the first slice; the in-place growth of
the first node no longer includes the failed reservation, so it asks the child for less
(`arena_reset 500 true` gives 5001 instead of 7001, `arena_reset 1500 true` succeeds where the
stock arena's second allocation fails: `expected-fixed.txt`). `arena_fit` (an empty node, and a
request whose reservation exceeds its buffer but whose aligned bytes fit) is served from the node
by both; without the resize-path `cmpxchg` the patched arena loops there forever (checked
natively). The stock standard library's
`ArenaAllocator` tests pass with the patch, in Debug and ReleaseSafe, the multi-threaded fuzz test
included (`zig test [-OReleaseSafe] --zig-lib-dir <patched lib> lib/std/std.zig --test-filter
ArenaAllocator`). In one thread the patched `alloc` keeps `end_index <= buf.len`; with other
threads, the bounds check in `free` and `resize` covers the window in which a racing `alloc`
holds a reservation past the buffer.

**Evidence.** The patched arena is translated from its real AIR (`arena-fixed-linux`,
`AllocArena/ArenaFixedLinux.lean`) and equals its native run on every fixture client
(`Eval.lean`). Its proof against `FAllocSpec` is in progress ([alloc-arena.md](../alloc-arena.md)
§What is proved): `free`, `resize` and `remap` are proved for the stock and for the patched
module (with its bounds check) over an invariant with `end_index <= buf.len`. That the
patched `alloc` keeps this invariant (with the child's `FAllocSpec`), and `reset`, are not proved
yet, so the patch is not yet proved correct.

## In the model

After the memory-model hardening (MM-3: `Zig.ptrProject` throws `.illegal` for an out-of-bounds
projection), the translated `free` and `resize` are `.illegal` in this state. So
`Arena ⊨ FAllocSpec` cannot hold for an invariant that admits the state that a failed `alloc`
leaves (`docs/alloc-arena.md`, O-E).
