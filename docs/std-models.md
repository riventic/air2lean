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
| `free(s)` | `Zig.Allocator.free a size s`; `Zig.Allocator.freeSentinel a size s` for a `[:s]T` (`len + 1` items, the sentinel too) |
| `dupe(T, s)` | `Zig.Allocator.dupe a size align srcAlign s` |
| `remap(s, n)` | `Zig.Allocator.remap a size s n` |

`size` and `align` come from the call's result or argument type. `dupeZ` (and in 0.16.0 `dupeSentinel`, which it calls) is translated from its AIR (`examples/lists/filter`): it calls `alloc`. `allocSentinel` is outside the subset: its sentinel is a comptime argument, and the exporter does not write it. Every other function of `std.mem.Allocator` is outside the subset. A `remap` of a slice with a sentinel is outside the subset.

The name of a generic instance has a number that differs between compiles (`mem.Allocator.dupeZ__anon_16959`). The translator gives each instance a stable number by first use (`Air2Lean/Air/Anon.lean`), so the Lean name is `mem_Allocator_dupeZ__anon_1` in every version and on every host. A golden file of an instance is named `<name>__anon_N.json`.

The diff test runs each function with `TestAllocator` (`tests/diff/common.zig`), which has the same rules. Its first argument is the allocation that fails; each result line has the number of live allocations after the call (`docs/generated-code.md` §Protocol).

## Thread model

`std.Thread.spawn`/`.join` are modelled, like the allocator. A function that reaches a sync op (an atomic op, `Thread.spawn`, `Thread.join`) is a concurrent function: it returns `Zig.ConcM Tgt α` (`ZigLean/Conc/`, `docs/generated-code.md` §Atomics and threads). Its run is a tree: it ends with a result, or it stops at a sync op and goes on from the scheduler's response. The scheduler (`Zig.Sched.run dispatch fuel o main m0`, `ZigLean/Conc/Sched.lean`) runs all threads; they take turns only at sync ops. Plain code between two sync ops runs without a stop: a data race there is `.illegal`, so its order cannot change a result. `Thread.detach`, `.yield`, `.spinLoopHint`, `std.Thread.Futex`, `.Mutex`, `.Condition` are outside the subset and rejected at translation time (`Air2Lean/Memory.lean`'s `rejectedThreadFn?`), with the reason in the error message.

| Rule | |
|---|---|
| Schedule | At each turn the oracle `o` picks one of the threads that can go on (`o i` modulo the number of options, so every `o` is a schedule). A spec of a concurrent function holds for every `o` and every `fuel`. Out of fuel is `none`, as a loop that does not end. |
| `spawn(config, f, args)` | A sync op: a new thread with the target `Tgt.f args` (the program's spawn-target type, `docs/generated-code.md`), forked from the caller. It starts at its first turn with `dispatch`. Never fails: the `SpawnConfig`'s stack size and allocator have no observable effect. `args` (the `.{...}` tuple) must have exactly 1 field (`Check.lean`). |
| `join(handle)` | A sync op that can go on only when the thread has ended. Requires `handle` to be joined by the thread that spawned it, and not already joined; anything else throws `.illegal`. A thread that ends with a handle it did not join throws `.illegal` (`checkJoinedByChild`); the main thread's end ends the run. |
| Atomic op | A `pick` of the oracle (another thread can run first; the choice below), then the op in `MemM`. |
| RC11 | An atomic location (`Zig.ALoc`) keeps its writes (`Zig.Msg`) in modification order; the block's bytes are the last one's. A read reads any message that is not older than one that happened before it (its clock is `≤` the reader's) or that the thread read or wrote before (`Mem.seen`); option 0 is the newest. A write goes to any place after those messages, not between an RMW and the message it read; option 0 is the end. An RMW, and a successful `cmpxchg`, reads a message with no RMW after it yet and goes right after it. A plain write to an atomic location becomes a message at the next atomic op. |
| Happens-before | A vector clock per thread (`Zig.VClock`). `spawn` bumps the parent's clock and gives the child a copy; `join` merges the joined thread's clock into the caller's. An acquire read (`acquire`, `acq_rel`, `seq_cst`) adopts the message's release clock (`Msg.relClock`): the writer's clock for a release write, joined along the RMWs after it (the release sequence), empty for a relaxed write. Two accesses are concurrent when neither clock is `≤` the other. |
| Footprint | Every access (`Mem.footprint`) is a byte range, a kind (plain read/write, atomic read/write) and the clock at that time. |
| Race check | Two concurrent accesses to the same bytes, at least one a write and at least one plain (not atomic), is a data race: `.illegal`. Two atomic accesses never race: the schedule orders them. |

The orderings: `monotonic` is relaxed; `unordered` is outside the subset (it has no read-read coherence). `seq_cst` has the rule of `acq_rel`: the model has no global SC order, so it allows more results than RC11 (a proof never depends on a result that RC11 forbids), but a proof that needs the SC order (store buffering with `seq_cst`, Dekker) does not go through. `cmpxchg_weak` never fails spuriously: both it and `cmpxchg_strong` compile to the same model. An atomic location with an overlap of another size throws `.unspecified`.

**Trusted assumption**: the compiled code has no load buffering, as RC11 requires (the model has no promises). LLVM does not promise this for relaxed atomics; no example depends on it. An atomic op's pointee is an integer, an enum, a `bool` or a packed struct (`Io.Condition`'s state): such an op is the integer op on its bits (`Zig.Packed`; `Zig.atomicLoadAs`, `atomicStoreAs`, `atomicRmwAs`, `cmpxchgAs`), and a loaded tag value without a name of an exhaustive enum is `.illegal`. No float or pointer atomic.

**Futex and `std.Io` (0.16.0).** `std.Io` is the model's `Zig.Io` (its `userdata` and `vtable` are not translated). The std sync primitives `Io.Mutex`, `Io.Condition`, `Io.Event`, `Io.Semaphore` (a mutex and a condition) and `Io.RwLock` (atomics on a `usize`, a mutex and a semaphore) are translated from their std code (`examples/<ex>/filter`); the futex under them is the model: `Io.futexWait`, `Io.futexWaitUncancelable` and `Io.futexWake` are sync ops (`Zig.futexWaitC`, `futexWaitCancelableC`, `futexWakeC`, `ZigLean/Conc/Call.lean`). A wait whose `u32` at the address is the expected value waits until a wake at the address (the waiters wake in the order they began to wait); else it goes on. The futex queue is in `Mem` (`Mem.waiters`, `Mem.woken`; `Thread.futexWait`, `Thread.futexWake`), as the thread table is. A wake gives no happens-before edge (the std code reads the value again with an acquire). The model has no spurious wakeup and never cancels (`error.Canceled` does not happen). `Io.futexWaitTimeout` is outside the model (it has no clock). If no thread can go on and one has not ended, the run is `Zig.Error.deadlock`. 0.15.2's `std.Thread.Mutex` is other std code (`os_unfair_lock` on macOS, the Linux futex); the example `sync` runs on 0.16.0 only (`examples/sync/zig-versions`).

**Diff test.** The Lean side of a concurrent function searches the schedules depth-first (`tests/diff/Diff.lean`'s `searchSchedules`, at most `scheduleCap` runs) for the result that the compiled Zig gave. A schedule with a data race matches any Zig result (the program is undefined; `unspecified.txt`). A search that stops at the cap without Zig's result writes `Zig.Error.capped` (pinned per function in `tests/diff/<ex>/capped.txt`). A search that misses a schedule can only give a false mismatch.

**Proofs over all schedules.** `Conc.Proto.run_sound` (`ZigLean/Conc/Logic.lean`): if `main` and each spawned thread keep a protocol (a global invariant and a ghost value per thread, rely–guarantee), every result of `Sched.run` under every `o` and `fuel` satisfies `main`'s post. In strict mode also no run gives an error (`run_safe`: no data race, no deadlock, also with futex waits). [docs/proofs.md](proofs.md) §Proofs over all schedules. `parallelCounter n` gives `4 * n` under every schedule, and no run of it gives an error (`Proofs/Threads/Counter.lean`); the same for `mutexCounter` with the std `Io.Mutex` (`Proofs/Sync/Mutex.lean`).

**Known limit (a plain write of the same value)**: a plain write to an atomic location becomes a message at the next atomic op only if it changed the bytes; a plain write of the value that the location already has makes no message, so a later read can read an older message than C11 allows. The model then has more results than RC11, never fewer.

**Known limit (fairness)**: RC11 has no progress rule, so a retry loop (a `cmpxchg` loop, a spin-wait) can read the same old message at every turn; such a run ends only at the scheduler's fuel, with no result (as a loop that does not end). A proof of "`run o = .ok v` → `P v`" is not affected; the diff test's search finds the schedule that real hardware took.

**Known limit**: a spin-wait on a flag that another thread sets goes on for every turn of the scheduler in which the other thread does not run: the search reaches a schedule that sets the flag, but a spin-wait without an atomic op in its loop never stops, and `Zig.loop` returns `none` for it.

## Versions

The std code differs between Zig versions: 0.15.2's `growCapacity` has a loop, 0.16.0's does not. So an example with translated std code has a translation per version (`tests/golden/<version>/<ex>/Gen.lean`), and the proofs hold for each of them (CI builds `Proofs/` after `check.sh` writes that version's translation). 0.14.1 does not run `lists`: its `ArrayListUnmanaged` is a different type (`ArrayListAlignedUnmanaged`).
