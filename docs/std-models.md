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
| Failure | Allocation number `Mem.failAt` (from 0, counted in `Mem.allocs`), indices in `Mem.allocPolicy.failures`, and requests above `Mem.allocPolicy.maxBytes` fail. The default is the legacy 1 MiB cap (`Zig.maxAllocBytes`) with no additional failure indices. The function returns `error.OutOfMemory`. An allocation of 0 bytes is no allocation: its pointer has no block (`Zig.zeroAllocPtr`). |
| `resize`, `remap` | Growth of nonzero-size items fails, so a growing `ArrayListUnmanaged` allocates, copies and frees in the model. `remap` to length 0 frees the slice and succeeds; a nonempty slice of zero-size items can change length without allocating. |
| Free | For a nonzero byte count, the pointer must be the start of a live `.heap` block and the length must cover the entire block. Anything else (a double free, a free of a global or of a stack block) throws `.illegal`. `free` records the std slice poison write before freeing, including sentinel bytes, so it races with an unjoined concurrent read. `destroy` uses raw free without that poison write. Zero-byte frees do nothing. |

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

`Mem.allocPolicy` is an explicit environment parameter: `maxBytes` bounds each request,
not total live bytes, and `failures` lists zero-based attempted nonzero allocations that
fail. An attempt advances `allocs` even when its size exceeds the cap. Duplicate failure
indices have no extra effect; indices beyond a finite run are unused. Every finite prefix
of an arbitrary failure trace can be selected, including several or all attempts failing.
Zero-byte allocation does not consume a decision. The model's fresh-address policy,
allocator identity, and unsuccessful resize/remap behavior are unchanged. Raising this cap
does not establish that native malloc has resources or the same address behavior.

`rawAlloc_run`, `create_run` and separation triples quantify over arbitrary `Mem`, including
every policy. `releaseAttempt_run` and `releaseAttempts_run` additionally establish an
actual returned outcome and restore the original heap after every successful allocation
or permitted failure. Their premises are positive request sizes/alignment and the existing
sequential memory invariant; they do not assume allocation success or a fixed resource cap.
The coordinator kernel-checked these definitions at `853cef53211d08a62e368739160f56dea6a3408e`;
[the policy report](allocation-policy-report.json) records the selected local profile and
remaining qualification/review gates.

The diff test runs each function with `TestAllocator` (`tests/diff/common.zig`), which has the same rules. Its first argument is the allocation that fails (legacy null/index), or
`{"fail_at": null, "failures": [0, 2], "max_bytes": 2097152}`. Missing object fields
use legacy defaults. Policy integers in the test transport are nonnegative signed-64-bit
JSON integers; semantic policy indices/caps are Lean naturals. The exact input policy is
part of the differential evidence; each result line has the number of live allocations after the call (`docs/generated-code.md` §Protocol).

## Thread model

`std.Thread.spawn`/`.join` are modelled, like the allocator. A function that reaches a sync op (an atomic op, `Thread.spawn`, `Thread.join`) is a concurrent function: it returns `Zig.ConcM Tgt α` (`ZigLean/Conc/`, `docs/generated-code.md` §Atomics and threads). Its run is a tree: it ends with a result, or it stops at a sync op and goes on from the scheduler's response. The scheduler (`Zig.Sched.run dispatch fuel o main m0`, `ZigLean/Conc/Sched.lean`) runs all threads; they take turns only at sync ops. Plain code between two sync ops runs without a stop: a data race there is `.illegal`, so its order cannot change a result. `Thread.yield` and audited `std.atomic.spinLoopHint` instructions are scheduler opportunities with no fairness or progress guarantee; yield can return `error.SystemCannotYield` (`docs/progress-hints.md`). `Thread.detach` and `Io.futexWaitTimeout` are outside the subset and rejected at translation time (`Air2Lean/Memory.lean`'s `rejectedThreadFn?`), with the reason in the error message.

| Rule | |
|---|---|
| Schedule | At each turn the oracle `o` picks one of the threads that can go on (`o i` modulo the number of options, so every `o` is a schedule). A partial-correctness spec constrains each completed result for every `o` and every `fuel`; a safety proof additionally excludes errors. Neither establishes termination or fairness. Out of fuel is `none`, as a loop that does not end. |
| `spawn(config, f, args)` | A sync op: a new thread with the target `Tgt.f args` (the program's spawn-target type, `docs/generated-code.md`), forked from the caller. It starts at its first turn with `dispatch`. The default `available` policy assumes assignment succeeds and ignores resource settings. Opt-in `--spawn-policy fallible` includes the declared spawn errors and accepts only audited stack requests with a null allocator ([scope](spawn-failure.md)). `args` (the `.{...}` tuple) may have zero or multiple fields; every field is copied into the target in source order. The number and types must match the worker runtime parameters (`Check.lean`). |
| `join(handle)` | A sync op that can go on only when the thread has ended. Requires `handle` to be joined by the thread that spawned it, and not already joined; anything else throws `.illegal`. A thread that ends with a handle it did not join throws `.illegal` (`checkJoinedByChild`); the main thread's end ends the run. |
| Atomic op | A `pick` of the oracle (another thread can run first; the choice below), then the op in `MemM`. |
| RC11 approximation | An atomic location (`Zig.ALoc`) keeps its writes (`Zig.Msg`) in modification order; the block's bytes are the last one's. A read reads any message that is not older than one that happened before it (its clock is `≤` the reader's) or that the thread read or wrote before (`Mem.seen`); option 0 is the newest. A write goes to any place after those messages, not between an RMW and the message it read; option 0 is the end. An RMW, and a successful `cmpxchg`, reads a message with no RMW after it yet and goes right after it. A plain write to an atomic location becomes a message at the next atomic op. The limits below describe additional outcomes the approximation admits. |
| Happens-before | A vector clock per thread (`Zig.VClock`). `spawn` bumps the parent's clock and gives the child a copy; `join` merges the joined thread's clock into the caller's. An acquire read (`acquire`, `acq_rel`, `seq_cst`) adopts the message's release clock (`Msg.relClock`): the writer's clock for a release write, joined along the RMWs after it (the release sequence), empty for a relaxed write. Two accesses are concurrent when neither clock is `≤` the other. |
| Footprint | Every access (`Mem.footprint`) is a byte range, a kind (plain read/write, atomic read/write) and the clock at that time. A failed `cmpxchg` records only an atomic read; a successful one records the read and write, while remaining one scheduler operation. |
| Race check | Two concurrent accesses to the same bytes, at least one a write and at least one plain (not atomic), is a data race: `.illegal`. Two atomic accesses never race: the schedule orders them. |

`ConcM.tryCatch` handles errors in a thread's computation. Across a sync boundary, its handler resumes from the shared memory returned by the scheduler, preserving other threads' intervening writes. Errors raised by the scheduler itself during spawn, join, wait, wake or the thread-end check terminate the run before the continuation and bypass that handler.

The orderings: `monotonic` is relaxed; `unordered` is outside the subset (it has no read-read coherence). `seq_cst` has the rule of `acq_rel`: the model has no global SC order, so it allows more results than RC11 (a proof never depends on a result that RC11 forbids), but a proof that needs the SC order (store buffering with `seq_cst`, Dekker) does not go through. `cmpxchg_weak` adds matching-value read-only failure choices; `cmpxchg_strong` retains success on a matching selected value. Failure uses the failure order, creates no message or RMW write, and may repeat forever. See `docs/weak-cas.md` for the qualified scope and remaining C11 gaps. An atomic location with an overlap of another size throws `.unspecified`.

**Trusted assumption**: the compiled code has no load buffering, as RC11 requires (the model has no promises). LLVM does not promise this for relaxed atomics; no example depends on it. An atomic op's pointee is an integer, an enum, a `bool` or a packed struct (`Io.Condition`'s state): such an op is the integer op on its bits (`Zig.Packed`; `Zig.atomicLoadAs`, `atomicStoreAs`, `atomicRmwAs`, `cmpxchgAs`), and a loaded tag value without a name of an exhaustive enum is `.illegal`. No float or pointer atomic.

**Futex and `std.Io` (0.16.0).** `std.Io` is the model's `Zig.Io` (its `userdata` and `vtable` are not translated). The std sync primitives `Io.Mutex`, `Io.Condition`, `Io.Event`, `Io.Semaphore` (a mutex and a condition) and `Io.RwLock` (atomics on a `usize`, a mutex and a semaphore) are translated from their std code (`examples/<ex>/filter`); the futex under them is the model: `Io.futexWait`, `Io.futexWaitUncancelable` and `Io.futexWake` are sync ops (`Zig.futexWaitC`, `futexWaitCancelableC`, `futexWakeC`, `ZigLean/Conc/Call.lean`). A wait whose `u32` at the address is the expected value waits until a wake at the address (the waiters wake in the order they began to wait); else it goes on. The futex queue is in `Mem` (`Mem.waiters`, `Mem.woken`; `Thread.futexWait`, `Thread.futexWake`), as the thread table is. A wake gives no happens-before edge (the std code reads the value again with an acquire). The model has no spurious wakeup and never cancels (`error.Canceled` does not happen). `Io.futexWaitTimeout` is outside the model (it has no clock). If no thread can go on and one has not ended, the run is `Zig.Error.deadlock`. The example `sync` runs on 0.16.0 only (`examples/sync/zig-versions`).

**`Io.Group` (0.16.0).** A task of a group is a thread of the model (example `iogroup`). `Group.async(g, io, f, args)` is a spawn of `f` that the group records (`Mem.groups`, by the group's address; `Zig.groupAsyncC`); `Group.await` joins each task of the group in the order of its spawn (`Zig.groupAwaitC`). Under the default `available` policy, assignment succeeds, so `Group.concurrent` follows `async`. The `fallible` policy adds caller execution as the `async` fallback and `ConcurrencyUnavailable` for failed `concurrent` assignment ([scope and proof rules](spawn-failure.md)). Cancellation remains outside this foundation, so `Group.cancel` is `await`. A task's args tuple supports the same zero and multiple fields as `Thread.spawn`. The thread that awaits a group must be the one that spawned its tasks (the model's `join` rule); `Io.async`/`Future` are outside the subset.

**`std.Thread` sync primitives (0.15.2).** `Thread.Mutex`, `Thread.Condition`, `Thread.ResetEvent` and `Thread.WaitGroup` are translated from their std code (example `threadsync`, 0.15.2 only). The OS boundary under them is the model:

- `Thread.Futex.wait`/`wake` are the futex sync ops (`Zig.threadFutexWaitC`, `threadFutexWakeC`), as `Io.futexWait`/`futexWake` are in 0.16.0.
- `Thread.Mutex` is other std code on each OS, so its translation differs by OS (`tests/golden/0.15.2/threadsync/Gen-darwin.lean`; `docs/generated-code.md`). On Linux it is `FutexImpl` (atomics and `Thread.Futex`). On macOS it is `DarwinImpl`, one C call of `os_unfair_lock_lock`/`unlock`/`trylock` each; the exporter does not name an `extern` function, so `Thread.Mutex.DarwinImpl.lock`/`unlock`/`tryLock` are the stop points. Their model is the lock's contract, built from the model's ops (`Zig.osUnfairLockC`, `ZigLean/Conc/Call.lean`): the word is 1 while a thread holds the lock; the lock is an acquire `cmpxchg` 0 → 1, and a thread that finds 1 sleeps at the futex; the unlock is a release `xchg` of 0 (an RMW, as the C function is a release `cmpxchg` of the owner to 0) and a wake. `Proofs/Threadsync/Lock.lean` proves `lock` and `unlock` from this model (`docs/proofs.md`).
- `Thread.Futex.Deadline` is translated (`Thread.Condition` and `ResetEvent` wait through it); its clock (`time.Timer.start`, `time.Timer.read`, `Thread.Futex.timedWait`) is reached only with a timeout. The model has no clock, so a call is `.unspecified` at run time (pinned 0 in the diff test), not a rejection.
- 0.15.2 lowers a field read of a local struct (`b.ready` for `var b: Box`) as a load of the whole struct. The model reads the AIR as it is, so that load races with another thread's atomics on the other fields (`.illegal`), though the compiled code reads the one field. `threadsync.handoff` reads through a pointer, which 0.15.2 lowers as a field load.

**Diff test.** The Lean side of a concurrent function searches the schedules (`tests/diff/ScheduleSearch.lean`'s `searchSchedules`, at most `scheduleCap` runs including probes). It first tries a bounded FIFO of sparse oracle prefixes, then resumes depth-first enumeration for the result that the compiled Zig gave. A schedule with a data race matches any Zig result (the program is undefined; `unspecified.txt`). A search that stops at the cap without Zig's result writes `Zig.Error.capped` (pinned per function in `tests/diff/<ex>/capped.txt`). A capped search is not a demonstrated result match: `scripts/diff.sh` accepts it only within its separately pinned count (default 0). An exhausted search with neither a match nor a data race returns the first schedule's result for comparison.

**Captured arguments.** Empty tuples become `Unit`, one field retains its scalar target type, and multiple fields become a right-associated product. Pointer fields retain pointer identity; the tuple copy does not copy the pointed-to bytes or grant ownership. In programs with an empty or multi-field capture, the generated `Tgt.spawnInit P target ghost` names the child protocol obligation for the entire capture. Proofs explicitly split private heaps with `Owned.fork`, or justify sharing through the global invariant (for example shared atomics). Ordinary aliased writes still fail the model's race check.

Existing one-field programs keep their generated source shape and express the same child obligation through `Conc.WP.spawnC` and the protocol directly.

The checker compares types across the caller and worker's separate AIR type tables. It permits a mutable pointer to become const and a pointer with sufficient alignment to satisfy a weaker alignment. Nested pointee and aggregate field types must match exactly. Other implicit `@call` coercions require an explicit source cast before capture. Thread workers returning `void`, `noreturn`, or unsigned `u8` are supported; Group workers must return `void` or `noreturn`. Worker error unions are rejected because the std panic/error handling at the worker boundary is not yet modeled.

**Proofs over all schedules.** `Conc.Proto.run_sound` (`ZigLean/Conc/Logic.lean`): if `main` and each spawned thread keep a protocol (a global invariant and a ghost value per thread, rely–guarantee), every result of `Sched.run` under every `o` and `fuel` satisfies `main`'s post. In strict mode also no run gives an error (`run_safe`: no data race, no deadlock, also with futex waits). [docs/proofs.md](proofs.md) §Proofs over all schedules. `parallelCounter n` gives `4 * n` under every schedule, and no run of it gives an error (`Proofs/Threads/Counter.lean`); the same for the `sync`, `iogroup` and `threadsync` examples over the translated std sync primitives ([docs/proofs.md](proofs.md) §Proved examples).

**Known limit (a plain write of the same value)**: a plain write to an atomic location becomes a message at the next atomic op only if it changed the bytes; a plain write of the value that the location already has makes no message, so a later read can read an older message than C11 allows. The model then has more results than RC11, never fewer.

**Known limit (read views across synchronization)**: `Mem.seen` records only each thread's own observations; release/acquire transfers clocks, but does not transfer those observed messages to the acquiring thread. With initially zero `x` and `y`, three parallel threads can therefore run: A stores `x := 1` relaxed; B reads `x = 1` relaxed and stores `y := 1` release; C reads `y = 1` acquire and then reads `x = 0` relaxed. B's read happens before C's read, so RC11 read-read coherence forbids the final zero. The model can allow it because B's relaxed read did not acquire A's writer clock, and C has no own observation of `x`. Proofs about this model must cover that additional atomic outcome; they cannot rely on read-read coherence transferred through another location's release/acquire.

**Known limit (fairness)**: RC11 has no progress rule, so a retry loop (a `cmpxchg` loop, a spin-wait) can read the same old message at every turn; such a run ends only at the scheduler's fuel, with no result (as a loop that does not end). A proof of "`run o = .ok v` → `P v`" is not affected; the diff test's search finds the schedule that real hardware took.

**Known limit**: a spin-wait on a flag that another thread sets goes on for every turn of the scheduler in which the other thread does not run: the search reaches a schedule that sets the flag, but a spin-wait without an atomic op in its loop never stops, and `Zig.loop` returns `none` for it.

## Versions

The std code differs between Zig versions: 0.15.2's `growCapacity` has a loop, 0.16.0's does not. So an example with translated std code has a translation per version (`tests/golden/<version>/<ex>/Gen.lean`), and the proofs hold for each of them (CI builds `Proofs/` after `check.sh` writes that version's translation). 0.14.1 does not run `lists`: its `ArrayListUnmanaged` is a different type (`ArrayListAlignedUnmanaged`).
