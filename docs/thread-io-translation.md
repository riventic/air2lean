# Translating `std.Thread`, the sync primitives and `std.Io` from OS primitives (design + spike)

Status: design and feasibility spike, Zig 0.16.0, `x86_64-linux` and `aarch64-macos`, as written
on 2026-10-09 (approved: OS primitives as the only trusted base). The branch names below record
where each piece was then; most have since merged. The phases it plans are implemented in
[os-threads.md](os-threads.md) (T2) and [thread-specs.md](thread-specs.md) (T3).

**Principle (user decision, 2026-10-08).** Only base OS primitives get trusted models. Std code
above them is translated from its AIR and proved. The allocator track does this already: OSM-01
trusts `posix.mmap`/`munmap`/`mremap`, `AllocSpec` is the generic vtable spec, and
`--allocator-model translated` is the dual mode (`docs/allocator-model.md` on
`codex/alloc-translated-p1`). This document applies the same plan to threads, futexes and
`std.Io`.

**Why.** The concurrency audit (`codex/audit-concurrency`, `docs/architecture-audit/concurrency.md`
findings 1, 2, 5, 6, 8, 12) and the models audit (`codex/audit-models`, rows S10–S31, T02, T03, Z05,
Z08, divergences D-IO-CANCEL, D-IO-INLINE, D5, D6) show that the hand-written models diverge from
std 0.16.0 in four ways:

* `Group.async` always spawns a thread. Std runs the task inline in four cases: when
  `busy_count >= async_limit`, when allocation fails, when spawning fails, and under
  `single_threaded`.
* `cancel` never yields `error.Canceled`.
* Futex waits have no spurious or `EINTR` return, and wakes are FIFO.
* `os_unfair_lock` has no owner.

All four come from cutting at the `std.Io` vtable instead of at the OS.

## 1. What std 0.16.0 bottoms out in

Sources are under `/opt/dev/air2lean-build/zig-0.16.0-src/lib/std`. In 0.16.0, `std.Thread` no
longer has `Mutex`, `Condition`, `RwLock`, `WaitGroup`, `Futex` or `ResetEvent`. The sync
primitives are `std.Io.{Mutex, Condition, Event, Semaphore, RwLock}` (`Io.zig:1587–1860`,
`Io/Semaphore.zig`, `Io/RwLock.zig`), and they reach the OS **only through the Io vtable** slots
`futexWait`, `futexWaitUncancelable` and `futexWake`. The only `WaitGroup` is private to
`Io.Threaded` (`Io/Threaded.zig:18592`). It is reached through `Threaded.join`/`deinit`. Std
`Io.Threaded` also has a private, vtable-free copy of the mutex, condition and event:
`mutexLock`/`mutexUnlock` (`:18722`, `:18741`), `condWait`/`condSignal`/`condBroadcast`
(`:18652`–`:18692`) and `eventWait`/`eventSet`. It uses them for its own pool, and they call
`Thread.futexWait*` directly.

### 1.1 Layers

```
client code ── Io.Mutex/Condition/Event/Semaphore/RwLock ──┐  (pure atomics + io.futex*)
            ── Io.Group.async/concurrent/await/cancel ──────┤
            ── io.async / Future.await / cancel ───────────┤  io.vtable.<slot>(io.userdata, …)
            ── io.sleep / Clock.now ───────────────────────┘
Io.Threaded (vtable impl): groupAsync/groupConcurrent/groupAwait/groupCancel, async/concurrent/
  await/cancel, futexWait*/futexWake, sleep, now, recancel/swapCancelProtection/checkCancel
  ├─ pool: mutexLock/condWait/condSignal on t.mutex/t.cond, run_queue, busy_count, async_limit,
  │        WaitGroup (pool size), worker() threads, Group.Task / Future heap objects (t.allocator)
  ├─ cancelation: per-worker Thread.status state machine (8 states, packed in usize), Syscall.start/
  │        finish/checkCancel, cancelAwaitable, signalCanceledSyscall (SIG.IO to the worker),
  │        waitForCancelWithSignaling (timed futex wait with exponential backoff)
  └─ Threaded.Thread.futexWaitInner / futexWake  ──►  OS
std.Thread.spawn/join/detach/yield/getCpuCount/getCurrentId  ──►  OS
```

### 1.2 OS primitives and exact call sites (0.16.0)

`Th` = `Io/Threaded.zig`, `T` = `Thread.zig`, `L` = `os/linux.zig`, `C` = `c.zig` / `c/darwin.zig`.

| Primitive | Linux x86_64, no libc (std `LinuxThreadImpl`) | macOS aarch64 (libc, std `PosixThreadImpl`) | Used by |
|---|---|---|---|
| futex wait | `L.futex_4arg(ptr, {.cmd=.WAIT,.private=true}, expect, ts)` at `Th:987`. Results: `SUCCESS`, `INTR` (spurious), `AGAIN` (≠ expect), `INVAL`, `TIMEDOUT` are all "return"; `FAULT` → `recoverableOsBugDetected`. Also `L.futex_4arg(&child_tid, {.WAIT,.private=false}, tid, null)` in `T:1561` (join) | `c.__ulock_wait2(UL{COMPARE_AND_WAIT, NO_ERRNO}, ptr, expect, timeout_ns, 0)` at `Th:1007` (`darwin_supports_ulock_wait2`, macOS ≥ 11, `Th:14753`). `__ulock_wait` (µs timeout) at `Th:1012` otherwise. `-INTR`/`-FAULT`/`-TIMEDOUT` → return | `Thread.futexWaitInner` (`Th:940`) ⇐ `Th.futexWait`/`futexWaitUncancelable` vtable slots, `mutexLock`, `condWait`, `eventWait`, `groupAwait`, `await`, `waitForCancelWithSignaling` |
| futex wake | `L.futex_3arg(ptr, {.WAKE,.private=true}, min(n, maxInt(i32)))` at `Th:1128` | `c.__ulock_wake(UL{COMPARE_AND_WAIT, NO_ERRNO, WAKE_ALL = n>1}, ptr, 0)` in a loop on `INTR`/`CANCELED`; `NOENT` = nobody woken (`Th:1147`) | `Thread.futexWake` (`Th:1105`) |
| thread create | `posix.mmap` (stack+TLS+instance, `T:1463`), `system.mprotect` (guard, `T:1485`), `L.tls.prepareArea` (`T`, TLS image), `L.clone(entryFn, stack, CLONE_{THREAD,DETACHED,VM,FS,FILES,PARENT_SETTID,CHILD_CLEARTID,SIGHAND,SYSVSEM,SETTLS}, instance, &parent_tid, tls, &child_tid)` (`T:1522`). `L.clone` is the naked-asm trampoline `os/linux/x86_64.zig:83` | `std.heap.c_allocator.create(Args)` (**malloc**, `T:746`), `pthread_attr_init`/`setstacksize`/`setguardsize`/`destroy`, `c.pthread_create(&h, &attr, entryFn, args)` (`T:770`) | `Thread.spawn` (`T:344`) ⇐ user code, `Th.async`/`concurrent`/`groupAsync`/`groupConcurrent` (`Th:2112`, `:2164`, `:2208`, `:2272`) |
| thread join | **translated std code**: loop of `child_tid.load(.seq_cst)` + futex WAIT on `&child_tid` until the kernel's `CHILD_CLEARTID` store of 0 and wake, then `posix.munmap(mapped)` (`T:1555–1575`) | `c.pthread_join(h, null)` (`T:798`) | `Thread.join` |
| thread detach / exit | `completion.swap(.detached)`. A detached thread exits through `ThreadCompletion.freeAndExit`: `set_tid_address(null)`, `sigprocmask(BLOCK, all)`, then inline asm `munmap(own stack)` + `exit(0)` (`T:1149–1415`) | `c.pthread_detach(h)` (`T:789`) | `Th` detaches every pool worker (`Th:2120`, …) |
| thread id | `L.gettid()` cached in `threadlocal tls_thread_id` (`T:1123–1130`) | `c.pthread_threadid_np(null, &id)` (`T:666`) | `Thread.getCurrentId`, `Th.worker` |
| self handle | — | `c.pthread_self()` (`Th:1741`) | `Th.worker` (signal target) |
| CPU count | `posix.sched_getaffinity(0)` → `CPU_COUNT` (`T:1134`) | `sysctlbyname("hw.logicalcpu")` (`T:730`) | `Threaded.init` → `async_limit = cpu_count - 1` (`Th:1634`) |
| yield | `L.sched_yield()` via `system.sched_yield` (`T:385`) | `c.sched_yield()` | `Thread.yield` |
| clock | `L.clock_gettime`: vDSO function pointer loaded `.unordered` and called indirectly, falling back to `syscall2` (`L:1937–1960`) | `c.clock_gettime` | `Th.nowPosix` (`Th:11428`) ⇐ `now` slot, `Timeout.toDurationFromNow` |
| sleep | `L.clock_nanosleep(clock, flags, &ts, &ts)` loop on `INTR` with `Syscall.checkCancel` (`Th:11598`) | `c.clock_nanosleep` if present, else `c.nanosleep` (`Th:11663`) | `Th.sleep` slot |
| signals (cancelation) | `posix.sigaction(.IO/.PIPE, doNothingSignalHandler)` in `Threaded.init`/`deinit` (`Th:1660`, `:1715`). `L.tgkill(pid, tid, .IO)` (`Th:1290`), with `L.getpid` cached in `t.pid` | `c.pthread_kill(handle, .IO)` (`Th:1277`) | `Thread.signalCanceledSyscall`: interrupts a worker blocked in a cancelable syscall (futex wait, sleep, I/O) so that it returns `EINTR` |
| signal stack | `posix.sigaltstack` into `threadlocal signal_stack` when `std.options.signal_stack_size` is set (`T:1724`) | same | `Thread.callFn` → `maybeAttachSignalStack` |
| TLS | `threadlocal var` `Th.Thread.current` (`Th:893`), `tls_thread_id`, `signal_stack`. Every exported use is a `runtime_nav_ptr` | same (`__thread`/TLV) | cancelation, `swapCancelProtection`, ids |
| `os_unfair_lock_*` | — | declared (`c.zig:11331`), **not used** by 0.16.0 std threads or Io | only 0.15.2 `Thread.Mutex.DarwinImpl` (THR-06, audit finding 5) |

The 0.16.0 `std.Io` concurrency layer reaches no `sched_yield` and no `os_unfair_lock`.
`Thread.yield` is user-facing only. `parking_futex`/`parking_sleep` (`Th:17235–17750`) are used
only on Windows, NetBSD and illumos, so they are out of scope.

## 2. Spike: export and translate with the hand models bypassed

### 2.1 Setup

The programs are in `scratch/spike/` of worktree `.claude/worktrees/spike-thread-io`. They are
not committed.

| Program | Entry points | What it exercises |
|---|---|---|
| `thread_mutex.zig` | `spawnMutex`, `spawnOnly`, `yieldOnce` | `std.Thread.spawn`/`join`/`yield` and the vtable-free `Io.Threaded.mutexLock`/`mutexUnlock` |
| `io_client.zig` | `ioMutex(io)`, `groupClient(io)`, `cancelClient(io)`, `futureClient(io)`, `sleepClient(io)` | clients of **any** `Io`: `Io.Mutex`, `Group.async/await/cancel`, `io.async`/`Future.await`, `io.sleep` through the vtable |
| `threaded.zig` | `threadedGroup()` | `Io.Threaded.init(page_allocator)`, `Group.async` ×2, `await`, `async`, `cancel`, `deinit` (pool, internal `WaitGroup`) |

The setup has five steps:

* **Export.** AIR was exported with the patched 0.16.0 compiler that has the P0 exporter fix
  (vtable global initializers, container layouts): `/tmp/a2l-p0/zigs/zig-air-0.16.0`, built from
  `codex/alloc-translated-p0` `zig-patch/air-json/json.zig`. The flags were
  `-OReleaseSafe -fno-error-tracing -mcpu=baseline -fno-emit-bin`, for both targets. The
  extern-name exporter (`codex/extern-calls`, built at `~/.cache/air2lean/ext/zig-air-0.16.0`)
  was used once, to confirm the extern callee form: `"extern": "__ulock_wait2"`,
  `"pthread_join"`, `"sched_yield"`, plus an `externs` table with library and cc.
* **Closure.** A call graph plus function-value closure from the entry points, stopping at
  `debug.FullPanic`. `threaded.zig` was also pruned at the `Io.Threaded.io()` vtable literal,
  with the used slots as extra roots. The full vtable pulls in all ~110 slots (file system,
  network, process): 1677 functions (Linux) and 1486 (macOS), against 164 and 139 pruned.
* **Bypass.** `bypass.py` renames the `Thread.*`/`Io.*` functions and the `Thread`/`Io` struct
  types (adding a `z` prefix). No `StdModels` thread or Io row matches, and neither does the
  `Ty.thread`/`Ty.io` specialization (`Air/Json.lean`). The translator then sees the real std call
  graph. This stands in for a future `--thread-model translated`.
* **Translator.** `air2lean --diagnostics-json --diagnostic-limit 4096 --allocator-model translated`,
  built from `codex/alloc-translated-p1` `eb85389a`. That build adds the P1 admissions: opaque
  context casts, `@returnAddress` oracle, integer pointer constants, `unordered` loads,
  pointer-valued atomic loads and strong cmpxchg.
* **Comparison.** Each program also ran in std mode (hand models active).

### 2.2 Results (functions whose local check passes / total in the closure)

| Closure | std mode (hand models) | translated + bypass |
|---|---|---|
| thread_mutex, Linux | 39 / 57 | **42 / 57** |
| thread_mutex, macOS | 21 / 45 | 24 / 45 |
| io_client, Linux | 40 / 59 | **43 / 59** |
| io_client, macOS | 26 / 49 | 28 / 49 |
| threaded (pruned), Linux | 115 / 164 | **124 / 164** |
| threaded (pruned), macOS | 80 / 139 | 86 / 139 |

No program elaborates end to end yet. That was expected, as it was for the allocator spike
before P1. Both sides of the split are informative.

**Accepted already (Linux, translated + bypass).** The cores below pass the local check unchanged:

* the whole mutex/condition/event/WaitGroup layer of `Io.Threaded`: `mutexLock`, `mutexUnlock`,
  `condWait`, `condSignal`, `condBroadcast`, `eventWait`, `eventSet`, `WaitGroup.start`,
  `finish`, `wait`, `value`;
* the vtable-side `Io.Mutex.lock`, `lockUncancelable` and `unlock`, `Io.futexWait*`, `futexWake`
  and `Io.sleep`;
* `Io.Group.await` and `Io.Group.cancel` (the token check and the vtable call);
* `Threaded.Thread.futexWaitInner` (its `EINTR`/`EAGAIN`/`TIMEDOUT` switch), `futexWake` and
  `Group.waitForCancelWithSignaling`;
* `groupAsyncEager`, `timestampToPosix`, `Thread.spawn`, `Thread.join`,
  `LinuxThreadImpl.join` (the `child_tid` futex loop), `detach`, `getCpuCount`, `Thread.yield`;
* the `os.linux.futex_3arg`, `futex_4arg`, `mmap`, `munmap`, `mprotect`, `sched_yield`,
  `set_tid_address`, `sigprocmask` and `sigaltstack` wrappers;
* all client entry points except `futureClient`.

**Rejections, grouped by blocker.** Counts are from the Linux pruned `threaded` closure unless
noted.

| # | Blocker | Diagnostics | Where | Fix (phase) |
|---|---|---|---|---|
| B1 | `noreturn` "in memory": a `noreturn`-typed union variant (`Io.Terminal.Mode.windows_api: noreturn` on non-Windows; the type is reached through `Threaded.stderr_mode`) and `?noreturn` (`Thread.futex_waiter`) | 89 + 2 | `Threaded.init`, `deinit`, `join`, `groupAsync`, `Group.Task.start`, `cancelThreads`, `cancelAwaitable`, `signalCanceledSyscall`, `Syscall.finish` | Treat a `noreturn` field or variant as uninhabited and zero-sized (T1, small). It masks other diagnostics in those functions. |
| B2 | OS syscall layer: inline asm `syscall` with a `memory` clobber (M21) in `os.linux.x86_64.syscall0..6`; `os.linux.clone` (naked trampoline, "indirect call through a constant"); `tls.prepareArea`; `freeAndExit` (asm munmap+exit) | 7 + 1 + 1 + 1 | all Linux closures | **Do not translate.** Cut at the named `os.linux.*` wrapper (§3), as `posix.mmap` is cut above `syscall6`. |
| B3 | macOS extern functions: `AIR_DECODE constant of unsupported type fn (…) callconv(.c)`. Every libc call (`__ulock_wait2`, `__ulock_wake`, `pthread_create`/`join`/`detach`/`self`/`kill`/`threadid_np`, `sched_yield`, `sysctlbyname`, `sigaction`, `malloc`/`free` via `c_allocator`) | 19 distinct | all macOS closures | `codex/extern-calls` (exporter names externs) + binding `extern:<sym>` to OS rows (T0) |
| B4 | `c.pthread_t` is an opaque type (`TYPE_FAILURE`) | 85 (macOS) | `Thread.spawn`, `join`, `Syscall.*` | Opaque handle type as an abstract `ThreadHandle` value (T1) |
| B5 | TLS: `runtime_nav_ptr` of `threadlocal` globals | 5 | `Syscall.start` and `worker` (`Thread.current`), `LinuxThreadImpl.getCurrentId`, `maybeAttachSignalStack` | Batch7 **C02** (`Zig.tlsPtr`, per-thread instances) already admits this; it is on `codex/roadmap-batch7`, not merged |
| B6 | Tuples in memory (`Ty.tuple`): spawn/async argument tuples copied into `Instance`/`Task` | 10 | `spawn.Instance.entryFn`, `Group.async.TypeErased.start`, `io.async.TypeErased.start` | Tuple storage layout (T1, medium) |
| B7 | Function-pointer constants to nested generic functions ("global function initializer must be its named constant function block") | 2–3 | `LinuxThreadImpl.spawn` (`&Instance.entryFn`), `Group.async` (`&TypeErased.start`), `io.async` | Translator: allow a function constant whose block is a nested instance (T1, small) |
| B8 | `*Threaded` recovered from `?*anyopaque` userdata ("recovering a symbolic error pointer … needs unsupported storage provenance"). `Threaded` holds error storage (`cpu_count_error: ?CpuCountError`) | 8 | every vtable slot of `Threaded` (`futexWait`, `futexWake`, `groupAsync`, `groupAwait`, `groupCancel`, …), `TypeErased.start` | Extend P1's opaque-context recovery from error-free pointees to finite error storage (T1, medium; shared with arena `ctx`) |
| B9 | Pointer punning: `Group.status()` reinterprets `*atomic.Value(?*anyopaque)` (`Io.Group.token`) as `*atomic.Value(Group.Status)` (packed `usize`); `Group.awaiter()` reinterprets `state: usize` as `**atomic.Value(u32)`; `Task.create`/`contextPointer` cast `alignedAlloc` bytes to `*Task` with a trailing context; `@fieldParentPtr("runnable", r)` | 8 + 3 | `Group.*`, `Task.*`, `Future.*` | Same header-punning and parent-recovery provenance as arena P5. It also needs an atomic word that holds a pointer **or** an integer (int↔ptr messages, provenance kept). T1, large |
| B10 | `noreturn` callee that is not a panic handler (`freeAndExit` in `entryFn`'s defer) | 1 | Linux `spawn.Instance.entryFn` | Becomes the OS row "detached thread exit" (§3) |
| B11 | `Io.AnyFuture` opaque type | 4 | `futureClient`, `Future(T).await` | Opaque pointee as an abstract handle (as B4) |
| B12 | `posix.mmap` translated file present while P1 has a built-in row ("conflicts with built-in std model") | 1 | Linux closures | Spike artifact: the closure must stop at `posix.mmap` (P1 already cuts there) |

Not yet observed, because B1, B8 and B9 mask them, but certain from the source:

* weak `cmpxchg` of a **pointer** (`worker_threads` push in `worker`). P1 admits only strong
  pointer cmpxchg and loads.
* `fetchOr`/`fetchXor`/`fetchSub` on packed `struct(usize)` atomics (`Thread.Status`,
  `Group.Status`, `Future.Status`).
* `Thread.PackedPtr` pack/unpack (`@intFromPtr` → bit-packed → `@ptrFromInt`).
* `std.SinglyLinkedList` intrusive nodes.
* the `@returnAddress` passed into `t.allocator`. P1's oracle already covers it.

**Std mode vs. bypass.** Std mode is *worse* on the same closures, because the hand rows cut the
call graph in the middle of std (`Io.futexWait` is modelled, but `Threaded.futexWait` is not
reachable as a model). It is not a usable baseline for translated `Io.Threaded`.

## 3. Proposed trusted base (explicit premises)

The cut sits at the **named OS wrapper** (Linux: the `os.linux.*` function above `syscallN`;
macOS: the `extern "c"` symbol). Every row is version-qualified (`0.16.0`) and active only in
translated thread mode. Each primitive is a `SyncOp` (a scheduling point) of the existing
`ZigLean/Conc` scheduler, over the same `Mem` and RC11-approximate memory model
(`ZigLean/Mem/Thread.lean`). New premise IDs follow `[A-Z]{3}-\d{2}`.

| Premise | Primitive(s) (Linux / macOS) | Model (new `ZigLean/Os/Thread.lean`, `Os/Futex.lean`, `Os/Clock.lean`) |
|---|---|---|
| **OSF-01** futex wait | `os.linux.futex_4arg` with `cmd=.WAIT` (private or shared) / `__ulock_wait2`, `__ulock_wait` with `COMPARE_AND_WAIT\|NO_ERRNO` | **Atomic read** of the u32 at `p`, with a footprint and `observe` (fixes audit finding #14). If it differs, return `EAGAIN`. Else `SyncOp.wait p expected`, after which the **oracle** picks among woken (`0`), spurious/`EINTR` (`-EINTR`), and, with a timeout, `ETIMEDOUT`. The spurious return is always allowed (batch7 C05 `spuriousWake`), which subsumes signal delivery. No happens-before edge from the waker. A bad pointer is `.illegal` (std's `FAULT` → `recoverableOsBugDetected`). Other ops or flags are rejected. |
| **OSF-02** futex wake | `os.linux.futex_3arg` with `cmd=.WAKE` / `__ulock_wake` (`WAKE_ALL` flag) | `SyncOp.wake p n` that wakes an **oracle-chosen** subset of size `min n waiters` (audit finding #6). Linux returns the count. macOS returns `0` or `-ENOENT`, and `-EINTR` may be returned spuriously (std loops). |
| **OST-01** thread create | Linux: `os.linux.clone` with exactly std's flag set; `tls.prepareArea` is part of the row. macOS: `pthread_create` (+ `pthread_attr_*` as no-op rows) | `SyncOp.spawn (entryFn, arg)`. The entry is a **constant** function pointer per call site, so `Emit` builds the spawn-target dispatcher as today. There is a happens-before edge parent→child, and the child gets a fresh TLS instance (batch7 C02). Failure is an oracle choice: `EAGAIN`/`ENOMEM` → `ThreadQuotaExceeded`/`SystemResources` under `fallible`. Linux `PARENT_SETTID` writes the tid. **Exit** (the child returns from `entryFn`) does Linux `CHILD_CLEARTID`: a **release** store of `0` to `ctid` that carries the child's final clock, then a wake-all on `ctid`. Std's translated `join` (seq_cst load loop + futex) then gets the join edge, and the hand `SyncOp.join` is not needed on Linux. |
| **OST-02** join/detach/exit | macOS: `pthread_join` (= `SyncOp.join`, with edge), `pthread_detach`. Linux: `ThreadCompletion.freeAndExit` (asm munmap + exit) | Detached exit frees the thread's stack mapping and ends the thread (batch7 C07 detach). A frame-end footprint is recorded over the stack (audit finding #3). Joining a detached or already-joined handle is `.illegal` (std: `unreachable`). |
| **OST-03** ids, handles, CPU count | `gettid`, `getpid`, `sched_getaffinity` / `pthread_self`, `pthread_threadid_np`, `sysctlbyname("hw.logicalcpu")` | Ids are distinct per live thread (oracle values). The CPU count is an **environment parameter** `cpus ≥ 1`, so it is a theorem premise, never a constant. It determines `async_limit = cpus - 1`, so inline `Group.async` falls out of the translated code (D-IO-INLINE). |
| **OSY-01** yield | `os.linux.sched_yield` / `sched_yield` | `SyncOp.yield`, always succeeds |
| **OSK-01** clock | `os.linux.clock_gettime` (above the vDSO) / `clock_gettime` | Oracle timestamp per clock. `.awake`/`.boot` are monotone per clock across the run (TMR-02 timed scheduler, opt-in). In the default mode the value is arbitrary but monotone. |
| **OSK-02** sleep | `os.linux.clock_nanosleep` / `clock_nanosleep`, `nanosleep` | `SyncOp.yield`, then return `0` or `EINTR` (oracle). There is no duration guarantee unless TMR-02 is on. |
| **OSG-01** cancel signals | `sigaction(.IO/.PIPE, doNothing)`, `tgkill`/`pthread_kill(.IO)`, `sigprocmask`, `sigaltstack` | Handler installation has no memory effect. `kill(t, .IO)` sets a **pending interrupt** on `t`, so its current or next OSF-01/OSK-02 call returns `EINTR`. This is the only liveness-relevant part: cancelation of a blocked worker terminates. For partial correctness the oracle `EINTR` of OSF-01 already over-approximates it. |
| **OSM-01** (existing) | `posix.mmap`/`munmap`/`mremap` | Thread stacks (Linux) and `Threaded`'s `page_allocator` |
| **OSM-02** *(decision needed)* | macOS `malloc`/`free`/`malloc_size` (`std.heap.c_allocator`, reached by `PosixThreadImpl.spawn` for the args box) | Fresh block or `null`, the same shape as OSM-01 at byte granularity. The alternative is to keep `c_allocator` out of the trusted base and treat macOS spawn as unprovable until a libc model exists. |

**What attaches where in `ZigLean/Conc`.** The current `SyncOp` constructors (`yield`, `choose`,
`pick`, `spawn`, `join`, `wait`, `wake`; `Conc/Basic.lean`) suffice. The OS rows are thin `CM`
wrappers (`Conc/Call.lean` style) that sequence `pick`/`choose` for the oracle outcomes with the
existing op. `Sched.run`'s thread table, `Mem.waiters`, `Mem.woken` and the vector clocks stay as
they are. Four things are new:

1. A thread-exit hook that performs Linux `CHILD_CLEARTID` (store + wake-all) or marks the
   pthread done.
2. A pending-interrupt bit per thread (OSG-01).
3. The waker-subset oracle in `Thread.futexWake`.
4. The environment record (`cpus`, spawn policy, TMR flag) as an explicit `Sched.run` argument
   (audit finding #7).

The hand `osUnfair*C`, `groupAsyncC`, `groupAwaitC`, `groupCancelC`, `futexWaitC`,
`futexWaitCancelableC`, `futexWakeC`, `threadFutex*C`, `spawnC` and `joinC` become std-mode-only
legacy.

## 4. Proof plan: generic specs, translated implementations, clients via the specs

### 4.1 Specs (`ZigLean/Sep/` style, parallel to P3 `AllocSpec`)

* **`FutexSpec`.** The contract of the two vtable-free functions `Threaded.Thread.futexWaitInner`
  and `futexWake`. They are proved once from OSF-01/02 per target.
  * Wait: if the location is an atomic u32 that the caller may read, it returns (any number of
    times) with no postcondition on the word. With `uncancelable = false` it may return
    `Canceled` only if the current task has a pending, unblocked cancel request.
  * Wake: the requested number of waiters becomes runnable.
  * Neither function adds a happens-before edge.
  * Lemma: on the same target, `futexWaitInner` is equivalent to OSF-01 plus the cancelation
    bracket (`Syscall.start`/`finish`).
* **`MutexSpec m R`.** The CSL lock spec: `lock` gives `R` and the holder token, and `unlock`
  takes them back, with acquire/release edges. `ZigLean/Conc/Lock.lean` already proves this
  for the *translated* `Io.Mutex` against the hand futex (THR-05). The work is to re-derive it
  on `FutexSpec`, which allows spurious returns. Std's loops re-check, so the proof shape stays
  and only the wait step gains a "spurious → loop" case. `Threaded.mutexLock`/`mutexUnlock` have
  the same code, so the same theorem applies through `FutexSpec` directly. Corresponding specs:
  `CondSpec` (Mesa semantics, spurious return allowed), `EventSpec`, `WaitGroupSpec`
  (`Threaded.WaitGroup`: `wait` returns only after `finish` matched every `start`, with an
  edge).
* **`IoSpec vt ud I S`.** The `std.Io` analogue of `AllocSpec`. It is a family of per-slot
  triples over an implementation invariant `I` (which owns `ud`'s state and every `Group.token`
  and `Group.state` word), for the slot subset `S` = {`futexWait`, `futexWaitUncancelable`,
  `futexWake`, `groupAsync`, `groupConcurrent`, `groupAwait`, `groupCancel`, `async`,
  `concurrent`, `await`, `cancel`, `recancel`, `swapCancelProtection`, `checkCancel`, `now`,
  `sleep`}. Clients see abstract predicates: `Group g Ts` (pending tasks with their
  postconditions), `Fut f Q`, `CancelState`.
  * **`groupAsync`**: three-way nondeterminism, which matches std's documented semantics and
    removes D-IO-INLINE by construction. Either `start(ctx)` ran to completion **before**
    return (eager), or the task is pending in `g` and runs on another thread, or it is deferred
    and runs no later than `await`/`cancel`. A client may not assume that progress before
    `await` comes from a spawned task.
  * **`groupConcurrent`**: a concurrent thread, or `ConcurrencyUnavailable` with nothing run.
  * **`groupAwait`**: all tasks done, with edges from each task's end. It may also return
    `Canceled` when the awaiting task was canceled, after all tasks are done.
  * **`groupCancel`**: every pending task gets a cancel request. Each task's next unblocked
    cancelation point may return `Canceled`, and the call returns when all tasks are done
    (D-IO-CANCEL).
  * **`futexWait`**: as `FutexSpec`, plus `Canceled`.
  * **`now`**: monotone for `.awake`/`.boot`.
  * **`sleep`**: returns, or `Canceled`.
  * **Other slots** (file, net, process, batch): outside `S`. A call to them in translated mode
    is a fail-closed `unsupported` outcome until E03 (`codex/roadmap-io-boundary`) adds their
    specs.
  * **Proved once for every `vt ⊨ IoSpec`**: the `std.Io` wrappers (`Io.futexWait*`,
    `Io.Group.*`, `io.async`, `Future.await`/`cancel`, `io.sleep`, `Io.Mutex`/`Condition`/
    `Event`/`Semaphore`/`RwLock`), exactly as P3 proves the `mem.Allocator` wrappers for any
    `vt ⊨ AllocSpec`.

### 4.2 Implementations proved against the specs

1. `Thread.spawn`/`join`/`detach`/`yield` (translated) ⊨ `ThreadSpec`: spawn runs `f(args)` on
   a new thread with an edge, and join gets an edge from the thread's end. The proof is from
   OST-01/02 and OSF-01 (the Linux join is a futex loop on `child_tid`) and OSM-01 (stack). On
   macOS it also needs OSM-02 for the args box.
2. `Threaded.mutexLock`/`condWait`/`eventWait`/`WaitGroup` ⊨ `MutexSpec`/`CondSpec`/
   `EventSpec`/`WaitGroupSpec` via `FutexSpec`.
3. **`Io.Threaded` ⊨ `IoSpec`**, for the slots in `S`. This is the hard part. The invariant
   covers:
   * the pool: `t.mutex` protects `run_queue`, `busy_count` and the `wait_group` count;
     `busy_count ≤` the number of workers; every queued runnable is a live `Task` or `Future`
     block from `t.allocator`;
   * the per-worker `Thread.status` cancelation state machine (8 states, CAS transitions in
     `cancelAwaitable`/`Syscall.*`);
   * `Group.Status{num_running, have_awaiter, canceled}` against the multiset of pending tasks
     of `g`, with the awaiter's `num_completed` handshake;
   * `Future.Status` (`pending`, `pending_awaited`, `pending_canceled`, `done`) with the packed
     thread pointer.

   The eager paths (allocation failure, `busy_count ≥ async_limit`, spawn failure) are exactly
   the IoSpec "ran before return" branch.
4. `Io.Threaded.global_single_threaded` (`async_limit = .nothing`, `.failing` allocator) ⊨
   `IoSpec`. This is mostly the eager branch. Its `futexWait` without a timeout is an assert
   failure, which the spec must allow as "does not return".

### 4.3 Clients

A translated function with an `io: Io` parameter is proved against `∀ vt ud I, IoSpec vt ud I S →
…` (the W1 fix from the models audit: the Io identity becomes an explicit premise, not a silently
substituted model). The examples `sync`, `iogroup` and `threads` and `Proofs/{Sync,Iogroup,Threads}`
are ported to state this premise. A concrete corollary for `Io.Threaded` follows from (3).

### 4.4 What gets replaced (migration, dual mode)

* **Add `--thread-model std|translated`**, a sibling of `--allocator-model`. Translated thread
  mode requires translated allocator mode, because thread stacks and `Task`/`Future` blocks come
  from translated allocators.
  * In `std` mode (the default) the output is **byte-identical**. Check this with P1's
    `goldens.py` over every committed golden and the fresh 0.16.0/0.15.2/0.14.1 example exports.
    New rows are gated by `StdModel.activeIn`.
  * In `translated` mode:
    * the `StdModels` rows S10–S31 (`Thread.spawn`/`join`/`yield`/`detach`, `Io.futex*`,
      `Io.Group.*`, `Thread.Futex.*`, `Thread.Mutex.DarwinImpl.*`, `time.Timer.*`,
      `Io.futexWaitTimeout`) are inactive;
    * `Ty.thread` and `Ty.io` are not specialized (`Thread` is the plain `{impl}` struct, `Io`
      the plain `{userdata, vtable}` struct);
    * the new OS rows (§3) are active and bound by module identity (B1,
      `Air2Lean/Air/Identity.lean`) and by extern symbol (docs/external-models.md).
* **Retired after the flip** (models audit class B): S10–S31, T02, T03, Z05 (`Conc/Call.lean` op
  wrappers), Z08 (`TimedCall` source-shaped mirror), THR-02/03/04 and THR-05 (replaced by
  OSF-01/02), THR-06 (0.15.2 only, kept for that version or dropped with it). `Conc/Spawn.lean`
  policies become the oracle of OST-01's failure branch.
* **Kept**: the scheduler and RC11 approximation (Z06, class A), `Lock.lean`/`Logic.lean`/
  `Csl.lean` (re-based on `FutexSpec`), `Word`/`WeakWord`, and TLS (C02).
* **0.15.2/0.14.1**: they keep std mode. Their `Thread.Mutex`/`Futex` would need their own OS
  rows (`os_unfair_lock` with an owner for 0.15.2 macOS, audit finding 5). That is out of scope
  until a user asks.

## 5. Phases, effort, blockers

Estimates are for one agent. The phases run in two lanes: T1/T3 in parallel with T2.

| Phase | Content | Depends on | Estimate |
|---|---|---|---|
| T0 exporter | Extern callee names and table (`codex/extern-calls`, in flight); keep the P0 vtable/global-init fix; spike re-export with both | P0, extern-calls | 1 week (mostly merge + re-export) |
| T1 translator | B1 `noreturn` variants (2 d), B4/B11 opaque handle types (2 d), B7 nested function constants (3 d), B6 tuples in memory (1 week), B8 opaque recovery of error-bearing pointees (1 week), pointer weak cmpxchg + pointer stores + packed-usize RMW (1 week), B9 punning/`@fieldParentPtr`/int↔ptr atomic words (2–3 weeks, **shared with arena P5**), `--thread-model` plumbing + `StdModel.activeIn` (3 d) | P1 | 6–8 weeks |
| T2 OS rows | `ZigLean/Os/{Futex,Thread,Clock}.lean`, the rows of §3, the exit hook (`CHILD_CLEARTID`), the pending-interrupt bit, the wake-subset oracle, the environment record; premises OSF/OST/OSY/OSK/OSG, docs, CI fixture (Linux + macOS AIR) | batch7 C02/C05/C07 merged; `fix-concurrency-soundness` #6/#7/#14 | 3–4 weeks |
| T3 Futex/Mutex specs | `FutexSpec`, re-base `Lock.lean` on spurious returns, `CondSpec`/`EventSpec`/`WaitGroupSpec`; `Threaded.mutexLock`/`cond*`/`event*`/`WaitGroup` proofs | T1 (B1, B5), T2 | 3–4 weeks |
| T4 `std.Thread` | `ThreadSpec`; spawn/join/detach proofs (Linux clone + `child_tid` futex join; macOS pthread + OSM-02) | T2, allocator P2/P4 (`PageAllocator` for stacks) | 2–3 weeks |
| T5 `IoSpec` + `Io.Threaded` | `IoSpec` and the wrapper proofs (any Io), then `Io.Threaded ⊨ IoSpec` (pool, group, future, cancelation state machine), then `global_single_threaded` | T3, T4, T1 B6–B9 | 8–12 weeks (largest; start with group + futex slots, then futures, then cancelation) |
| T6 migration | Port `sync`/`iogroup`/`threads` and their proofs to IoSpec premises; byte-identity checks; flip the default for 0.16.0; retire rows; coverage, premise index, inventory regeneration | T5 | 2–3 weeks |

The total is about 6–8 months for one agent, or about 4 months with two lanes (T1 ∥ T2, then
T3 ∥ T4). The first useful milestone is T0+T1(B1, B4, B5, B7)+T2+T3, about 2 months. It gives
translated `std.Thread` and `Io.Mutex`/`Condition` on real futexes with spurious wakeups, and
retires THR-05 and the D5 divergence.

### Blockers and their status

* **Exporter extern names.** On `codex/extern-calls` (in progress): `"extern": "<sym>"` callees
  plus an `externs` table. This was confirmed on the spike for `__ulock_wait2`, `pthread_join` and
  `sched_yield`. It does not yet include the P0 global-init fix, so both are needed together.
  Every macOS rejection in the spike (B3) depends on it.
* **Atomics on pointers.** P1 has pointer loads and strong cmpxchg. Still missing:
  * weak cmpxchg and stores of pointers (`worker_threads`);
  * atomic words that switch between pointer and integer interpretation (`Group.token` used
    as `Group.Status`, `Future.Status` with `PackedPtr`);
  * RMWs on packed `struct(usize)`.

  The batch7 C09 pointer atomics overlap and should be reconciled with P1's `AtomicWord`.
* **Io vtable.** The translator handles the dispatch (the allocator path proved it: plain
  struct + indirect calls). The problems are closure size, because the vtable literal references
  ~110 slots, and B8. Proposal: the closure follows only the slots in `S`, and the remaining
  slots are emitted as fail-closed `unsupported` stubs, so reaching one is an explicit
  non-success outcome and never an assumption.
* **Cancelation.** In `Io.Threaded` this is a lock-free 8-state machine per worker, plus
  signals with exponential-backoff timed futex waits. For partial correctness the OSF-01 oracle
  `EINTR` plus timeouts as spurious returns suffice. Termination of `cancel` needs OSG-01's
  pending interrupt and a fairness premise (THR-09). This is the riskiest proof in T5.
* **`@returnAddress`.** Solved by P1's `Zig.returnAddress` oracle in translated allocator mode.
  `Threaded` only passes the value to its allocator, so no new work.
* **Thread-locals.** Batch7 C02 (`Zig.tlsPtr`) must merge before T3, because `Syscall.start`
  reads `Thread.current` on every cancelable futex wait.
* **macOS malloc (decision D1).** Should `c_allocator`'s `malloc`/`free` be a trusted primitive
  (OSM-02)? If not, macOS spawn stays unprovable.
* **Environment premises (decision D2).** `cpus`, the spawn policy and the allocator thread
  safety must appear in theorem statements (audit findings 7 and 11). This is a breaking change
  to `Sched.run` callers.

## 6. Spike artifacts (not committed)

Everything is in `.claude/worktrees/spike-thread-io/scratch/spike/`:

* `thread_mutex.zig`, `io_client.zig`, `threaded.zig`;
* `export.sh` (AIR, about 350 MB, in `air-p0/`), `closure.py`, `bypass.py`, `diag.sh`;
* `summ.py`, whose summaries are in `diag/<program>-<target>.{std,tr}.txt` (raw JSON next to
  them);
* `air-ext/tm-mac/` (the extern-name export);
* `g.sh`, the build-guard wrapper on lane D.
