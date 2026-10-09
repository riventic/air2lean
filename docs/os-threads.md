# OS thread primitives: the trusted base of translated `std.Thread` and `std.Io`

`std.Thread`, the `std.Io` sync primitives and `Io.Threaded` are to be translated from their Zig
code (`docs/thread-io-translation.md` on `codex/spike-thread-io`, phase T2). Only the OS calls
below them get a trusted model, one premise per group
([premises.md](premises.md#os-thread-primitives)). The models are in `ZigLean/Os/`, imported by
`ZigLean.lean` through `ZigLean/Os.lean`. The proof-only rules are in `ZigLean/Sep/OsMalloc.lean`
and `ZigLean/Conc/OsRules.lean`, which `ZigLean.lean` does not import.

The cut is at the named OS wrapper: on Linux the `std.os.linux` function above `syscallN`, on
macOS the `extern "c"` symbol (bound by symbol, `codex/extern-calls`). Zig 0.16.0,
x86_64-linux and aarch64-macos. Under the planned `--thread-model translated`, the translator
calls the Lean definition of the same name (table below). Each call that can let another thread
run is a `ConcM` function. It stops at sync ops of the existing scheduler (`ZigLean/Conc/Sched.lean`:
`yield`, `pick`, `spawn`, `join`, `wait`), over the same memory and RC11-approximate atomics
(`ZigLean/Mem/Thread.lean`). No scheduler op was added. The kernel's wait queue is
`Mem.waiters`/`Mem.woken`, as for the std-mode futex rows. The only new state is
`Mem.os : OsState`: the pending interrupts, the clock-read count and the `errno` cells.

## Signatures

Arguments map as for the OSM-01 rows (`docs/os-mmap.md` on `codex/alloc-translated-p2`): a
`packed struct(u32)` or an `enum(u32)` is its bits (`BitVec 32`), `?*T` is `Option Ptr`, a
`pthread_t` is the model's `ThreadId` (`Enc ThreadId`, 8 bytes), `c_int` is `BitVec 32`, and
`std.c.E` (macOS, `enum(u16)`) is `BitVec 16`. A Linux wrapper returns the raw `usize`, `-errno`
on failure (`Os.negErrno`), which the translated `linux.errno` decodes. A function pointer and
its argument (`clone`'s `func`/`arg`, `pthread_create`'s `start_routine`/`arg`) are constants at
each call site, so the translator passes the spawn target `t : Tgt` that it builds from them, as
for `std.Thread.spawn` today. `env : Os.Env` is the explicit environment (below).

| Zig 0.16.0 | Lean (`Zig.Os.…`) | Premise |
|---|---|---|
| `os.linux.futex_4arg(uaddr, futex_op, val, timeout) usize` | `Linux.futex_4arg (uaddr : Ptr) (futex_op val : BitVec 32) (timeout : Option Ptr) : ConcM Tgt (BitVec 64)` | OSF-01 |
| `os.linux.futex_3arg(uaddr, futex_op, val) usize` | `Linux.futex_3arg (uaddr : Ptr) (futex_op val : BitVec 32) : ConcM Tgt (BitVec 64)` | OSF-02 |
| `__ulock_wait2(op: UL, addr, val: u64, timeout_ns: u64, val2: u64) c_int` | `Darwin.__ulock_wait2 (op : BitVec 32) (addr : Option Ptr) (val timeout_ns val2 : BitVec 64) : ConcM Tgt (BitVec 32)` | OSF-01 |
| `__ulock_wait(op, addr, val: u64, timeout_us: u32) c_int` | `Darwin.__ulock_wait (op : BitVec 32) (addr : Option Ptr) (val : BitVec 64) (timeout_us : BitVec 32) : ConcM Tgt (BitVec 32)` | OSF-01 |
| `__ulock_wake(op, addr, val: u64) c_int` | `Darwin.__ulock_wake (op : BitVec 32) (addr : Option Ptr) (val : BitVec 64) : ConcM Tgt (BitVec 32)` | OSF-02 |
| `os.linux.clone(func, stack, flags, arg, ptid, tp, ctid) usize` | `Linux.clone (env : Env) (t : Tgt) (stack : BitVec 64) (flags : BitVec 32) (ptid : Option Ptr) (tp : BitVec 64) (ctid : Option Ptr) : ConcM Tgt (BitVec 64)` | OST-01 |
| dispatcher of a `clone` target | `Linux.cloneThread (entry : ConcM Tgt α) (ctid : Ptr) : ConcM Tgt Unit` (entry, then `cloneExit ctid`) | OST-02 |
| `os.linux.gettid() pid_t`, `getpid() pid_t` | `Linux.gettid (env : Env) : MemM (BitVec 32)`, `Linux.getpid (env : Env) : MemM (BitVec 32)` | OST-03 |
| `os.linux.tgkill(tgid, tid, sig: SIG) usize` | `Linux.tgkill (env : Env) (tgid tid sig : BitVec 32) : MemM (BitVec 64)` | OSG-01 |
| `os.linux.sched_getaffinity(pid, size, set) usize` | `Linux.sched_getaffinity (env : Env) (pid : BitVec 32) (size : BitVec 64) (set : Ptr) : MemM (BitVec 64)` | OST-03 |
| `os.linux.sched_yield() usize` | `Linux.sched_yield : ConcM Tgt (BitVec 64)` | OSY-01 |
| `os.linux.clock_gettime(clk_id, tp) usize` | `Linux.clock_gettime (env : Env) (clk_id : BitVec 32) (tp : Ptr) : ConcM Tgt (BitVec 64)` | OSK-01 |
| `os.linux.clock_nanosleep(clockid, flags: TIMER, request, remain) usize` | `Linux.clock_nanosleep (clockid flags : BitVec 32) (request : Ptr) (remain : Option Ptr) : ConcM Tgt (BitVec 64)` | OSK-02 |
| `pthread_create(newthread, attr, start_routine, arg) E` | `Darwin.pthread_create (env : Env) (newthread : Ptr) (attr : Option Ptr) (t : Tgt) : ConcM Tgt (BitVec 16)` | OST-01 |
| `pthread_attr_init/destroy(attr) E`, `pthread_attr_setstacksize/setguardsize(attr, usize) E` | `Darwin.pthread_attr_init (attr : Ptr) : MemM (BitVec 16)`, … | OST-01 |
| `pthread_join(thread, arg_return) E` | `Darwin.pthread_join (thread : ThreadId) (arg_return : Option Ptr) : ConcM Tgt (BitVec 16)` | OST-02 |
| `pthread_detach(thread) E` | `Darwin.pthread_detach (thread : ThreadId) : MemM (BitVec 16)` | OST-02 |
| `pthread_self() pthread_t` | `Darwin.pthread_self : MemM ThreadId` | OST-03 |
| `pthread_threadid_np(thread: ?pthread_t, thread_id: *u64) c_int` | `Darwin.pthread_threadid_np (env : Env) (thread : Option ThreadId) (thread_id : Ptr) : MemM (BitVec 32)` | OST-03 |
| `pthread_kill(thread, sig: SIG) c_int` | `Darwin.pthread_kill (thread : ThreadId) (sig : BitVec 32) : MemM (BitVec 32)` | OSG-01 |
| `sysctlbyname(name, oldp, oldlenp, newp, newlen) c_int` | `Darwin.sysctlbyname (env : Env) (name : Ptr) (oldp oldlenp newp : Option Ptr) (newlen : BitVec 64) : MemM (BitVec 32)` | OST-03 |
| `sched_yield() c_int` | `Darwin.sched_yield : ConcM Tgt (BitVec 32)` | OSY-01 |
| `clock_gettime(clk_id, tp) c_int` | `Darwin.clock_gettime (env : Env) (clk_id : BitVec 32) (tp : Ptr) : ConcM Tgt (BitVec 32)` | OSK-01 |
| `nanosleep(rqtp, rmtp) c_int` | `Darwin.nanosleep (rqtp : Ptr) (rmtp : Option Ptr) : ConcM Tgt (BitVec 32)` | OSK-02 |
| `__error() *c_int` | `Darwin.__error : MemM Ptr` | OSK-02 |
| `malloc(usize) ?*anyopaque` | `Darwin.malloc (env : Env) (size : BitVec 64) : MemM (Option Ptr)` | OSM-02 |
| `free(?*anyopaque) void` | `Darwin.free (ptr : Option Ptr) : MemM Unit` | OSM-02 |
| `malloc_size(?*const anyopaque) usize` | `Darwin.malloc_size (ptr : Option Ptr) : MemM (BitVec 64)` | OSM-02 |

Arguments that std never passes (other futex commands or flags, other `clone` flags, other
clocks, other signals, other `sysctl` names, a non-null `pthread_join` result pointer) are outside
the model: `.unspecified`. The translator must still check, as for OSM-01, that each call site's
types match.

## Environment

`Os.Env` (`ZigLean/Os/Env.lean`) is what the OS decides (user decision D2: the CPU count, the
spawn policy and the allocator's thread safety are explicit, never constants):

| Field | Meaning | Used by |
|---|---|---|
| `cpuMask` | affinity mask (bits below 1024); `Env.cpus` counts it | `sched_getaffinity`, `sysctlbyname("hw.logicalcpu")`; `Io.Threaded.async_limit = cpus - 1` |
| `spawn` | `available` or `fallible` (`ZigLean/Conc/Spawn.lean`, with `Mem.spawnLimit`) | `clone`, `pthread_create` |
| `tid`, `pid` | kernel ids of model threads, process id | `gettid`, `pthread_threadid_np`, `getpid`, `clone`'s `ptid`, `tgkill` |
| `clock k i` | nanoseconds of the `i`-th clock read of the run, per clock | `clock_gettime` |
| `mallocSlack i n` | usable bytes beyond `n` at allocation attempt `i` | `malloc`, `malloc_size` |

`Env.Valid` is the premise a theorem states: `cpus ≥ 1`; ids distinct and positive; the
`awake`/`boot` clocks monotone; values fit a `timespec`. Libc's `malloc` is thread-safe (OSM-02).
The model's `std.mem.Allocator` thread safety (audit finding #11) is a separate question.

## Futex

**Wait** (`Os.futexWait`). One `pick`, then in the same turn the kernel's compare: an atomic read
of the newest message of the `u32` (`atomicLoadAt 0 .relaxed`). It records an atomic-read
footprint, so a racing plain write is `.illegal`, and an `observe` (audit finding #14). A bad
pointer is `.illegal`. A different value returns `mismatch` (`EAGAIN`; macOS `0`). Otherwise the
oracle picks:

1. sleep. An untimed wait stops at the scheduler's `wait p e`, which compares again and sleeps
   until a wake. A changed word goes on, which is a return with `0`, as Linux allows. A timed
   wait joins `Mem.waiters` and stops at a `yield`, so it stays runnable: at any later turn it
   returns `woken` if a wake reached it, else `timedOut`. A timed wait never deadlocks.
2. `EINTR` at once: a signal or any spurious return (audit finding #2).
3. with a timeout, `ETIMEDOUT` at once.

**Wake** (`Os.futexWake`). One `pick` among the subsets of `min n k` of the `k` threads queued at
the address (`wakeSets`), with no FIFO order (audit finding #6). The woken threads go on at their
next turn. A wake accesses no memory and gives no edge: std re-reads the word with an acquire.
macOS `__ulock_wake` has the extra option `-EINTR` with nobody woken, and std retries.

## Threads

**Create.** Linux `clone` with std's exact flags and macOS `pthread_create` are the scheduler's
`spawn t` (the fork edge), or under `fallible` an oracle failure (`-EAGAIN`/`-ENOMEM`, `EAGAIN`).
The new thread's thread-local instances are batch7 C02's (`tlsEnter` in the dispatcher), and
`clone`'s `stack`/`tp` and `tls.prepareArea` belong to the row. Linux `PARENT_SETTID` writes
`Env.tid child` to `ptid` after the fork. A child that reads `ptid` unsynchronized races, which is
stricter than the kernel; std's child never reads it.

**Linux exit and join.** The dispatcher of a `clone` target is `Linux.cloneThread entry ctid`.
After `entry` returns, `cloneExit` does `CHILD_CLEARTID` in one turn: a release store of `0` to
`ctid` that carries the thread's final clock, a wake of every waiter at `ctid`, and the end of
the join obligation (`ThreadRec.joined`). The thread then ends, in the same turn. Std's
translated `LinuxThreadImpl.join` (a `seq_cst` load loop with `futex_4arg` on `child_tid`) gets
its happens-before edge from that store. A parent that ends before its child exits is `.illegal`
(`checkJoinedByChild`). A detached thread's `freeAndExit` (inline `munmap` + `exit`) is not
modelled: it needs OSM-01's `munmap` (`codex/alloc-translated-p2`).

**macOS join and detach.** `pthread_join` is the scheduler's `join`, with the edge from the
thread's end. `pthread_detach` releases the obligation (batch7 C07's `Thread.detach` semantics).
A join or detach by a thread that does not own the handle, or of a consumed handle, is
`.illegal` (std: `unreachable`).

**Yield.** `sched_yield` is the scheduler's `yield` and returns `0`.

## Interrupts

`tgkill(pid, tid, SIG.IO)` and `pthread_kill(h, SIG.IO)` are std's cancelation of a blocked
syscall (`signalCanceledSyscall`). On a live thread (`Mem.threadAlive`) the signal wakes the
thread if it sleeps in a futex wait, and that wait returns `EINTR`. Otherwise it records a pending
interrupt in `OsState.interrupts`, and the thread's next futex wait or sleep delivers it at its
start. Delivery forces no `EINTR`: a signal that arrives before the syscall runs the no-op
handler and is gone, and std re-signals with backoff. For partial correctness the oracle `EINTR`
of every wait and sleep covers every timing. The pending bit is a hook for liveness arguments
under a fairness premise. An unknown or ended thread gives `ESRCH`.

## Clocks

`clock_gettime` is a scheduling point (`yield`), then the `i`-th read of the run
(`OsState.clockReads`) gives `Env.clock k i`, written as a `timespec`. The scheduling point keeps
reads of different threads in the order of the run, so monotonicity holds across threads.
Linux `REALTIME`/`MONOTONIC`/`BOOTTIME` and macOS `REALTIME`/`UPTIME_RAW`/`MONOTONIC_RAW`/
`MONOTONIC` map to `real`/`awake`/`boot` (`Io.Threaded.clockToPosix`). Linux `clock_nanosleep`
and macOS `nanosleep` are one oracle choice: `0`, or `EINTR`, which writes the request as the time
left. No duration is promised. On macOS, `EINTR`/`EINVAL` are `-1` and the thread's `errno` cell
(`__error()`), a 4-byte block that the thread makes at first use.

## Malloc

macOS `malloc`/`free`/`malloc_size` (user decision D1) reuse the allocator machinery of
`ZigLean/Mem/Alloc.lean`. A `malloc` block is a `.heap` block made by `rawAlloc`, so it shares
the attempt count and failure decision (`Mem.allocDenied`) with the model's `std.mem.Allocator`.
It has `n + Env.mallocSlack i n` undefined bytes at a 16-byte-aligned address, or the call returns
`null`. `free(p)` needs offset 0 of a live heap block. It is a write of all its bytes for the race
check (`poisonFree`), then the block ends. A double free, a use after free, an inner pointer or a
stack, global, mapping (OSM-01 `.mapped`) or arena block is `.illegal`.

## Rules (proof-only)

| Theorem | Statement |
|---|---|
| `Triple.malloc` | `emp` before; after, `mallocPost n`: `null` and no bytes, or a block of `S ≥ n` undefined bytes, 16-byte aligned. For every failure policy and slack. |
| `Triple.mfree`, `Triple.mfreeNull` | the whole owned block before, `emp` after; `free(null)` keeps `emp`. |
| `Os.Darwin.free_dead`, `free_inner` | `free` of a dead block (a double free) or an inner pointer is `.illegal`. |
| `Os.wakeCount_pos`, `Os.wakeSets_mem` | a wake always has an option; each option is a sublist of the queue at the address of length `min n k`. |
| `Os.wakeAt_frame`, `Os.interrupt_frame` | a wake and an interrupt change no block, clock, footprint, atomic location or thread record: no happens-before edge. |
| `Os.waitCount_ne`, `Os.waitCount_eq` | the compare has one option for a different word, two (three with a timeout) for the expected one. |

Kernel-checked examples (`decide +kernel`): `OsMallocExamples` covers a store into a fresh block,
a double free, a use after free, an inner-pointer free and a stack-block free. `OsRulesExamples`
covers a spurious `EINTR` with nobody waking, the deadlock of an untimed wait nobody wakes, a
timed wait that times out, a wake without an edge (the woken waiter's plain read races), and the
Linux join loop over `CHILD_CLEARTID` that reads the thread's write.

Runtime regressions over every schedule: `tests/roadmap/os-threads/Check.lean`
(`lake env lean tests/roadmap/os-threads/Check.lean`).

## Not yet modelled

The following are missing:

* Linux `freeAndExit` and `set_tid_address` (detached thread exit, after OSM-01's `munmap`
  merges).
* `sigaction`, `sigprocmask` and `sigaltstack`: no memory effect for std's use, but they need rows
  before translated code can call them.
* `posix_memalign` (`c_allocator` for alignments above 16).
* `__ulock_wait*`'s non-negative waiter count, which is always `0`.

Batch7 C02 (TLS), C05 (cancelation) and C07 (`Thread.detach`) are not on `main`. The models
follow their semantics and must be re-pointed at them when batch 7 merges.
