# Generic sync specifications (`FutexSpec`, `MutexSpec`, `EventSpec`)

Status: proof-only modules, not imported by `ZigLean.lean`. This is phase T3 of the plan in `docs/thread-io-translation.md` on branch
`codex/spike-thread-io`. Threads, futexes and `std.Io` are to be translated from their
Zig 0.16.0 code over a trusted base of OS primitives (premises OSF/OST/…, T2). These specs are
the contracts between the layers:

* T2 proves its OS futex rows against `FutexSpec`.
* The translated std sync code (`Io.Mutex`, `Io.Threaded.mutexLock`/`mutexUnlock`, `Io.Event`,
  `eventWait`/`eventSet`) is proved against `MutexSpec`/`EventSpec` from `FutexSpec` alone.
* Clients are proved against `MutexSpec`/`EventSpec` alone.

The allocator track does the same with `AllocSpec` (`docs/alloc-spec.md` on branch
`codex/alloc-translated-p3`).

| Module | Contents |
|---|---|
| `ZigLean/Conc/Spec/Sys.lean` | systems of threads, reachable states, inductive invariants, `Enabled` |
| `ZigLean/Conc/Spec/Futex.lean` | `Futex` (the signature), `FutexSpec`, the queue lemmas, `FutexSpec.of_abs` |
| `ZigLean/Conc/Spec/FutexToy.lean` | `Futex.ref`, `fifo` and `spin` satisfy it; `lazyWake` and `noRecheck` do not |
| `ZigLean/Conc/Spec/Mutex.lean` | views (`AWord`), `Impl`, the most general client `mgc`, `MutexSpec`, `MutexSpec.resource` |
| `ZigLean/Conc/Spec/MutexToy.lean` | a spin mutex satisfies it; one with a monotonic `unlock` does not |
| `ZigLean/Conc/Spec/IoMutex.lean` | std `Io.Mutex` satisfies `MutexSpec` over **every** futex that satisfies `FutexSpec`; it deadlocks over `lazyWake` and `noRecheck` |
| `ZigLean/Conc/Spec/Event.lean` | `EventSpec`, and a spin event that satisfies it |

CI builds all seven (`Generic sync specifications`). None of them uses `sorry`, `admit` or
`native_decide`. They import nothing outside `ZigLean/Conc/Spec`, and they state no premise
beyond TRU-01 (`assurance/premises.json`). How `ioMutex` and `spinEvent` relate to the real std
code is described in [What the translated std code must satisfy](#what-the-translated-std-code-must-satisfy).

## The logic

A **system** (`Sys`) has a type of global states, the initial states, and the atomic steps of
each thread. A proof over all schedules is an **inductive invariant** (`Sys.Inductive`): it
holds initially, and every step of every thread keeps it. This is the rely–guarantee form of
`ZigLean/Conc/Logic.lean`, `Proto.inv`, with the ghost values made part of the state: each
thread's steps keep the invariant (the guarantee), and each thread relies on the others keeping it.
A negative result is a reachable state that breaks the property (`Sys.not_invariant`), given as
an explicit run.

The specs do not depend on `Mem`, on the scheduler or on the batch-7 changes to `Conc/Logic`.
The futex, the memory words and the views are abstract. So the specs stay valid while the
concrete model changes, and T2 can instantiate them from whatever concrete model it builds on.

### Environment (decision D2)

These systems have every thread id from the start. Every step of every thread is allowed at
every point, with no spawn, no allocation and no CPU count. So each theorem here holds for every
`cpus ≥ 1`, every spawn policy and every allocator. The D2 parameters first matter one layer up,
in `ThreadSpec` (T4: spawn may fail) and `IoSpec` (T5: `async_limit = cpus - 1`, `Group.async`
runs inline or deferred, `Task` blocks come from `t.allocator`). Their systems must take an
explicit environment record with `cpus`, the spawn policy and the allocator's thread-safety
premise, and every theorem must state it.

## `FutexSpec`

**Signature** (`Futex M A`). `M` is the memory the words live in, and `A` is the set of word
addresses. `W : M → A → Option (BitVec 32)` is the atomic view of the `u32` at an address
(`none` means there is no valid word there). It is a parameter of the spec, because it belongs
to the memory model. The futex has its own state `F` and a **queue view**
`queue : F → List (Tid × A)` that lists the threads asleep at each address. Its ops are
relations, so an implementation may be nondeterministic:

| op | meaning |
|---|---|
| `wait t a e tm m f r f'` | the first, atomic step of `wait(a, e)` by `t` (`tm`: with a timeout) in memory `m`. `r = none`: `t` sleeps. `r = some ret`: it returns at once |
| `resume t tm f r f'` | a thread that went to sleep returns `r` |
| `wake t a n f k f'` | `wake(a, n)` woke `k` threads |

No op gets or changes `M`. A futex op only reads the word, and it carries no view, so it adds no
happens-before edge.

**Contract** (`FutexSpec W X`):

| clause | statement |
|---|---|
| `init` | the queue starts empty |
| `wait_word` | `wait` reads a valid word `v`, and `t` sleeps only if `v = e` (the recheck) |
| `wait_local` | `wait` depends on the memory only through that word |
| `wait_sleep` | a sleeping `wait` adds exactly `(t, a)` to the queue (up to order) |
| `wait_ret` | a returning `wait` leaves the queue unchanged. `woken`, `again` and `intr` are always allowed (a spurious return); `timeout` only with a timeout |
| `resume` | the resumed thread leaves the queue, which it may still be in (spurious, `EINTR`, timeout); others stay |
| `wake` | for a well-formed queue (each thread asleep at most once), it wakes an **arbitrary** set of exactly `min n c` distinct threads asleep at `a`, where `c` is the number asleep there, and returns that number |
| `wait_total` | progress: a `wait` on a valid word by a thread that is not asleep can always step |
| `resume_total` | progress: a thread that is no longer in the queue can always resume |
| `wake_total` | progress: a `wake` can always step |

A thread that is still in the queue need not be able to resume. Only a wake is sure to make it
go on, so a client needs a wake for progress and re-checks the word after every return.

**Lemmas for clients** (`FutexSpec.*`): `sleep_word`, `mem_wait`, `mem_resume`, `mem_wake`,
`wake_keeps`, `wf_wait`/`wf_resume`/`wf_wake` (the queue stays well formed), `wake_one` (a wake
of `n ≥ 1` at an address where a thread sleeps removes a thread asleep there), and `wake_all` (a
wake of at least as many threads as sleep at `a` empties `a`; this is `Event.set`'s
`maxInt(u32)`).

**Satisfiable, and not by everything** (`FutexToy.lean`):

* `ref_spec`: `Futex.ref W` is the most permissive futex of the contract.
* `fifo_spec`, `fifo_spec_of_ref`: the FIFO futex (the hand model THR-05, rewritten as an
  abstract futex) satisfies the contract, both directly and through `of_abs` into `ref`.
* `spinFutex_spec`: a futex whose wait never sleeps and always returns `intr` satisfies it. So a
  client cannot assume that a wait blocks.
* `lazyWake_not_spec`: a wake that never wakes does not satisfy it.
* `noRecheck_not_spec`: a wait that sleeps without comparing the word with the expected value
  does not satisfy it, as soon as some word differs from some expected value.

## `MutexSpec`

**Views.** The mutex protects a resource whose values have a type `X`. Each thread sees the
resource through its own **view** `cur t`, and the ghost `val` is the resource's real value.
Views move between threads only through the shared state of the implementation. An atomic
word (`AWord`) carries the view of its newest message. A release write puts the writer's view
in the message, an RMW without release keeps the old one (a release sequence), and an acquire
read adopts the message's view. This is the part of RC11's happens-before order that a lock
needs. A thread with a stale view has not synchronised with the last writer.

**Implementations** (`Impl Op`): a shared state for each resource type, the threads' places in
the code, an atomic step relation (which may read and change the shared state and the stepping
thread's view), and `done`.

**The most general client** (`mgc I X`). Each thread is idle, holds the lock, or runs an op.
An idle thread calls `lock` or `tryLock`, and a holder calls `unlock` or writes the resource. A
thread in an op takes the implementation's steps and returns when `done`: `lock` and a
successful `tryLock` make it a holder, while `unlock` and a failed `tryLock` make it idle.

**Contract** (`MutexSpec I`), for every resource type `X` and every reachable state:

| clause | statement |
|---|---|
| `excl` | at most one thread holds the lock |
| `view` | a holder's view is the real value. This is **ownership transfer**: the thread that returns from `lock` sees every write of the earlier holders |
| `live` | no deadlock: if a thread runs an op and no thread holds the lock, some thread in an op can step |

`MutexSpec.resource` gives CSL's lock invariant. In a client whose writes keep `R`, the thread
that returns from `lock` sees a value that satisfies `R`. `live` is the repo's notion of
deadlock freedom (`Conc.Proto.Live`, strict mode). Like that notion, it does not rule out a
livelock, which needs a fairness premise (THR-09).

**Satisfiable, and not by everything:**

* `spinMutex_spec` (`MutexToy.lean`): a spin mutex satisfies the contract. Its `lock` is an acquire
  `cmpxchg(0 → 1)` loop, its `tryLock` is one such `cmpxchg`, and its `unlock` is a release
  `xchg(0)`.
* `relaxed_not_spec`: the same mutex with a monotonic `unlock` does not satisfy it. In a run of
  two threads, the second holder adopts an older message and misses the first holder's write.
  Mutual exclusion still holds, and only the views catch the bug.
* `ioMutex_spec` (`IoMutex.lean`): **the std 0.16.0 `Io.Mutex` algorithm satisfies `MutexSpec`
  over every futex `Fx` with `FutexSpec wordView Fx`**. This covers spurious returns,
  interrupts and any choice of woken thread. The waits are uncancelable, as in
  `lockUncancelable` and `Threaded.mutexLock`.
* `lazyWake_deadlock`, `noRecheck_deadlock`: over the two broken futexes, `Io.Mutex` deadlocks
  in a run of two threads. So both futex clauses that the proof uses are needed.

The invariant of the `Io.Mutex` proof (`IoInv`) is the abstract form of `Lock.Inv`:

| `IoInv` | `Lock.Inv` (`ZigLean/Conc/Lock.lean`) |
|---|---|
| `excl` | `one` |
| `word`, `bound` | `word` |
| `view`, `msg` | `free`, `res`, `Owns`, `rel` (with clocks) |
| `qloc` | `fq` |
| `wit` | `wit` |
| `qwf` | (a scheduler invariant) |

The futex clauses that the proof uses are `sleep_word` (the recheck: a thread sleeps only on
`2`, so a thread owns the lock and is the new witness), `mem_wait`/`mem_resume`/`mem_wake`,
`wake_one` (the waker's wake takes a thread out of the queue, and that thread is the new
witness), and the three progress clauses. FIFO order is never used.

## `EventSpec`

`Io.Event` and `Threaded.eventWait`/`eventSet`. Thread `0` is the producer. While no `set` has
been called it may write the resource, and only it calls `set`. Any thread calls `wait` or
`isSet`. A thread that returns from `wait`, or from `isSet` with `true`, has **got** the event.

| clause | statement |
|---|---|
| `view` | a thread that got the event sees the real value: every write that the producer made before `set` |
| `live` | no deadlock: once a `set` has returned, if a thread waits, some thread in an op can step |

`view` also means that `wait` does not return before `set`. `spinEvent_spec`: a word that `set`
writes with a release store and that `wait`/`isSet` read with acquire loads satisfies the
contract. `reset` is outside the contract: std allows it only with no pending wait, and
`Io.Threaded` never calls it.

## Not mechanised yet: `CondSpec`, `WaitGroupSpec`

These are the statements the next T3 step must mechanise in the same style.

* **`WaitGroupSpec`** (`Threaded.WaitGroup`: `start`, `finish`, `wait`, `value`; one waiter).
  `wait` returns only when every `start` has a matching `finish`. Each finisher's writes before
  `finish` happen before the return of `wait`, through the `acq_rel` `fetchSub` and the release
  of `eventSet`. `Threaded.WaitGroup` is a counter plus an `Io.Event`, so the proof combines a
  counter invariant with `EventSpec`. Stating the happens-before part for several finishers
  needs views that merge (a join of the views, not only adoption). This extends `AWord`.
* **`CondSpec`** (`Io.Condition`, `Threaded.condWait`/`condSignal`/`condBroadcast`, Mesa
  semantics). Its most general client has the mutex's clauses (`excl`, `view`), and `wait`,
  called by a holder, returns holding the mutex. A return may be spurious, so a client
  re-checks its predicate. For progress, a `signal` (or `broadcast`) made while holding the
  mutex creates an obligation: one waiter that called `wait` before it (or all such waiters)
  returns from `wait`. The `live` clause is "no reachable state has an open obligation, no
  holder, and no thread in an op that can step". A later waiter may take the signal, as std's
  `signals` counter allows.

## What T2 must provide

To use these specs, T2's OS futex rows (premises OSF-01/02) provide one instance per target:

1. `M`, `A` and `W`. The memory is `Mem`, or the part of it that the futex sees. `A` is `Ptr`.
   `W m p` is the `u32` that an atomic read of `p` gets in `m`: `m.access p 4 4` succeeds and
   the bytes decode. Otherwise `W m p = none`, which is std's `FAULT`, `.illegal` in the row.
2. A `Futex M A` whose state `F` holds the scheduler's queue (`Mem.waiters`, the woken set and
   the pending interrupts of OSG-01), whose `queue` lists the threads still asleep (in
   `waiters` and not yet woken), and whose relations are the OS rows' atomic steps:
   * `wait`: the atomic read with its footprint (audit finding #14), then enqueue or return. The
     oracle may return `EINTR` instead of sleeping.
   * `resume`: the scheduler resuming a sleeping thread. It is woken, or returns spuriously,
     `EINTR` or `ETIMEDOUT` (timeout only with a timeout).
   * `wake`: OSF-02 with the oracle subset (audit finding #6). It wakes `min n c` threads. On
     macOS it returns `0` or `-ENOENT`, which std ignores.
3. `FutexSpec W thatFutex`. The route is `FutexSpec.of_abs (ref_spec W)`: map each step to a
   step of `Futex.ref W` (whose queue is the same list), and prove the three progress clauses.
   The concrete rows record a footprint for the atomic read, which the abstract `M` does not
   see. That is the one obligation the concrete client proofs keep: their invariant must be
   stable under an atomic read of the word. `Lock.Step.fp` already admits this, and
   `Inv.record` proves it for the lock.

`Linux CHILD_CLEARTID` (the exit store and wake that a Linux `join` waits on) is a separate row
(OST-01). The join proof (T4) uses it through `FutexSpec`, as a wait loop on `child_tid`.

## What the translated std code must satisfy

`ioMutex` and `spinEvent` are hand transcriptions of the algorithms, one atomic step per atomic
op of the source (`lib/std/Io.zig:1587`, `Io/Threaded.zig:18722`, `:18741`). They are not
generated code. To carry `ioMutex_spec` over to the translated `Io.Mutex.lockUncancelable`/
`unlock` and `Threaded.mutexLock`/`mutexUnlock`, T3 must show that every run of the generated
`ConcM` code is a run of `ioMutex` under an abstraction of `Mem` that maps:

* the word to `AWord` (its value, and the release view of its newest message);
* the protected heap to the views (the clocks of `Lock.Owns`);
* the futex rows to the T2 instance.

That forward simulation covers each sync op of the generated code (`cmpxchgAsC`,
`atomicRmwAsC .xchg`, the futex rows) plus the plain steps in between. In the meantime,
`Conc/Lock.lean` already proves the generated `Io.Mutex` code correct in the concrete model with
the hand futex, so the gap is narrow:

* **Re-derived at the algorithm level.** The `Io.Mutex` lock protocol (exclusion, ownership
  transfer, no deadlock) holds over every `FutexSpec` futex (`ioMutex_spec`). The witness
  argument of `Lock.Inv.wit` needs only `wait_word` (the recheck) and `wake_one`, and not FIFO.
* **Already concrete.** On `codex/roadmap-batch7`, `Lock.lean` handles spurious returns
  (`Inv.spurious`, `Inv.spuriousOff`, and the spurious case of `wp_waitOn`/`wp_waitD`).
* **The gap in the concrete proof.** `Inv.wake` relies on the hand wake's FIFO choice
  (`woken = first n at p`). Re-basing it on T2's subset oracle means proving that the woken
  thread, whichever it is, is asleep at the word and becomes the witness. This is the argument
  of `ioMutex_step`'s `wake` case. `Inv.wait` must take the atomic read's footprint entry
  (`Inv.record`). `THR-05` is then replaced by OSF-01/02 for 0.16.0.
* **Outside the abstract layer.** The RC11 clock details, which `AWord`'s single message view
  approximates: adoption on acquire instead of a join, which is enough for one resource per
  lock. Byte-level ownership (`Owned`). Cancellation (`lock` can return `Canceled`; that is T5,
  `IoSpec`).
