# Sync contracts: where the retired `Conc/Spec` results live now

`ZigLean/Conc/Spec/` (`FutexSpec`, `MutexSpec`, `EventSpec`, `WaitGroupSpec`, `CondSpec`, and
their toy instances) was phase T3 of [thread-io-translation.md](thread-io-translation.md). It
proved hand transcriptions of std's sync algorithms over an abstract futex, as transition systems
with one message view per word. Nothing outside the directory imported it. Its own plan for
carrying the results to generated code was a forward simulation, which was never built. Instead,
the full-state logic proves the generated code itself. So the directory was deleted
(`docs/legacy-retirement.md`). This page records, for each result, the full-state theorem that
replaces it, and what has no replacement.

## The map

| Retired (`ZigLean/Conc/Spec/…`) | Full-state replacement |
|---|---|
| `Sys`: systems, reachable states, inductive invariants, `Enabled` | `Proto` (`inv`, `strict`, `Live`), `Proto.Step`, `run_spec`/`run_safe` (`ZigLean/Conc/Logic.lean`) |
| `Futex`: `FutexSpec` (recheck, spurious returns, a wake of an arbitrary set of waiters, no happens-before edge, progress) | The model futex is that contract: `Proto.Step`'s `.wait`/`.wake` (`ZigLean/Conc/Logic.lean`) over `Thread.futexWait`/`futexWake` (`ZigLean/Mem/Thread.lean`, run by `ZigLean/Conc/Sched.lean`). A wait compares the word atomically and sleeps only on a match, or returns spuriously in place of the sleep (`Sched.spuriousWake`). A wake wakes `min n k` waiters that the oracle picks (`Thread.wakePick`, no queue order), and gives no edge. A sleeper leaves the queue only through a wake, a cancelation request (`Thread.requestCancel`) or an OS interrupt (`Os.interrupt`, OSG-01). Each OS futex is proved against these rules: `WP.osFutexWait`, `WP.osFutexWake` and the rows `WP.futex_4arg`, `WP.futex_3arg`, `WP.ulock_wait2`, `WP.ulock_wake` (`ZigLean/Sep/Full/OsFutex.lean`, premises OSF-01/02) |
| `FutexToy`: `ref`, `fifo` and `spin` meet `FutexSpec`; `lazyWake` and `noRecheck` do not | not restated: the full-state futex is the model's, not a parameter, so no client proof can be instantiated with a broken futex. A real futex enters only through its OS row, which must reduce to the model's wait and wake (`OsFutex.lean`) under OSF-01/02. The same holds for `IoMutex`'s `lazyWake_deadlock`/`noRecheck_deadlock` |
| `Mutex`: `MutexSpec` (`excl`, `view`, `live`) | `MutexImpl` (`ZigLean/Sep/Full/Mutex.lean`): `lock_wp`/`unlock_wp` for every protocol that has the lock (`FLock.Fits`). Exclusion: `LockWord.WInv.one`. Ownership transfer: the lock's resource `rL` moves to the holder, with the clocks of `LockWord.Owns` and `WInv.rel`. No deadlock: `WInv.wit` with strict mode's `Proto.Live` |
| `IoMutex`: std `Io.Mutex` meets `MutexSpec` over every `FutexSpec` futex; it deadlocks over `lazyWake` and `noRecheck` | `IoMutexCode.impl` (`ZigLean/Sep/Full/IoMutex.lean`): `Io.Mutex`'s generated code (0.16.0; 0.17.1 is the same code) meets `MutexImpl` once for every program. Instances: `Sync.ioMutex` (`Proofs/Sync/IoMutex.lean`) and `Proofs/Iogroup/Lock.lean`. 0.15.2's `Thread.Mutex` meets `MutexImpl` by its own proof (`Threadsync.threadMutex`, `Proofs/Threadsync/ThreadMutex.lean`). The proof covers spurious returns and any choice of woken waiters, because the model futex allows both (the `Futex` row) |
| `MutexToy`: a spin mutex meets `MutexSpec`; one with a `monotonic` `unlock` does not | none yet (below) |
| `Event`: `EventSpec`, and a spin event that meets it | `EventImpl`/`FEvent` (`ZigLean/Sep/Full/Event.lean`): the waiter returns synchronized with the set (`FEvent.Synced`), and its sleep is no deadlock (`hlive`). Instances on generated code: `Sync.ioEvent` (`Io.Event`, 0.16.0/0.17.1) and `Threadsync.resetEvent` (0.15.2). `EventSpec`'s only instance was the toy spin event. `EventImpl.wait_wp` admits one waiter at a time (`hone`) |
| `Count`: `tsum`, `Lat` | `ZigLean/Sep/Full/TSum.lean`; views are vector clocks (`VClock`) |
| `WaitGroup`: `WaitGroupSpec`; std `Io.Threaded.WaitGroup` meets it over every `FutexSpec` futex | The same algorithm (a counter with `is_waiting`/`one_pending` and an event), as 0.15.2's generated `Thread.WaitGroup`, is proved in `Proofs/Threadsync/WaitGroup.lean` (`waitGroup_spec`, `waitGroup_safe`: the waiter sees every task's write, no data race, no deadlock). It is a client of `MutexImpl` and `EventImpl`. 0.16.0 and 0.17.1 have no public `WaitGroup`. `Io.Threaded`'s private one counts the pool's workers, and the model's `Io.Group` replaces that pool (`docs/std-models.md`, STD-08), so no generated code runs it |
| `Cond`: `CondSpec`; std `Io.Condition` with `Io.Mutex` meets it over every `FutexSpec` futex, for at most 65535 threads and fewer than `2^32` signals | `CondImpl`/`FCond` (`ZigLean/Sep/Full/Cond.lean`, `CondInv.lean`, `CondEpoch.lean`). Instances: `Sync.ioCond` (`Proofs/Sync/Cond.lean`) and `Threadsync.threadCond` (0.15.2). No lost wakeup: `Inv.noDeadlock`. The thread bound is the wait entry's `hroom` (fewer than `65535` registered waiters), the `2^32` bound the client's `Fits.win` (engine-ledger row `cond-window-multi-waiter`). `CondImpl.wait` is the uncancelable wait, as `CondSpec`'s was |

## What has no replacement yet

* A generic wait-group contract (`WaitGroupImpl`): engine-ledger row `waitgroup-impl-contract`.
* A witness that `MutexImpl` rejects a `monotonic` `unlock`, as `MutexToy.relaxed_not_spec`
  did for `MutexSpec`: engine-ledger row `mutex-impl-relaxed-witness`.
* The `Io` futex slots as a contract that every `Io` implementation proves (today
  `futexWaitC`/`futexWakeC` are the model futex itself): STD-05's open part
  (`docs/std-models.md`) and `IoSpec` ([thread-io-translation.md](thread-io-translation.md)
  section 4.1).
