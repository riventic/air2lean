# Futures (`std.Io.Future`, Zig 0.16.0)

`Io.Group` support is **not** general async support. Groups are a separate model
([std-models.md](std-models.md) §Thread model, [spawn-failure.md](spawn-failure.md)). Futures
are qualified separately, and only for the APIs listed here. Every other `std.Io` async,
cancelation or I/O-operation API is rejected with a reason, or has no model.

## Qualified APIs (Zig 0.16.0 only)

| Zig API | Model (`ZigLean/Conc/Future.lean`) | Notes |
| --- | --- | --- |
| `io.async(function, args)` | `Zig.asyncC`, `Zig.asyncWithPolicyC` | Any worker result type `T` that the memory model encodes. |
| `Future(T).await(io)` | `Zig.awaitC` | Returns the task's complete result. An `E!T` result propagates its error. |
| `Future(T).cancel(io)` | `Zig.cancelC` | Returns the task's result or the `error.Canceled` that the task propagated. |
| `io.checkCancel()` | `Zig.checkCancelC` | The only cancelation point that the model delivers. |

The table rows are in `Air2Lean/StdModels.lean` and are version-qualified to `0.16.0`. The
translator maps `Io.Future(T)` to `Zig.Future T` (`Ty.future`). It checks the exporter's field
offsets (`any_future` at 0, `result` at `alignUp 8 (align T)`) and the worker's signature
against the future's result type.

## Rejected APIs

| API | Reason |
| --- | --- |
| `Io.concurrent` | Its guaranteed unit of concurrency and `ConcurrencyUnavailable` are not modelled for futures. |
| `Io.recancel`, `Io.swapCancelProtection` | Re-arming and cancel protection are not modelled. |
| `Io.Select(U).async/concurrent/await/cancel/cancelDiscard` | Select queues task results. Only `Io.async` futures are qualified. |
| `Io.Batch.awaitAsync/awaitConcurrent/cancel`, `Io.operate`, `Io.operateTimeout` | Io operations and batches are not modelled. |
| `Io.sleep`, `Io.futexWaitTimeout` | The model has no clock. |
| A cancelation point other than `Io.checkCancel` that an `Io.async` task can reach, in a program that calls `Future.cancel` | This covers a cancelable `Io.futexWait` (also inside `Io.Mutex.lock` or `Io.Condition.wait`), `Io.Group.await` and a nested `Future.await`. std would deliver the request there, but the model does not (`checkFutureCancelation`). |

## Semantics

These rules follow the audited `lib/std/Io.zig` and `lib/std/Io/Threaded.zig` of 0.16.0.

- **Task states.** `Io.async` allocates a runtime record (`Io.AnyFuture`, `Future.slotAlloc`)
  and spawns the task. The task is a thread. It is *pending/running* until its last step writes
  the worker's result into the record (`Future.complete`), and then it is *completed*. `await`
  and `cancel` *consume* the future. They join the task, copy the result into
  `Future.result`, free the record and set `any_future = null`.
- **Await** returns the result. Error unions are values, so a task's `error.X` reaches the
  awaiter unchanged.
- **Cancel** first passes a scheduling point (std's request is an atomic status update). It then
  records a request (`Mem.cancels`) and awaits. A task observes the request only at
  `Io.checkCancel`. That point acknowledges the request once and returns `error.Canceled`. A
  task that completes without reaching it returns its ordinary result. An unacknowledged
  request is dropped. Cancel never invents a result: it returns the task's own value.
- **Idempotent, as std documents.** `await`/`cancel` on a consumed future return the stored
  `result` without a sync op (`Future.awaitC_consumed`). The native fixture `awaitTwice`
  confirms this behaviour. A *second sequential* await is therefore not illegal.
- **Not threadsafe.** Two threads that await one future concurrently race on the `Future`
  value, or join a task they did not spawn. The result is `.illegal`. Only the spawner may
  consume a future (`Thread.join`).
- **Must be consumed.** Only `await`/`cancel` release the record and join the task. A spawner
  that ends with an unconsumed future fails `checkJoinedByChild` (`.illegal`). The model
  reports this as a leak.
- **Spawn policy.** `available` (the default) assigns every task. `fallible` (`--spawn-policy
  fallible`) also covers the audited `Io.Threaded.async` fallbacks: record allocation failure,
  the async limit, a failed worker spawn, and single-threaded builds. Each fallback runs the
  task in the caller, so the future is born consumed. In that case there is no record, no thread
  and no ownership transfer.
- **Ownership.** The task gets its by-value argument tuple as a spawn target. `Tgt.captures`
  classifies every field for `Zig.Conc.Capture.grant`, as for `Thread.spawn`. The task owns the
  result cells of its record until the join returns them to the awaiter. The record is not a
  capture.

## Proofs and evidence (`tests/roadmap/futures`)

`ZigLean/Conc/FutureLemmas.lean` holds the semantic rules. It is proof-only and is not part of
`ZigLean.lean`. It provides the result-cell rules (`Holds`, `complete_holds`, `take_eq`), the
round trips of pending and consumed futures, idempotence, and a rely-guarantee protocol for one
task (`futureProto`). The protocol has a task rule (`task_wp`), spawner rules (`wp_asyncC`,
`await_wp`, `cancel_wp`) and a cancelation-point rule (`wp_checkCancelC`).

`Futures/Proofs.lean` applies these rules to the **generated** code of `futures.zig`. The
results are partial correctness over every oracle and every fuel (`Conc.run_sound`):

- `awaitValue_result`: every result is `x *% x` (completion).
- `awaitError_result`: every result is the task's `error.Zero` or `x - 1` (error propagation).
- `cancelValue_result`: every result is `x +% 1` or `error.Canceled`. It is never another
  value (cancelation).
- `second_await`, `consumed_reads_back`: idempotence.
- `leak_illegal`, `foreignAwait_illegal`, `doubleAwait_illegal`: kernel-checked schedules
  (`decide +kernel`) that report `.illegal`. `join_foreign_illegal` is the model rule behind
  them.

`Futures/Runtime.lean` and `FallibleRuntime.lean` enumerate **every** schedule (and policy
choice) of each fixture and of the negative clients. Both cancel outcomes occur. Every schedule
of leak, foreign await and concurrent double await is `.illegal`. `native.zig` runs the same
source on stock Zig 0.16.0 `Io.Threaded`, with assigned tasks and with `async_limit = .nothing`.
`check.sh --export` re-exports fresh AIR with a patched compiler and requires the committed
translation.

## Limits

- The all-schedule proofs are partial correctness: an error or no result satisfies them. No
  schedule is proved free of errors (strict mode). The negative results hold for every
  enumerated schedule at runtime, and the kernel checks one schedule.
- A `Future.cancel` request is delivered only at `Io.checkCancel` (see Rejected APIs).
  `Io.Group.cancel` (C05, [std-models.md](std-models.md#spurious-wakeups-and-cancelation)) shares
  the request set `Mem.cancels`: its requests are also delivered at cancelable futex waits and
  `Io.Group.await`, and at `Io.checkCancel` when a group task reaches it.
- Only the spawning thread may consume a future. std allows a future value to be moved to and
  awaited by another thread. The model rejects that as `.illegal`.
- The model has no fairness, termination, timing or native allocator claim.
