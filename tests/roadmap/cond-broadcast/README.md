# C14: condition broadcast

`cond_broadcast.zig` references std's condition broadcast of the Zig version that compiles it:
`Io.Condition.broadcast` (0.16.0, 0.17.1) or `Thread.Condition.broadcast`, which is
`FutexImpl.wake(.all)` (0.14.1, 0.15.2). `exports.json` exports it for every supported version
into `air/<version>` (pinned by `exports.lock.json`).

The contract is `CondImpl.broadcast_wp` (`ZigLean/Sep/Full/Cond.lean`): a thread out of the
condition's code, outside or holding the mutex, returns with its caller part and the history post
`FCond.SigPost … true`: the state write it read or wrote at or after every write that happened
before its call is served (`waiters ≤ signals`), so every waiter registered before the call has
its signal. Every implementation proves it: `Sync.ioCond` (`Proofs/Sync/Cond.lean`,
`Io.Condition.broadcast`, which `examples/sync` references) and `Threadsync.threadCond`
(`Proofs/Threadsync/Cond.lean`, `Thread.Condition.broadcast`, referenced by
`examples/threadsync`).

| Version | std function | Proved translation it equals |
|---|---|---|
| 0.17.1 | `Io.Condition.broadcast` | `tests/golden/0.17.1/sync/Gen.lean` |
| 0.16.0 | `Io.Condition.broadcast` | `Proofs/Sync/Gen.lean` |
| 0.15.2 | `Thread.Condition.broadcast`, `FutexImpl.wake(.all)` | `Proofs/Threadsync/Gen.lean` |
| 0.14.1 | `Thread.Condition.broadcast`, `FutexImpl.wake(.all)` | `Proofs/Threadsync/Gen.lean` |

`check.sh` translates each export and requires every translated function to equal, line for
line, the same function of the proved program's translation, so the theorem about the proved
one is a theorem about each version's code. 0.14.1's `Thread.Condition` differs from 0.15.2's
only outside `wake` (`std.time.sleep` in its timed wait), and its translation is the same.

```sh
lake build air2lean
bash tests/roadmap/cond-broadcast/check.sh
bash tests/roadmap/cond-broadcast/check.sh --export    # needs the patched compilers
```

Scope: no client in the examples calls broadcast, and the fixture has no native run. Timeouts
and cancellation (`Io.Condition.wait`, `waitTimeout`) stay outside the contract (register C14).
