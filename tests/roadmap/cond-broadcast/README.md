# C14: condition broadcast

`cond_broadcast.zig` references std's condition broadcast of the Zig version that compiles it:
`Io.Condition.broadcast` (0.16.0, 0.17.1) or `Thread.Condition.broadcast`, which is
`FutexImpl.wake(.all)` (0.14.1, 0.15.2), with `Thread.Futex.wake`. `exports.json` exports it
for every supported version into `air/<version>` (pinned by `exports.lock.json`).

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
| 0.15.2 | `Thread.Condition.broadcast`, `FutexImpl.wake(.all)`, `Thread.Futex.wake` | `Proofs/Threadsync/Gen.lean` |
| 0.14.1 | rejected | none |

`check.sh` translates each export and requires every translated function to equal, line for
line, the same function of the proved program's translation, so the theorem about the proved
one is a theorem about each version's code. The wake goes down to the translated
`Thread.Futex.wake`. 0.14.1's `Thread.Futex.LinuxImpl.wake` calls `math.cast`, which 0.15.2's
proved wake does not, so it is not the proved code. The export holds no `math.cast`, so the
translator rejects 0.14.1 (`the callee 'math.cast…' has no AIR file and no model`), and
`check.sh` requires that rejection. `examples/threadsync`, the proved implementation, is
0.15.2-only.

## The client

`examples/threadsync` has `handoffAll` (Zig 0.15.2): the hand-off whose producer, `producerAll`,
calls `Thread.Condition.broadcast`. Its proof uses only the contracts:

- `Handoff.wp_broadcast` (`Proofs/Handoff/Ops.lean`), once for every layout and every
  `CondImpl`: the producer's broadcast step from `CondImpl.broadcast_wp`. The post with
  `all = true` gives the signal's post (`FCond.SigPost.mono`), so the registered waiter is
  signalled.
- `Threadsync.HO.handoffAll_spec` (every completed run returns 7) and `handoffAll_safe` (no data
  race, no deadlock, no panic, under every schedule) in `Proofs/Threadsync/Handoff.lean`: the
  walk of the generated code with `Threadsync.threadMutex`, `threadCond` and `resetEvent`.
- The differential test runs it natively and in the model (`tests/diff/threadsync`).

`mutations.py` holds the client's designated mutants. Each is one change of `producerAll` in
the committed translation, built in a check tree where the sync objects' contract proofs must
still build and `producerAll_spec` must fail:

| Mutant | Change | Killed by |
|---|---|---|
| `broadcast-is-signal` | `signal` in place of `broadcast` | the client's proof: it has the broadcast contract's rule only |
| `broadcast-dropped` | no wake-up | the client's proof: the producer does not reach its `set` place (a lost wake-up) |

The client has one waiter, the main thread, so `broadcast-is-signal` is still a correct program
and the differential run does not tell it from the original. A client with two or more waiters,
where the signal leaves a waiter asleep, is open (register C14).

```sh
lake build air2lean
bash tests/roadmap/cond-broadcast/check.sh
bash tests/roadmap/cond-broadcast/check.sh --export    # needs the patched compilers
```

Scope: the client is 0.15.2's `Thread.Condition`; no client calls `Io.Condition.broadcast`
(0.16.0, 0.17.1) yet. Timeouts and cancellation (`Io.Condition.wait`, `waitTimeout`) stay outside
the contract (register C14).
