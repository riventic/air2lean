# Opt-in timed scheduler foundation

`ZigLean.Time` and `ZigLean.Conc.TimedSched` are explicitly imported modules, absent from
the runtime umbrella. Existing `SyncOp`, `Sched.run`, strict deadlock rules and translated
calls retain their behavior. This foundation does not make `Io.Clock.now` or
`Io.futexWaitTimeout` supported by the translator. The selected source adapter and its
generated-client proof require separate qualification.

The smallest selected source boundary is awake observation, a finite nonnegative i96
absolute deadline or zero duration, and one caller waiting on an owned u32 with a framed
sentinel. The implementation additionally represents checked nonnegative awake durations
and unbounded waits. Other clock kinds, negative values, overflowing durations, cancellation
and OS correspondence are outside this boundary. `defaultEnvNoClock` returns the existing
model's unspecified error at clock-dependent operations. No timestamp is clamped.
Every Program.wait, including an unbounded wait, requires the selected awake environment.

The working v5 atomic-comparison candidate is documented separately in
`docs/deadline-atomic-compare.md`; the v4 qualification below applies to its frozen inputs.

The observation environment supplies timestamps below 2^95 and proves observations are
nondecreasing. Equal observations remain valid indefinitely. `Environment.awake` requires
a separate `NoCancellation` witness. The scheduler snapshot retains that selected
environment and its observation cursor across `resume`; callers do not provide a new clock
when resuming. Arbitrarily editing a snapshot is not a validated environment transition.

Frozen v4 `Kernel.begin` validates the pointer and performs a tracked atomic read before comparing
the newest bytes. It rejects overlapping waits by this owner. The read records a footprint
and bumps the caller's own vector clock; it creates no acquire edge. Concurrent plain writes
are rejected by the ordinary race rule. Matching unexpired words are enqueued in
`Mem.waiters`, paired with the registration and a `Control.waiting` continuation. That
continuation executes only after a normal-return event. Fuel exhaustion retains it and the
registration in `Outcome.state`; it does not return source Unit.
This kernel comparison supplies no source atomic-load message/view bookkeeping or mixed
atomic-width correspondence; those require separate source integration contracts.

A blocked caller has an observation event even when no time advances. The environment may
wake queued owners at that same observation boundary. Wake, timeout and spontaneous normal
return become independent oracle choices: when a queued waiter is woken at its deadline,
either wake or timeout can win. Spurious return is always available for a registration.
Every normal-return event removes this owner's registration, queued entry and every pending
wake marker, preserving other owners' entries. Subsequent wakes cannot resurrect that wait
or leak a marker into its next wait. Release and wake change no bytes, access evidence or
vector clocks. They provide no acquire edge.

The interpreter is a single-caller program tree with explicit environment wake events.
Ordinary MemM operations run through Program.memory/liftMem, preserving their memory and
error checks. The interpreter does not model spawning, notifier completion or joins.
Success is partial correctness of this boundary, with no fairness, eventual completion or
wall-clock claim. A client must recheck its predicate and time after every normal return;
the continuation receives Unit and cannot infer the internal reason. Resource reclamation
requires absence of registrations and independent ownership/task lifetime evidence.

`tests/roadmap/deadline-futex/Kernel.lean` proves cleanup, framing, Unit resumption, zero-fuel
snapshot retention and agreement with the legacy memory wake function. `Runtime.lean`
checks mismatch, zero duration, equal and later times, indefinite equal-clock blocking,
spurious return, wake-before-expiry, simultaneous wake/expiry, repeated waits, stale marker
removal, other-owner framing, pointer rejection and tracked atomic-read race handling.
ROOT qualified frozen v4 on 2026-10-06: both module builds, all eleven kernel proofs,
and the executable Runtime.lean model suite passed in its serialized Linux container lane.
The retained container receipt is
`/artifacts/c04-runtime-q1/deadline-runtime-vjpo61a0/report.json`; the host runner log is
`/private/tmp/air2lean-C04-runtime-v4-local.log`. The frozen source hashes and scope are
recorded in `tests/roadmap/deadline-futex/foundation-qualified-v4.json`.
These results qualify this opt-in, single-caller model foundation under the selected bounded
monotone awake environment and explicit NoCancellation premise. They establish no
translated public-source API support, atomic message/view correspondence, native or OS
correspondence, cancellation behavior, fairness, liveness, or notifier/task completion.

ROOT owns all toolchain execution. A prepared recipe is available without executing tools:

```sh
python3 tests/roadmap/deadline-futex/root-runtime.py
```

From ROOT's frozen source extraction inside its existing serialized lane, qualification is:

```sh
AIR2LEAN_ROOT_LANE=1 python3 tests/roadmap/deadline-futex/root-runtime.py --execute --artifacts /private/tmp
```

The recipe uses no compiler-version probes and runs each build/check sequentially. It
retains the transitive local Lean source closure, verifies each retained copy, and detects
persistent source drift at completion. It requires ROOT's external freeze: an edit reverted
before the final hash check is not detected by this recipe. Every reap follows TERM and
KILL to the whole process group. Timeout cleanup allows a TERM grace period; after an
observed normal leader exit, remaining workers are cleared without a grace period.
Execution requires POSIX waitid with WNOWAIT in ROOT’s Linux container. Exit polling
does not reap the leader. Scoped INT/TERM handlers record requests during process creation
and cleanup; requests become exceptions only at controlled boundaries after the process is
owned. This preserves the process-group anchor until cleanup and records an interrupted
receipt. A cleanup error fails qualification even when the leader exits successfully.
The frozen v4 inputs passed all four commands. Any subsequent runtime or proof change
requires qualification of its new frozen inputs; this result does not qualify the separately
owned selected source adapter or generated clients.
