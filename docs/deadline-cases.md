# C04 named deadline cases and solver budget path

Opt-in timed interpreter only; [deadline-runtime.md](deadline-runtime.md) describes its
foundation.

`tests/roadmap/deadline-cases/Contracts.lean` states the four C04 cases as kernel and
interpreter theorems over explicit awake observations. Deadline boundary: a matching word
whose deadline equals (or precedes) the current observation returns timeout without
registering; one nanosecond earlier it registers. A mismatching word is decided first.
Timeout: a registration may time out exactly when the latest observation has reached its
deadline; an earlier timeout is a model error that retains the snapshot; the next
observation reaching the deadline enables timeout whatever wake it delivers.
Wake-before-timeout: a woken caller before its deadline has wake enabled and timeout
disabled. Wake-at-timeout: both are enabled, and the two post-states differ only in the
internal reason log, so the race is not source-observable. The selected adapter rejects
wall-clock (`real`) deadlines, durations and clock reads.

`ZigLean.Conc.TimedBudget` is an opt-in solver budget client, absent from the runtime
umbrella. Clock kinds are separate types: `Time.Timestamp` (awake monotonic observation),
`MonoDuration` (monotonic budget length) and `WallTimestamp` (signed wall clock, no order
contract, no coercion). `solveWithin` observes a start, derives `start + budget` without
clamping (overflow is the `unrepresentable` outcome) and checks the monotonic clock before
every solver step; `pausedLoop` additionally pauses on an owned word with the same
deadline and rechecks the clock after every wake, timeout or spurious return. `*_sound`
proves, for every oracle, fuel, wake schedule and selected awake clock, that a returned
`solved` was produced by a reachable solver state at an actual observation before the
deadline, `expired` was decided at an actual observation at or after it, and `capped` is
a distinct outcome. Safety assumes no fairness. `loop_decides` is the only liveness
statement and requires an explicit premise that observation `k` reaches the deadline with
`k` below the iteration cap. The paused loop has no liveness claim: an oracle that only
observes an equal clock keeps it paused. `Runtime.lean` in the same directory executes
these cases, the cap, an equal clock, overflow, and type errors for wall or duration
values passed as deadlines. CI runs both files. No translated source call, OS clock,
cancellation or native correspondence is claimed.
