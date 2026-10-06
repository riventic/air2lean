# Selected single atomic comparison candidate

This v5 candidate replaces the timed kernel's v4 newest-byte comparison with exactly one
existing `atomicLoadAt` action of width 32, alignment 4 and relaxed ordering. The accepted
v4 archive and its receipt remain unchanged. The working v5 runtime is unqualified until
ROOT runs the separately frozen v5 qualification recipe.

`Inputs.readChoice` supplies a readable-option index for each attempted comparison.
`State.reads` stores that cursor across resumptions, independently of time observations and
scheduler-event choices. Index zero is the default and means the newest currently readable
option. No index is clamped or reduced modulo the option count; invalid indices retain the
existing atomic load's error. An awake observation and checked timeout resolution precede
consuming the comparison choice. A rejected overlap is still an attempted comparison but
performs no atomic read.

`readWord` is definitionally the existing relaxed `atomicLoadAt` action. Its preparation
validates access and records a single atomic-read footprint before `locIdx`, `readOpts` and
selected-message decoding. Completion records the selected message id in `seen`. Relaxed
ordering adds no acquire edge. A mismatch or expired matching value returns normally after
that read; a matching unexpired value registers the post-read memory and pauses the same
Unit continuation as v4. Wake, expiry, spurious return and normal cleanup retain their
existing behavior. Cleanup preserves the coherent seen floor and frames other owners.

The source-side `TimedCompare` contract is owned and qualified separately. It uses the
existing `Conc.Proto.atomicLoadAt_ok` event witness, including access, race exclusion,
location preparation, readable choice, decoding and final `loadM` state. Agreement with a
current-byte comparison additionally requires an explicit selected-message bytes premise.
Two readable messages can produce different predicate results; there is no unconditional
state or value equivalence to the v4 newest-byte comparison. No extra source read is
prepended to `Program.wait`.

`AtomicKernel.lean` checks the action identity, conditional enqueueing of the post-read
state, coherent-floor preservation on cleanup and the relaxed-load frame. `RuntimeAtomic.lean`
checks newest and older messages, multiple readable choices, an invalid choice, a seen
floor that removes the older option, retained choice cursors, repeated waits, single-read
footprints, concurrent plain-write rejection, atomic-footprint acceptance, expiry, source
location creation and location-width rejection. The original kernel and runtime regressions
also run against the v5 candidate.

ROOT owns actual execution in its existing serialized Linux Docker lane:

```sh
AIR2LEAN_ROOT_LANE=1 python3 tests/roadmap/deadline-futex/root-atomic-runtime.py --execute --artifacts /private/tmp
```

Without `--execute`, this prints the plan without starting toolchains. It reuses the v4
bounded process supervisor, retains the transitive local source closure and requires ROOT's
external frozen-input isolation. This candidate adds no UI or default CLI enablement. It
retains the bounded monotone awake and explicit NoCancellation premises. It establishes no
OS correspondence, cancellation behavior, fairness, liveness or notifier/task completion.
