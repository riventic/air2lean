# C04 first boundary: design and probe preparation

Prepared from main 302996f. ROOT qualified the separate Time/TimedSched foundation
and the bounded selected generated interpreter candidate. The latter is not std source
atomic or OS conformance qualification. C04 stays incomplete; C05 and E03 stay open.

The original roadmap asks for monotonic observations, deadlines, timeout and wake races
(C04), separate cancellation/spurious cleanup (C05), and explicit environment boundaries
(E03). The existing scheduler has only unbounded wait/wake, queued waiters in Mem and no
happens-before edge on wake. Threadsync.Deadline proves the no-timeout path for Zig15;
it does not supply a clock theorem. StdModels.stdModels currently maps Timer/timedWait to
clock-free models and leaves Io.futexWaitTimeout outside the admitted fragment.

Zig16 source corrects the suggested API: std.Thread.Futex.timedWait is absent from
Thread.zig. The selected public entry is std.Io.futexWaitTimeout, whose timeout union
contains none, duration and deadline, with a tagged Clock. It returns Cancelable!void.
Timeout, wake and spurious wake all return normally; error.Canceled is separate. It is
unsound to turn timeout into a source error union member or infer the reason from success.
The first probe therefore selects .awake, an i96 timestamp and absolute deadline, plus
zero duration and a concrete cleanup client. Its native checks assert no measured latency.

## Proposed observation environment

Keep observations separate from scheduler choices. A selected environment supplies
nonnegative awake timestamps, monotonically nondecreasing across actual observations;
equal successive observations are permitted. This is an explicit model premise, not a
theorem about an OS clock. A finite observation prefix must be extendible without requiring
strict advancement. Invalid decreasing observations must be rejected as invalid model
input, rather than silently clamped or reported as a program race. Initial implementation
should admit only awake/deadline values in a checked representable nonnegative i96 range;
negative durations, saturation and other clocks need separate contracts or rejection.

No state field or SyncOp constructor is selected yet. Actual exported callee names,
layouts, signed-width handling and pointer casts determine the narrow checked adapter.
The probe may expose indirect vtable calls, tags or layouts unsupported by today's
translator. Those are recorded blockers; do not replace actual AIR with a synthetic body.

## Wait boundary and simultaneous events

At a timed wait turn, validate the same pointer access/footprint boundary as the existing
futex path and atomically compare the word before enqueuing. A mismatched word returns
normally without waiting. A matching word with observed now >= deadline may return
normally with an internal timeout reason. A matching, unexpired word may enqueue.

At subsequent observation/event boundaries, a queued waiter with now < deadline may
return through a matching wake. With now >= deadline it may return through timeout.
If a matching wake and expiration are both enabled at the same boundary, both resolutions
must be admitted, with identical source Unit success and distinct internal evidence.
Selecting either removes precisely that waiter and consumes its pending wake bookkeeping;
a later wake cannot resurrect it or leave a stale woken entry for its next wait. Timeout
alone gives no memory clock/acquire edge. Do not classify a timed queue as deadlocked merely
because no ordinary thread is currently runnable: enabled environment events need explicit
participation. Conversely no enabled event need be chosen within finite scheduler fuel.

C05 cannot be hidden: the real API permits spontaneous wake and cancellation. A restricted
first theorem can quantify only over an explicitly no-cancellation selected environment
and include normal spurious return as another permitted internal reason. If that reason is
excluded, label the theorem as a reduced environment theorem, never all native API behavior.
Full cancellation ownership/task cleanup remains a separate implementation and proof scope.

## Client and proof obligations after the actual probe

Prove partial correctness of a predicate-checking loop that observes awake time, waits at
most until a fixed deadline, then rechecks the predicate and time after every normal return.
Its returned status is a caller decision from the rechecks, not the wake reason. At the
deadline boundary choose an explicit predicate-versus-expiration priority and test it.
Start with owned stack state and a disjoint literal sentinel; successful completion must
retain the sentinel, leave no waiter/wake registration and free only after those obligations
are discharged. A spawned notifier adds independent join/lifetime requirements; omit it
from the first client rather than assuming a wake means its task has finished.

Prove observation monotonicity, wake/timeout/spurious registration removal and a framed
wait contract before composing the client. Exercise earlier, equal and later observations,
predicate mismatch, wake before expiration, simultaneous wake/expiration and repeated
spurious return. An infinite equal-time or spurious sequence is allowed: there is no fairness,
eventual completion, wall-clock, cancellation-completeness or fuel-independent termination
claim. Successful native smoke runs are API observations, not evidence for these theorems.

## ROOT handoff

Freeze this worktree including the new files and extract it inside the prepared Linux
container. Set DEADLINE_SOURCE_ROOT to that extraction and run root-probe.sh sequentially
under the owned toolchain/cache lock. The recipe uses the cached stock 70e496 and patched
08aafd Zig16 installations under /opt/toolchains; it performs no compiler bootstrap or Lean
execution. Retain actual AIR, lowering inventory, pinned API source, source/tool hashes and
native logs under /artifacts/deadline-futex-probe. Inspect all four public function exports
and the exact pinned API before authoring any model. New formal code later needs independent
MED8 review and ROOT kernel qualification.

ROOT reports that the four-function AIR export passed, while the original Threaded native
build exhausted its 300-second bound. That is not a native PASS. The separate native-mock.zig
fixture initializes only VTable.now and VTable.futexWait: the selected public API call closure
reads only these fields, and calls no Io lifecycle operation. Other fields remain undefined
and must never be inspected or invoked. Set DEADLINE_NATIVE_SOURCE to that file for a fresh
ROOT attempt. Its equal observations and wake/timeout boundary cases are deterministic mock
environment observations only; OS clock/futex conformance remains unqualified.

ROOT subsequently reports the lightweight callback native fixture passed under Zig16 GNU
ReleaseSafe baseline. The earlier AIR export used musl; these are deliberately separate
feasibility steps, not a paired-target model qualification. Diagnostics locally normalized
and checked all four functions; remaining program blockers are missing Io.Clock.now and
the explicit unsupported/no-clock Io.futexWaitTimeout call. Original Threaded OS smoke
remains timed out and no OS clock conformance follows.

The isolated Deadline.lean transition-relation prototype has been retired in favor of the
authoritative Zig.Time and opt-in TimedSched interpreter owned by the runtime lane.
TimedCall.lean now supplies a source-shaped, typed bridge using Program.observe and
Program.wait. A wait continuation is actually retained by the interpreter's waiting control;
it returns source Except ErrName Unit success after normal return, with no exposed reason.
These bridge values have no Enc instances and are not actual emitted type replacements.
ROOT ran Adapter.lean successfully in selected q3 after independent static review. Default translator rejection and the existing runtime are unchanged.

For actual translator support, a separate explicit selected-environment option must be
threaded through Check, program dependency validation, memory/concurrency classification
and emission together. Recognition by name alone is insufficient. Gate Zig16 schema12,
the selected target/profile, Io argument, const one-pointer to u32 with alignment4, u32
expected argument and exact error{Canceled}!void result. Clock.now argument order is
clock,Io and result Io.Timestamp. Match Clock's exhaustive u3 real/awake/boot/cpu_process/
cpu_thread tags0..4, Timestamp/Duration signed-i96 field at0 with size16 alignment16,
clock-tagged payload raw@0/clock@16 size32 alignment16, and Timeout tagged none/duration/
deadline order0/1/2 size48 alignment16. Validate normalized layouts rather than fixed local
type IDs. Runtime projections still reject a non-awake tag, negative timestamp/duration,
unbounded .none in this selected adapter and overflowing duration resolution.

The emitter must generate a TimedSched.Program path including ordinary memory operations;
an immediate Result/ConcM wrapper around the wait would defeat paused continuation semantics.
Unknown timed calls remain unsupported under ordinary emission. Do not retrofit the existing
Sched or protocol theorems without explicit proof migration. The bridge tests currently
exercise the real paused timed interpreter, but not translated AIR execution. Allocation,
source predicate/time recheck, frame preservation and task reclamation are later client
composition obligations, not consequences of a successful Unit wait.

TimedClient.lean is a separate, unqualified composition candidate using Program.liftMem:
it allocates an eight-byte owned stack block, initializes its predicate and sentinel,
waits with a retained continuation, then loads the predicate, observes time, reads the
sentinel and frees the block. A mismatch takes priority over expiry; a normal spurious
return before the deadline yields retry. Its environment performs wake bookkeeping only,
so the ordinary predicate load is scoped to absence of concurrent source writers.
ROOT ran Client.lean paused-lifetime, retry, exact-boundary and mismatch checks successfully in selected q3.
Neither file is the generated definition of any of the four retained source exports.
In particular boundaryClient's constant word lowered as a global: it does not establish
the allocation/reclamation behavior of this new interpreter client.

Source qualification must also reconcile the timed kernel's tracked newest-byte compare
with the source atomic model's locIdx/seen and read-choice semantics. A tracked footprint
alone establishes no such correspondence. This atomic correspondence obligation remains open; actual generated type/body
integration passed the bounded interpreter checks; default timed-call rejection is intentionally unchanged.

An isolated source-only acyclic generation candidate now exists in TimedCheck/TimedEmit
and TimedBody, with a ROOT-only Translate.lean driver. It shares actual named-type,
encoding, global and scalar-op emission; each ordinary scalar action forwards locals and
memory through an explicit Program memory node. Selected calls bind real paused wait
continuations. It rejects unsupported opcodes, loops, recursion, indirect calls and other
sync primitives before emission, and checks selected profiles and typed layouts. This
candidate produced a compiler-checked full generated file in ROOT selected q3;
all four emitted definitions passed Generated.lean runtime checks. The ordinary translator
still rejects timed calls. See deadline-translator-scope.md for the current boundary.
