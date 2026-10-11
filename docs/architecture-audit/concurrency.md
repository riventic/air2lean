# Architecture audit 3/6: concurrency and atomics model

Scope: `ZigLean/Conc/*` (ConcM, scheduler, spawn/join, futex, `Io.Group`, logic), the atomics
and race check in `ZigLean/Mem/{Basic,Thread}.lean`, and the std boundary in
`Air2Lean/StdModels.lean` and `ZigLean/Conc/Call.lean`. Base: `origin/main` `d9dfa689`.
Unmerged `codex/roadmap-batch7` work (C02 TLS, C05 cancelation and spurious futex returns, C07
detach, C08 futures, C09 pointer atomics, address reuse) is noted where it changes a finding.

Question: where can an all-schedule theorem be true of the model and false of the real Zig
program on real hardware?

Fixtures: `tests/roadmap/architecture-audit/concurrency/` (`check.sh` reproduces everything).
`litmus.zig` is translated by the normal pipeline (0.16.0 patched exporter, `scripts/translate.sh`)
and `Enumerate.lean` enumerates every oracle prefix of `Sched.runTrace` (exhaustive at the given
fuel, depth-first over the reported option counts). `native_litmus.zig`, `native_io.zig` and
`native_unfair_lock.c` run on the host (aarch64 macOS, Apple silicon, 18 CPUs, stock Zig 0.16.0).

## What the model is (verified, no finding)

* **Memory model.** An operational approximation of RC11 without promises: per-location
  modification order of write *events* (`ALoc.msgs`), per-thread vector clocks, read views
  (`Mem.seen`), release clocks propagated along RMW release sequences. A read may read any
  message not older than the newest one that happened before it or that the thread observed;
  writes may be placed anywhere after that floor. `.monotonic` loads are **not** SC: the
  message-passing stale outcome is in the model (`mpAllRelaxed` yields `100`, which the host
  produced 316,479 times in 10M runs). `seq_cst` is treated as `acq_rel` (an over-approximation,
  sound; incomplete for store buffering). The documented read-view-transfer limit only adds
  outcomes (sound). Zig 0.16 has no `@fence`; `.unordered`, float/pointer atomics, mixed-size
  atomics (`.unspecified`), volatile and `threadlocal` are rejected.
* **Race detection.** Every plain/atomic load, store, `memcpy`/`memset`/`memmove`, poisoning
  `Allocator.free` and remap records a byte-range footprint with the access's vector clock, and
  `recordAccess` checks every overlapping concurrent entry (`racePair`: a write and a plain
  access). Detection is happens-before based, hence independent of the interleaving actually
  chosen. That is what makes the coarse granularity sound: threads switch only at sync ops
  (every atomic op is `pick` + op, plus spawn/join/futex/yield), and a non-atomic multi-byte
  access executes as one step, but any schedule-sensitive plain access is a race on some
  explored run. Footprints are keyed by `BlockId`; block ids are never reused (address reuse on
  batch7 keeps block ids unique).
* **Schedules.** `o i % n` makes every oracle a valid schedule; theorems quantify over all `o`
  and all `fuel`.

The findings below are the places where that argument breaks.

## Findings (ranked)

Severity: **SOUNDNESS** (model proves something real executions violate), **FAIL-OPEN** (a
default or reading of a theorem silently assumes something), **HARDENING**.

| # | Severity | Finding | Counterexample status | Batch7 |
|---|---|---|---|---|
| 1 | SOUNDNESS | `Io.Group.async` is always a new concurrent thread | model + native (deadlock) | open |
| 2 | SOUNDNESS | futex has no spurious return | model + native (EINTR) | fixed by C05 |
| 3 | SOUNDNESS | a stack frame's end records no access | model (no `.illegal`); native not observable | open |
| 4 | SOUNDNESS (trusted) | no load buffering for `.monotonic` | model forbids; host 0/10M | open |
| 5 | SOUNDNESS | `os_unfair_lock` contract has no owner | model returns; native killed | n/a |
| 6 | SOUNDNESS (minor) | futex wake is FIFO-deterministic | model only; host FIFO 20/20 | open |
| 7 | FAIL-OPEN | `available` spawn policy is the default | by construction | opt-in `fallible` only |
| 8 | FAIL-OPEN | `Group.cancel` = `await`; never `error.Canceled` | by construction | fixed by C05 |
| 9 | FAIL-OPEN | out-of-fuel is silent; spin deadlocks are never `.deadlock` | model (`groupGate`: 85% `none`) | open |
| 10 | FAIL-OPEN | non-strict `run_sound` is satisfied by data-race runs | by construction | open |
| 11 | FAIL-OPEN | the one model `Allocator` is implicitly thread-safe | by construction | open |
| 12 | HARDENING | Std is modelled at the `std.Io` vtable, not at OS primitives | root cause of 1, 2, 8 | partly |
| 13 | HARDENING | non-footprint shared state in `Mem` changes only once per segment | by construction | open |
| 14 | HARDENING | futex word read is not a footprint access and ignores the waiter's view | by construction | open |
| 15 | HARDENING | `seq_cst` is `acq_rel` (incomplete, sound) | model allows SB 0/0; host 0/10M | open |

### 1. SOUNDNESS: `Io.Group.async` is always a concurrent thread

`groupAsyncC` (`ZigLean/Conc/Call.lean`) is a `spawn` op. std 0.16.0 `Io.Group.async` makes
no such promise ("asynchronous tasks are not guaranteed to run until `Group.await` or
`Group.cancel` is called", `lib/std/Io.zig`). `Io.Threaded.groupAsync` runs the task **in the
caller** (`groupAsyncEager`) when `busy_count >= async_limit` (default `cpu_count - 1`), on
allocation failure, on `Thread.spawn` failure, and always under `single_threaded`. This is not
a resource failure. It is the default behaviour once enough tasks are busy.

* Model: `litmus.groupGate` (two tasks wait on a gate that the caller opens after `async`)
  gives `ok(7)` or `none` in every explored schedule, never `.deadlock`, so `run_safe` and
  `run_sound` style theorems hold.
* Native: `native_io.zig` part 3 starts `cpu_count` (18) such tasks with the default
  `Io.Threaded`. The 18th runs eagerly in the caller, which never reaches the gate:
  `group: DEADLOCK - 18 tasks started`. The same happens with one task under
  `-fsingle-threaded` or `async_limit = .nothing`.

On batch7 the `fallible` policy adds an eager branch, but only as opt-in and only tied to
resource failure. **Structural fix:** `Group.async` (and `Io.async`) should be an oracle choice
between {spawn, run eagerly in caller now, defer to `await`} under *every* policy, because
eager and deferred execution are the normal semantics. Better still, translate
`Io.Threaded.groupAsync` from std above `Thread.spawn` and the mutex, with `async_limit` /
CPU count as an explicit environment parameter. An `available` claim would then need a premise
that the number of busy tasks stays below `async_limit`.

### 2. SOUNDNESS: no spurious futex return (fixed on batch7)

On origin/main `Thread.futexWait` sleeps until a matching wake. std documents spurious
returns for `Io.futexWait`/`futexWaitUncancelable`/`Thread.Futex.wait`, and the darwin and
Linux backends return on `EINTR`.

* Model: `litmus.futexEarly` returns 1 iff the waiter got past its wait before the caller
  changed the word. Every schedule gives `ok(0)`.
* Native: `native_io.zig` part 1 sends `SIGUSR1` to a thread blocked in
  `futexWaitUncancelable`. The wait returns with the word still 0 and no wake issued:
  `spurious: waiter returned before any wake with value 0`.

std's own primitives re-check in a loop, so the translated `Io.Mutex`/`Condition` proofs are
not affected. User code that calls the futex directly is affected. Batch7 C05 adds the
`spuriousWake` oracle option. **Fix:** merge C05 and keep `futexEarly` as a regression; it must
then produce `ok(1)`.

### 3. SOUNDNESS: the end of a stack frame is not an access

`free` (used for stack blocks at frame exit) only marks the block dead. It records no
footprint, unlike the heap `poisonFree`. A plain access by another thread that is not
happens-before the frame's end is a data race in Zig/LLVM terms: the slot is reused by later
frames' plain writes. The model detects it only when some schedule lets the access run *after*
the free (dead block, `.illegal`). If the ordering is forced through a relaxed handshake, no
schedule does that.

* Model: `litmus.stackLifetime`. A helper spawns a reader of its local `x`, spins on a
  `.monotonic` `done` flag that the reader sets after reading, and returns. The caller then
  calls a function whose local can reuse the slot. Every schedule gives `ok(14)` (or `none`).
  There is no `.illegal` (`exhaustive=true`, 378 runs).
* Native: the manifestation needs the reader's load to be satisfied after its relaxed store
  (load→store reordering). That is allowed by the Arm architecture and by LLVM for a
  non-atomic load, but it was not observed on this host. The finding is therefore
  semantic-level UB that the model accepts.

`docs/std-models.md` already says that "a stack region needs the proof obligation, not the
dynamic check", but `Sched.run` theorems carry no such obligation. **Structural fix:** at frame
exit, record a `.write` footprint over every escaping stack block before killing it (the same
rule as `poisonFree`). The race check then rejects any unordered access, in every schedule.
Batch7 C07 (detach, frames dying under running threads) makes this more pressing.

### 4. SOUNDNESS (trusted assumption): no load buffering

The model has no promises, so for relaxed atomics it never produces the LB outcome.
`litmus.lbRelaxed` gives `{0,1,2}` and never 3. RC11 and the Arm architecture allow 3. LLVM
does not promise to avoid it, and LB has been reported on some Arm implementations. On this
host it was 0 in 10M runs. That is consistent with Apple cores, but it is not a guarantee for
other aarch64 targets. The assumption is documented ("Trusted assumption" in
`ZigLean/Mem/Thread.lean`), but no theorem, receipt or claim records it as a premise.
**Structural fix:** pick one of two sound fragments.

* (a) DRF/no-LB fragment: the translator rejects, or tags as needing `--assume-no-lb`, any
  thread path where a `.monotonic` load is followed, before an acquire or release op, by a
  `.monotonic` store or RMW to a different location. With acquire loads or release stores
  on either side, LB is forbidden by RC11 itself, so the model is exact there.
* (b) Add a promise step: a thread may commit a future relaxed store early if its
  certification run (the thread alone) reaches it.

Record the assumption as a premise in the assurance report.

### 5. SOUNDNESS: the `os_unfair_lock` contract has no owner (0.15.2 macOS `Thread.Mutex`)

`osUnfairUnlockC` is an ownerless release `xchg 0` and a wake. The real `os_unfair_lock`
records the owner and terminates the process on an unlock by another thread.
`native_unfair_lock.c` (lock in thread A, unlock in main after join) is killed (exit 137). The
model's `crossThreadUnlock` analogue returns normally. std documents this as UB. This is the
one OS primitive the model hand-writes, and its contract is weaker than the primitive.
**Fix:** model the lock word as the owner's thread id, with `.illegal` on unlock by a
non-owner. More generally, std-documented UB preconditions (cross-thread unlock, double
unlock) are not checked when std is translated in ReleaseSafe. Consider exporting the
`DebugImpl` variants, which assert ownership, for verification.

### 6. SOUNDNESS (minor): FIFO-deterministic futex wake

`futexWake p n` always wakes the *earliest* `n` waiters. Neither Linux (priority plist) nor
darwin ulock guarantees an order, so a theorem that depends on which waiter wakes is
unsupported. The host woke the first waiter 20/20 times, so no native counterexample was
observed. **Fix:** let the oracle choose the woken subset (any `min n |waiters|` of them).
This costs one `pick`.

### 7. FAIL-OPEN: `available` is the default spawn and concurrency policy

`spawnC` and `groupConcurrentC` never fail (no `SystemResources`, `ThreadQuotaExceeded`,
`ConcurrencyUnavailable`). Batch7 keeps `fallible` opt-in (`--spawn-policy`). The policy is
in the receipt but not in the theorem statement, so `parallelCounter`-style "always `4n`"
theorems are false whenever spawning fails. **Fix:** make `fallible` the default, or make the
environment (spawn policy, `async_limit`, allocator thread-safety, LB assumption) an explicit
parameter of `Sched.run`. Each theorem then states it.

### 8. FAIL-OPEN: cancelation (fixed on batch7)

On origin/main `Group.cancel` is `await` and `Io.futexWait` never returns `error.Canceled`.
`examples/iogroup.groupConcurrent` documents this. A task that would be canceled in reality
completes in the model. Batch7 C05 adds cancel requests delivered at cancelation points.
Merge it.

### 9. FAIL-OPEN: fuel exhaustion and spin deadlocks are silent

Out of fuel is `none`, which every partial spec and `run_safe` accept. `.deadlock` is raised
only when every thread blocks in `join` or the futex. A deadlock or livelock through spinning,
CAS retry or weak-CAS spurious failure is just `none`. `groupGate` at fuel 20: 1704 of the
first 2000 oracles ran out of fuel. Nothing requires even one schedule to finish, so a program
whose every schedule diverges satisfies every concurrent theorem. **Fix:** require a
non-vacuity witness (`∃ o fuel, run = some (.ok _)`, one `decide`/`native_decide` schedule) for
every published concurrent claim. State "deadlock-free" only for blocking primitives, or add
`EventuallyReturns` under a fairness premise (fair oracles) for spin-based code.

### 10. FAIL-OPEN: non-strict protocols admit races

`Proto.run_spec`: "an error or no result satisfies every spec". A non-strict `run_sound` on a
racy program is provable while every schedule is `.illegal`. That is weaker than the
sequential `Triple`, which is false on a safety error. All shipped proofs use `strict := true`,
and `claims.py` classifies the conclusions as `none` (an `Exists`), so nothing over-claims
today. **Fix:** remove non-strict mode from the public surface, or rename its conclusion
(`run_sound_if_no_ub`) so that it cannot be mistaken for partial correctness.

### 11. FAIL-OPEN: allocator thread-safety is implicit

The single model `std.mem.Allocator` updates `nextAddr`, `allocs` and the policy state
atomically within a segment, with no footprint. Concurrent use of a non-thread-safe allocator
(`FixedBufferAllocator.allocator()`, a `DebugAllocator` configured `thread_safe = false`) races
in reality and can return overlapping memory. In the model it always yields disjoint blocks.
**Fix:** record a ghost "allocator state" footprint write per alloc/free unless the allocator is
declared thread-safe, or carry the declaration as a premise (with finding 7's environment
record).

### 12. HARDENING: std is modelled at the `std.Io` vtable, not at OS primitives

`Io.futexWait`/`futexWake`/`Group.*` (and `Thread.spawn`/`join`) are hand-written models of
std interfaces. `Io.Threaded`'s thread pool, eager fallback, cancelation via signals and
internal mutex are skipped. Findings 1, 2 and 8 all come from this layer. Following the
project principle (trust only base OS primitives), translate `Io.Threaded` and `std.Thread`
from std and model only pthread create/join/detach, the futex/ulock syscalls (with spurious and
`EINTR` returns) and signals.

### 13. HARDENING: segment-atomic non-footprint state

`Mem.allocs`, `failAt`, `nextAddr`, `allocators`, `groups` and `spawnLimit` change without
footprints, and other threads see them only at segment boundaries. Interleavings inside a
segment are unreachable. For example, with `failAt` the "A, B, A" allocation order is never
explored, and address order across threads is segment-ordered. Today this matters for
`failAt` differential runs and address-observing code. **Fix:** make allocation a scheduling
point, or quantify over failure oracles only, as the theorems already do.

### 14. HARDENING: the futex word read

`Thread.futexWait` reads the block bytes (the newest message) with no footprint and no
`observe`. A plain write that races with the kernel's compare is not flagged, and the compare
ignores the waiter's read view. This is harmless for std's atomics-only use. Record an
`atomicRead` footprint for the compare.

### 15. HARDENING: `seq_cst` = `acq_rel`

The model allows `SB` with `seq_cst` to end 0/0, which the host never produced (0/10M).
Dekker/SB proofs cannot go through. This is sound, but it rules out common lock-free
algorithms. **Fix:** add an SC order (psc) for SC accesses.

## Reproduction

`bash tests/roadmap/architecture-audit/concurrency/check.sh`. Observed on 2026-10-08:

```
lbRelaxed: fuel=20 runs=14 exhaustive=true outcomes=[ok(1)x3, ok(0)x10, ok(2)x1]
mpAllRelaxed: fuel=20 runs=19 exhaustive=true outcomes=[ok(0)x10, ok(42)x7, ok(142)x1, ok(100)x1]
futexEarly: fuel=20 runs=13 exhaustive=true outcomes=[ok(0)x13]
groupGate: fuel=20 runs=2000 exhaustive=false outcomes=[ok(7)x296, none(out of fuel)x1704]
stackLifetime: fuel=14 runs=378 exhaustive=true outcomes=[none(out of fuel)x158, ok(14)x220]
LB relaxed r1=r2=1: 0/10000000
MP relaxed r1=1,r2=0: 316479/10000000
SB seq_cst r1=r2=0: 0/10000000
spurious: waiter returned before any wake with value 0 (model: impossible; 99 = still waiting)
order: first woken A=20 B=0 C=0 (model: always A)
group: 18 cpus, async_limit default = cpus - 1, spawning 18 tasks
group: DEADLOCK - 18 tasks started, caller never reached gate.store (model: returns)
native_unfair_lock: killed (exit 137)
```
