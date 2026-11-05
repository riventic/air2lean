# Build budgets

`scripts/build-guard.py` runs one command on Linux or macOS once a user-wide lock admits it.
It uses Python's standard library, `ps`, and optional read-only Git metadata. It never probes
compiler versions or starts another build itself. Use the same lock for every participating
worktree and coordinator; never a private lane of your own (see [Admission](#admission)):

```sh
export AIR2LEAN_BUILD_LOCK="$HOME/.cache/air2lean/build.lock"
python3 scripts/build-guard.py \
  --cwd "$PWD" --profile runtime --phase proof --cache warm \
  --timeout 900 --rss-mib 8192 \
  --input lean-toolchain --input ZigLean/Basic.lean \
  --tool lean --report /tmp/runtime-budget.json --log /tmp/runtime-budget.log \
  -- lake build ZigLean
```

The default lock is `$HOME/.cache/air2lean/build.lock`; `--lock` overrides
`AIR2LEAN_BUILD_LOCK`. Lock files are never removed, so waiting coordinators retain
the same flock inodes. A workload that is not admitted fails with exit 75 without starting a
child. `--lock-wait SECONDS` permits bounded waiting; without it a guard waits
`AIR2LEAN_LOCK_WAIT` seconds (the scripts' common setting; the remote host's jobs set it), else
none, so a guard a script starts without the option (the proof-receipt audit) waits like the
script's others instead of failing at the first busy moment. A nested guard in the same checkout
also fails or waits (one build per workspace): wrap a whole workload once. Advisory locking
coordinates participating callers; unguarded builds are outside its control. Existing
`zig-patch/build.sh` already uses `-j1` for its compiler bootstrap.

## Admission

The machine's guarded workloads share one memory budget, `--mem-budget-mib` (default
`AIR2LEAN_BUILD_MEM_MIB`, else 75% of physical memory), cut into slots of 1 GiB
(`<lock>.d/slot-NNN`). A workload holds ceil(`--rss-mib` / 1 GiB) slots, at most all of them,
and the guard stops it above `--rss-mib`, so the admitted workloads stay within the budget
(up to the sampling limits below). On the 64 GB development Mac that is 48 slots: four
single-process builds (`--rss-mib 11000`) run at once instead of one. `scripts/full-build.sh`
and `scripts/fixture-checks.sh` are [elastic workloads](#elastic-workloads): each Lean process
and fixture unit holds slots of its own, charged its measured need, only while it runs.

- One build per Lake workspace: Lake has no build lock, so a workload holds
  `<lock>.d/ws-<digest>` of the git top level of `--cwd` (else `--cwd`) exclusively. Check trees
  under a checkout's `.lake/` and `tests/diff` (which requires the checkout by path) share the
  checkout's. `--shared-workspace` holds it shared, for workloads that write nothing Lake owns.
- `<lock>` itself is held shared; `--exclusive` holds it exclusively and runs alone. Use it only
  for timing measurements (`perf-budgets.py record` refuses a shared admission), never for a
  build: it drains the machine (below). The guard exports `AIR2LEAN_GUARD_MODE` (`shared` or
  `exclusive`). A guard from a checkout older than this scheme holds `<lock>` exclusively and so
  still runs alone.
- Arrival order: acquirers queue on `<lock>.d/queue`; the one holding it (the head) collects its
  slots while later ones wait, so a large workload is not starved by small ones. The workspace
  lock is taken before the queue, so waiting for one's own checkout holds up nobody.
- Backfill: a head that holds all the free slots and waits for running workloads to free the
  rest leaves the machine partly idle. On the remote build host (2026-11-03), 11-slot heads
  waited up to 20 minutes while 18 GB were unused. So a head short of its slots holds only a
  reservation: ceil(weight x waited / `--backfill-ramp`) slots, where `waited` counts from when
  it became the head. The ramp is 900 s by default, and after it the head holds every slot it
  needs. The head publishes in `<lock>.d/heads/`, flock-held, the part of its reservation that
  it does not hold yet (`unmet`) and the slots it still lacks (`need`). A normal guard waiting
  behind the head, with no drain ticket queued, may run ahead in what is left.
  - It must take all its slots at once.
  - The head's unmet reservation must stay free beside them.
  - The free slots must not cover the head's `need`: free slots that would admit the head now
    go to the head.
  - Backfilling guards and the head's bound check are serialized by `<lock>.d/register`. A
    backfill attempt skips when the lock is busy, and the head waits for it within
    `--lock-wait`, so a stalled holder cannot block admission past that.
  - Bound on the head's wait: the ramp, plus the backfilled workloads already running, each
    bounded by its `--timeout`. After the ramp, a backfill only uses slots the head does not
    need. `--backfill-ramp 0` reserves everything at once, which is the earlier behavior.
  - A queue holder that publishes nothing gets no backfill. That covers a guard of an older
    checkout, and a stand-in in a test. An entry of another shape also gets none.
  - `free_mib` (the sizing hint of `scripts/full-build.sh`) does not count the head's unmet
    reservation as free.
  - Memory safety is unchanged: a backfilled workload holds its slots like any admitted one, and
    the report records `backfilled`.
- Drain tickets: a merge guard and an `--exclusive` guard take a ticket in `<lock>.d/merge/`
  (`<ns>-<pid>-<lane>`, flock-held by its guard). While a ticket is queued no normal guard is
  admitted, and one that is still collecting slots gives them back; running workloads are never
  preempted. Tickets are served in arrival order, merge and exclusive alike: the head merge
  guard collects its slots as usual, the head exclusive guard holds the queue until every running
  workload has ended, then runs alone, and normal admission resumes once no ticket is left. An
  exclusive guard thus waits for the longest running workload plus the ticket holders ahead of
  it, not for an idle moment that never comes on the shared Mac (before, it only tried at the
  head of the queue and never queued: on 2026-10-18 the perf-budget record failed with
  `lock_busy` 24 times in a row). Arrival order rather than a strict priority, because a strict
  priority either way lets a stream of one lane starve the other: a merge guard waits at most
  for the ticket holders ahead of it, an exclusive guard cannot be overtaken by later merge
  guards. A normal guard waits behind every ticket, so its `--lock-wait` must cover a drain; a
  guard nested inside a running workload waits too, while the exclusive guard waits for that
  workload (one waits out its `--lock-wait`): wrap a workload in one guard only. A dead guard's
  ticket is not held, so the next guard to look removes it. Guards of
  checkouts since the merge lane (#424) read every ticket in `<lock>.d/merge/` as a merge ticket,
  so they wait behind an exclusive one too; that is why the directory keeps its name.
- Merge lane: `AIR2LEAN_GUARD_PRIORITY=merge` (or `--priority merge`; `full-build.sh`, `regen.sh`
  and `preflight.sh` pass the variable on) gives a guard a drain ticket, so it is admitted ahead
  of every waiting normal guard as soon as its slots are free. The one-build-per-workspace rule
  still holds, a merge priority adds nothing to an `--exclusive` guard (its lane is `exclusive`),
  and a guard of a checkout older than #424 does not know the tickets. The lane is only for the
  coordinator's integration gate, never for agent or Codex builds; a waiting guard prints one
  line naming its lane (`normal`, `merge`, `background` or `exclusive` priority) and the tickets
  queued.
- Background lane: `AIR2LEAN_GUARD_PRIORITY=background` (or `--priority background`) is for work
  no one waits on, such as the periodic main health run. As a normal guard, the health run's full
  build (11 of arc's 16 slots) waits as the queue head and, past its ramp, reserves every slot it
  lacks, so lane gates queued behind it wait until enough running workloads end. A background
  guard is admitted only while no other guard waits (no ticket, no head, no entry in
  `<lock>.d/waiting/`, which every waiting guard keeps), with its workspace and all its slots at
  once; it holds nothing while it waits, so it delays no one, and its `--lock-wait` bounds its
  own wait (then `lock_busy`). The mechanism is in the module docstring of
  `scripts/build-guard.py`. Caveats: a guard of an older checkout publishes no waiting entry, so
  a background guard can be admitted ahead of it between two queue heads; a guard of a checkout
  older than this lane rejects the value (`AIR2LEAN_GUARD_PRIORITY must be one of normal,
  merge`).
- Usage-aware charge (Linux): `--rss-mib` is a ceiling a workload seldom reaches (a regen step
  declared 11000 MiB and peaked below 4.2 GB), so declared slots alone kept a 23 GB build host
  idle while 20 guards queued. The guard therefore records each command's last 5 runs (outcome,
  exit code, sampled peak) in `<lock>.d/history/<key>.json`; the key is the command with its
  workspace path abstracted, its directory in the workspace, the phase, profile, jobs and Lean
  threads. After 2 successes among them, with no run stopped at its limit (`rss_limit`),
  preempted or SIGKILLed (exit 137, the OOM killer), it holds the slots of ceil(1.3 x the largest
  sampled peak of those successes) MiB, at least one, instead of those of `--rss-mib`, which
  stays the hard limit. Only successes measure the need, and only by sampled peaks (every
  `--interval`). A command whose runs differ widely (a no-op `lake build` and a rebuild after a
  core change) is charged by its recent successes; the two bounds below carry that risk:
  - The declared limits of the running workloads add up to at most 1.5 x the budget. Held slots
    never exceed the budget, and an overcommitted workload registers its excess (declared minus
    held slots) in `<lock>.d/running/`, flock-held, under `<lock>.d/register`; the registered excess
    stays within 0.5 x the budget, and a workload that would break that collects its declared
    slots instead. Guards at their declared charge and guards of older checkouts need no check.
  - Backstop: when MemAvailable falls below max(2 GiB, 10% of RAM), the youngest overcommitted
    workload (the least work lost) is stopped, outcome `preempted`, at most one per 5 s per lock
    (chosen under the flock of `<lock>.d/preempted`, which holds the last preemption's time;
    MemAvailable is read once a second); it leaves the registry at once, so the next can be chosen while it is torn down. The guard
    runs it again holding its declared slots, within what is left of `--lock-wait` and
    `--timeout`; the log keeps both runs' output, the report the stopped run in
    `preempted_run`, and the command stays at its declared charge while the preemption is among
    its last 5 runs.

  Never overcommitted: the Mac (macOS reports no MemAvailable), a cgroup-limited process (a
  container's `--memory`, whose pressure MemAvailable does not show), `--lock-wait 0` (a stopped
  run could not wait to run again), `--exclusive` and `--no-overcommit`. A nested guard inherits
  its admission and records nothing.
- The report's `admission` records the budget, slots, weight (the slots held), mode, priority
  and workspace, and the charge: `declared_slots`, `overcommit`, `charge_mib`, `history_runs`,
  `why_declared` (why it holds its declared slots), `preempted_at_available_mib` and
  `backfilled`; `lock_wait_seconds` the time to admission.

## Elastic workloads

A full build used to hold one admission of 11000 MiB per Lean process for all its phases: on
the remote build host (17000 MiB budget) that was one Lean process at a time, a serial build,
and 11000 MiB held for the whole health run (about 3 h) while its processes mostly used 1–3 GB.
Lane jobs queued meanwhile on an idle host. An elastic workload instead holds slots by need:

- **Base.** `--elastic --rss-mib B` holds B (full-build.sh and fixture-checks.sh: 4096 MiB) for
  the part of the workload that is not a sub-admission: Lake itself, the scripts, the assurance
  extractor's build, the canon phase (about 2 GB). Its guard enforces B on that part only.
- **Plain fallback.** `build-guard.py --elastic-plan B` prints how the two scripts run: elastic
  with base B (at most an enclosing elastic grant's), or one plain admission where the budget
  leaves no room for a base beside one 11000 MiB process (at most 11000 MiB, one Lean thread) or
  inside a guard that is not elastic (its whole limit).
- **Parts.** A guard in it with `--sub-admission` holds slots of its own while it runs, charged
  `--charge-mib` (its measured need), which is also its limit with no excess; `--rss-mib` is its
  declared bound, at most 11000 (`PROCESS_MIB`, under the 12 GiB
  per-process watchdog). A part over its charge is stopped and run again once at that bound
  (`stopped_run` in its report; for a part without `--log` the stopped run's output is
  dropped). The enclosing guards leave a running part's processes out of their sums.
- **Lean processes.** `--lean-processes SYSROOT` (SYSROOT: `lean --print-prefix`) makes every
  Lean elaboration of the workload a part: Lake takes its Lean from a sysroot of links to the
  toolchain whose `bin/lean` runs each elaboration of a `.lean` file as
  `build-guard.py --lean-process` (`LAKE_OVERRIDE_LEAN`, `LEAN_SYSROOT`, `LEAN`). `lake env`
  puts the toolchain's own `bin` first on `PATH`, so a script elaborates a file with
  `lake env "$LEAN" FILE` (scripts/lean-deps.py), not `lake env lean`. Lake traces no sysroot
  path (its Lean trace is the githash), so the same modules are up to date with or without it,
  and the guard of a process is silent unless it fails (Lake keeps a process's output in its
  traces and replays it). Server, worker, `--run`, `--stdin` and `--deps` runs go straight to the
  real `lean`. Each process runs on one Lean thread, charged
  1.3 x its module's measured peak (Measured peaks below for a module not measured). Lake runs up to
  `--lean-threads` of them at once (full-build.sh: min(8, cores)), and the slots they hold, not
  the thread count, bound their memory. The assurance tools refuse a `LEAN_SYSROOT` overlay, so
  only builds use it: the root, tests/diff and standalone-file phases and the proof-fixture
  package's build in fixture-checks.
- **Measured peaks** (`scripts/lean-peaks.py`). Each successful elaboration records the
  kernel's high-water mark of its Lean process (`peak_process_rss_kib`, exact, not sampled) for
  its module's path and source SHA-256, the last 3, in `<lock>.d/lean-peaks.json` on the machine
  (replaced whole on each record). `assurance/lean-peaks.json` seeds a machine that has not
  measured a module yet. It is generated (`python3 -B scripts/lean-peaks.py write`, from the
  store and the table before it; never hand-edited). It is measurement data, not a derived file:
  `scripts/regen.sh` does not rewrite it (every run would differ) and no check fails on it. A
  module whose source changed is charged 1.3 x the peak of its earlier source (the row `write`
  keeps, with that source's SHA-256, until the module is measured again): a guess, safe because
  the charge is the process's limit, so a module that grew costs one retry at 11000 MiB. A module
  never measured is charged 1.3 x the table's 95th-percentile peak (nearest rank;
  `typical_peak_kib`), computed from the committed table on each charge, not a constant (2000 MiB
  over the 803 rows of 2026-11-05, so a 2600 MiB charge; 11000 MiB only for an empty table). The
  same guess: about one new module in twenty outgrows it and costs one retry at 11000 MiB.
  Before, every changed or new module was charged 11000 MiB, and `write` dropped a changed
  module's row: after one main merge (2026-11-05) 49 rows went and 223 of 977 tracked modules had
  none, so the remote host's after-run met one 11-slot queue head after another, with lane jobs
  waiting beside them on a host 86% free; with rows kept, the 174 modules never measured still
  made such heads (an unmeasured cross-target tutorial file while two lane jobs waited, 83%
  free). A refresh is an ordinary PR after a build on the remote host. `lean-peaks.py top` lists
  the largest. A seeding run (a cold build to measure every module) may set
  `AIR2LEAN_LEAN_UNMEASURED_MIB` instead: a guess that is too low costs a retry at 11000 MiB. `AIR2LEAN_LEAN_REPORTS=DIR` keeps each process's guard
  report (full-build.sh: `<logs>/lean-processes`).
- **Fixture units.** In an elastic admission each fixture-check unit is a part charged its
  measured peak (scripts/fixture-checks.py `schedule`; 11000 MiB unmeasured), with the units'
  guard's jobs and Lean threads.
- **Waiting.** A part waits for slots like any guard, up to 8 h (`PART_TIMEOUT`, the full
  build's own `--timeout`), and so do the full build's phases: on a busy host its processes
  wait, they do not fail.
- **No deadlock.** The bases of the admitted elastic workloads leave 11000 MiB of the budget
  free (`<lock>.d/elastic/`, checked under `<lock>.d/register`; an elastic guard without room
  waits outside the queue, holding nothing, and a base too large ever to fit fails with
  `elastic_too_large`). A part of a workload none of whose parts runs takes the workload's
  lifeline: a ticket in `<lock>.d/lifeline-tickets/`, served behind the merge tickets (a merge
  guard waits for no running workload, so it is admitted and ends) and ahead of every exclusive
  ticket (which waits for every running workload, the elastic one too). The lifeline reserves,
  it does not drain. Behind no drain ticket, the first lifeline leads the normal lane as its
  queue head. The exceptions are normal guards that began to wait before it and whose weight
  fits beside the elastic bases: such a guard can be admitted while every elastic workload
  waits, so it keeps or takes the head first. Every other normal head gives the queue back to the
  lifeline. Normal guards backfill beside the lifeline's reservation as beside any head (Backfill
  above). So a lifeline waits for finitely many heads, each admitted in bounded time, and a
  large normal guard is not sent back by every later lifeline. Each elastic workload always has a
  part running or coming up, and that part finds 11000 MiB that no base holds once its ramp has
  passed and the running workloads, backfilled ones included, end. Its ticket is kept out of
  `<lock>.d/merge/` because guards of older checkouts read every ticket there as a drain ticket.
  On the remote host (2026-11-05) a drain-style lifeline of an unmeasured part (11 slots, 20 of
  28 held) made 7 lane jobs wait 8 to 19 minutes with 4.7 of 24 GB in use. Those older guards
  do not see `lifeline-tickets/`, though, and would keep the queue from a lifeline (a large
  head or an exclusive one, until its `--lock-wait`). So a lifeline whose turn it is mirrors its
  ticket in `merge/` under a name for time 0, which they drain behind first. It does so only
  while it does not hold the queue and no queue head that knows lifelines publishes its
  reservation: new heads mark their `heads/` entry `lifeline_aware`. New guards ignore the
  mirror, and it is withdrawn as soon as that no longer holds. So older guards drain only while
  one of them stands in the lifeline's way, never while the lifeline waits for a head that may
  lead (the first version of the mirror did, and made two lane jobs wait beside 10 free slots on
  the remote host). The mirror is a workaround for those older checkouts only: it goes once
  none of them runs a guard (ledger `guard-lifeline-mirror`: the date and the check). A part
  of a running workload waits like a normal guard: the
  workload yields memory to lane jobs between its processes. A background workload (the health
  run) gets one part at a time ahead of others through its lifeline; its other parts wait for an
  idle moment as before.
- **Safety stays.** The 12 GiB watchdog, every guard's sampled limit and the MemAvailable
  backstop are unchanged; a part never overcommits (its charge is its limit).

A private lock lane (another `AIR2LEAN_BUILD_LOCK` to skip the queue) escapes the budget: the
machine overcommits memory and thrashes, and every build gets slower. Do not use one; lower
`--rss-mib` to a workload's real peak instead, so more workloads fit.

The guard sets `LEAN_NUM_THREADS=1` (`--lean-threads N` sets N; proof receipts and the
performance gate require 1), `AIR2LEAN_JOBS=1` (`--jobs N` sets N) and `AIR2LEAN_MEM_MIB` to the
`--rss-mib` budget; `scripts/par.py` sizes its worker pool from the last two (see
[Parallel jobs](#parallel-jobs)). For a direct `zig build` command, it inserts
`-j1` at a guaranteed build-option position, rejects conflicting build job counts
and response files that could hide job options, and records both requested and
executed arguments. Validation distinguishes the frontend from the later build
runner: `--prefix -j2` is rejected because the frontend sees that job override
before the runner consumes the prefix value. The exact operand-consuming tables
of pinned 0.14.1/0.15.2/0.16.0 frontends are checked independently; tokens must
be safe under every supported frontend. The runner is also checked, so
`--prefix -- -j2` cannot hide an override behind a consumed
boundary. Genuine forwarded application arguments after `--` are preserved.
Response-like `@...` tokens before that boundary are refused conservatively,
including literal filename values. Version-specific operands can also cause a
conservative refusal (for example, `--debug-libc -j2`, absent in 0.14.1). A value
named `-j1` does not replace the injected build option. It also stops a
workload when a sample contains more Zig compiler invocations than `--jobs` (default 1):

- One invocation counts once, together with the Zig children it starts for its own tools: a Zig
  process whose parent is a Zig process. Those are `zig clang` for C sources and libc,
  `zig ld.lld`, and `zig rc`. A cold global cache makes one `zig build-exe … -lc` start several
  `zig clang` processes at once. `--jobs` bounds invocations, not these children; `--rss-mib`
  bounds their memory.
- An invocation that supervises others through non-Zig processes is not counted; the ones below
  it are. That is the `zig build` driver of 0.14–0.16 above its build runner (0.17 execs into
  its runner, `maker`). So `zig build`'s parallel compilers count one each.
- This relies on Zig never starting several compilers as its own direct children, which holds
  for 0.14–0.17. A wrapper named like a compiler must exec it, not spawn it; zig-patch/lock.sh
  execs.

`zig`, `zig-air`, and `zig-unlocked`
are recognized; use `--zig-name NAME` for a renamed executable. Linux `comm`
truncation is matched conservatively at 15 bytes, so aliases sharing that prefix
can cause a refusal even when the longer names differ. Scripts must
choose sequential compiler flags themselves. The guard never automatically
parallelizes workloads; single-thread Lean settings do not guarantee that an
arbitrary build system launches only one process.

The child starts in a new session/process group. Timeouts, sampled RSS excess,
SIGINT/SIGTERM/SIGHUP, and detected parallel Zig work trigger group TERM followed
by KILL after `--grace` seconds. The original group catches orphaned children;
observed descendants remain tracked if they change groups or sessions. Cleanup
checks that observed live processes stop before releasing the lock. A leader
that exits while children remain is a failed workload, and those children are
stopped. The leader's exit is observed with POSIX `waitid(WNOWAIT)` and its PID is
retained until cleanup ends. This prevents original-group ID reuse during a
TERM/KILL fallback when `ps` fails after the leader exits. Zombies are already
stopped and excluded. Process-generation checks
use `ps lstart` (one-second resolution) when following detached descendants.

This is a cooperative build coordinator, not a security sandbox. A descendant
that detaches and is reparented entirely between samples can escape observation.
SIGKILL of the coordinator or host failure cannot run cleanup. A `ps` failure
causes a failed check and attempts to stop the original group; inability to
confirm cleanup is reported as `cleanup_failed`. For untrusted processes or hard
containment, use an OS service/container with stronger process ownership.

A `ps` sample that fails or exceeds `--ps-timeout` (default 15 s; the dev Mac under heavy
shared load sometimes needs more than 5 s) is skipped and retried at the next interval; the
count is `failed_samples` in the report. The memory cap is never left unenforced for long: if no
sample succeeded for `--sample-stale` seconds (default 60, four full attempts), the guard
aborts with `guard_error` (exit 70) and stops the workload. After the workload exits, the
guard waits for a successful sample (same bound) before judging orphaned children.

**Idle limit (opt-in).** `--idle-minutes N` (default `AIR2LEAN_GUARD_IDLE_MINUTES`, else 0: no
limit) stops a workload that makes no progress for N minutes, with outcome `hung` (exit 123),
well before `--timeout`. Progress is any of: a process started in the workload's tree (a
process is its PID and start time), output, or max(1 s, 1% of N minutes) of CPU time gained by
the processes already seen. All three come from what the guard observes anyway: its `ps`
samples (the `time` column) and the workload's output pipe. `ps` shows a process's own CPU time
only, so the time of a child that ended between samples is lost; a stream of short tools still
counts, by their starts. A working build always shows one of the three. A deadlocked one shows
none: Lake 4.34 can wait on itself at 0% CPU forever ([upstream/lake-concurrent-needs.md](upstream/lake-concurrent-needs.md)).
A workload that legitimately sits idle that long (waiting for a lock or a network peer) is
stopped too, so the limit fails closed; choose N above the longest such wait. A nested guard's
`ps` sampling is CPU time in the tree of the guard above it, but not in its own workload's tree.
So set the variable once for a whole job (nested guards inherit it): the innermost guard sees
the idle workload.

`--rss-mib` is a **reactive sampled RSS threshold**, not a hard allocation limit.
The default interval is 0.25 seconds. Summing process RSS can double-count shared
pages; bursts between samples can exceed the threshold before termination.
Parallel-compiler detection has the same sampling limitation. The reported peak
is the largest observed sum, not an exact kernel high-water mark. Timeout
observation and TERM/KILL cleanup add time beyond the requested workload budget;
metadata hashing and lock waiting are recorded in total elapsed time separately.
Choose a threshold comfortably below available memory. Do not interpret this
mechanism as a guarantee against a sudden host-wide memory spike.

JSON reports are atomically replaced and limited to 128 KiB. They record exact
arguments, working directory, tracked Git revision/dirty state when available,
host, profile, phase, declared cache label, budgets, exit outcome, elapsed and
workload time, sampled peak RSS, bounded log size/hash, input/output file sizes
and SHA-256 hashes, and resolved command/Python/ps/additional-tool hashes. Execution
fingerprints and revision are collected after acquiring the lock, before launch;
a lock-busy report contains no execution attestation. Initial fingerprints are
cached by file identity while preserving ordered duplicate entries. Output
fingerprints are collected afresh after execution. Paths
in `--input`, `--output` and relative tools are resolved against `--cwd`.
`--tool` records a binary without executing it; wrappers and pins are evidence,
not a claim that every compiler they later resolve was independently hashed.
`--input` and `--output` accept regular files, not recursive directory inventories
or devices/FIFOs. Lock, log and report paths also require regular files.
`--profile`, `--phase` and `--cache` are caller labels; a warm cache is not
detected or proved. Missing files/tools/Git metadata are explicitly unavailable.
The tracked-dirty flag excludes untracked files; list relevant untracked inputs
explicitly. Reports contain local paths/command arguments; select evidence for
publication deliberately.

Child output is drained even after the saved log reaches `--log-bytes` (default
1 MiB, maximum 16 MiB), avoiding a full-pipe deadlock. Extra output is discarded
and reported as truncated. The final pipe drain is capped at 16 reads (1 MiB),
50 milliseconds, the workload deadline and cancellation, even if cleanup is
unconfirmed or a writer keeps replenishing the pipe. `drain_incomplete` indicates
that EOF was not confirmed; `output_bytes` counts consumed bytes, not unknown
unread output, and an incomplete drain marks the saved log as truncated. Cleanup
retries and reporting remain reachable. Use distinct report/log names for concurrent attempts.
The log and report must not alias the lock. Child exit codes are preserved;
signal exits become `128 + signal`. Guard outcomes disambiguate reserved codes:

| Exit | Guard outcome |
| --- | --- |
| 0 | successful child |
| 2 | invalid CLI arguments, before any child |
| 70 | guard/observer failure or unconfirmed cleanup |
| 71 | leader exited with live children |
| 75 | lock busy or lock-wait expired |
| 123 | no progress for `--idle-minutes` (`hung`) |
| 124 | workload timeout |
| 125 | sampled RSS threshold exceeded |
| 126 | observed more parallel Zig compilers than `--jobs` |
| 127 | command could not be started |
| 128 + signal | cancellation or child signal |

Run `python3 tests/roadmap/build-budgets/test_guard.py` for offline tests. They
use small Python children (32 MiB sampled workload thresholds), mocks, temporary
locks and logs; no Zig/Lean/Lake/elan invocation or compiler-version probe runs.
CI runs these tests before toolchain installation and saves their output under
`RUNNER_TEMP` without adding an upload step.

This supplies measurement/coordination infrastructure for Q06. The real-module
workload suite, per-phase translator timing, baseline derivation and regression
gate are in `docs/perf-budgets.md`; run that recorder once under this guard. Its
budgets remain pending until a serial measurement is recorded and committed.

## Parallel jobs

`scripts/par.py` runs independent jobs (one per item) on a bounded number of workers:

```sh
python3 scripts/par.py [--jobs N] [--mem-mib M] [--log-dir DIR] -- COMMAND... ::: ITEM...
```

The worker count is `--jobs`, else `AIR2LEAN_JOBS`, else the CPU count (affinity and a Linux
cgroup quota, so `docker --cpus 4` counts 4). `--mem-mib M` is one job's peak memory: at most
`AIR2LEAN_MEM_MIB / M` jobs run at once (default budget: 80% of the physical memory or of a lower
cgroup limit). Each job's stdout and stderr are captured separately and written in job order, the
first unfinished job live, so the output does not depend on the worker count; with one worker it
is that of a sequential run. Every job runs; the exit status is that of the first failed job in
job order, after a list of every failed job. A signal stops every job's process group. Jobs get
`AIR2LEAN_JOBS=1`, so a job does not fan out again.

Users: `scripts/check.sh` checks its examples (AIR export, translation, golden comparison) in
parallel and builds every module in one `lake build`; `scripts/diff.sh` builds and runs the
native harnesses of the examples in parallel (the Lean side is one `difftest` process). Under the guard both stay
sequential unless the guard is given `--jobs`; on the shared development Mac use the default
lock and a moderate count (the jobs share the workload's `--rss-mib`):

```sh
python3 scripts/build-guard.py --jobs 4 --rss-mib 12000 \
  --report /tmp/check.json --log /tmp/check.log -- scripts/check.sh
```

`tests/roadmap/parallel/test_par.py` tests the helper offline; `tests/roadmap/parallel/determinism.py`
runs a changed script with `AIR2LEAN_JOBS=1` and in parallel and requires identical output and
generated files.

Cheaper local runs:

- With `AIR2LEAN_CAS_DIR` set, `diff.sh` builds its stock-Zig artifacts through `scripts/cas.py
  native` ([build-cache.md](build-cache.md)); an unchanged harness, libm or asm archive is not
  compiled again. Unset, nothing is cached.
- `scripts/build-mode-docker.sh` cross-compiles the native side on the host (`diff.sh --build-only`,
  `-target x86_64-linux`) and runs only the binaries in the emulated container;
  `AIR2LEAN_BUILD_MODE_CROSS=0` builds in the container instead.
- `AIR2LEAN_CHANGED_FROM=REF` makes the default example selection of `check.sh`, `diff.sh` and
  `build-mode-docker.sh` only the examples the changes since REF can affect
  (`scripts/changed-examples.py`; a change outside one example's own files selects all). Local runs
  only: CI always runs every example.
- `AIR2LEAN_LOCAL_CPUS` / `AIR2LEAN_LOCAL_MEMORY` size the containers of `scripts/local-ci.sh`
  (defaults 2 and 8g).
