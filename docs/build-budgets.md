# Sequential build budgets

`scripts/build-guard.py` runs one command under a user-wide exclusive lock on
Linux or macOS. It uses Python's standard library, `ps`, and optional read-only
Git metadata. It never probes compiler versions or starts another build itself.
Use the same lock for every participating worktree and coordinator:

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
`AIR2LEAN_BUILD_LOCK`. The file is never removed, so waiting coordinators retain
the same flock inode. A busy lock fails with exit 75 without starting a child.
`--lock-wait SECONDS` permits bounded waiting. Nested guards using the same lock
also fail or wait: wrap a whole workload once. Advisory locking coordinates
participating callers; unguarded builds are outside its control. Existing
`zig-patch/build.sh` already uses `-j1` for its compiler bootstrap.

The guard sets `LEAN_NUM_THREADS=1`. For a direct `zig build` command, it adds
`-j1` if absent, rejects other job counts and response files that could hide job
options, and records both requested and executed arguments. It also stops a
workload when a sample contains multiple leaf Zig processes. A build driver
supervising one compiler is counted once. `zig`, `zig-air`, and `zig-unlocked`
are recognized; use `--zig-name NAME` for a renamed executable. Scripts must
choose sequential compiler flags themselves. The guard never automatically
parallelizes workloads; single-thread Lean settings do not guarantee that an
arbitrary build system launches only one process.

The child starts in a new session/process group. Timeouts, sampled RSS excess,
SIGINT/SIGTERM/SIGHUP, and detected parallel Zig work trigger group TERM followed
by KILL after `--grace` seconds. The original group catches orphaned children;
observed descendants remain tracked if they change groups or sessions. Cleanup
checks that observed live processes stop before releasing the lock. A leader
that exits while children remain is a failed workload, and those children are
stopped. Zombies are already stopped and excluded. Process-generation checks
use `ps lstart` (one-second resolution) when following detached descendants.

This is a cooperative build coordinator, not a security sandbox. A descendant
that detaches and is reparented entirely between samples can escape observation.
SIGKILL of the coordinator or host failure cannot run cleanup. A `ps` failure
causes a failed check and attempts to stop the original group; inability to
confirm cleanup is reported as `cleanup_failed`. For untrusted processes or hard
containment, use an OS service/container with stronger process ownership.

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
and SHA-256 hashes, and resolved command/Python/ps/additional-tool hashes. Paths
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
and reported as truncated. Use distinct report/log names for concurrent attempts.
The log and report must not alias the lock. Child exit codes are preserved;
signal exits become `128 + signal`. Guard outcomes disambiguate reserved codes:

| Exit | Guard outcome |
| --- | --- |
| 0 | successful child |
| 2 | invalid CLI arguments, before any child |
| 70 | guard/observer failure or unconfirmed cleanup |
| 71 | leader exited with live children |
| 75 | lock busy or lock-wait expired |
| 124 | workload timeout |
| 125 | sampled RSS threshold exceeded |
| 126 | observed parallel Zig compilers |
| 127 | command could not be started |
| 128 + signal | cancellation or child signal |

Run `python3 tests/roadmap/build-budgets/test_guard.py` for offline tests. They
use small Python children (32 MiB sampled workload thresholds), mocks, temporary
locks and logs; no Zig/Lean/Lake/elan invocation or compiler-version probe runs.
CI runs these tests before toolchain installation and saves their output under
`RUNNER_TEMP` without adding an upload step.

This supplies measurement/coordination infrastructure for Q06. It does not
qualify translation or proof-performance budgets on real modules, attribute
time inside a compiler pipeline, compare a regression baseline, or demonstrate
preservation of an optimization. Record representative per-phase workloads,
inputs, emitted output and cold/warm runs under agreed budgets before making
those claims.
