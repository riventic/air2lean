# Lean 4.34 Lake: two facet keys in a library's `needs` create the same jobs twice, and the build can deadlock

> **DRAFT. Not filed upstream.** Filing requires the maintainer's decision. A row for issue #131's
> table is at the end. Found on 2026-11-04 while looking into Lake builds of the assurance audit that
> hung at 0% CPU on the remote build host (x86_64-linux, WSL2). Workaround: ledger
> `lake-needs-race` (scripts/assumptions.py `needs_first`).

## Summary

A `lean_lib` whose `needs` lists two facet keys whose import closures overlap, such as
`["@dep/+Dep.M39:olean", "@dep/+Dep.M39:depTrace"]`, makes Lake create the jobs of that closure
twice. Without the second key the same build runs 43 jobs; with it, 82. A fresh build then runs two
`lean` processes on the same module, and one of them fails with
`no such file or directory … Dep/M0.olean` (6 of 6 fresh builds). An up-to-date build can deadlock:
Lake waits forever at 0% CPU with no child process. On macOS (aarch64) this happened in 2 of 25
runs with `LEAN_NUM_THREADS=2` and 1 of 25 with `LEAN_NUM_THREADS=4`. On x86_64-linux it happened
with `LEAN_NUM_THREADS=1`. Almost every run with 2 or 4 threads prints
`` `Task.get` called from a `(sync := true)` task `` (24 of 25 and 22 of 25).

Three behaviours combine. All three are unchanged on `master` (2026-11-04).

1. **Each facet key of `needs` is fetched in a task of its own.** `LeanLib.recBuildExtraDepTargets`
   calls `PartialBuildKey.fetchIn` for each key. For `.facet target f`,
   `PartialBuildKey.fetchInCoreAux` (`Lake/Build/Target/Fetch.lean`) returns
   `job.bindM fun data => fetch (.facet target kind data facet)`. `bindM` is not `sync`, so each
   key's recursive fetch runs as a separate pool task, and the tasks run at the same time.
   `Module.recFetchPreSetup` awaits the extra-dependency job (`discard extraDepJob.await`), which
   lets the pool grow, so this happens even with `LEAN_NUM_THREADS=1`.
2. **The job store is check-then-create.** `fetchOrCreate` (`Lake/Util/Store.lean`) runs
   `fetch?`, then `create`, then `store`. Each step is atomic on the shared `IO.Ref`, but the
   sequence is not. Two tasks that traverse the same closure both miss a key, both create its job,
   and the later `store` replaces the earlier entry. Jobs that were bound to the first copy stay
   bound to it.
3. **`Module.computeExportInfo` blocks inside a `(sync := true)` continuation.** It runs
   `(← mod.leanArts.fetch).mapM (sync := true) fun arts => do let input ← (← mod.input.fetch).await;
   let importInfo ← (← mod.importInfo.fetch).await; …`. Normally both jobs have already finished
   when `leanArts` finishes. After a replaced store entry, the store returns the other copy, which
   may still be queued. The runtime's `task_manager::wait_for` (`src/runtime/object.cpp`) then
   prints the panic above and does not count the waiting worker as blocked: `in_pool` is false for
   `LEAN_SYNC_PRIO`, so `m_max_std_workers` is not raised. The worker keeps its pool slot while it
   waits. When every slot is held this way, an idle worker sees
   `m_std_workers.size() - m_idle_std_workers >= m_max_std_workers` and waits on `m_queue_cv`, and
   the queued `Job.async` input tasks that the waiters need never run.

## Evidence (x86_64-linux)

`gdb -batch -ex 'thread apply all bt'` of a hung `lake build AssuranceExtraction.M…`
(`LEAN_NUM_THREADS=1`), whose library `needs` `+AllocatorApplications:olean` and
`+AllocatorApplications:depTrace`:

- one worker in `lean::task_manager::spawn_worker()::{lambda}` → `condition_variable::wait`: an
  idle worker held back by the throttle above;
- one worker in `resolve_core` → `run_task` → `lean_io_bind_task_fn` → `Job.mapM` →
  `Module.computeExportInfo.lam_0` → `Job.await` → `lean_io_wait`: the sync continuation of (3);
- three workers in `Job.await`, from `Module.recFetchPreSetup.lam_6` and
  `Module.importInfoFacetConfig.lam_0` (awaiting `header`, a map of the queued `Job.async` input
  task): the parallel fetch trees of (1);
- the monitor thread in `Monitor.sleep` and the libuv loop in `epoll_pwait`.

A kernel-replay workspace with 123 such libraries hung the same way.

## Reproducer

Two Lake packages in sibling directories `dep` and `ws`, both with the `lean-toolchain`
`leanprover/lean4:v4.34.0`.

`dep/lakefile.toml`:

```toml
name = "dep"

[[lean_lib]]
name = "Dep"
```

`dep/Dep/M0.lean` … `dep/Dep/M39.lean`: `Mi` imports `Dep.M(i-1)` and `Dep.M(i-2)` (if they exist)
and declares `def mi : Nat := i`.

`ws/lakefile.toml`:

```toml
name = "ws"

[[require]]
name = "dep"
path = "../dep"

[[lean_lib]]
name = "W"
roots = ["W.R"]
needs = ["@dep/+Dep.M39:olean", "@dep/+Dep.M39:depTrace"]
```

`ws/W/R.lean`: `def r : Nat := 0`.

```sh
cd dep && lake build Dep.M39 && cd ../ws
LEAN_NUM_THREADS=1 lake build W.R    # "Build completed successfully (82 jobs)"; with one need: 43
for i in $(seq 25); do LEAN_NUM_THREADS=2 timeout 15 lake build W.R >/dev/null 2>&1 || echo "exit $?"; done
                                     # a few "exit 124": hung at 0% CPU
```

The runtime part alone, as a compiled program:

```lean
def main : IO Unit := do
  let a ← IO.asTask (do IO.sleep 300; pure ())
  let s ← IO.mapTask (sync := true) (fun _ => do
      let b ← IO.asTask (pure (5 : Nat))
      let v ← IO.wait b
      IO.println s!"sync continuation got {v}") a
  discard <| IO.wait s
```

With `LEAN_NUM_THREADS=1` it prints the panic and never ends; with 2 or more threads it ends.
(`lean --run` sizes its pool differently and ends either way.)

## Suggested fix

Any one of these removes the deadlock. The first two also remove the duplicate builds.

- Make `fetchOrCreate` create each key once, for example by storing a promise or task before
  `create` runs, so that concurrent fetches of a key share one job.
- Fetch the facet keys of `needs` on the calling thread, as command-line targets are already
  fetched (`buildSpecs`).
- In `Module.computeExportInfo`, bind the `input` and `importInfo` jobs with `bindM` instead of
  awaiting them inside a `sync` continuation, or let `wait_for` grow the pool for a sync waiter too.

## Our workaround

`scripts/assumptions.py` `needs_first` puts the needed modules' `:olean` keys on the command line
before the generated modules. Lake fetches command-line targets one after another on its build
thread, so every job of the needed closures is created once, before any library's `needs` tasks
run. Those tasks then find the jobs instead of creating copies. The generated libraries' `needs`,
and so their traces, are unchanged. `tests/roadmap/fixtures-lake/test_needs_race.py` builds the
reproducer both ways with a real Lake. When a toolchain update fixes the race, its control
assertion fails, and the workaround and the ledger row are deleted.

## Row for issue #131

| 17 | Lean 4.34 Lake: two facet keys in a library's `needs` create the same jobs twice (duplicate `lean` runs); a `(sync := true)` continuation in `Module.computeExportInfo` then blocks, and the build deadlocks at 0% CPU — draft `docs/upstream/lake-concurrent-needs.md` | **yes** (Lean/Lake, not Zig) |
