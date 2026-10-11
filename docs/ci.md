# CI: structure, result reuse, merge queue and caches

This document is the design of `.github/workflows/ci.yml` and `.github/workflows/ci-cache.yml`:
what runs where, when a check's earlier result may stand in for a new run, how a change reaches
`main`, and how the Actions cache is kept useful. Local runs come first (CLAUDE.md, "Local first,
CI confirms"); CI is the final, independent check.

## Baseline (2026-10-11, after PR #141 split CI into part rows)

| quantity | value |
| --- | --- |
| jobs per run | 28 (21 test rows, 3 macOS rows, 3 aarch64-linux jobs, `lake`, `all-checks`) |
| slowest rows | macOS 0.15.2 18.9 min, macOS 0.17.0 16.1 min, test receipt 14.6 min, test inputs 14.0 min |
| `lake` | 6.4 min cold, 1.0 min warm |
| whole run | 49.8 min wall, queue-dominated (max queue 29.7 min) |
| queue | median 35 min with 4-5 open PRs (Free plan: 20 concurrent jobs, 5 macOS) |
| Actions cache | 10.9 GB / 10 GB, 196 entries, 78 % of it PR-scoped duplicates |

Every PR push ran the full CI, and every merge to `main` ran it again on the merge commit.

## Design overview

1. **Merge queue gates every merge with the full CI.** `main` requires the single status
   `all-checks`, through a merge queue. A `merge_group` run executes every check on the exact
   commit that becomes `main`, without reuse. That run is the merge commit's evidence (release
   record, receipts, theorem inventory).
2. **PR pushes run the cheap set.** On `pull_request` CI checks out the PR head (not GitHub's
   synthetic merge with `main`: the queue tests the merge) and runs `preflight`, `lake`, and every
   part whose inputs changed. A part whose complete input set equals one that a green run already
   executed reports success by reference to that run (item 1).
3. **`main` pushes only warm caches.** `ci-cache.yml` runs on push to `main`, builds what the PR
   and queue runs restore (Lake builds, patched compilers, harness caches) and prunes stale cache
   entries. Only `main` saves cache entries; PR and queue runs restore only and share in-run
   build products as artifacts (item 4).
4. **macOS rows run only macOS evidence** and start from a warm `main` cache that already holds
   the built `Proofs` (item 3).

## 1. Input-hash result reuse

### Parts and their input sets

A *part* is one CI job row: a `test` matrix row (`test/<zig>/<part>[/<shard>]`), a `macos` row
(`macos/<zig>`) or a matrix-free job (`aarch64-linux`, `bitops-native-arm`,
`build-modes-aarch64-linux`). `.github/ci-inputs.json` declares for each part either
`"reuse": false` (always runs) or its input set:

- `inputs`: path patterns (`dir/**`, `*.lean`, exact paths) whose tracked content (path, mode,
  blob id) the part may read;
- `listings`: directories whose tracked entry *names* the part may list (Python's import system
  lists the script directory; a glob lists its directory);
- `commit_bound`: the part reads commit identity (`git rev-parse HEAD`, history, receipts that
  bind the revision): its key is the tested commit itself, so it is reused only for that commit.

The **key** of a part is SHA-256 over:

- the schema of `scripts/ci-reuse.py` and the content of the reuse machinery itself
  (`scripts/ci-reuse.py`, `scripts/ci-trace.sh`, `.github/ci-inputs.json`);
- the part's job definition (the parsed job with every step, its `env`, `runs-on`, `needs`, and
  its own matrix row in place of the matrix), the workflow-level keys other than `jobs`, and the
  definitions of the jobs it `needs` (they produce the artifacts it consumes);
- every `hashFiles(...)` pattern of those jobs, added to the content inputs (a restored cache is
  derived from exactly those files);
- the runner: `ImageOS`, `ImageVersion`, `RUNNER_OS`, `RUNNER_ARCH`;
- the declared inputs: `(path, mode, blob)` of every tracked file matching a pattern, and the
  tracked entry names of every declared listing;
- for a `commit_bound` part, the tested commit id.

A reusable job may not use `github.*` expressions other than `github.workspace` (their values
differ per run while the job text does not); `ci-reuse.py check-workflow` rejects that.

### Why a key match justifies reuse (soundness argument)

Claim: if part P passed in run R on tree T1 and every recorded observation of R lies inside the
declared input set I(P), then running P on a tree T2 with the same key passes too, up to the
nondeterminism that a re-run of P on T1 already has (timing, scheduling, cache warmth).

- P is a deterministic program of its job definition, its runner image, its pinned downloads
  (the pins are tracked files in I(P) or text of the job) and the files it observes.
- Every observation of a workspace path goes through a system call that names the path:
  `open*`, `stat*`, `access*`, `readlink*`, `exec*`, `getdents64`, `mkdir*`, `unlink*`,
  `rename*`, `chdir`/`fchdir`. The tracer records all of them for every process of every `run:`
  step of the part (`strace -f --seccomp-bpf -y`, cwd tracked per process).
- An observation is covered when it cannot differ between T1 and T2 given equal keys:
  - a tracked file opened, executed, stat'ed or written: its content pattern is in I(P);
  - a tracked directory listed: it is a declared listing, or a prefix pattern covers it;
  - a tracked directory stat'ed: its parent's listing is covered;
  - a path that is not in the tracked tree (absent, or a build output under `.lake/`,
    `zig-air-*`, `$RUNNER_TEMP`): the listing of its deepest tracked ancestor directory is
    covered, so a tracked file cannot appear there unnoticed. Untracked content is derived:
    produced by this run from covered inputs, restored from a cache keyed on included
    `hashFiles` patterns, or downloaded against a pinned digest.
- By induction over P's system calls in order: as long as every earlier observation returned the
  same result on T1 and T2, the next call is the same; a covered observation returns the same
  result. So P on T2 makes the same calls, observes the same data and reaches the same verdict.
- Git is modelled by command, not by its reads of `.git/`: the tracer attributes every access by
  a `git` process to the command line. `git ls-files` (names) needs all tracked names (the key
  then includes the full name list); `git status --porcelain` in the final "Checkout unchanged"
  step needs nothing beyond the step's own traced writes; any other git command (or any
  non-git read of `.git/`) needs commit identity, which only a `commit_bound` part may have.
- Environment variables cannot be traced, so the traced shell runs each step with the
  run-specific `GITHUB_*` variables removed (`GITHUB_SHA`, `GITHUB_REF*`, `GITHUB_RUN_*`,
  `GITHUB_EVENT_*`, ...); the step keeps only the workspace path and the write-only channels
  (`GITHUB_ENV`, `GITHUB_PATH`, `GITHUB_OUTPUT`, `GITHUB_STEP_SUMMARY`).
- Actions (`uses:`) are not traced: cache restores enter the key through their `hashFiles`
  patterns, artifact downloads through the producing job's definition and patterns, uploads do
  not influence the verdict.

What is *not* claimed: the macOS rows are not traced (no `strace`); they are reusable only as
`commit_bound` (same commit). A part that the tracer cannot cover is `"reuse": false`.

### Enforcement

- **Every executed Linux part is traced**, and its last gate, "Declared inputs cover every
  observation", fails the job when an observation is uncovered. The error names the step, the
  path and the pattern to add. This is the CI check that fails when a step reads outside its
  declared inputs; `tests/roadmap/ci-reuse/` holds the unit tests of the checker (a synthetic
  trace that reads an undeclared file must fail; one inside the declaration must pass; the git,
  listing and absent-path rules each have a case).
- **A record is written only by a passing, traced execution**: the job's final step uploads the
  artifact `ci-reuse-<key>` (the key's full preimage manifest and the trace summary) after every
  gate passed.
- **Self-check.** Each `pull_request` run picks one part uniformly (seeded by the run id; every
  row computes the same choice). That part executes even when a record exists; when it had a
  record, its summary says so and a failure is reported as a reuse mismatch against the recorded
  run. Over many runs every reusable part is re-executed.
- `ci-reuse.py check-workflow` (in preflight and in the `inputs` row) checks that every part of
  the workflow has a declaration, that every step after the reuse decision is guarded by it, and
  that reusable jobs use no run-specific expressions.

### Where records live, and how a reused result is attested

Records are **workflow artifacts** named `ci-reuse-<key>`, looked up through the REST API
(`GET /repos/{repo}/actions/artifacts?name=ci-reuse-<key>`). An artifact is immutable after
upload and GitHub binds it to the run that uploaded it; it is not in the evictable cache.
Retention: 90 days. A record is accepted only when, according to the API (not the artifact
content):

- the producing run belongs to this repository's `CI` workflow (`.github/workflows/ci.yml`),
  its head repository is this repository (no fork can produce a record), and its event is
  `pull_request`, `merge_group` or `workflow_dispatch`;
- the producing job with the part's name completed with conclusion `success` in that run
  attempt.

A reused row skips every step after "Reuse a recorded result" and writes to the job summary the
key, the producing run id, job id and URL. **Attestation:** a reused result is "passed by
reference": the check was executed by the named run, on a tree with the same key. The release
record never counts a reused (skipped) gate as passed: `scripts/release-record.py` reports it as
missing, so a release record only lists runs that executed each gate. Because the merge queue
runs every check without reuse, every `main` commit has one `merge_group` run that executed all
of them; release records, receipts and the theorem inventory name that run.

Reuse affects only PR feedback in this rollout. A wrong reuse could at worst show a PR as green
that the queue then rejects; it can never merge an unchecked change.

## 2. Merge queue

- `ci.yml` triggers: `pull_request`, `merge_group`, `workflow_dispatch` (a full run, e.g. for a
  commit that reached `main` outside the queue). No `push` trigger: the queue already tested the
  exact commit that `main` advances to.
- `pull_request` runs: reuse on, PR head checked out. `merge_group` and `workflow_dispatch`
  runs: reuse off, every part executes and is traced, and records are written.
- `all-checks` aggregates every job; it is the one required status.
- Repository ruleset on `main` (applied with `gh api` after this workflow is on `main`):
  required status check `all-checks` (integration: GitHub Actions), merge queue with merge method
  `MERGE`, grouping `ALLGREEN`, build concurrency 2, group size 1-5, no wait for a minimum group,
  status timeout 120 min; block force pushes and deletion. Admins keep bypass for emergencies;
  a bypassing push gets a `workflow_dispatch` run.
- `scripts/release-record.py` and the target-matrix tooling accept `merge_group` runs as
  evidence: a `merge_group` run's `headSha` is the commit the queue merges.

### Coordinator merge flow

1. The PR is green (`all-checks`) on its head, after `/review` and `/simple`.
2. `gh pr merge <N> --merge --auto` (or "Merge when ready" in the UI) adds it to the queue;
   with no further checks pending it enters the queue at once.
3. The queue builds `main` + the PRs ahead of it + this PR as a `merge_group` commit and runs
   the full CI on it; on green it fast-forwards `main` to that commit, on red it removes the PR
   and comments. `gh pr merge <N> --disable-auto` leaves the queue.
4. Integration failures appear only in the queue; merge `main` into a PR branch before
   queueing when `main` moved under it substantially.

## 3. macOS rows

Each macOS row keeps only aarch64-macos evidence: stock-Zig install, ABI probes and T04 ABI
qualification, the Darwin AIR export, translation and native differential test (`check.sh`),
the proof build of the Darwin translations (Q05 requires `proof_check` on the host; it stays),
and the native wide bit-operation differential. What changes:

- The `main` macOS cache entry (`ci-cache.yml`) contains the root package *and* `Proofs`, so the
  row's proof build only rebuilds the modules that the PR or a Darwin translation changes. Before,
  the macOS cache held only `lake build` defaults and every row rebuilt all of `Proofs` in its
  check tree (5-10 min).
- Patched compilers are cached under a key over exactly the inputs of `zig-patch/build.sh` for
  that version: `air-json/*.zig`, `<version>/hook.patch`, `build.sh`, `lock.sh`, `toml-get.sh`,
  the version's own `versions.toml` table and the host-Zig pin (`scripts/ci-cache-key.py`). A pin
  change of another version no longer invalidates it. Only `main` builds and saves them.
- Platform-independent work has no macOS copy left to move: the Linux rows already run every
  version-neutral regression.

## 4. Cache hygiene

- Only `ci-cache.yml` on `main` saves cache entries (Lake root and `tests/diff` package per
  platform, patched compilers per version and platform, native harness caches). PR and queue
  runs use `actions/cache/restore` only.
- Within a run, the `lake` job uploads its build as one zstd-compressed artifact (retention 1
  day) and the `zig-air` job uploads each patched compiler it had to build; the rows download
  them. A PR therefore builds each changed thing once per run instead of once per row, and saves
  nothing to the cache.
- `ci-cache.yml` prunes after every `main` push and daily: it keeps the newest `main` entry per
  key prefix and deletes every other entry (older `main` entries, every PR- or queue-scoped
  entry). `main` stays far under 10 GB, so no `main` entry is ever evicted by size.

## Rollout order

1. This document (first commit).
2. Cache hygiene and build-ahead: `ci-cache.yml`, restore-only rows, `lake`/`zig-air` artifacts,
   per-version compiler keys, cleanup. Measurable on its own.
3. macOS: warm `Proofs` in the macOS cache.
4. Merge queue triggers, PR-head checkout, `release-record`/`target-matrix` evidence rules.
5. Reuse: tracer, checker, declarations derived from traces of this PR's own CI runs, records,
   lookup, self-check, release-record handling of reused gates.
6. After merge: ruleset with `all-checks` and the merge queue (`gh api`), verified with a test PR.
7. Later, maintainer decision after a clean self-check record: reuse in `merge_group` runs for
   parts whose key matches a record from a `merge_group` run.

## Expected savings

- Merges: one full run per merge (queue) instead of one per PR push plus one per `main` push.
- PR pushes: parts whose inputs a push does not touch are free. Lean sources are inputs of every
  Linux row (each consumes the `lake` build), so Lean changes still re-run most rows; tooling,
  test, documentation and assurance-record changes re-run only the rows that read them.
- macOS rows: about 8-10 min instead of 13-19 min (proof build incremental from `main`).
- Cache: about 1.5 GB of `main` entries instead of 10.9 GB, so no `main` miss through eviction.
- The measured before/after (wall time, runner minutes, queue time) is in the PR description.
