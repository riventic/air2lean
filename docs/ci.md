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
2. **PR pushes run the cheap set.** On `pull_request` CI checks out GitHub's merge of the PR
   into `main` (the tree the workflow file itself comes from, so a step that `main` added never
   runs on a tree without its files) and runs `preflight`, `lake`, `generated`, `provenance`,
   and every part whose inputs changed. A part whose complete input set equals one that a green run already
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
  step needs nothing beyond the step's own traced writes; `fetch`, `show`, `cat-file` and
  `rev-parse` naming only full object ids read content-addressed objects (the ids come from
  observed tracked files); any other git command (or any non-git read of `.git/`) needs commit
  identity, which only a `commit_bound` part may have.
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

- **Every executed Linux part is traced** (`defaults: run: shell: bash scripts/ci-trace.sh {0}`;
  the coverage and record steps after every gate are the only steps that run untraced, which
  `check-workflow` enforces), and its step "Declared inputs cover every observation" fails the
  job when an observation is uncovered. The error names the step, the
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
- `pull_request` runs: reuse on, the PR's merge with `main` checked out. `merge_group` and `workflow_dispatch`
  runs: reuse off, every part executes and is traced, and records are written.
- `all-checks` aggregates every job; it is the one required status.
- Repository ruleset on `main` (applied with `gh api` after this workflow is on `main`):
  required status check `all-checks` (integration: GitHub Actions), merge queue with merge method
  `MERGE`, grouping `ALLGREEN`, build concurrency 2, group size 1-5, no wait for a minimum group,
  status timeout 120 min; block force pushes and deletion. Admins keep bypass for emergencies;
  a bypassing push gets a `workflow_dispatch` run.
- Repository ruleset on `generated`: block force pushes and deletion, restrict updates; bypass
  only for the GitHub Actions app (integration 15368), which `generated.yml` pushes as.
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

### Whole-tree generated files

Decision (user, 2026-10-11): generated files that describe the whole tree leave PRs; they are
produced in CI at merge, they are still in the repository, and they are still checked. They are
listed in `assurance/generated.json` (scripts/generated.py is the one tool that produces,
publishes and supplies them):

| group | files | generator |
| --- | --- | --- |
| `coverage` | `coverage/<version>.json` per supported version | `coverage.py generate --os linux` over the pinned pristine source |
| `premise-index` | `docs/premise-index.md` | `premises.py write` |
| `provenance`, `provenance-gap` | `manifest.json`, `pins.json`, `receipt/{audit,plan,receipt}.json` of `assurance/provenance{,-gap}/` | `provenance-evidence.py regenerate --refresh`, `install`, `record` |

A file is whole-tree when its content depends on most of the tree (translator, runtime, goldens,
toolchain), so every merge to `main` can make it stale even when the PR did not touch its subject;
committed, it was regenerated after nearly every merge (16 coverage, 14 provenance-receipt, 9 + 8
manifest/pin and 6 premise-index regeneration commits in the week before this change). A file
that changes only with its own subject stays committed and is checked for staleness as before:
goldens, `Gen.lean` modules, the fixtures' source, AIR and proofs, `docs/support-matrix.md`
(its coverage counts change only with dispositions, i.e. with a translator change), the trust
report. The theorem inventory's run records (`assurance/theorem-inventory.json` `runs`) are
whole-tree too but are recorded from Lean builds that CI does not run per translation yet; they
stay committed until CI records them (next step: one deterministic swap-build record per
required translation, timing fields dropped).

**Not committed.** The files are in `.gitignore`. No PR adds or changes one, and agents never
regenerate them for a PR.

**Produced twice on the tested tree.** Every CI run (PR, `merge_group`, `workflow_dispatch`) has
two jobs that regenerate them on exactly the checked-out tree:

- `generated` (no build; about a minute): `scripts/generated.py produce --group coverage --group
  premise-index`. Each generator runs twice; the two outputs must be byte-identical. The files
  and `generated-manifest.json` (commit, tree, sha256 of each file) are uploaded as
  `generated-files`. Every test row and `preflight` downloads it and runs `scripts/generated.py
  install`, which refuses files produced for another commit or tree or with a wrong digest; the
  gates that read the files (L14 fixtures, support matrix, AIR validation, premise checks,
  tutorials, inventory regressions) then check exactly them.
- `provenance` (after `lake` and `zig-air`): the same for both provenance fixtures. A receipt
  records its own run (the build-guard report and log digests in `receipt.json`'s artifacts,
  whether the audit rebuilt its extractor, and the manifest and pin digests that chain those
  files), so the two runs must agree on everything else, including every compiled theorem and
  every source, AIR, profile, `Gen.lean` and native digest (`run_bound` in the registry names the
  excluded fields); then the strict `check` and strict
  `replay` of both fixtures and the fixture regressions run on them. Uploaded as
  `generated-provenance`.

A generator that fails (a missing coverage disposition, a fresh AIR or `Gen.lean` that differs
from the committed one, a strict check) fails the job, so a PR whose tree does not regenerate
cleanly is red, and the queue never merges one.

**Published per main commit on the `generated` branch.** The queue fast-forwards `main` to the
exact merge commit M its `merge_group` run tested, so that run's artifacts are M's files.
`.github/workflows/generated.yml` runs on every push to `main`: `scripts/generated.py publish`
walks main's first-parent history back to the newest commit that has an entry and, for each
newer commit M (oldest first), finds M's successful `merge_group` (or `workflow_dispatch`) CI
run, downloads its two artifacts, checks that both manifests name M and `M^{tree}`, that every
digest matches and that together they hold exactly the registry's files, and appends one commit
to `generated`. Nothing is regenerated there. Layout: each `generated` commit's tree is exactly
the registry's files at their repository paths (no other files); its parent is the previous
entry; its message names the main commit, its tree and the run:

```
Generated files for main 1a2b3c4d5e6f

Produced twice by CI run 38200000000 (merge_group) on the merged tree; not regenerated here.

Main-Commit: <M>
Main-Tree: <tree of M>
CI-Run: https://github.com/riventic/air2lean/actions/runs/38200000000
```

So `git log origin/generated --grep "Main-Commit: <M>"` finds M's entry, and
`https://github.com/riventic/air2lean/blob/generated/<path>` always shows the newest main
commit's file (the documentation links to the premise index point there). A push to `main` that
did not come through the queue (admin bypass) has no `merge_group` run: run CI on it with
`workflow_dispatch`, and the next publish picks it up. Entries stay in main's order: publishing
stops at the first commit without a run.

**Freshness, loudly.** The same workflow runs every 30 minutes and after each publish:
`scripts/generated.py freshness` fails when a main commit has been main's head for longer than
`freshness_minutes` (30; landing time from the repository activity API) without an entry, and
the workflow opens (or comments on) the issue "generated branch is stale or failed to publish".
A failed verification in `publish` fails the same way.

**Reading the files.** Every tool reads them at their repository paths; `scripts/generated.py`
puts them there:

- `materialize` (what `scripts/preflight.sh` runs first): regenerates the cheap groups locally
  (offline: the pristine sources are cached in `$AIR2LEAN_CACHE`), and fetches the provenance
  fixtures of the newest published first-parent ancestor of `merge-base(HEAD, origin/main)` (or
  skips them offline: CI regenerates and checks them for the PR's tree); `--heavy regen`
  regenerates them locally too (patched 0.16.0, stock 0.16.0, Lean).
- `fetch --rev SHA [--group G]`: the published files of main commit SHA, e.g. to inspect or
  diff a released revision's coverage or provenance; `regen [--group G]`: regenerate in place.
- `scripts/regen.sh`: its `tree` steps are exactly these groups (it asserts that against the
  registry) and regenerate them in place through this helper; `--pr` skips them.
- CI rows: `install` of the run's own artifact, as above.

A gate that reads a whole-tree file reads data derived from the whole tree, so the reuse checker
(item 1) counts such an observation as covered only by a whole-tree (`**`) declaration.

**Trust argument.** Every file on `generated` for main commit M was produced by CI on exactly
M's tree (the manifest's commit and tree are checked against M at publication), by the
generators in M itself, twice with identical results (deterministic), and the same run's gates
checked it strictly (strict provenance check and replay, L14 and AIR validation over the
inventories, premise checks over the index) before the queue let M become `main`. No such file
comes from a developer machine, and none is written by a bot commit on `main`: `main` holds only
reviewed commits, so the queue never re-runs for a generated-file commit. The files stay in the
repository (the `generated` branch, one commit per main commit, never rewritten: the
recommended ruleset below blocks force pushes and deletion), and anyone can reproduce one with
`scripts/generated.py regen` on M.

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
- Within a run, the `lake` job (restored from `main`'s newest entry, built on top) uploads its
  build as one zstd archive and the `zig-air` job each version's patched compiler (restored from
  `main` or built), as artifacts with retention 1 day; the rows download and unpack them. The
  unpack steps, like the reuse steps, are CI-only (`ci_only` in scripts/local-ci-steps.py;
  `scripts/local-ci.sh --prepare` provides both locally) and are not release gates. A PR therefore builds each changed thing once per run instead of once per row, and saves
  nothing to the cache.
- `ci-cache.yml` prunes after every `main` push and daily: it keeps the newest `main` entry per
  key prefix and deletes every other entry (older `main` entries, every PR- or queue-scoped
  entry). `main` stays far under 10 GB, so no `main` entry is ever evicted by size.

### Current declarations

- Traced and reusable by content, declared `"inputs": ["**"], "tree_names": true` (the whole
  tree): golden and lean rows of 0.14.1, 0.15.2 and 0.17.0, the three build-mode rows and the five
  mutation shards. Most of them build the Lake package or a check tree, which read nearly every
  file, so narrowing gains little there.
- Narrowed from their traces (`scripts/ci-reuse.py suggest` over the uploaded `ci-trace-<key>`
  artifacts, verified by the next execution's coverage check): `aarch64-linux`,
  `bitops-native-arm`, `build-modes-aarch64-linux`.
- `commit_bound` (untraced, reused only for the same commit): the macOS rows (no strace), and
  the 0.16.0 `golden`, `lean`, `inputs`, `native` and `receipt` parts, whose gates read commit
  identity (receipts and assumption reports bind `HEAD`; release-record, manifest and
  generated-branch regressions run git on `HEAD`).
- `"reuse": false` (always runs, untraced): `audit` (under strace it exceeded the 90-minute job
  limit; untraced it takes 10-17 min), `generated` and `provenance` (their artifacts are inputs of
  other jobs and of the `generated` branch).

Tracing costs time: in the first runs a traced row took 1.2-2x its untraced time (build modes on
arm64 16-17 min instead of 8.4, golden 0.17.0 19 instead of 11, mutation shards 11-18 instead of
8-12). It is paid only by parts that execute; a reused part costs about a minute.

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
