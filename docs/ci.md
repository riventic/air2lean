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

### Measured after the merge queue (2026-10-12, before PR "CI speed")

Five full runs of the reuse/queue workflow (`gh api .../actions/runs/<id>/jobs`). *Wall*: run
start to last job end. *Queue*: job created to job started. *Setup*: checkout, installs,
downloads, unpacks, cache restores, patched-compiler and translator builds; *test*: every
other step.

| run | event | wall | runner min (macOS) | queue max / sum | setup / test min | longest test row | longest macOS row |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 38182713444 | workflow_dispatch | 30.8 | 332 (66) | 11.9 / 51 | 38 / 292 | 18.0 (golden 0.15.2) | 24.0 |
| 38182983305 | pull_request (docs only) | 35.7 | 275 (43) | 16.0 / 197 | 25 / 249 | 16.1 | 16.2 |
| 38180914212 | pull_request | 26.6 | 343 (60) | 6.0 / 36 | 39 / 302 | 20.6 (golden 0.17.0) | 24.2 |
| 38178362017 | pull_request | 37.5 | 349 (72) | 11.7 / 81 | 39 / 308 | 19.4 | 25.6 |
| 38179421984 | push (old workflow) | 32.2 | 265 (58) | 12.6 / 156 | 13 / 250 | 17.4 | 23.4 |

- 35 jobs per run (20 test rows, 3 macOS, 3 aarch64-linux, 4 `zig-air`, `lake`, `generated`,
  `preflight`, `provenance`, `all-checks`). The Free plan runs 20 jobs at a time, 5 of them
  macOS, across all workflows: from 23:06 to 23:33 on 2026-10-11 every one of the 20 slots was
  busy (one dispatched run, one PR run, `ci-cache.yml`), so a run's wall time is mostly the
  runner-minutes of everything in flight divided by 20. One run alone needs at least
  332 / 20 = 17 min.
- Setup is about 12 % of runner time; the build-ahead jobs finish 1.4-2.7 min into an
  uncontended run. The rest is test steps and queueing.
- Sinks: (1) the macOS rows rebuilt all of `Proofs` (13.7 min of the 24-min 0.16.0 row): the
  `main` cache entry had been saved by the old workflow without `Proofs` under the same key, so
  `ci-cache.yml` saw a hit and never rebuilt it; (2) tracing cost 1.3-1.9x on the rows that
  declare the whole tree (golden 0.17.0 17-19 min instead of 10-14) although such a row can only
  be reused on an identical tree; (3) the docs-only PR #149 reused 3 of 35 jobs: every traced
  row observed every tracked file, because `git status` in the final "Checkout unchanged" step
  stats them from threads that the reducer did not attribute to git; and any edit of a `test`
  step changed every test row's key.

### After PR #153 (2026-10-12)

| run | event | wall | runner min (macOS) | queue max / sum | golden 0.15.2 / 0.17.0 / 0.14.1 | macOS rows |
| --- | --- | --- | --- | --- | --- | --- |
| 38220406483 | merge_group (#149, docs only) | 29.5 | 286 (53) | 6.2 / 43 | 9.3 / 10.0 / 4.5 | 14.6-20.3 |
| 38221218328 | pull_request (#151, 94 Lean files) | 51.0 | 370 (61) | 18.9 / 215 | 10.0 / 10.3 / 6.9 | 17.5-21.6 |
| before: 38182713444, 38180914212 | dispatch, PR | 26.6-30.8 | 332-343 (60-66) | 6-12 / 36-51 | 18.0-20.6 / 17.2-19.5 / 7.1-7.5 | 17.6-24.2 |

- Golden rows of 0.15.2 and 0.17.0: 17-21 min to 9-10 min. Part of it is PR #152 (in-job
  parallelism, merged just before): the 0.16.0 golden row, untraced before and after, went from
  15 to 9 min; the rest is dropping the tracer (`commit_bound`).
- The narrowed rows (mutation, build modes, lean of 0.14.1/0.15.2/0.17.0) are reusable for
  changes outside their directories; a `merge_group` run still executes them (see
  [reuse in the merge queue](#reuse-in-the-merge-queue)).
- macOS: both runs above restored a `main` entry from before `ci-cache.yml` rebuilt it with
  `Proofs` (08:02Z), or changed Lean sources, so their proof builds (7-13 min) were legitimate;
  the recipe-keyed entry is now restored (run 38221218328 hit the new key prefix).
- Wall time is set by the 20-slot queue: run 38221218328 waited 215 job-minutes. One run alone
  needs at least runner-minutes / 20 = 14-18 min; its critical path (build-ahead 2 min, then the
  longest of `receipt`, `audit`, `lean` 0.16.0 and a mutation shard, 15-18 min) is about the same.

## Design overview

1. **Merge queue gates every merge.** `main` requires the single status `all-checks`, through a
   merge queue. A `merge_group` run checks the exact commit that becomes `main`: every part whose
   input key changed executes on it, and every other part is passed by reference to an earlier
   `merge_group` (or `workflow_dispatch`) run, on a commit that is now on `main`, that executed
   it on a tree with the same key (item 1). That run is the merge commit's evidence (release
   record, receipts, theorem inventory).
2. **PR pushes run the cheap set.** On `pull_request` CI checks out GitHub's merge of the PR
   into `main` (the tree the workflow file itself comes from, so a step that `main` added never
   runs on a tree without its files) and runs `preflight`, `lake`, `generated`, `provenance`,
   and every part whose inputs changed; any green run's record may stand in.
3. **Nightly full run.** A `schedule` run on `main` executes every part on the whole,
   unrestricted checkout (the support jobs stay restricted, item 1), reusing and recording nothing: every gate is executed for real at
   least once a day, so a declaration that is narrower than what a gate means to check (one that
   lets a gate pass on fewer files rather than fail) is found within a day.
4. **`main` pushes only warm caches.** `ci-cache.yml` runs on push to `main`, builds what the PR
   and queue runs restore (Lake builds, patched compilers, harness caches) and prunes stale cache
   entries. Only `main` saves cache entries; PR and queue runs restore only and share in-run
   build products as artifacts (item 4).
5. **macOS rows run only macOS evidence** and start from a warm `main` cache that already holds
   the built `Proofs` (item 3).

## 1. Input-hash result reuse

### Parts and their input sets

A *part* is one CI job row: a `test` matrix row (`test/<zig>/<part>[/<shard>]`), a `macos` row
(`macos/<zig>`) or a matrix-free job (`aarch64-linux`, `bitops-native-arm`,
`build-modes-aarch64-linux`). `.github/ci-inputs.json` declares for each part either
`"reuse": false` (always runs, on the whole checkout) or its input set: `inputs`, path patterns
(`dir/**`, `*.lean`, exact paths) of the tracked files whose content the part may read; the
`exclude` patterns remove paths from the wildcard patterns (an exact path is always an input). `defaults` apply to every part; the reuse machinery
(`scripts/ci-reuse.py` and what it imports, `.github/ci-inputs.json`,
`assurance/generated.json`) and every `hashFiles(...)` pattern of the part's jobs are always
inputs. The support jobs `lake` and `zig-air` have their own declared inputs (`support`), run
restricted to them, and every part that needs one adds them to its own. `ci-reuse.py
check-workflow` (preflight, `inputs` row) fails when a part has no declaration or a reusable part
declares no inputs.

### Restricted checkout

An executing part never sees more than its key. After the reuse decision it runs in a
*restricted checkout* (`ci-reuse.py restrict`, called by the decision step):

- HEAD is a parentless commit with fixed author, committer, date (`@0`) and message, whose tree
  is the tested commit's with every file outside the declared inputs replaced by one fixed
  placeholder blob (a NUL byte, then "withheld by the restricted CI checkout ..."). So `git
  rev-parse HEAD`, `git ls-files`, a proof receipt that binds HEAD, a directory listing: all are
  functions of the declared content and the tracked names, which the key contains.
- A withheld file keeps its name, has mode 000 and the skip-worktree bit: any read fails
  (`EACCES`, the runner user is not root), `git status` ignores it, and `scripts/check-tree.py`
  copies it as the same unreadable placeholder into a check tree. A declaration that is too
  narrow therefore fails the part; it cannot let a result pass for content it never keyed.
- In CI the repository is then sealed: every remote (with the credentials `actions/checkout`
  configured), ref, reflog and unreachable object is removed, so the tested commit and the
  withheld content are no longer in `.git` (`git show $GITHUB_SHA:path` fails too) and `git
  fetch origin` cannot bring them back. `restrict` checks that the tested tree is gone.
- `ci-reuse.py check-restricted` (in "Checkout unchanged by verification" and before every
  record) fails when a withheld file was changed or removed, and, when the steps run as root
  (local Docker runs, where mode 000 stops nothing), when one was read (its access time is newer
  than the checkout). As another user a read already failed, and an access time can come from a
  system daemon (Spotlight on macOS), so it is not checked there.
- The whole-tree generated files (`generated` job) are installed before the restriction and stay
  (they are untracked); the key contains their digests.

`scripts/local-ci.sh part test/<zig>/<part>` runs one Linux test row the same way in the local
container (as root: the access-time check is what fails it there). `scripts/local-ci.sh discover
test/<zig>/<part>` is the diagnostic for writing a declaration: the checkout stays whole, every
step runs even after a failure, and the run ends with the list of undeclared files it read
(never an input of a key or a record).

### The key

The **key** of a part is SHA-256 over:

- the schema of `scripts/ci-reuse.py`; the reuse machinery's content is among the inputs;
- the part's job definition (the parsed job with its `env`, `runs-on`, `needs`, its own matrix
  row in place of the matrix, and every step that may run for that row), the workflow-level keys
  other than `jobs`, and the definitions of the jobs it `needs` (they produce the artifacts it
  consumes). A step is left out only when its `if` is false for the row in every executing run:
  the condition reads nothing but `matrix.*`, `runner.os` (from `runs-on`) and
  `env.AIR2LEAN_REUSED` (empty in an executing run) and evaluates to false
  (`scripts/target-matrix.py`'s evaluator). A step that never runs cannot affect the verdict;
  a condition with a status function, another step's output or any other context keeps the step.
  So adding a step for the `lean` rows does not change a mutation shard's key;
- the runner: `ImageOS`, `ImageVersion`, `RUNNER_OS`, `RUNNER_ARCH`;
- the declared inputs (with the forced and support patterns): `(path, mode, blob)` of every
  tracked file they select;
- the SHA-256 of all tracked names (they are visible in the restricted checkout);
- for a part that needs `generated`, the SHA-256 of every installed whole-tree generated file.

Not the commit: a change confined to withheld files (for most parts: the prose documentation)
leaves the key unchanged. Adding, removing or renaming any tracked file changes every key.

A reusable job may not use `github.*` expressions other than `github.workspace`, nor `vars.*`,
`secrets.*` or `inputs.*` (their values can differ between runs while the job text does not);
`ci-reuse.py check-workflow` rejects them.

### Why a key match justifies reuse (soundness argument)

Claim: if part P passed in run R on tree T1 and P runs on tree T2 with the same key, P passes
on T2 too, up to the nondeterminism that a re-run of P on T1 already has (timing, scheduling,
cache warmth).

- P is a deterministic program of its job definition, its runner image, its pinned downloads
  (the pins are declared files or text of the job), the artifacts of the jobs it needs, and its
  checkout.
- The restricted checkouts of T1 and T2 are identical: the same declared files with the same
  content and mode, the same withheld names with the same placeholder, the same HEAD commit (its
  id is computed from exactly these), and no other commit or ref (sealed). This does not depend
  on what P reads or how; no observation of P's system calls is needed.
- The needed artifacts: `lake` and `zig-air` ran restricted to their declared inputs, which are
  in P's key, so their outputs are functions of the key (the Lake caches they restore are keyed
  by `hashFiles` patterns, also in the key, and Lake's content traces rebuild what differs);
  `generated` derives its files from the whole tree, and the key contains their digests. The
  support jobs are cache producers: `lake` builds with `continue-on-error`, so a support
  declaration that is too narrow costs time (the parts rebuild what is missing in their own
  checkouts), never soundness; for the same reason they stay restricted in the nightly run.
- The network is not an input: a part downloads only pinned, digest-checked artifacts and does
  not read repository content over the network (it could fetch the public repository by URL;
  no gate does, and such a gate would be nondeterministic with or without reuse).
- Environment variables are not inputs that could differ in effect: `GITHUB_SHA` and the
  `GITHUB_REF*` values name a commit and refs that the sealed repository no longer holds; the
  remaining run-specific variables (run ids, URLs) are not read by any gate. Actions (`uses:`)
  enter the key through their job definition and `hashFiles` patterns; uploads do not influence
  the verdict.
- So P on T2 starts from the same state as P on T1, and reaches the same verdict.

What can still be wrong is the declaration's *meaning*, not reuse: a gate that enumerates a
directory and silently checks fewer files when some are withheld (rather than failing on the
unreadable placeholder) checks less on every tree, executed or reused. The nightly unrestricted
run executes every gate on the whole checkout and catches that within a day.

### Enforcement

- **Every executing part runs restricted** (the decision step restricts before any gate; the
  support jobs restrict right after their checkout, which `check-workflow` enforces), and
  `check-restricted` runs after the gates.
- **A record is written only by a passing restricted execution**: the job's final steps check
  that HEAD is still the restricted commit, that no withheld file was touched and that the key's
  preimage (incl. the generated files) did not change, then upload the artifact
  `ci-reuse-<key>` (the key's full preimage manifest).
- **Self-check.** Each `pull_request` run picks one part uniformly (seeded by the run id; every
  row computes the same choice). That part executes even when a record exists; when it had a
  record, its summary says so and a failure is reported as a reuse mismatch against the recorded
  run.
- **Nightly full run** (design item 3), unrestricted, nothing reused or recorded.
- `ci-reuse.py check-workflow` (in preflight and in the `inputs` row) checks that every part of
  the workflow has a declaration, that every reusable part declares inputs, that every step after
  the reuse decision is guarded by it, that the support jobs restrict, and that reusable jobs use
  no run-specific expressions. `tests/roadmap/ci-reuse/` holds the unit tests, including the
  regression that reading an undeclared file in a restricted checkout fails.

### Where records live, and how a reused result is attested

Records are **workflow artifacts** named `ci-reuse-<key>`, looked up through the REST API
(`GET /repos/{repo}/actions/artifacts?name=ci-reuse-<key>`). An artifact is immutable after
upload and GitHub binds it to the run that uploaded it; it is not in the evictable cache.
Retention: 90 days. A record is accepted only when, according to the API (not the artifact
content):

- the producing run belongs to this repository's `CI` workflow (`.github/workflows/ci.yml`) and
  its head repository is this repository (no fork can produce a record);
- for a `pull_request` run: the producing event is `pull_request`, `merge_group` or
  `workflow_dispatch`; for a `merge_group` run: only `merge_group` or `workflow_dispatch`, and
  the producing run's head commit is `main` or an ancestor of it (GitHub compare API), never a
  PR's run or a queue run whose group did not merge;
- the producing job with the part's name completed with conclusion `success` in that run
  attempt.

`workflow_dispatch` and `schedule` runs never reuse.

A reused row skips every step after "Reuse a recorded result", writes the key, the producing
run id, job id and URL to the job summary, and uploads them as `ci-reuse-ref-<key>`.
**Attestation:** a reused result is "passed by reference": the check was executed by the named
run, on a tree with the same key. `scripts/release-record.py record --reuse-references DIR
--reference-run RUN_JSON` (the downloaded `ci-reuse-ref-*` artifacts of the cited runs, and the
run JSON of each producing run they name) lists such gates with status `by-reference`, the
producing run, job and key, but only when the reference was made for the recorded revision and
the producing run's JSON shows that job passed every one of its gates; otherwise a reused gate
stays `missing`. `verify` refuses a `by-reference` gate whose evidence names no reference for
its job.

## 2. Merge queue

- `ci.yml` triggers: `pull_request`, `merge_group`, `workflow_dispatch` (a run without reuse,
  e.g. for a commit that reached `main` outside the queue; `generated.yml` dispatches it
  itself), `schedule` (nightly full run, unrestricted). No `push` trigger: the queue already
  tested the exact commit that `main` advances to.
- `pull_request` runs: the PR's merge with `main` checked out, any green record reused.
  `merge_group` runs: records of `merge_group`/`workflow_dispatch` runs on `main` reused (item
  1). Every executing part runs restricted and records its result.
- `all-checks` aggregates every job; it is the one required status.
- Repository ruleset `main-protection` on `main` (applied with `gh api`, 2026-10-12):
  required status check `all-checks` (integration: GitHub Actions), merge queue with merge method
  `MERGE`, grouping `ALLGREEN`, build concurrency 2, group size 1-5, no wait for a minimum group,
  status timeout 120 min; block force pushes and deletion. Admins keep bypass for emergencies;
  a bypassing push gets a `workflow_dispatch` run.
- Repository ruleset `generated-protection` on `generated`: block force pushes and deletion
  (append-only); bypass only for the admin role. `generated.yml` only fast-forwards it.
- `scripts/release-record.py` and the target-matrix tooling accept `merge_group` runs as
  evidence: a `merge_group` run's `headSha` is the commit the queue merges.

### Coordinator merge flow

1. The PR is green (`all-checks`) on its head, after `/review` and `/simple`.
2. Enqueue it. While the repository setting "Allow auto-merge" is off, `gh pr merge <N> --merge
   --auto` fails; enqueue the verified head directly (fails if the head moved):

   ```
   gh api graphql -f id="$(gh pr view <N> --json id -q .id)" -f head=<verified head sha> -f query='
     mutation($id: ID!, $head: GitObjectID!) {
       enqueuePullRequest(input: {pullRequestId: $id, expectedHeadOid: $head}) {
         mergeQueueEntry { position state } } }'
   ```

   With auto-merge on, `gh pr merge <N> --merge --auto` (or "Merge when ready") does the same
   once the checks are green.
3. The queue builds `main` + the PRs ahead of it + this PR as a `merge_group` commit and runs
   CI on it (parts with an unchanged key passed by reference, item 1); on green it fast-forwards `main` to that commit, on red it removes the PR
   and comments. `gh pr merge <N> --disable-auto` leaves the queue.
4. Integration failures appear only in the queue; merge `main` into a PR branch before
   queueing when `main` moved under it substantially.

### Reuse in the merge queue

Design change (2026-10-12; the user had approved input-hash reuse and asked for faster CI at
the same quality; "the queue never reuses" was this document's own rule): a `merge_group` run
reuses like a PR run, but only records of `merge_group` or `workflow_dispatch` runs whose
commit is on `main`, and only through the restricted-checkout key, which does not rely on
observing what a part reads. Before, docs-only PR #149 took 29.5 min in the queue (`merge_group`
run 38220406483, 07:54-08:24Z 2026-10-12, 286 runner-minutes): all 35 jobs executed, the longest
`mutation/3` 18.1, macOS 0.15.2 20.2, `audit` 17.0, `receipt` 16.4 min. With this design such
a change keeps the key of every reusable part except `test/0.16.0/inputs` and
`test/0.16.0/receipt`, which read the documentation (see "Current declarations"); `generated`, `provenance` (`"reuse": false`: their
artifacts are this commit's `generated` branch entry) and the support jobs run too. The measured round is in "After the
restricted checkout" below.

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
- Every root-package Lake cache key (`lake-root-*`) contains
  `hashFiles('.github/workflows/ci-cache.yml')` after the toolchain hash: the recipe that built
  the entry (which targets) is part of the key, so an entry saved by an older recipe is never a
  hit for a newer one. `restore-keys` prefer the newest entry of the same recipe and fall back to
  any recipe as a warm start (Lake's content traces rebuild what differs). The hash covers the
  whole file, so any edit of `ci-cache.yml` costs one rebuild of these entries on `main`. The
  `tests/diff` package entries keep their toolchain-only keys (one recipe: `lake build`). Before, the macOS
  entry built by the old workflow without `Proofs` kept its key, `ci-cache.yml` skipped the
  build, and every macOS row rebuilt `Proofs`.
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

- Narrowed to top-level directories (from the syscall traces of run 38187552806 under the
  former tracer, then coarsened so that a new file in an already-read directory needs no
  declaration change): the three build-mode rows and the five mutation shards (`Air2Lean`,
  `Proofs`, `ZigLean`, `assurance`, `examples`, `scripts`, `tests`, `zig-patch` and the Lake
  files), the lean rows of 0.14.1 (the same without `examples`), 0.15.2 and 0.17.0 (plus
  `case-studies`, `tutorials` and `docs/allocation-policy-report.json`, the one file under
  `docs/` they read). `aarch64-linux`, `bitops-native-arm` and `build-modes-aarch64-linux` from
  the traces of runs 38166335511 and 38173731089.
- Every tracked file except the prose documentation (`docs/**`, top-level `*.md`), plus the
  documentation files their gates are known to read (`docs/allocation-policy-report.json`;
  `README.md` for the host-accounting claims of the golden rows; `docs/premises.md` for
  `audit`): the 0.16.0 `golden`, `lean`, `native` and `audit` parts,
  the golden rows of 0.14.1, 0.15.2 and 0.17.0, and the macOS rows. They were commit-bound (their
  gates read `HEAD`) or `"reuse": false` (`audit`: under the former tracer it exceeded the job
  limit); in the restricted checkout `HEAD` is a function of the key. Conservative: a gate that
  reads another documentation file fails red and the file is added; narrowing further is a
  follow-up.
- The whole tree: `test/0.16.0/inputs` and `test/0.16.0/receipt`. The support-matrix,
  build-mode-record and host-accounting gates of `inputs` read `README.md`, `PLAN.md`,
  `ROADMAP.md` and every `docs/*.md`; the proof receipt fingerprints every tracked file (run
  38235990118 failed red on the withheld `CLAUDE.md`). So a documentation change executes both
  (about 11-16 min); moving the documentation gates into a small part, and binding the receipt
  to the restricted HEAD, are the next steps for a docs-only round of a few minutes.
- `"reuse": false` (always run, whole checkout): `generated` and `provenance`. Their artifacts
  are published as this commit's `generated` branch entry, which binds the commit and its tree
  (docs/ci.md#whole-tree-generated-files): a result passed by reference to another commit's run
  has no such artifacts. `provenance` also builds the receipt that binds the tested revision.

## Rollout order

1. This document (first commit).
2. Cache hygiene and build-ahead: `ci-cache.yml`, restore-only rows, `lake`/`zig-air` artifacts,
   per-version compiler keys, cleanup. Measurable on its own.
3. macOS: warm `Proofs` in the macOS cache.
4. Merge queue triggers, PR-head checkout, `release-record`/`target-matrix` evidence rules.
5. Reuse with a syscall tracer (PR #141-#153), replaced by the restricted checkout (PR "CI:
   restricted checkout"): reuse in PR and queue runs, nightly full run, release records by
   reference.
6. After merge: ruleset with `all-checks` and the merge queue (`gh api`), verified with a test PR.

## Expected savings

- Merges: one full run per merge (queue) instead of one per PR push plus one per `main` push.
- PR pushes: parts whose inputs a push does not touch are free. Lean sources are inputs of every
  Linux row (each consumes the `lake` build), so Lean changes still re-run most rows; tooling,
  test, documentation and assurance-record changes re-run only the rows that read them.
- macOS rows: about 8-10 min instead of 13-19 min (proof build incremental from `main`).
- Cache: about 1.5 GB of `main` entries instead of 10.9 GB, so no `main` miss through eviction.
- The measured before/after (wall time, runner minutes, queue time) is in the PR description.
