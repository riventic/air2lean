# Release record (Q08)

`scripts/release-record.py` publishes the release gates of one exact revision with their
evidence, the checks that could not run and the review ledger's reviewed revisions. It never
builds, runs CI or uses the network; evidence is collected separately and passed in.

```sh
python3 scripts/release-record.py plan                    # gates per CI job and the reproduction command
gh run view RUN_ID --json databaseId,headSha,headBranch,conclusion,status,event,workflowName,url,jobs > run.json
python3 scripts/release-record.py record --github-run run.json \
  [--local-ci .lake/local-ci-results/run.XXXXXX] \
  [--unavailable 'JOB[::STEP]=REASON'] --out release-record.json
python3 scripts/release-record.py verify release-record.json
python3 scripts/release-record.py ledger
```

## Source and profile

`record` requires a clean checkout (no tracked changes, no untracked files) and binds to `HEAD`.
The profile is read from Git objects at that revision: the `.github/workflows/ci.yml` matrix
(one job per row, named as GitHub names matrix jobs), the blob ids of the workflow,
`scripts/local-ci-steps.py` and `compatibility.json`, and the translation target. A gate is a
`run:` step whose `if:` holds for the row, evaluated with the local runner's own `expression()`.
Actions and the tool-setup recipes that `scripts/local-ci.sh` substitutes are not gates.
Unsupported workflow syntax or conditions fail instead of guessing. Each job records its
reproduction command (`scripts/local-ci.sh full VERSION` or `scripts/local-ci.sh mutations`),
and `commands` keeps each gate's exact `run`, `env` and `if` text.

The matrix-free `macos` job (Q05, [target-matrix.md](target-matrix.md)) is one more job named
`macos`, with `matrix: null`. Its gates are its `run:` steps except tool setup that depends on
another step's cache output; any other condition fails the plan. Its commands are keyed
`macos::STEP`. Local CI runs in a Linux container and never covers it, so its gates need GitHub
Actions evidence or an `--unavailable macos=REASON` declaration.

## Evidence

A gate is `passed` only with evidence for the recorded commit:

- GitHub Actions run JSON: `headSha` must equal the revision, the run must be completed and
  come from the same workflow name, and every job must be a matrix row at that revision.
  The run's event must be `push` or `workflow_dispatch`. A `pull_request` run tests a merge
  with the base branch, not the head commit, so it is rejected.
  A step that ran even though its condition is false at the revision rejects the run, because
  it came from another workflow. Only step conclusion `success` passes; `skipped`, `failure`
  and `cancelled` fail a required gate.
- `scripts/local-ci.sh` results directory: the script writes `source-revision` (HEAD, whether
  tracked files were clean, mode, version) and `exit-status` next to `container.log`. The
  revision must match and the tracked tree must be clean. Step headers must follow the
  workflow order for rows of that mode. With exit status 0 every gate of those rows must
  have started. A nonzero run fails the last started step. Targeted runs are not gate
  evidence.

When evidence disagrees, the gate fails. A gate with no evidence is `missing`, which leaves
the record `incomplete` (exit 1). `--unavailable JOB=REASON` (every evidence-free gate of
the job) or `JOB::STEP=REASON` marks a check as explicitly unavailable, and the reason is
published. A step-level declaration for a gate that has evidence is an error, and no
declaration hides a failure. The record is `complete` when no gate is failed or missing.

`verify` recomputes the gate list from the record's revision. It rejects missing or extra
gates, `passed`/`failed` without cited evidence, cited evidence for another revision or
job, unavailable gates without a reason, and summary or status drift.

## Review ledger

`REVIEW_COVERAGE.tsv` has a `reviewed_revision` column. `ledger` fails when an entry lacks
a full commit id, when the path is absent at that commit, or when the stored baseline SHA-256
differs from the file content at that commit. Unfetched revisions fail unless
`--allow-unfetched` is passed, which reduces the check to structure. CI fetches the listed
revisions into its shallow checkout first. Local CI snapshots have no history and check
structure only. The record's `review` section lists the reviewed revisions,
`changed_since_review` (ledger paths whose content differs at the release revision) and
`not_in_ledger` (tracked paths without a ledger entry) as known exclusions.

## Limits

The record covers the CI workflow's `test` and `macos` jobs only; any other job fails the
plan. It does not re-check the evidence files' content during `verify`; their SHA-256 values
are stored for comparison.
Local CI evidence relies on the step headers that `scripts/local-ci-steps.py` prints.
