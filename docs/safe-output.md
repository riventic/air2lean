# Safe output and execution controls

Generated artifacts are written to a staging location, then published by one atomic
filesystem operation. A failed, interrupted or timed-out run leaves each previously
published artifact byte-identical. It never leaves a prefix of a new file at the
published path.

## Publication

`scripts/safe-output.py publish (--overwrite | --no-clobber) STAGED DEST` copies the
staged file into a hidden temporary file beside `DEST` (`.NAME.*.partial`), fsyncs it,
then renames it over `DEST` (`--overwrite`) or hard-links it (`--no-clobber`). The link
fails if `DEST` exists, including a `DEST` created by a concurrent writer. The directory
is fsynced afterwards. The overwrite policy is required: an omitted flag is a usage
error. Symlink, directory and non-regular destinations are refused. An existing
destination's mode is kept.

| Writer | Artifact | Policy |
| --- | --- | --- |
| `scripts/translate.sh` | `-o OUTPUT.lean` after Lean elaboration | `--overwrite` (default) or `--no-clobber` |
| `scripts/check.sh` | `Proofs/<Ex>/Gen.lean`, check report `<ex>.json` and `<ex>.Gen.lean`, `AIR2LEAN_OUT_DIR` copies | overwrite (a rerun replaces its own output) |
| `scripts/proof-receipt.py` | `plan.json`, `before.json`, `after.json`, `receipt.json` | no-clobber (`os.link`); a sealed receipt is never replaced |
| `scripts/assumptions.py` | audit report (`--output`) | overwrite, fsynced; failure writes an error report |
| `scripts/project.py` | report / artifact directory | see [project-workflow.md](project-workflow.md) |

`translate.sh --no-clobber` refuses an existing output before running any stage. It
also refuses at publication time if the output appears during the run.
`check.sh` writes `Proofs/<Ex>/Gen.lean` before `lake build` checks it. This tracked
source is replaced atomically, but it is the input to the check, not a verified
artifact. The build and the proof-receipt flow establish verification.

## Bounded stages and cancellation

`scripts/safe-output.py run [--timeout S] [--grace S] -- COMMAND...` starts the command
in a new session/process group. `workflow_run_stage` in `scripts/workflow-common.sh`
starts it in the background and waits, so a trapped signal interrupts the shell at
once. Without this, bash would defer the trap until the foreground child exited.

- Timeout: TERM to the whole group, KILL after the grace period (default 2s). Exit 124.
- SIGINT/SIGTERM/SIGHUP to the shell script: its trap sends TERM to the runner. The
  runner stops the group in the same way and waits for it, and the script exits
  130/143/129. Only then does the `EXIT` cleanup remove staging directories and the
  translate lock, so no stopped stage can still be writing into them.
- A command that exits while members of its group remain (for example, a translator
  that leaves a background helper) fails with exit 125. The helpers are killed and
  nothing is published.

The per-stage timeout is `--timeout SECONDS` or `AIR2LEAN_STAGE_TIMEOUT`. The default
is 3600, and 0 disables the limit. `translate.sh` bounds the Lean build, the AIR export,
translation and the Lean check. `check.sh` bounds the AIR dump and translation. Its
final `lake build` and differential tests remain bounded by the CI job timeout or an
outer `scripts/build-guard.py` ([build-budgets.md](build-budgets.md)).
`proof-receipt.py worker` runs the auditor in its own group. SIGINT/SIGTERM/SIGHUP, an
exception, or an auditor exiting with live children stops that group, and no
`after.json`/receipt is written. The outer guard owns its timeout.

Input size and depth bounds are documented in [input-validation.md](input-validation.md)
and enforced by `project.py` and `proof-receipt.py`.

## Limits

- SIGKILL of the script itself cannot run cleanup. A hidden `.air2lean-output.*`
  staging directory or `.partial` temporary file may remain beside the output. The
  published path still holds the previous complete file.
  `translate.sh` also leaves its empty lock directory, which must be removed by hand.
- A process that calls `setsid` or otherwise leaves the stage's process group is outside
  the runner's control. `scripts/build-guard.py` tracks such descendants with `ps`
  sampling.
- After the leader is reaped, the group is probed by its ID. In the brief window
  after the group empties, an unrelated new group could reuse that ID. The runner sends
  KILL once, while the last probe still saw members, and afterwards only probes, so a
  reused ID can delay its exit by the grace period but is not signalled.

## Tests

`tests/roadmap/safe-output/test_safe_output.py` drives the real `translate.sh`,
`check.sh`, runner and receipt writer with stub `elan`/`zig`/`lake`/`air2lean` tools.
It covers interrupts mid-write (SIGINT/SIGTERM/SIGHUP), a failing translator after a
partial write, a translator child that ignores SIGTERM, timeouts, leftover child
processes, an interrupted Lean check, and the overwrite policy. Each case asserts
that the prior artifact is unchanged, no partial file is published, staging and lock
are cleaned, and every recorded stage process is gone.
