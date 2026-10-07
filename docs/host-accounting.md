# Host and skipped-case accounting

`scripts/accounting.py` publishes one table covering every differential summary
(`scripts/diff-report.py`, [outcome accounting](outcome-accounting.md)), with one row for each
Zig version and host target. It also checks the README's legacy-version claims against the CI
matrix and against the runs. It starts no compiler, Lake or Lean process.

```sh
python3 scripts/accounting.py publish --summary 0.16.0/report.json --summary 0.15.2/report.json \
  --json accounting.json --markdown accounting.md
python3 scripts/accounting.py check --json accounting.json --summary 0.16.0/report.json --summary 0.15.2/report.json
python3 scripts/accounting.py claims --summary 0.16.0/report.json --summary 0.15.2/report.json --require-full-versions
python3 tests/roadmap/host-accounting/test_accounting.py
```

## Columns

Each summary status falls into exactly one partition column, and the partition columns of a row
add up to its `cases`:

| Column | Summary statuses |
| --- | --- |
| `exact_matches` | `value_match`, `error_return_match`, `panic_match` |
| `host_differences` | `host_difference` |
| `illegal` / `unspecified` | `illegal_exclusion` / `unspecified_exclusion` |
| `capped_searches` | `search_cap` (including any capped search that would otherwise have matched) |
| `bounded_no_result` | `bounded_no_result` |
| `mismatches` | `mismatch` |
| `setup_failures` | `input_failure`, `native_harness_failure` |

`skipped_examples`, `skipped_functions` and `proof_exclusions` are listed beside the partition.
They are not cases. `proof_exclusions` counts the selected examples whose proof applicability the
differential runner did not evaluate, which today is every selected example. The headline
`successful_comparisons` is the `exact_matches` total and nothing else. The table always records
`qualified: false`.

## Failures

`publish` and `check` exit 1 when any of these hold:

- a summary is incomplete, records `qualified` other than false, has an unknown status,
  has counts that do not sum to `case_count`, or has an `exact_matches` value that differs
  from its exact-match status total (so it would count excluded cases as successes);
- a summary claims evaluated proof applicability, or has missing or duplicate proof exclusions;
- two summaries share the same version/target;
- (`check` only) a row does not partition its cases, a total is not the sum of its rows, the
  headline is not the exact-match total, or the published table differs from the table
  regenerated from its summaries.

`claims` exits 1 in any of these cases:

- README's supported versions differ from the CI matrix versions;
- a README "full job ... diff test" row has no full CI job;
- a "restricted job ... no diff harness" row is not a restricted CI job, or its example list
  differs from CI's explicit list;
- the README sentence saying a restricted row skips the differential harness names a version
  whose row says otherwise;
- in README's headline report sentence, the exact, illegal and unspecified counts do not add
  up to the cases;
- a summary exists for a version README marks as having no diff harness;
- a run selected examples other than README's list for its version (`asm` is omitted when the
  target is not x86_64);
- skipped examples do not account for the unselected ones;
- with `--require-full-versions`, a full-diff version has no summary.

A focused `AIR2LEAN_EXAMPLES` run therefore cannot serve as evidence for a version claim.

## CI

Full jobs (0.16.0 and 0.15.2) publish, check and claim-check their own summary after the
differential gate and append the table to the job summary. They upload
`tests/diff/out/report.json` as the artifact `diff-summary-<zig>-<os>-<arch>`, even when the
gate fails, in which case the summary is incomplete and `publish` rejects it. The restricted
0.14.1 job runs no diff harness and uploads no summary. To publish the cross-version table for
a run:

```sh
gh run download <run-id> --pattern 'diff-summary-*' --dir summaries
python3 scripts/accounting.py publish $(printf -- '--summary %s ' summaries/*/report.json) \
  --json accounting.json --markdown accounting.md
python3 scripts/accounting.py claims $(printf -- '--summary %s ' summaries/*/report.json) --require-full-versions
```

Only Linux x86_64 full jobs exist today, so the table has one target per version. Cross-target
rows wait on Q05.
