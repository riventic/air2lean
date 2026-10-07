# Schedule exploration coverage and caps (Q03)

`scripts/diff-report.py compare` adds a `schedule_exploration` block to the schema-1 summary and prints one `SCHEDULES:` headline line. The block keeps two kinds of evidence apart:

| Counter group | Source | Meaning |
| --- | --- | --- |
| `observed_matching` | per-case `search` metadata from the differential runner | FIFO/DFS search that stops at the first execution whose result matches the native one. Reports searched and unsearched cases, `schedules_explored` (sum of `runs`), `max_runs`, status counts (`witness`, `exhausted`, `bounded`, `capped`), no-result branches, replayable witnesses, and the distinct `fuel` and `cap` values used. |
| `bounded_enumeration` | `scripts/schedules.py` receipts passed with `--schedule-receipts` (or `AIR2LEAN_SCHEDULE_RECEIPTS` in `scripts/diff.sh`) | DFS enumeration that does not stop at a match. Reports receipts, `schedules_explored`, complete/truncated runs, node-cap and prefix-cap hits, no-result branches, replay seeds (complete traces), verified replays, and the distinct `fuel`, `node_cap` and `prefix_cap` values used. |

`enumeration_receipts` gives each receipt's path, SHA-256, input index, limits, flags, distinct outcome count and `replay_seed_indices`. Any listed index can be replayed with `scripts/schedules.py replay --receipt <path> --execution-index <i>`. Before a receipt is counted, it is validated with the `schedules.py` checks against the current runner/runtime source fingerprints and input row. The report rejects stale, inconsistent or duplicate receipts, and receipts for examples outside the selection. Replay receipts count under `replays`, not as enumeration coverage.

## Caps never count as correspondence

- A case whose search status is `capped` cannot be a match. If the model value or panic would otherwise agree, the typed status becomes `search_cap` and the legacy bucket becomes `capped`. The case is therefore excluded from `exact_matches` and checked against `capped.txt` pins. Every capped case is listed in `capped_cases`, with its runs, cap and fuel.
- A `capped` search must have consumed its whole run cap (`runs == cap`). Other cap metadata is rejected as a setup failure.
- `scopes` has one entry per example/function. A scope is `capped` if any of its observed searches was capped or any of its enumeration receipts was truncated. `counts_as_correspondence` is true only when the scope has no blockers: every case is an exact match, no search is capped, no enumeration is truncated and no no-result branch was seen. If a scope is both `capped` and counted as correspondence, the report fails. `qualified` is always `false`, and every scope lists `proof_applicability_not_evaluated`.
- The headline reports `correspondence_scopes` and `capped_scopes` separately.

All exploration is fuel-bounded. `exhausted` and `exploration_complete` refer only to the fuel-bounded oracle tree. They establish neither all-schedule nor fuel-independent correspondence.

## Reduction

The report has `reduction: {technique: none, soundness: not_proved}`. Every counted schedule was executed. No partial-order, sleep-set or symmetry reduction is used. Proofs that such reductions are sound remain out of scope as research work. Until such a proof exists, no reduction can shrink the reported coverage.

## Validation

```sh
python3 tests/roadmap/schedule-caps/test_exploration.py
```

The test uses synthetic reports and receipts, mocks the model process and needs no compiler. Its positive controls cover witnesses, complete enumeration, replays and the CLI headline. Its negative controls cover capped value and panic matches, mixed scopes with a capped case, truncated enumeration, bounded no-result branches, inconsistent cap runs, and stale, foreign or inconsistent receipts.
