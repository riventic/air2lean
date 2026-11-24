# Mutation map (Q02)

`assurance/mutation-map.json` maps every [ROADMAP.md](../ROADMAP.md) register ID to the
negative tests and designated semantic mutants that show the feature's wrong behaviour is
detected. A feature cannot close on positive examples alone: a `complete` row needs at least
one negative test, at least one designated mutant, and a mutant for every category it declares.

## Entries

```json
"T01": {
  "categories": ["profile-selection"],
  "negative_tests": [{"path": "tests/roadmap/profiles/test_golden_pipeline.py",
                      "anchor": "def test_unknown_profile_name_is_rejected"}],
  "mutants": [{"name": "profile-name-unchecked", "category": "profile-selection",
               "path": "tests/roadmap/mutation-map/mutants.py"}],
  "note": "optional"
}
```

- `categories`: the mutant categories this requirement is sensitive to. Each one needs a
  mapped mutant of that category; a missing one fails a `complete` row and is reported as a gap
  for any other row.
- `negative_tests`: a repository file and a literal anchor inside it (a test definition, a
  rejected-input assertion or an expected error message).
- `mutants`: one category each, from `forwarding`, `layout`, `operand-order`,
  `failure-cleanup`, `profile-selection`, `invariant-transfer`, or `other`. A mutant must exist:
  - `scripts/mutate.sh`: the name is a mutation label (`echo "== mutation (m)"`) that is also
    listed in `scripts/mutation-shards.txt`;
  - `tests/roadmap/mutation-map/mutants.py`: the name is a key of its `MUTANTS`;
  - any other file: the name is a quoted string literal in it, or, for an inline mutant without
    a name (for example the tuple-order rewrite in `tests/roadmap/thread-tuples/check.sh`), the
    entry's `anchor` is the mutated text.

## Checker

```sh
python3 scripts/mutation-map.py check          # exit 0 ok, 1 problems, 2 unreadable inputs
python3 scripts/mutation-map.py check --json   # problems, per-category mutants, gaps
```

`check` fails when the map's IDs differ from the register, a reference is missing, a `complete`
row lacks evidence, a `scripts/mutate.sh` or `mutants.py` mutation is mapped to no ID, or one of
the six categories has no mutant anywhere. It prints the mutants per category and one `gap` line
per incomplete row that lacks negative tests, mutants or a declared category. Classification
comes from ROADMAP.md, so promoting a row to `complete` fails until its evidence is mapped. Every
designated mutant outside `mutants.py` must also have a recorded kill (below); a `complete` row
may not rely on a mutant whose kill is `unrecorded`.

## Python-side mutants

`tests/roadmap/mutation-map/mutants.py` holds mutants for checks that are Python code: profile
and schema selection (`scripts/normalize-generated.py`), float-semantics selection
(`scripts/float-semantics.py`), release host metadata (`scripts/compat.py`), transfer of trust
violations through theorem dependencies (`scripts/assumptions.py`), the ROADMAP header check
(`scripts/support-matrix.py`), unclassified and stale-override inventory rows and rejected std
model table rows (`scripts/coverage.py`), non-standard evidence axioms in the external
contract report (`scripts/external-contracts.py`), stale check results and over-broad schedule
claims in the theorem inventory (`scripts/theorem-inventory.py`), probe profiles of another
optimize mode (`scripts/build-modes.py`), automation limits classified as counterexamples
(`scripts/counterexample.py`), evidence from a CI job on another host
(`scripts/target-matrix.py`), hidden compiled-mode source gaps and unmapped runtime modules
(`scripts/premises.py`), and pull-request runs, masked failures and ledger entries without a
reviewed revision in release records (`scripts/release-record.py`), untyped
host differences and unpinned model exclusions in differential accounting (`scripts/diff-report.py`),
and a dropped asm fault-condition premise (`scripts/claims.py`), the perf-budget gate
(`scripts/perf-budgets.py`), safe publication (`scripts/safe-output.py`), upgrade qualification records
(`scripts/qualify-upgrade.py`), schedule-cap accounting (`scripts/diff-report.py`), the AIR validator
and trust report (`scripts/validate-air.py`, `scripts/trust-report.py`), the ABI probe
(`scripts/abi-probe.py`) and the Q01 generator's type checker and evaluator
(`tests/roadmap/fuzz/zig_gen.py`). Each one replaces one exact anchor, compiles the result under the
script's own path, swaps it into the loaded regression test module and runs only the named
killing tests. The control (unmutated) must pass those tests. The mutant is killed only by an
assertion failure. A test error such as a crash does not count.

```sh
python3 -B tests/roadmap/mutation-map/mutants.py           # all; exit 1 if any survives
python3 -B tests/roadmap/mutation-map/mutants.py --list
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/mutation-map/test_mutation_map.py
```

All three run in CI ("Mutation map and Python-side mutants"). The other Lean/Zig mutants the
map names (`tests/roadmap/*/check.sh`, `mutations.py`) stay in their own gates, which report
their kills to the ledger below.

## Kill evidence

`assurance/mutation-kills.json` records, for each `scripts/mutate.sh` mutation and each
designated fixture mutant, the regression that killed it: `{"kind": "diff", "target":
"<example>"}` (the differential test of that example reported a mismatch or an eligible count
change), `{"kind": "proof", "target": "<module>"}` (`lake build <module>` failed with a Lean
error, possibly in a dependency such as `ZigLean.Conc.Lemmas`), or `{"kind": "check", "target":
"<path>"}` (a `tests/` or `scripts/` file that a `.github/workflows/*.yml` step names, so a
hyphenated fixture such as `tests/roadmap/big-endian/check.sh` can be the killer), plus
`block_sha256`. A `mutate.sh` mutation's key is its label and its hash covers the mutation's text
in `mutate.sh`; a fixture mutant's key is `<path>#<name>` (the map entry's path and name) and its
hash covers the whole file at `path`. `check` fails when a designated mutant has no recorded
kill, the killing example, module or check does not exist (or the check is run by no workflow),
the hash differs (the mutant's file was edited after its kill was recorded), or the ledger names
a mutant that is no longer designated. A survivor can never be recorded. A mutant no CI check
runs may carry `{"unrecorded": reason, block_sha256}` (for example the patch-only
`tests/roadmap/resize-remap/mutations.py`): `check` lists it as a gap, and a `complete` row
relying on it fails.

Fixture runners report a kill only after their own classification: `scripts/mutation_kill_log.py`
(`killed(path, names, check)` from Python, or `python3 -B scripts/mutation_kill_log.py --check
CHECK MUTANT_FILE NAME...` after a check that must reject the mutants, for example a Lean file of
`fail_if_success` mutants) appends `<path>#<name> killed check <check>` to
`AIR2LEAN_MUTATION_KILL_LOG` and does nothing when it is unset.

```sh
AIR2LEAN_MUTATION_KILL_LOG=kills.log scripts/mutate.sh        # also per shard (heavy)
python3 scripts/mutation-map.py kills record --log kills.log  # merge killed mutations into the ledger
python3 scripts/mutation-map.py kills verify --log kills.log  # fail unless each was killed by the recorded regression
```

`mutate.sh` appends one line per mutation it runs (`<label> killed|survived diff|proof <target>`);
running a fixture's CI check with the variable set appends its fixture kills the same way.
`record` refuses a log with a survivor; the CI mutation shards run `verify` on their own log, so a
mutant that survives or is killed by something else than the recorded regression fails the job.
`mutate.sh` aborts as a setup failure, never reporting "killed" or "survived", when a mutation
changed none of the sources it may edit. Differential kills of host-dependent functions
(`tests/diff/<ex>/host.txt`, e.g. `floatops` for mutation (d)) count only on the reference host
(Linux x86_64); on another host their mismatches are host differences. The (d) and (i) kills were
recorded in the `linux/amd64` local-ci container (emulated on Apple silicon).
The ledger is evidence of what was run when it was recorded; it is not rechecked offline
beyond the block hash, so a change to the mutated Lean source alone is caught by the CI shards, not by `check`.

## Scope

Coverage is per register ID and category, not per pipeline stage. Most incomplete rows still
list gaps (`check` prints them). `other` mutants count as designated mutants but cover no
category.
