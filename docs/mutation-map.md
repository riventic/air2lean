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
comes from ROADMAP.md, so promoting a row to `complete` fails until its evidence is mapped. The
checker reads text only; it does not show that a mutant is killed.

## Python-side mutants

`tests/roadmap/mutation-map/mutants.py` holds mutants for checks that are Python code: profile
and schema selection (`scripts/normalize-generated.py`), float-semantics selection
(`scripts/float-semantics.py`), release host metadata (`scripts/compat.py`), transfer of trust
violations through theorem dependencies (`scripts/assumptions.py`), the ROADMAP header check
(`scripts/support-matrix.py`), unclassified and stale-override inventory rows and rejected std
model table rows (`scripts/coverage.py`), and non-standard evidence axioms in the external
contract report (`scripts/external-contracts.py`). Each one replaces one exact anchor, compiles the result under the
script's own path, swaps it into the loaded regression test module and runs only the named
killing tests. The control (unmutated) must pass those tests. The mutant is killed only by an
assertion failure. A test error such as a crash does not count.

```sh
python3 -B tests/roadmap/mutation-map/mutants.py           # all; exit 1 if any survives
python3 -B tests/roadmap/mutation-map/mutants.py --list
PYTHONDONTWRITEBYTECODE=1 python3 tests/roadmap/mutation-map/test_mutation_map.py
```

All three run in CI ("Mutation map and Python-side mutants"). The Lean/Zig mutants the map
names stay in their own gates (`scripts/mutate.sh` shards, `tests/roadmap/*/check.sh` and
`mutations.py`). The map records that they exist and what they target. Their kills are shown by
those gates.

## Scope

Coverage is per register ID and category, not per pipeline stage. Most incomplete rows still
list gaps (`check` prints them). `other` mutants count as designated mutants but cover no
category.
