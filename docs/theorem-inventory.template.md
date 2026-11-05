# Theorem inventory

[`assurance/theorem-list.json`](../assurance/theorem-list.json) (committed, hand-written) lists the headline
theorems of `Proofs/` (the [proved examples](proofs.md#proved-examples), the
[vector proofs](vector-proofs.md), the `floatops` selector theorems, the C14 RwLock client and
its rules, the C14 contract clients, and the single-schedule and single-step facts) with:

- the Lean name and module, and the example whose translation the module imports;
- a scope class (below) and the precise domain of the statement;
- the check result for each translation of that example.

## Scope classes

| Scope | Meaning |
|---|---|
| `sequential` | one thread (no `ConcM`): a `Triple` or `*_run` lemma with `Mem.Seq`, or a pure function equation |
| `single-step` | one operation or one step of a concurrent program (a `WP` rule or a step fact); a program theorem uses it, it is not one |
| `single-schedule` | one concrete oracle and fuel of `Sched.run`, computed by the kernel |
| `bounded-schedules` | a finite, enumerated set of schedules or a bounded fuel/oracle domain (no listed theorem has it; the differential schedule search of `tests/diff` is a test, not a theorem) |
| `all-schedules` | every fuel and every oracle of `Sched.run`: the statement binds both. Partial correctness or strict safety in the model; no termination or fairness |

Only an `all-schedules` theorem can be said to hold "under every schedule". The checker
rejects that phrase next to a narrower theorem in README.md, PLAN.md, docs/proofs.md,
docs/vector-proofs.md, docs/rwlock-contracts.md, docs/std-models.md and in the doc comment of
a listed theorem. It also rejects an `all-schedules` scope whose statement does not quantify
`Sched.run` over a bound `fuel : Nat` and `o : Nat → Nat`.

An `all-schedules` theorem allows runs that never complete (out of fuel), so a protocol that
spins forever satisfies it. Its entry may name a `completes` witness: a listed
`single-schedule` or `bounded-schedules` theorem of the same example whose statement shows a
`Sched.run` of the same program with a successful result (`= some ...`), so at least one
schedule completes within its fuel. The table labels an `all-schedules` theorem without one
`all-schedules (no run shown to complete)`: correctness if a run completes, or safety only.

## Translations and check results

A theorem must hold for the translation of every Zig version its example supports
(`examples/<ex>/zig-versions`, else every version of `compatibility.json`) and every target
with its own translation. As in `scripts/check.sh`, the translation file is
`tests/golden/<version>/<ex>/Gen-<os>.lean`, else `tests/golden/<version>/<ex>/Gen.lean`, else
the committed `Proofs/<Ex>/Gen.lean`. Each available target-specific golden adds a
required translation.

A check result is an index of a supported explicit-module build under
`scripts/build-guard.py`, in the trusted local recorder/runtime context. The recorder
selects Lake through the pinned `lean-toolchain`, resolves that entry physically, and
checks its current bytes against the guard's producer capture and pin. A nested
`swap-build` executes that same binary and requires its explicit `--tool` capture.
The saved physical path, hash and byte count identify the captured producer; command
spelling or a basename alone is insufficient. Existing records without that capture
are stale and need a genuine fresh build, never inferred or relabelled identity.

Offline checking validates historical producer structure and the retained command/pin
binding without opening another host's old physical path. Renewal reconstructs the
supported command using this host's selected Lake; it never executes a saved foreign
producer. A recorded `--no-build` check can be current, but fresh renewal removes
that rebuild-suppressing flag so changed sources are actually rebuilt. This guard
index does not replace the existing proof-receipt seal/verify
path or change its `NOT_ATTESTED` native/source-correspondence boundaries.

Each theorem result checks the `Proofs` dependencies returned by the existing shared
import-discovery API. Complete header parsing, path enrollment and compiled import
coverage remain separate obligations. A swap keeps the canonical module identity
while discovery reads its selected translation, including that translation's imports.
Body validity belongs to the compiler. The
exact canonical `Proofs.<Example>.Gen` alone owns a short example key; every deeper
`*.Gen` or profile-bearing retained translation has its full module key/path/hash.
The recorded canonical path must agree with the last normalized swap declared by
the command. Missing, foreign or incomplete evidence is stale. Alias normalization
preserves supported mixed-case examples and `./` paths; absolute/parent-escape swap
paths, whitespace/NUL source spellings and malformed example identifiers are refused.

An edit to a dependency or selected translation makes a theorem result stale. An
unrelated generated module that the theorem does not import does not invalidate that
theorem, but whole-invocation renewal checks every recorded entry and the complete
module membership. A change in `ZigLean/` does not make this index current by itself;
the actual proof/compiler gates remain separate obligations.

## Generated, not committed

`assurance/theorem-inventory.json` (the list plus the recorded check runs) and this document
(this template with the table filled in) are whole-tree generated files
([ci.md](ci.md#whole-tree-generated-files), group `theorem-inventory`): the runs depend on every
`Proofs` source and translation, so they go stale whenever main moves. They are never
committed. `scripts/generated.py materialize` (or `fetch --group theorem-inventory`) puts the
copy CI published into a checkout; `scripts/generated.py regen --group theorem-inventory`
(`scripts/regen.sh --only inventory`) rebuilds the runs that are stale. `check` fails closed
when the file is missing or was generated from another list. `check --list` checks the list
alone (every theorem exists, scopes, claims, tables) and needs no generated file.

The runs are planned from the list (`plan` in `scripts/theorem-inventory.py`): one `lake build`
of every theorem module over the committed translations (run `committed`), and one `swap-build`
per Zig version and target over the other translations (run `<version>-<target>`). The recipe
below is what `regen` does for each planned run:

```sh
lake=$(ELAN_TOOLCHAIN="$(cat lean-toolchain)" elan which lake)
lake=$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve(strict=True))' "$lake")
python3 scripts/build-guard.py --cwd "$PWD" --report /tmp/r.json --log /tmp/r.log \
  --timeout 7200 --rss-mib 12000 --lock-wait 21600 --log-bytes 8388608 --tool "$lake" -- \
  python3 scripts/theorem-inventory.py swap-build --lake "$lake" \
    --swap lists=tests/golden/0.15.2/lists/Gen.lean -- Proofs.Lists.Append
python3 scripts/theorem-inventory.py record --run 0.15.2-linux-lists --zig 0.15.2 \
  --guard-report /tmp/r.json --guard-log /tmp/r.log
python3 scripts/theorem-inventory.py write
```

`swap-build` builds in a check tree (`.lake/check-tree/theorem-inventory`, a copy of the
checkout with each translation in place of `Proofs/<Ex>/Gen.lean`;
[generated-code.md](generated-code.md#check-trees)), so the committed files are never written. `record` checks the log against the report, refuses a translation
file that `scripts/gen-integrity.py attest` does not find to be a fresh translation of its
committed AIR (so it needs the built translator), and stores the outcome, revision and hashes. `check` (CI, offline) needs no Lean.

The index retains a guarded build outcome and its current dependency identities.
Compiled/kernel claims use the existing [assumption audit](assumptions-audit.md) and
[proof receipt](proof-receipts.md) mechanisms at their stated scope. The indexed
translation files remain committed goldens; this is not a fresh Zig export.

## Remaining scope

- F05 (complete): `op128_spec` still excludes the `f128` selectors 3, 5, 6 and 9 (`/`,
  `@divTrunc`, `@divFloor`, `@sqrt`), which call a different model function per Zig version;
  its domain says so. `op128_spec_full` covers every selector with each translation's helpers
  ([floats.md](floats.md) §Per-version differences).
- C14: `snapshotPair_spec`/`snapshotPair_safe` hold for the restricted protocol of
  `Proofs/Sync/RwLockContract.lean` (one fixed client: main reader, one writer, writer count
  at most 2). `cache_spec`/`cache_safe` and `mailbox_spec`/`mailbox_safe` are Lean model
  clients proved only against the full-state contracts `MutexImpl`/`SemImpl`, for every
  implementation; they have no Zig source or native/model differential. There is
  no reusable RwLock contract for arbitrary readers or resources, no Event/WaitGroup contract,
  and no fairness or native adequacy claim ([rwlock-contracts.md](rwlock-contracts.md)).

## Inventory

<!-- BEGIN theorem-inventory -->
<!-- END theorem-inventory -->
