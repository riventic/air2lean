# Project diagnostic checks

`project-diagnostics.py` is a separate check-only consumer of the typed translator
protocol. Existing `project.py report`, `translate` and `verify` commands are unchanged.
Use a separately qualified diagnostic-capable translator:

```sh
python3 scripts/project-diagnostics.py check project.json \
  --translator .lake/build/bin/air2lean --out check-receipt.json
```

The consumer targets schema 2, `air2lean-check-diagnostics`, frozen at producer
revision `6b6a20c329ee2639c39b09e1e7b312c6722bfd31`. The required diagnostic-capable
producer is supplied by [PR 78](https://github.com/riventic/air2lean/pull/78), separately
from the project manifest base in [PR 68](https://github.com/riventic/air2lean/pull/68).
Matching the protocol is not executable qualification: the adapter records the actual
executable hash and reports qualification as `not_attested_by_adapter`. It never builds or downloads tools.

The new `air2lean-project-diagnostics` envelope retains the existing manifest/profile,
input hashes, declared source closure, Git availability, goals, assumptions, exclusions
and trust disclosures under `evidence`. Each root additionally has a `root_checks` entry,
with typed preflight failures, an original-path/numeric-staging inverse map, execution
hashes and the validated producer report. Numeric paths preserve declared AIR ordering.
The adapter stages the retained original bytes, including readable malformed JSON;
missing bytes never receive fabricated replacement files. A missing AIR dependency or
invalid shared profile blocks that root. Other independently readable roots still run.
Missing source/contract evidence is retained as an import blocker even when supplied AIR
can be checked. Supplied AIR still does not attest source/export correspondence.

The optional manifest `spawn_policy` is `available` by default or explicitly
`fallible`. The adapter passes `--spawn-policy` with the effective value on every
check-only invocation and records it in `evidence` and the execution argv. This does
not add a field to the producer's report. Fallible checking requires a
producer with the shared fallible-spawn validator; the producer decides which AIR
is supported. Manifest preflight alone does not establish semantic support. All
proof, runtime and source disclosures remain unchanged.

Preflight syntax/import, schema and manifest-profile checks have separate typed stages.
Producer codes, phases, categories, ID spaces, prerequisites and dependency chains are
validated against the frozen vocabulary and retained. Generic `AIR_DECODE` or validator
boundary failures are not reclassified by scraping display messages. The legacy evidence
report's `AIR_JSON` remains a legacy preflight code; the separate checks identify the
known boundary precisely. Whole-program shared-definition errors can overlap local
errors. Missing/ambiguous/blocked dependency chains cover selected normalized direct
calls and explicit spawn workers only. They do not establish compiler dependency closure.
Source spans are validated (`statement`/`declaration` granularity, module-relative
file, absolute 1-based line, optional 1-based column; null with `unavailable_in_AIR`)
and retained unchanged: they are exporter provenance, not host paths. `fatal` is
validated as a boolean and retained. Canonical instruction IDs are not relabeled as
original/exported IDs.

Root statuses are `checked`, `rejected`, `blocked`, `error` or `not_run`. `checked` requires
a complete, successful producer validation and no manifest preflight blockers. It does
not mark `analyzed`, `exported`, `translated`, `compiled`, `tested` or `proved` as passed.
Proof status remains `not_run`, runtime outcomes `not_observed`, and source correspondence
`not_attested`. Hashes bind supplied evidence and observed receipts; no theorem receipt or
proof-stage failure is imported by this command. Ordinary artifact verification still
reports hash agreement rather than proof attestation.

`--diagnostic-limit` is 1–4096, default 256, per root, and `--unit-diagnostic-limit`
1–4096, default 64, per input file; both are forwarded to the producer. The producer's
retained diagnostic payload is bounded to 1 MiB, files to 256, and input contents to
64 MiB per invocation. The receipt's `caps` must equal these bounds exactly; per-unit
retained counts must respect the unit cap; `capped_units` must be sorted, name known
files, and account (with the retained diagnostics) for `diagnostics_observed`; and it
must be non-empty exactly when the receipt is truncated.
Its `diagnostics_observed` counts attempted additions, not every possible blocker.
`first_error_in_unit`, `complete: false` and `truncated: true` survive import. The project
manifest's stricter input/time/output limits still apply. Separate stdout/stderr capture
uses bounded files and POSIX process-group cancellation, including unfinished descendants.
Combined receipt/log bytes consume `max_total_output_bytes`; later roots explicitly become
`not_run` after exhaustion. Final report encoding must also fit that limit. These are
bounds for specified resources, not a hostile-process sandbox or a global time guarantee.

The adapter accounts for payload bytes using Lean’s compact serializer rules, including
six-byte escapes for tab, backspace and formfeed and UTF-8 for non-ASCII scalar characters.
Its own report encoding remains separate. It validates strict UTF-8/JSON, schema, vocabulary, inventory, count/payload caps,
source/proof disclosures and exit/status agreement. Invalid receipts become `error`,
never successful validation evidence. Diagnostics follow manifest-root order and producer
order. Paths and known staging-directory references in display messages are normalized;
raw stdout/stderr SHA-256 and byte counts describe retained stream bytes before rewriting.
Resource or execution failures can retain bounded prefixes; successful producer receipts
still pass complete receipt validation. Producer counters describe the original receipt
before path mapping, as marked by
`producer_counters_basis`; they are not recomputed for the rewritten display paths.
Raw receipt hashes may differ across temporary directories even when normalized diagnostics
match. The report does not independently authenticate the producer or its receipts.

No Lean output is emitted. Reports publish with atomic no-clobber links and cannot target
an input or producer file. There is no overwrite flag. Failures and cancellation preserve
prior artifacts; an invalid producer can still yield an explicitly rejected diagnostic
report. A report-size or publication failure emits no successful receipt to stdout.
Exit codes are 0 for all roots checked, 1 for a published rejected report, 2 for a command/
publication failure and 130 for interruption. Malformed manifests prevent trusted root
selection and are reported as command failures.

Offline tests use bounded Python mocks, not the translator or a compiler:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s tests/roadmap/project-diagnostics -v
```

Local integration qualification passed at consumer revision
`a17882e297875cd124ba8da51b275d8aecb985d2`, against producer checkpoint
`2f3a86a65cfaa90a40b70daaceb545441c1ddaa6`. The tested executable was compiled from
production source revision `1c174cea9b9c7a234bbd6b4fab98c1f2ef53c636`; its SHA-256 was
`dea3cacb093cc31615a2e09cc29659f363f37848307c24562f49a844c8b69e40`.
The observed checks covered the 37 project compatibility and 30 consumer mock tests,
actual example success, malformed and valid sibling roots, a missing declared input
with an independent sibling, a missing direct callee, profile and schema rejection,
diagnostic cap 1, absence of generated Lean, no-clobber publication, protected inputs,
and ordinary example translation followed by hash verification. This records observed
checks; the adapter continues to report `not_attested_by_adapter` and does not attest
native-program behavior or proofs.

The integrated full Zig 0.16.0 project CI step runs the 30 offline consumer tests and
checks the example manifest with the diagnostic-capable translator built by that job.
It publishes to a fresh temporary path, compares stdout with the published receipt,
and requires checked status while preserving the explicit proof, runtime, source and
adapter-qualification disclosures above. The existing example translation and artifact
verification still run in the same step. This gate adds no artifact upload. Its actual
execution and result remain separate from the historical local qualification recorded
above; offline tests alone do not qualify the integrated executable.
