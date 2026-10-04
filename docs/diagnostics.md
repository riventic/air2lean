# Check-only translator diagnostics

The diagnostic mode inspects selected AIR files without emitting Lean, invoking a
compiler, running a program, or checking a theorem:

```sh
air2lean --diagnostics-json ./air --diagnostic-limit 256
```

It prints one JSON object to stdout and exits 0 for `checked` or 1 for `rejected`,
including argument and directory errors. The leading `--diagnostics-json` selects
this mode. It accepts `--profile` and `--diagnostic-limit` (1–4096); `-o`,
`--namespace`, `--prefix`, and `--float-semantics` are incompatible. The ordinary
emission mode keeps its fail-fast interfaces and generated source format.

Schema 1 (`kind: air2lean-check-diagnostics`) gives each diagnostic an enum-backed
stable `code`, `phase`, `category`, file/function identity, anchor, dependency chain,
prerequisites and `first_error_in_unit`. Messages remain human-readable display
text and are never scraped for codes, classifications or locations. The bounded log
copies at most 2048 message characters before retaining a diagnostic and preserves
an explicit original-message truncation flag. Standalone compatibility rendering
outside that log retains the original message. Input is bounded to
256 sorted JSON files and an aggregate 64 MiB of contents. Function names and the
directory argument are limited to 1024 characters. The diagnostic payload is
bounded to 1 MiB and the requested count; `truncated: true` and `complete: false`
disclose dropped diagnostics. Rejection survives either cap. Files skipped because
of input limits are not accepted as checked.

The schema vocabulary is fixed independently of message text:

| Field | Values |
| --- | --- |
| `code` | `CLI_ARGUMENTS`, `INPUT_READ`, `INPUT_LIMIT`, `JSON_SYNTAX`, `AIR_DECODE`, `EXPORTER_UNSUPPORTED`, `OPTIMIZED_UNSUPPORTED`, `CANONICAL_FAILURE`, `NORMALIZATION_FAILURE`, `STRUCTURE_FAILURE`, `TYPE_FAILURE`, `GLOBAL_FAILURE`, `MEMORY_FAILURE`, `INSTRUCTION_FAILURE`, `CONSTANT_FAILURE`, `SIGNATURE_FAILURE`, `MODEL_FAILURE`, `PROGRAM_FAILURE`, `PROFILE_FAILURE`, `DUPLICATE_FUNCTION`, `CALLEE_MISSING`, `CALLEE_BLOCKED`, `CALLEE_AMBIGUOUS`, `PREREQUISITE_SKIPPED` |
| `phase` | `cli`, `input`, `decode`, `canonicalize`, `normalize`, `check`, `program`, `profile` |
| `category` | `malformed_input`, `unsupported_semantics`, `validation_failure`, `resource_limit`, `io_failure`, `skipped_prerequisite` |
| `anchor.id_space` | `unavailable`, `exported`, `canonical` |

`diagnostics_observed` counts attempted diagnostic additions; it is not the total
number of blockers in the inputs. Dependency reporting stops once truncated.
Diagnostics follow sorted file inspection and local traversal order, then duplicate
identities, call checks, root-ordered dependency chains and the final program check.
Unreadable-input errors precede readable-file checks. `files` is sorted by path.

Strict JSON failures are distinct from explicit exporter-unsupported and optimized
instruction markers. Each readable file is inspected independently. All explicit
unsupported markers are reported with **exported** IDs. Successful canonicalization
produces full normalized functions; structural validation gates further inspection.
The collector then checks independent parameter/return types, globals, escaping
allocations, constant-pointer uses, instructions in each branch, and call sites.
An instruction whose result type fails validation receives a skipped-prerequisite
diagnostic; its dependent operation check is not called. Nested bodies and siblings
remain inspectable. Structural results and operand indexes are reused by program
collection, which builds function references and unique/ambiguous safe-subset call
targets once. Duplicate identities across all selected files are reported separately.
Pointer/global alignment and spawned-worker tuple signatures share the ordinary
validator policies with caller-specific messages; cache publication stays transactional.
Instructions diagnosed after canonicalization use **canonical** IDs. Rewrites can
renumber, merge or drop instructions, so no original-ID correspondence is inferred.
The function identity uses the ordinary anonymous-name normalization over readable
selected inputs. `source_span` is null: this AIR does not supply reliable Zig
file/column spans. `nearest_dbg_line` is an approximate lexical debug-line hint,
not a source span. Unavailable anchors stay explicitly unavailable.

Named direct calls and explicit spawn workers supply dependency edges. Missing,
blocked and ambiguous selected callees receive separate codes. Deterministic BFS
records shortest root-to-caller-to-blocker chains, handles cycles, and bounds its
queue to 257 names. The selected function identities serve as reporting roots;
this is not compiler-discovered closure, and indirect targets do not contribute
chains. A blocked function can retain its declared identity without any fabricated
partial function, SSA value or replacement instruction.

This is an initial I05 collector, with explicit limits. Parsing, canonicalization,
normalization, normalized structural validation, a single instruction/constant/
global/signature validator, shared-definition checks and profile comparison can
still return their first error within that unit. Generic boundary codes use
`validation_failure`; they do not pretend to distinguish every malformed operand
from every unsupported representation. Failed boundaries set `first_error_in_unit`
and `complete: false`; failed prerequisites also receive skipped-check diagnostics.
Later files, branches and call sites remain inspectable. The authoritative existing
whole-program validator runs on structurally valid normalized functions; its first
error can overlap a separately collected call failure. It still covers checks not
decomposed here, including shared definitions, indirect targets and memory effects.
Complete fine-grained diagnostic migration and exporter source maps remain work.

`checked` means the selected AIR passed the translator's validation boundary. Per-file
`local_check: passed` does not attest dependencies or a whole-program result. Reports
always state `proof_status: not_run`, `runtime_outcomes: not_observed` and
`source_correspondence: not_attested`. No counterexample, divergence, absence of a
failure or theorem strength is inferred from rejection, a dependency cycle or a
successful check. I06/I07 proof receipts, P08 failed-contract/source linkage, and V06
structured runtime/search evidence need separate integrations. The project wrapper
can later consume this versioned protocol and preserve manifest filename mappings;
that integration is outside this PR.

Root validation commands after building the translator:

```sh
lake env lean tests/roadmap/diagnostics/Collector.lean
python3 tests/roadmap/diagnostics/test_cli.py .lake/build/bin/air2lean \
  --baseline /path/to/validated-v05/air2lean
```

The CLI driver checks independent malformed files and exporter markers, both
branches, missing/blocked/duplicate dependencies and cycles, deterministic bytes,
caps, incompatible flags, failure output preservation, and ordinary successful
emission bytes against the supplied V05 baseline. The collector evaluation also
checks failed-type prerequisite gating, nested siblings, retained-message bounds,
pointer/global alignment, shared spawn validation and snapshot ambiguity/order.
The CLI's large-message case uses one 100 KiB type name and two failed instructions.
Without `--baseline`, that byte
comparison is explicitly reported as not run. `--self-test` runs only offline
harness-oracle tests; it does not execute or validate the translator.

CI runs the collector evaluation, offline harness checks and actual CLI driver in
that order, in the full non-mutation Zig 0.16.0 lane after the translator build.
Evidence remains under `RUNNER_TEMP/diagnostics`; this gate adds no artifact upload.
CI does not supply a historical V05 binary, so its emission-byte comparison is
explicitly not run. The baseline comparison remains a separate qualification command
above. Accepted V05 Parser/Emitter test fixtures are included without production changes.

Recorded validation currently covers a serialized translator core build and three
offline harness tests. Collector evaluation, actual diagnostics CLI checks, the V05
baseline comparison, input-validation compatibility and CI replay await qualification;
the presence of the CI gate does not claim that these checks have passed.
