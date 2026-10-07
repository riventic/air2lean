# Check-only translator diagnostics

The diagnostic mode inspects selected AIR files without emitting Lean, invoking a
compiler, running a program, or checking a theorem:

```sh
air2lean --diagnostics-json ./air --diagnostic-limit 256
```

It prints one JSON object to stdout and exits 0 for `checked` or 1 for `rejected`,
including argument and directory errors. The leading `--diagnostics-json` selects
this mode. It accepts `--profile`, `--diagnostic-limit` (1–4096), and
`--spawn-policy available|fallible`; `-o`,
`--namespace`, `--prefix`, and `--float-semantics` are incompatible. The ordinary
emission mode keeps its fail-fast interfaces and generated source format.

The spawn policy defaults to `available`, an explicit availability assumption in
the scheduling model. `fallible` applies the translation checker's additional
spawn boundary after the ordinary selected-program check passes. It supports the
audited default/1 MiB stack requests with a null allocator, and Zig 0.16 Io.Group
calls. Unsupported configurations produce `MODEL_FAILURE` in phase `program`,
category `unsupported_semantics`; a failed ordinary program prerequisite produces
a skipped policy check. Missing, invalid, or duplicate policy flags are CLI errors.
The project manifest's effective `spawn_policy` is passed explicitly to both
translation and diagnostics. This does not add a producer-schema field or turn
check-only validation into a proof, a host availability test, or a liveness claim.

Schema 1 (`kind: air2lean-check-diagnostics`) gives each diagnostic an enum-backed
stable `code`, `phase`, `category`, file/function identity, anchor, dependency chain,
prerequisites and `first_error_in_unit`. Messages remain human-readable display
text and are never scraped for codes, classifications or locations. The bounded log
copies at most 2048 message characters before retaining a diagnostic and preserves
an explicit original-message truncation flag. Standalone compatibility rendering
outside that log retains the original message. Input is bounded to
256 sorted JSON files and an aggregate 64 MiB of actual reader bytes, plus at most
one byte for growth detection across the entire selected input. Every returned chunk
is charged before UTF-8 decoding; invalid UTF-8 and later partial I/O failures retain
their byte charges. Once the detection byte is consumed, later files are skipped
without another read allowance. A fresh metadata check rejects oversized inputs
before open, then requires a regular file; actual bounded reads also detect growth.
Function names and the directory argument are limited to 1024 characters. The diagnostic payload is
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
unsupported markers are reported with **exported** IDs. Markers no longer stop the
unit: canonicalization is tag-agnostic and still runs. When the composed normalizer
rejects a canonical function (or markers are present), each canonical instruction is
normalized on its own, with nested bodies flattened and inspected separately, so
every independently rejected instruction receives its own `NORMALIZATION_FAILURE`
with a **canonical** ID. Known compiler-state/runtime-effect tags get category
`unsupported_semantics`; other rejections (unknown tags, missing operands or fields)
keep the generic `validation_failure` boundary, without message scraping. Only an
unsupported `zig_version` remains one unit-wide normalization error. Successfully
normalized direct calls of such a blocked function still contribute dependency edges,
so its own missing or blocked callees are reported with chains. No partial function,
SSA value or replacement instruction is built, and the check stage is still skipped
(`fully_normalized_function`). Malformed input stays fatal and separate: strict JSON,
AIR decode, canonicalization (duplicate IDs, dangling references, scopes) and
normalized structure failures each yield one error for that unit plus skipped-check
diagnostics. Successful canonicalization and normalization
produce full normalized functions; structural validation gates further inspection.
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
queue to 257 names. Its adjacency index keeps each caller's first occurrence of a
neighbor; full instruction edges and blocker diagnostics remain distinct. The selected function identities serve as reporting roots;
this is not compiler-discovered closure, and indirect targets do not contribute
chains. A blocked function can retain its declared identity without any fabricated
partial function, SSA value or replacement instruction.

This is an initial I05 collector, with explicit limits. Parsing, canonicalization,
a single instruction's normalization, normalized structural validation, a single instruction/constant/
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
python3 tests/roadmap/blocker-collection/test_cli.py .lake/build/bin/air2lean
```

The blocker-collection driver gives one unit four independent unsupported constructs
(an exporter marker, nested and top-level runtime-effect tags, an unknown tag) plus a
missing callee, and requires all five in one run. A five-file selection with blocked,
check-failing, missing-leaf and supported units must report every blocker and its
call-graph chain from one invocation, both directly and through
`scripts/project-diagnostics.py check`. Malformed JSON, duplicate instruction IDs and a
structurally invalid unit each remain exactly one fatal unit error (`JSON_SYNTAX`,
`CANONICAL_FAILURE`, `STRUCTURE_FAILURE`) without suppressing sibling units.

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

At revision `1c174ce`, serialized qualification passed the translator build, collector
evaluation, 15 diagnostics CLI checks including V05 emission-byte comparison, the
input-validation API checks, all 78 input-validation CLI checks, and the extracted
CI step replay. The subsequent test-oracle repair independently requires rejected
status and exit 1 for negative fixtures; checked receipts must be complete, untruncated,
diagnostic-free and have passed local file checks. At revision `209e1e3`, the targeted
rerun passed collector evaluation, four offline harness tests including contradictory
checked receipts, all 15 diagnostics CLI checks including V05 emission-byte comparison,
the input-validation API and 78 CLI checks, and exact CI replay with 14 diagnostics
CLI checks. CI replay explicitly excludes the historical baseline comparison.
These test changes do not alter the producer.

Compiler-state and runtime-effect tags remain rejected with specific guidance. Temporary
`inferred_alloc`/`inferred_alloc_comptime` instructions are not ordinary allocations;
the exporter omits their type, and the normalizer gives the inference-stage reason
before its missing-type check. Other missing-type and malformed-input checks are unchanged.
Zig 0.16's `legalize_vec_store_elem`, `legalize_vec_elem_val` and
`legalize_compiler_rt_call` belong to later code generation, beyond the accepted
`analyzed-air` export stage. `runtime_nav_ptr` (0.15/0.16) requires TLS or external
runtime pointer identity and lifetime semantics. Error-return-trace tags in all three
versions require mutable trace semantics; a recorded tracing setting supplies no such model.
The structured collector retains its existing codes and exported instruction anchors,
while using the same reasons for explicit exporter markers.

The inventory selects these classifications only for tags present in each compiler's enum.
Its `normalizer-rejected-compiler-state-or-effect` disposition is source-only rejection
policy, with no admitted semantics, proof or compiler-generated fixture qualification.
Synthetic regressions cover diagnostic routing; compiler fixture qualification remains
pending. The older `vector_store_elem` tag (0.14/0.15) is rejected as a vector-memory
write requiring lane bounds and memory semantics, separately from Zig 0.16 legalization.
`cmp_lt_errors_len` (0.14/0.15) and `cmp_lte_errors_len` (0.16) depend on the
compiler's finalized error universe; the analyzed-AIR export cannot substitute a
currently known count. Their version-dependent comparison also precludes treating
the rename as identical semantics. Nested synthetic CLI fixtures retain exported IDs
and rejection reasons for every actual version/tag member, including untyped
inferred allocations. No source feature is newly accepted by these classifications.
