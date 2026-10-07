# Target and build profiles

The current runtime models a reference 64-bit, little-endian ABI. Profile metadata
makes the source assumptions visible; it does not prove correspondence with a
shipping executable. Existing type, pointer, layout, and unsupported-instruction
checks still apply. Pointer-width and endian generalization remain separate work. Schema 12 retains
the existing Linux x86_64 reference and macOS aarch64 model workflows. These are
accepted model ABI scopes with per-type layout checks, not hardware or binary
qualification claims.

New exporter output uses **schema 12**. The function's owning module supplies its
target, CPU/features, optimization mode and error-tracing setting. The compiler
configuration supplies the backend, and the compiler supplies its Zig version and
error-set width. The dump is analyzed AIR, before backend code generation.
`float_mode: "per-instruction"` means strict/optimized operation tags carry the
float choice; optimized tags remain rejected by the normalizer. It does not claim
that the entire source function used one float mode.

Every schema-12 function has a mandatory `profile` object:

| Field | Accepted value or meaning |
| --- | --- |
| `name` | `"abi64-le-v1"` |
| `target_triple` | Zig's `arch-os-abi` triple; currently restricted to `x86_64-linux-<abi>` and `aarch64-macos-<abi>` (OS and ABI version suffixes are retained) |
| `pointer_bits` | `64`; narrower targets are rejected |
| `endian` | `"little"`; big endian is rejected |
| `abi` | Target ABI tag; must equal the triple's ABI component before a version suffix |
| `zig_version` | Must equal the file's top-level `zig_version`; normal supported-version checks still apply |
| `backend` | Actual configured compiler backend, such as `stage2_llvm`; recorded for provenance |
| `cpu` | Resolved CPU model name |
| `features` | Enabled CPU feature names, emitted in sorted order; empty/duplicate names are rejected |
| `build_mode` | `Debug`, `ReleaseSafe`, `ReleaseFast`, or `ReleaseSmall`; recording a mode does not qualify it ([build-modes.md](build-modes.md)) |
| `float_mode` | `"per-instruction"` |
| `error_set_bits` | `16`; other widths are rejected |
| `error_layout` | `"type-table"`; each exported type's ABI size/alignment remains checked against the model |
| `error_tracing` | Boolean from the owning module |
| `export_stage` | `"analyzed-air"`; a shipping-binary correspondence claim is rejected |

Unknown profile fields are rejected. A schema-12 file with absent, null, malformed
or contradictory required metadata fails before emission. A supplied top-level
`target_endian` still must be little endian. Supported schemas are explicitly
**1–12**; schema 0 and future schemas fail closed. Schema 1–11 cannot carry a
schema-12 profile object.

Old schema 1–11 exports select **`legacy-abi64-le`**. This is the existing reference
model assumption, not recovered target/build information. Target triple, ABI,
backend, CPU, build mode, float mode and export stage are reported as `unverified`;
error tracing is reported as `null`. The model still assumes 64-bit pointers,
little-endian bytes and 16-bit error codes. Explicit big-endian metadata is
rejected even for legacy exports. No flag is required for existing translation
scripts or old fixtures.

One translation must use identical profiles, including schema, Zig version,
CPU/features (including their array order), build mode and error tracing. Legacy
and schema-12 files cannot be mixed. A mismatch or any checked-program failure
leaves an existing output file untouched. This policy complements structural,
reference, layout, global and call checks; profile agreement alone establishes
none of those invariants.

The optional flag asserts the expected input profile:

```sh
air2lean AIR_DIR -o Gen.lean --namespace My.Program --profile abi64-le-v1
```

`--float-semantics ieee|compiler-rt` selects the numerical model as before, with
`ieee` the default. The output records the selected choice explicitly. `ieee`
concerns the project's IEEE operation model; `compiler-rt` concerns the modeled
version-specific compiler-rt operations described in [floats.md](floats.md).
Neither choice qualifies a backend, CPU, optimization setting or shipping binary.
Abstract numerical specifications must identify their additional contracts.

The CLI writes a one-line JSON record before the generated Lean source:

```text
-- air2lean-profile: {"profile":{...},"float_semantics":"ieee","correspondence":"model"}
```

The normalized report profile includes `schema`, which belongs at the top level
of raw AIR, rather than inside the exporter's raw `profile` object. This marker
lets proof/report tooling retain the target assumptions with the generated model.
A theorem about generated functions concerns the semantics named in this marker;
changing the profile or float selection requires regenerating and checking its
proofs. Historical committed outputs lacking a marker should be classified as
legacy/unverified, rather than treated as schema-12 evidence.

## Regression checks

After building `air2lean` under the project's serialized compiler guard, run:

```sh
python3 tests/roadmap/profiles/test_cli.py .lake/build/bin/air2lean
lake env lean tests/roadmap/profiles/Profiles.lean
```

The Python driver only invokes the built translator: positive current/legacy
fixtures, mandatory fields, invalid widths/endian/schema/stage, explicit profile
selection, mixed files and preservation of existing output on every rejection.
The Lean driver checks parser/profile selection directly. Exporter builds and
live-export fixture checks must also cover each supported Zig version; this file
does not turn metadata capture into a semantic-preservation theorem.

## Golden comparisons and check receipts

`scripts/check.sh` first translates the actual complete AIR program, so profile,
layout and program checks run before metadata is ignored for comparison. It binds
the generated first-line profile record to every actual AIR file's metadata and
SHA-256 hash. Only that receipt permits the known schema-12/profile to schema-11
comparison transition; older schemas, malformed metadata and observable nested
AIR data remain checked.

Generated comparisons omit only a valid first-line JSON profile marker. The real
header stays in the generated file that the Lean proof gate builds. In CI, the
script checks committed, staged and working-tree sources before replacement;
only a header matching the checked profile may differ while the committed body
stays identical. Untracked and unrelated proof changes fail. Version/OS generated
goldens still require the exact generated body to match their selected snapshot.
The proof build and optional differential gate keep their existing behavior.

Each example records its profile, selected float semantics, input hashes, full
generated-source hash and body hash in
`.lake/check-reports/<zig-version>/<example>.json`, alongside the actual
`<example>.Gen.lean`. `AIR2LEAN_CHECK_REPORT_DIR` changes this destination.
`AIR2LEAN_OUT_DIR` additionally copies these receipts and generated artifacts under
`check-reports/<zig-version>/`, separately from the reusable AIR directories.
These are provenance receipts, not semantic-preservation or binary-equivalence
certificates.

Fake-tool integration regressions run without a Zig or Lean compiler:

```sh
python3 tests/roadmap/profiles/test_golden_pipeline.py
bash scripts/review-checks.sh
```

AIR comparison now processes each directory as one batch. The batch loads helpers
and the receipt once, rejects duplicate receipt filenames, and indexes input
hashes by their original filenames. Every actual file still passes its raw-hash
and profile checks before any overlay is replaced. Later golden directories
replace all earlier variants of the same normalized basename. Generic-instance
collisions retain the SHA-1 first-12-digit suffix of the exact pretty JSON plus
its final newline. The existing single-file `normalize-air.py INPUT.json` command
is unchanged; `--output-dir DIRECTORY` selects the batch overlay operation.


## Bounded Linux native ABI observations

`scripts/abi-probe.py` builds and executes the stock Zig 0.16.0 LLVM probe under
`tests/roadmap/abi-probes/`. Its four profile inputs select baseline x86_64-linux-gnu
or aarch64-linux-gnu, each in ReleaseSafe or ReleaseFast. Run on the selected Linux
CPU, or under an explicitly recorded execution emulator; foreign compilation alone
cannot produce a report. The runtime rejects discrepancies in target, endian,
pointer width, backend, CPU/features, mode, error-set width and tracing. Per-mode status:
[build-modes.md](build-modes.md).

Two more profile inputs select baseline `aarch64-macos-none` (CPU `apple_m1`) in
ReleaseSafe and ReleaseFast. They execute only on a Darwin host; the CI `macos` job
observes both ([target-matrix.md](target-matrix.md); per-mode status:
[build-modes.md](build-modes.md)). A macOS report stays outside the
paired Linux `compare` relation.

```sh
python3 scripts/abi-probe.py observe --zig /absolute/path/to/stock/zig \
  --profile tests/roadmap/abi-probes/x86_64-linux-gnu-ReleaseSafe.json \
  --output x86-safe.json
# On the aarch64 Linux execution environment, run the matching aarch64 profile.
python3 scripts/abi-probe.py compare x86-safe.json arm-safe.json
python3 -B tests/roadmap/abi-probes/test_probe.py
```

The explicit bounded contract records u9/u24/u40/u128 ABI size/alignment, pointer
size/alignment, a packed u32 backing layout, a four-lane u32 vector, and offsets
in an extern record. Volatile-backed native operations observe u24 wrapping,
packed bit encoding, vector addition and a pointer load. Only these listed layouts,
offsets and integer outputs form the exact paired observation relation. Each run
binds probe/compat source bytes, the stock compiler executable, generated binary,
command and source profile. No expected native report is committed: actual outputs
must be collected by the serialized Linux validation workflow.

Imported reports are evidence inputs, not execution attestations. The comparison
checks current source hashes and all expected observations; synthetic Python test
records are strictly parser/contract tests. A successful pair does not prove a
compiler preservation theorem, ABI completeness, synchronization, float ABI or
WASM correspondence. f80/f128 operations and numerical tolerances remain outside
this fragment, and the existing float probe remains a separate reference gate.
ReleaseFast is a separate observation profile, not inferred from ReleaseSafe
([build-modes.md](build-modes.md)).

This tool does not change the translator's accepted target profiles. In particular,
aarch64-linux translation remains guarded, and wasm32 pointer parameterization
remains absent. The native probe records a bounded candidate for T04/T05/T06;
profile-bound generated proofs and broader target qualification remain pending.
