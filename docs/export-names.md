# Exported function filenames

The exporter keeps the complete fully qualified function name in JSON `name`, call
operands, and `ZIG_AIR_JSON_FILTER` matching. Filenames are storage keys. The
translator reads JSON identities; changing a storage key does not rename a function.
After all validation guards succeed, emission uses the historical virtual
`<original full JSON name>.json` order. The key is cached before anonymous
renumbering, so hashes and numeric project staging paths cannot reorder definitions
or change which generic instance receives a preferred declaration name. Reads,
validation errors and profile receipts continue using the actual storage paths.

A nonempty ASCII name uses its existing `<name>.json` spelling when it begins
with a letter, digit, or underscore, contains only letters, digits, underscores,
hyphens and dots, and the complete basename including `.json` fits in 255 bytes
(or the platform's smaller `std.fs.max_name_bytes`). Windows device stems
`CON`, `PRN`, `AUX`, `NUL`, `COM1`–`COM9`, and `LPT1`–`LPT9`, ignoring case and
extensions, also use the fallback. Other names use
`~air2lean-sha256-<64 lowercase hex digits>.json`: SHA-256 of the exact UTF-8
function name. This includes long names, Unicode, separators, leading dots or
hyphens, and names containing the reserved `~` character. The two new filename
namespaces are disjoint. JSON names are never shortened or normalized by export.

Fresh output files are created exclusively. Re-analysis of the same function can
write the same filename again: the exporter opens the existing file without
truncating, obtains a nonblocking exclusive advisory lock, parses its JSON with
standard duplicate-key rejection, and checks the complete `name`. Only an exact
identity match permits truncation and replacement. A distinct identity, malformed
JSON, nonregular file, changed read length, file larger than 64 MiB, or unavailable
lock produces an explicit warning and preserves the existing contents. Validation
uses a separate arena released before serialization. Successful writes hold the
lock until close. These checks coordinate cooperating exporters;
output directories are trusted, and this is not protection against concurrent
path replacement or writers that ignore advisory locks. A failed JSON write still
reports incomplete output, as before.

Golden normalization first verifies the actual raw artifact's receipt hash and
profile, then checks a reserved filename against the full original JSON name.
It derives every canonical filename from the normalized JSON name using one
portable direct-or-SHA policy, so compiler anonymous IDs can differ between
versions even when their raw lengths cross the direct-name limit. Comparison
basenames reserve 13 of the 255 bytes for the legacy collision suffix; normalized
identities longer than 237 ASCII bytes therefore use SHA storage keys, regardless
of whether a particular overlay currently contains one or several instances.
Production export filenames retain their full 255-byte direct-name budget. Several
raw identities that normalize to one identity retain the existing SHA-1 suffix over
exact normalized pretty JSON.
Directory overlays continue removing every earlier variant of the same normalized
basename. Neither production JSON identities nor receipt hashes are rewritten.

## Qualification

Offline checks invoke only Python; they do not qualify the Zig implementation:

```sh
python3 tests/roadmap/export-names/test_offline.py
python3 tests/roadmap/profiles/test_golden_pipeline.py
```

The public `export_names.zig` fixture retains ten functions, including a 250-byte
name (255-byte direct basename), a 251-byte name, two distinct 408-byte names,
separators, a reserved character, and Unicode. The checked-in expected-name list
contains their exact identities. After rebuilding each supported patched compiler
with the usual single-job bootstrap, the root validation queue runs the following
for Zig 0.14.1, 0.15.2 and 0.16.0. Set `PATCHED_ZIG` to the guarded compiler and
`WORK` to an isolated temporary directory; no native execution is required.

```sh
mkdir -p "$WORK/air"
ZIG_AIR_JSON_DIR="$WORK/air" ZIG_AIR_JSON_FILTER=export_names. \
  "$PATCHED_ZIG" build-obj tests/roadmap/export-names/export_names.zig \
  -O ReleaseSafe -fno-error-tracing -fno-emit-bin --cache-dir "$WORK/cache-1"
python3 tests/roadmap/export-names/check_dump.py "$WORK/air"
lake exe air2lean "$WORK/air" -o "$WORK/Gen.lean" \
  --namespace ExportNames --prefix export_names. --profile abi64-le-v1
lake env lean "$WORK/Gen.lean"
python3 tests/roadmap/export-names/check_dump.py "$WORK/air" --mode seed-reexport
ZIG_AIR_JSON_DIR="$WORK/air" ZIG_AIR_JSON_FILTER=export_names. \
  "$PATCHED_ZIG" build-obj tests/roadmap/export-names/export_names.zig \
  -O ReleaseSafe -fno-error-tracing -fno-emit-bin --cache-dir "$WORK/cache-2"
python3 tests/roadmap/export-names/check_dump.py "$WORK/air" --mode check-reexport
python3 tests/roadmap/export-names/check_dump.py "$WORK/air" --mode seed-collision
ZIG_AIR_JSON_DIR="$WORK/air" ZIG_AIR_JSON_FILTER=export_names. \
  "$PATCHED_ZIG" build-obj tests/roadmap/export-names/export_names.zig \
  -O ReleaseSafe -fno-error-tracing -fno-emit-bin --cache-dir "$WORK/cache-3" \
  2> "$WORK/collision.log"
python3 tests/roadmap/export-names/check_dump.py "$WORK/air" --mode check-collision
```

The collision run must report `OutputIdentityCollision`; the inspector verifies
byte preservation and that independent siblings remain present. Distinct cache
directories force fresh analysis instead of relying on a compiler cache hit.
The root also runs the existing exporter regressions and fresh profile/golden/proof
pipeline. The qualification record below distinguishes completed checks from
pending checks; the commands alone are not qualification evidence.

CI runs `bash scripts/check-export-names.sh` after the existing runtime/translator
build in each non-mutation Zig 0.14.1, 0.15.2 and 0.16.0 job. It reuses that job's
guarded patched compiler, requires the explicit collision warning, and checks the
public translation with a temporary Lean package root. All generated artifacts and
local/global Zig caches live under a disposable `RUNNER_TEMP` directory; this gate
adds no uploads and does not update tracked generated files. Its synthetic importer
CLI cases also require identical complete generated output for direct, hash, and
numeric filenames, including two reached anonymous instances whose raw and
renumbered lexical orders differ, and preserve the first path error and output on
rejection.

Root qualification on 2026-10-05 passed with a freshly rebuilt AIR-only Zig
0.15.2 exporter: all ten exact public identities and seven hash filenames,
translation with `abi64-le-v1`, kernel checking of the generated Lean source,
same-identity re-export, and explicit distinct-identity collision warning with
byte preservation and retained siblings. The 14 bounded offline filename tests
and 21 existing profile/golden mock tests also passed. The exact CI helper at
`4bb3080` then passed with the existing Zig 0.15.2 compiler (4.1 seconds, 100 MiB peak), and with
a freshly rebuilt AIR-only Zig 0.16.0 compiler (10.3 seconds, 541 MiB peak). The
0.16.0 bootstrap also passed (199.9 seconds, 4,239 MiB peak). Both helper runs cover
the ten identities, translation and kernel check, re-export, collision warning,
preservation, and retained siblings using the unchanged exporter source.
Zig 0.14.1 actual qualification and the full golden/profile/proof pipelines for
0.15.2 and 0.16.0 remain pending. These results cover the public filename fixture
rather than a source-to-binary correspondence theorem.

The subsequently attempted full Zig 0.15.2 pipeline passed raw AIR/profile golden
checks through Lists, then rejected Lists generated-source ordering. Static
comparison found identical declaration chunks in a different order: hashed generic
storage names changed the emitter's input traversal. The repair above retains
historical emission order without changing the golden comparison. Actual importer
CLI and repaired full 0.15.2/0.16.0 pipeline qualification remain pending.
