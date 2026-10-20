#!/usr/bin/env bash
# The translated FixedBufferAllocator against the generic allocator specification (P4a):
# the retained translation is the fresh one; the bridge (generated std.mem.Allocator wrappers =
# Wrap.*), FBA.allocSpec and the client proof check; the client evaluates to the native results;
# a mutated alloc fails the proof (mutant.sh); the entries satisfy the full-state FAllocSpec, proved
# natively by the general tactic fsym (Full.lean). Every Lean file is a module of the fixture's
# library AllocFba (tests/roadmap/lakefile.toml), built by Lake with what it imports
# (scripts/fixtures.py; run it under scripts/build-guard.py). Needs a built translator; runs no
# compiler. With AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also builds and runs native.zig and
# compares it with expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-fba
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-fba.XXXXXX")
trap 'rm -rf "$work"' EXIT
python3 - "$here" <<'EOF'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
record = json.loads((here / 'provenance.json').read_text())
for name, digest in record['source_sha256'].items():
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here / 'air')): hashlib.sha256(p.read_bytes()).hexdigest()
         for p in sorted((here / 'air').rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance.json'
EOF
# The retained translation is the fresh one, byte for byte (Lake builds the retained file).
"$translator" "$here/air/0.16.0/client-linux" -o "$work/Gen.lean" \
  --namespace AllocFba.Gen --prefix client. --allocator-model translated
cmp "$work/Gen.lean" "$here/AllocFba/Gen.lean"
# The library, including creation/domain controls and AllocFba/Eval.lean (`#guard`s).
python3 -B scripts/fixtures.py build AllocFba
# Axioms of every theorem of the proof modules, from the built environment: only the standard ones.
# Named: the theorems, and `FBA.ledger`, a definition (a `ResetLedger` whose fields are proofs).
named=()
for name in FBA.allocSpec Wrappers.realloc_of Wrappers.allocSentinel_of FBA.fallocSpec \
    FBA.fthread_alloc FBA.fthread_resize FBA.fthread_remap FBA.fthread_free FBA.freset_spec \
    FBA.fown_init FBA.fallocator_init FBA.fallocator_creation FBA.fallocSpec.creation \
    FBA.ledger realloc_eq Client.client_spec; do
  named+=(--declaration "AllocFba.$name")
done
python3 -B scripts/fixtures.py audit AllocFba.Bridge AllocFba.Fba AllocFba.Client AllocFba.Full \
  AllocFba.Wrappers AllocFba.Creation AllocFba.CreationDomain "${named[@]}"
bash "$here/mutant.sh"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe ${AIR2LEAN_ROSETTA_LINK_FLAGS:-} -OReleaseSafe "$here/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
fi
echo "alloc-fba: ok"
