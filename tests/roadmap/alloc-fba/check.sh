#!/usr/bin/env bash
# The translated FixedBufferAllocator against the generic allocator specification (P4a):
# the retained translation is the fresh one; the bridge (generated std.mem.Allocator wrappers =
# Wrap.*), FBA.allocSpec and the client proof check; the client evaluates to the native results;
# a mutated alloc fails the proof (mutant.sh). Needs `lake build air2lean ZigLean` and
# `lake build ZigLean.Sep.AllocSpec.Dispatch`; runs no compiler. With AIR2LEAN_NATIVE_ZIG (a stock
# Zig 0.16.0), also builds and runs native.zig and compares it with expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/alloc-fba
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-alloc-fba.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/AllocFba"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
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
"$translator" "$here/air/0.16.0/client-linux" -o "$work/AllocFba/Gen.lean" \
  --namespace AllocFba.Gen --prefix client. --allocator-model translated
cmp "$work/AllocFba/Gen.lean" "$here/AllocFba/Gen.lean"
for m in Gen Bridge Fba Client; do
  if [ "$m" != Gen ]; then cp "$here/AllocFba/$m.lean" "$work/AllocFba/$m.lean"; fi
  "${lean_cmd[@]}" -R "$work" -o "$work/AllocFba/$m.olean" "$work/AllocFba/$m.lean"
done
"${lean_cmd[@]}" "$here/Eval.lean"
cat > "$work/Axioms.lean" <<'EOF'
import AllocFba.Client
#print axioms AllocFba.FBA.allocSpec
#print axioms AllocFba.realloc_eq
#print axioms AllocFba.Client.client_spec
EOF
"${lean_cmd[@]}" "$work/Axioms.lean" > "$work/axioms.txt"
if grep -v "\[propext, Classical.choice, Quot.sound\]" "$work/axioms.txt" | grep -q .; then
  cat "$work/axioms.txt" >&2; echo 'alloc-fba: unexpected axioms' >&2; exit 1
fi
bash "$here/mutant.sh"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$here/native.zig" --cache-dir "$work/cache" \
    --global-cache-dir "$work/cache" -femit-bin="$work/native"
  "$work/native" 2> "$work/native.txt"
  diff "$here/expected.txt" "$work/native.txt"
fi
echo "alloc-fba: ok"
