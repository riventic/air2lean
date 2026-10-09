#!/usr/bin/env bash
# G1: extern C calls (docs/air-json.md §Extern calls). Needs a built translator and
# `lake build ZigLean`; runs no compiler. For each Zig version, extern_calls.zig's `memset`/
# `strlen` calls bind to libc_ref.zig's `export fn` definitions, and the translation evaluates to
# expected.txt (Eval.lean). trusted.zig's `extern "c" fn abs` binds to a registry model with a
# premise. abi_calls.zig declares `@export`ed abi_ref.zig symbols with other types: the calls bind
# through C ABI conversions (AbiEval.lean). With AIR2LEAN_NATIVE_ZIG (a stock Zig 0.16.0), also runs
# native.zig and abi_native.zig against expected.txt and abi_expected.txt.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/extern-calls
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-extern-calls.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/ExternCalls"
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
for version in 0.16.0 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/ExternCalls/Gen.lean" \
    --namespace ExternCalls --prefix extern_calls.
  # The retained translation is the fresh 0.16.0 one, byte for byte.
  if [ "$version" = 0.16.0 ]; then cmp "$work/ExternCalls/Gen.lean" "$here/ExternCalls/Gen.lean"; fi
  "${lean_cmd[@]}" -R "$work" -o "$work/ExternCalls/Gen.olean" "$work/ExternCalls/Gen.lean"
  "${lean_cmd[@]}" "$here/Eval.lean"
done
# The trusted-base binding: registry model with premise, kernel-checked obligation.
"$translator" "$here/air/0.16.0-trusted" -o "$work/ExternCalls/Trusted.lean" \
  --namespace ExternCalls.Trusted --prefix trusted. --model-registry "$here/registry.json"
cmp "$work/ExternCalls/Trusted.lean" "$here/ExternCalls/Trusted.lean"
cp "$here/Model.lean" "$work/ExternModel.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ExternModel.olean" "$work/ExternModel.lean"
"${lean_cmd[@]}" "$work/ExternCalls/Trusted.lean"
# Declarations with other types than their `@export`ed definitions: C ABI conversions.
"$translator" "$here/air/0.16.0-abi" -o "$work/ExternCalls/Abi.lean" \
  --namespace ExternCalls.Abi --prefix abi_calls.
cmp "$work/ExternCalls/Abi.lean" "$here/ExternCalls/Abi.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/ExternCalls/Abi.olean" "$work/ExternCalls/Abi.lean"
"${lean_cmd[@]}" "$here/AbiEval.lean"
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
if [ -n "${AIR2LEAN_NATIVE_ZIG:-}" ]; then
  for t in native abi_native; do
    "$AIR2LEAN_NATIVE_ZIG" build-exe -OReleaseSafe "$here/$t.zig" --cache-dir "$work/cache" \
      --global-cache-dir "$work/cache" -femit-bin="$work/$t"
    "$work/$t" 2> "$work/$t.txt"
  done
  diff "$here/expected.txt" "$work/native.txt"
  diff "$here/abi_expected.txt" "$work/abi_native.txt"
fi
echo "extern-calls: ok"
