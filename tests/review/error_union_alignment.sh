#!/usr/bin/env bash
# ROOT-only qualification of one approved compiler at a time. Keeps fresh AIR and Lean artifacts.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
if [ "$#" -ne 3 ]; then echo 'usage: error_union_alignment.sh PATCHED_ZIG VERSION OUTPUT_DIR' >&2; exit 2; fi
zig_air=$1 version=$2 output=$3
case "$version" in 0.14.1|0.15.2|0.16.0) ;; *) echo 'unsupported qualification version' >&2; exit 2 ;; esac
case "$zig_air" in /*) ;; *) zig_air="$PWD/$zig_air" ;; esac
case "$output" in /*) ;; *) output="$PWD/$output" ;; esac
[ -x "$zig_air" ] || { echo 'patched compiler missing' >&2; exit 1; }
[ ! -e "$output" ] || { echo 'output must be fresh' >&2; exit 1; }
mkdir -p "$output/air" "$output/ErrorUnionABI"
cd "$repo_root"
[ "$("$zig_air" version)" = "$version" ] || { echo 'compiler version mismatch' >&2; exit 1; }
lib_args=()
if [ -n "${AIR2LEAN_ZIG_LIB_DIR:-}" ]; then lib_args=(--zig-lib-dir "$AIR2LEAN_ZIG_LIB_DIR"); fi
ZIG_AIR_JSON_DIR="$output/air" ZIG_AIR_JSON_FILTER=error_union_alignment. \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  -target x86_64-linux -mcpu=baseline "${lib_args[@]}" \
  "$repo_root/tests/review/error_union_alignment.zig" 2>"$output/export.stderr"
python3 - "$output" "$version" <<'PY'
import json, pathlib, sys
output, version = pathlib.Path(sys.argv[1]), sys.argv[2]
errors = output.joinpath('export.stderr').read_text()
if any(s in errors for s in ('air2lean: cannot open', 'air2lean: name too long for a file',
                            'air2lean: no JSON for', 'air2lean: incomplete JSON for')):
    raise SystemExit('incomplete AIR export')
files = sorted(output.joinpath('air').glob('*.json'))
expected = {f'error_union_alignment.{name}' for name in
            ('scalar', 'pair', 'array', 'writeScalar', 'payloadPointer')}
seen = []
for p in files:
    data = json.loads(p.read_text())
    if data['zig_version'] != version:
        raise SystemExit('AIR compiler version mismatch')
    seen.append(data['name'])
if len(seen) != 5 or set(seen) != expected:
    raise SystemExit(f'fresh AIR function inventory mismatch: {seen}')
PY
"$repo_root/.lake/build/bin/air2lean" "$output/air" -o "$output/ErrorUnionABI/Gen.lean" \
  --namespace ErrorUnionABI --prefix error_union_alignment.
# Compile the generated module before importing its definitions in the independent memory oracle.
lake env lean -R "$output" -o "$output/ErrorUnionABI/Gen.olean" "$output/ErrorUnionABI/Gen.lean"
cp "$repo_root/tests/review/ErrorUnionGenerated.lean" "$output/Model.lean"
lean_path=$(lake env printenv LEAN_PATH)
LEAN_PATH="$output:$lean_path" lake env lean -R "$output" --run "$output/Model.lean"
# Exercise actual compiler layouts for the version-sensitive zero-array edge.
mkdir "$output/zero-air"
ZIG_AIR_JSON_DIR="$output/zero-air" ZIG_AIR_JSON_FILTER=error_union_zero_array. \
  "$zig_air" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
  -target x86_64-linux -mcpu=baseline "${lib_args[@]}" \
  "$repo_root/tests/review/error_union_zero_array.zig" 2>"$output/zero-export.stderr"
python3 - "$output" "$version" <<'PYZERO'
import json, pathlib, sys
output, version = pathlib.Path(sys.argv[1]), sys.argv[2]
if 'air2lean:' in output.joinpath('zero-export.stderr').read_text():
    raise SystemExit('zero-array exporter warning')
files = list(output.joinpath('zero-air').glob('*.json'))
if len(files) != 1:
    raise SystemExit('zero-array AIR inventory mismatch')
data = json.loads(files[0].read_text())
if data['name'] != 'error_union_zero_array.zeroArray' or data['zig_version'] != version:
    raise SystemExit('zero-array AIR identity mismatch')
PYZERO
mkdir "$output/ErrorUnionZero"
if [ "$version" = 0.16.0 ]; then
  "$repo_root/.lake/build/bin/air2lean" "$output/zero-air" -o "$output/ErrorUnionZero/Gen.lean" \
    --namespace ErrorUnionZero --prefix error_union_zero_array.
  lake env lean -R "$output" -o "$output/ErrorUnionZero/Gen.olean" "$output/ErrorUnionZero/Gen.lean"
  cp "$repo_root/tests/review/ErrorUnionZeroGenerated.lean" "$output/ZeroModel.lean"
  LEAN_PATH="$output:$lean_path" lake env lean -R "$output" --run "$output/ZeroModel.lean"
else
  if "$repo_root/.lake/build/bin/air2lean" "$output/zero-air" -o "$output/ErrorUnionZero/Gen.lean" \
      --namespace ErrorUnionZero --prefix error_union_zero_array. 2>"$output/zero-rejection.stderr"; then
    echo 'accepted incompatible legacy zero-array memory ABI' >&2; exit 1
  fi
  python3 - "$output/zero-rejection.stderr" <<'PYREJECT'
import pathlib, sys
message = pathlib.Path(sys.argv[1]).read_text()
if 'size 8 and alignment 8, the compiler 2 and 2' not in message:
    raise SystemExit('wrong legacy zero-array rejection')
PYREJECT
fi
printf 'Generated error-union ABI qualification passed: %s\n' "$version"
