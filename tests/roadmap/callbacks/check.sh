#!/usr/bin/env bash
# E02: function-pointer call sites bound to registry contracts. Needs a built translator and
# `lake build ZigLean ZigLean.External.Callback ZigLean.Mem.Run Proofs.Asm.Effects`; runs no
# compiler. For each Zig version the committed exports translate under their registries (the
# 0.17.0 ones byte for byte to Callbacks/Gen.lean and Callbacks/Async.lean); the proofs check
# against the fresh 0.17.0 translations; test_cli.py covers the rejections.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/callbacks
here=tests/roadmap/callbacks
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
lean_cmd=(lake env lean)
if [ -n "${AIR2LEAN_LEAN:-}" ]; then lean_cmd=("$AIR2LEAN_LEAN"); fi
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-callbacks.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/Callbacks"
export LEAN_PATH="$work:$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
python3 - "$here" <<'PY'
import hashlib, json, pathlib, sys
here = pathlib.Path(sys.argv[1])
record = json.loads((here / 'provenance.json').read_text())
for name, digest in record['source_sha256'].items():
    assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest, name
files = {str(p.relative_to(here)): hashlib.sha256(p.read_bytes()).hexdigest()
         for d in ('air', 'air-async') for p in sorted((here / d).rglob('*.json'))}
assert files == record['air_sha256'], 'AIR fixtures differ from provenance.json'
PY
cp "$here/CallbackModel.lean" "$work/CallbackModel.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/CallbackModel.olean" "$work/CallbackModel.lean"
for version in 0.17.0 0.16.0 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/Callbacks/Gen.lean" --namespace Callbacks \
    --prefix callbacks. --profile abi64-le-v1 --model-registry "$here/registry-$version.json"
  "$translator" "$here/air-async/$version" -o "$work/Callbacks/Async.lean" --namespace Callbacks.Async \
    --prefix async_cb. --profile abi64-le-v1 --model-registry "$here/registry-async-$version.json"
  "${lean_cmd[@]}" -R "$work" -o "$work/Callbacks/Gen.olean" "$work/Callbacks/Gen.lean"
  "${lean_cmd[@]}" -R "$work" -o "$work/Callbacks/Async.olean" "$work/Callbacks/Async.lean"
done
# The proofs are about the fresh 0.17.0 translations, which are the retained ones.
for version in 0.17.0; do
  "$translator" "$here/air/$version" -o "$work/Callbacks/Gen.lean" --namespace Callbacks \
    --prefix callbacks. --profile abi64-le-v1 --model-registry "$here/registry-$version.json"
  "$translator" "$here/air-async/$version" -o "$work/Callbacks/Async.lean" --namespace Callbacks.Async \
    --prefix async_cb. --profile abi64-le-v1 --model-registry "$here/registry-async-$version.json"
done
cmp "$work/Callbacks/Gen.lean" "$here/Callbacks/Gen.lean"
cmp "$work/Callbacks/Async.lean" "$here/Callbacks/Async.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/Callbacks/Gen.olean" "$work/Callbacks/Gen.lean"
"${lean_cmd[@]}" -R "$work" -o "$work/Callbacks/Async.olean" "$work/Callbacks/Async.lean"
cp "$here/Callbacks/Proofs.lean" "$here/Callbacks/AsyncProofs.lean" "$work/Callbacks/"
"${lean_cmd[@]}" -R "$work" "$work/Callbacks/Proofs.lean"
"${lean_cmd[@]}" -R "$work" "$work/Callbacks/AsyncProofs.lean"
# The assumed foreign callback is the only reported assumption.
python3 -B scripts/external-contracts.py --check --expect-assumptions=extern:ext_visit \
  "$work/Callbacks/Gen.lean" > "$work/contracts.json"
# Semantic mutants of the retained translations: the unchanged proofs must reject each one.
python3 -B "$here/mutants.py" --self-test
python3 -B "$here/mutants.py" generate callbacks "$work/mutants" | while IFS=: read -r name module proofs; do
  mroot="$work/mutants/$name"
  for m in Callbacks/Gen.lean Callbacks/Async.lean; do
    [ -f "$mroot/$m" ] || cp "$here/$m" "$mroot/$m"
    "${lean_cmd[@]}" -R "$mroot" -o "$mroot/${m%.lean}.olean" "$mroot/$m"
  done
  cp "$here/$proofs" "$mroot/$proofs"
  status=0
  LEAN_PATH="$mroot:$LEAN_PATH" "${lean_cmd[@]}" -R "$mroot" "$mroot/$proofs" > "$mroot/log" 2>&1 || status=$?
  python3 -B "$here/mutants.py" classify "$name" "$status" "$mroot/log" "$mroot/$proofs"
done
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "callbacks: ok"
