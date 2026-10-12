#!/usr/bin/env bash
# L14 error return tracing: translate the committed exports of every version (air/<version>),
# run the model on the native `main`'s inputs and compare with expected.txt, then run the CLI
# rejections. `--native ZIG` instead runs error_tracing.zig with a stock Zig (`-ferror-tracing`,
# ReleaseSafe) on this host and compares its output with expected.txt. Needs a built translator
# and `lake build ZigLean`.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
here=tests/roadmap/error-tracing
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-error-tracing.XXXXXX")
trap 'rm -rf "$work"' EXIT
if [ "${1:-}" = --native ]; then
  zig=${2:?usage: check.sh --native ZIG}
  cp "$here/error_tracing.zig" "$work/"
  "$zig" build-exe -OReleaseSafe -ferror-tracing "$work/error_tracing.zig" -femit-bin="$work/native" \
    --cache-dir "$work/cache" --global-cache-dir "$work/global-cache"
  "$work/native" 2> "$work/native.txt"
  diff -u "$here/expected.txt" "$work/native.txt"
  echo "error tracing native: $("$zig" version) ok"
  exit 0
fi
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
for version in 0.17.0 0.16.0 0.15.2 0.14.1; do
  "$translator" "$here/air/$version" -o "$work/$version.lean" --namespace ErrorTracing
  cat "$here/Runner.lean" >> "$work/$version.lean"
  lake env lean --run "$work/$version.lean" > "$work/$version.txt"
  diff -u "$here/expected.txt" "$work/$version.txt"
done
PYTHONDONTWRITEBYTECODE=1 python3 "$here/test_cli.py" "$translator"
echo "error tracing: 4 versions match expected.txt"
