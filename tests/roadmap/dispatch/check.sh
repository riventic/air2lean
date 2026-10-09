#!/usr/bin/env bash
# Run only under the root's serialized compiler guard; CI runs one profile per matrix job.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
synthetic=1
native=1
case "$#" in
  0) ;;
  1) case "$1" in
    --synthetic-only) native=0 ;;
    --native-only) synthetic=0 ;;
    *) echo 'usage: dispatch/check.sh [--synthetic-only|--native-only]' >&2; exit 2 ;;
  esac ;;
  *) echo 'too many arguments' >&2; exit 2 ;;
esac
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-dispatch.XXXXXX")
case "${AIR2LEAN_DISPATCH_KEEP_WORK:-0}" in
  0) trap 'rm -rf "$work"' EXIT ;;
  1) trap 'echo "retained fresh dispatch artifacts: $work"' EXIT ;;
  *) rm -rf "$work"; echo 'AIR2LEAN_DISPATCH_KEEP_WORK must be 0 or 1' >&2; exit 2 ;;
esac
python3 tests/roadmap/dispatch/test_harness.py
lake build Air2Lean Air2Lean.Check Air2Lean.Emit ZigLean air2lean
if [ "$synthetic" = 1 ]; then
  lake env lean tests/roadmap/dispatch/Proofs.lean
  lake env lean --run tests/roadmap/dispatch/Emitter.lean "$work/generated"
  python3 - "$work/generated" <<'CHECK'
from pathlib import Path
import sys
root = Path(sys.argv[1])
expected = {'step','fixedCapture','blockCapture','nested','crossed','ranges','boolLoop','fieldCollision','plainExit','blockDispatch','nestedExit','innerValue','countdown'}
actual = {p.stem for p in root.glob('*.lean')}
assert actual == expected, (actual, expected)
CHECK
  for source in "$work/generated/"*.lean; do
    lake env lean -R "$work/generated" -o "${source%.lean}.olean" "$source"
  done
  # Invariant/measure proofs about the fresh generated nested dispatch machine.
  # Compiled and audited (axioms, sorry, kernel replay), not only elaborated: it is indexed (F2).
  python3 -B scripts/theorem_universe.py gate tests/roadmap/dispatch/CountdownProof.lean \
    --root tests/roadmap/dispatch --lean-path "$work/generated" --output-dir "$work/universe"
  python3 tests/roadmap/dispatch/mutations.py "$work/generated" "$work/mutants"
fi
if [ "$native" = 0 ]; then echo 'dispatch synthetic and kernel-proof regressions passed'; exit 0; fi
version=${AIR2LEAN_DISPATCH_ZIG_VERSION:-0.16.0}
zig_air=${AIR2LEAN_DISPATCH_ZIG_AIR:-"$repo_root/zig-air-$version/bin/zig"}
zig_stock=${AIR2LEAN_DISPATCH_ZIG_STOCK:-zig}
case "$version" in 0.14.1|0.15.2|0.16.0) ;; *) echo "unsupported dispatch profile: $version" >&2; exit 2;; esac
[ "$("$zig_stock" version)" = "$version" ] || { echo 'dispatch stock compiler version mismatch' >&2; exit 1; }
[ "$("$zig_air" version)" = "$version" ] || { echo 'dispatch exporter version mismatch' >&2; exit 1; }
# Native behavior and exporter/translator behavior must both be exercised; neither is optional.
"$zig_stock" test tests/roadmap/dispatch/source.zig -OReleaseSafe
mkdir -p "$work/air"
ZIG_AIR_JSON_DIR="$work/air" ZIG_AIR_JSON_FILTER=source. "$zig_air" \
  build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing tests/roadmap/dispatch/source.zig
python3 tests/roadmap/dispatch/native_checks.py "$work/air" "$version" "$work/native-checks.lean"
.lake/build/bin/air2lean "$work/air" -o "$work/native.lean" --namespace DispatchNative --prefix source.
cat "$work/native-checks.lean" >> "$work/native.lean"
lake env lean -R "$work" "$work/native.lean"
echo "dispatch source/native/generated checks passed: Zig $version"
