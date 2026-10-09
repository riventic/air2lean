#!/usr/bin/env bash
# Architecture audit (concurrency): reproduce the model-side and native counterexamples of
# docs/architecture-audit/concurrency.md. Not a CI gate: it prints observations.
#   AIR2LEAN_ZIG_AIR     patched 0.16.0 AIR compiler (default /opt/dev/air2lean-build/zig-air-0.16.0/bin/zig)
#   AIR2LEAN_ZIG_NATIVE  stock 0.16.0 compiler (default ~/.cache/air2lean/host-0.16.0/zig)
# Run heavy steps through scripts/build-guard.py with the shared lock.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../../.." && pwd)
cd "$repo_root"
zig_air=${AIR2LEAN_ZIG_AIR:-/opt/dev/air2lean-build/zig-air-0.16.0/bin/zig}
zig_native=${AIR2LEAN_ZIG_NATIVE:-$HOME/.cache/air2lean/host-0.16.0/zig}
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-audit-conc.XXXXXX")
trap 'rm -rf "$work"' EXIT

# Model side: translate litmus.zig and enumerate every schedule of each fixture.
scripts/translate.sh "$here/litmus.zig" -o "$work/Litmus.lean" --namespace Litmus \
  --zig-air "$zig_air" --filter 'litmus.,atomic.Value(u32).init'
cat "$work/Litmus.lean" "$here/Enumerate.lean" > "$work/Run.lean"
lake env lean --run "$work/Run.lean" | tee "$work/model.txt"

# Native side (host: aarch64 macOS or Linux).
"$zig_native" build-exe -OReleaseFast "$here/native_litmus.zig" -femit-bin="$work/native_litmus" \
  --cache-dir "$work/zc"
"$work/native_litmus"
"$zig_native" build-exe -OReleaseSafe "$here/native_io.zig" -femit-bin="$work/native_io" \
  --cache-dir "$work/zc"
"$work/native_io"
if [ "$(uname -s)" = Darwin ]; then
  cc -O2 "$here/native_unfair_lock.c" -o "$work/native_unfair_lock"
  status=0
  "$work/native_unfair_lock" || status=$?
  echo "native_unfair_lock exit status $status (model: returns normally)"
fi

# Expected model observations (fuel 20 / 14); `fixed` lines flip an audit finding:
grep -q 'lbRelaxed: .*exhaustive=true' "$work/model.txt"
! grep -q 'lbRelaxed: .*ok(3)' "$work/model.txt"           # no load buffering (S4)
grep -q 'mpAllRelaxed: .*ok(100)' "$work/model.txt"         # stale MP allowed (sound)
! grep -q 'futexEarly: .*ok(1)' "$work/model.txt"           # no spurious wakeup (S2)
grep -q 'groupGate: .*deadlock' "$work/model.txt"           # S1 fixed: async may run eagerly
! grep -q 'stackLifetime: .*illegal' "$work/model.txt"      # frame end not an access (S3)
echo "audit observations reproduced"
