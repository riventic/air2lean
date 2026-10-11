#!/usr/bin/env bash
# S1.1 property test (tests/roadmap/instance-identity/README.md): a generic instance has the same
# content-addressed key in every program and source order, and two different instances never
# share one.
#
# Env: AIR2LEAN_ZIG_AIR (required) a patched compiler with this exporter;
#      AIR2LEAN_TRANSLATOR (default .lake/build/bin/air2lean).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
zig_air=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to a patched compiler with this exporter}
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$zig_air" ] && [ -x "$translator" ] || { echo 'instance identity: missing compiler or translator' >&2; exit 1; }
fixture=tests/roadmap/instance-identity
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-instance-identity.XXXXXX")
trap 'rm -rf "$work"' EXIT
fail() { echo "instance identity: $*" >&2; exit 1; }

programs="a a_reordered b"
for p in $programs; do
  mkdir -p "$work/$p"
  (cd "$fixture" && ZIG_AIR_JSON_DIR="$work/$p" ZIG_AIR_JSON_FILTER="$p.,lib." "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
    --cache-dir "$work/cache-$p" --global-cache-dir "$work/global-cache" "$p.zig") 2> "$work/$p.log" ||
    { cat "$work/$p.log" >&2; fail "export of $p.zig failed"; }
  "$translator" "$work/$p" -o "$work/$p.lean" --namespace "P_$p" --prefix "$p." 2> "$work/$p.translate.log" ||
    { cat "$work/$p.translate.log" >&2; fail "translation of $p.zig failed"; }
done
python3 "$fixture/check_instances.py" "$work" $programs
