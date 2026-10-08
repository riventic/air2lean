#!/usr/bin/env bash
# B1 regression (tests/roadmap/module-identity/README.md): two declarations with one fully
# qualified name in different modules must never become one exported identity.
#
# Env: AIR2LEAN_ZIG_AIR (required) a patched compiler with this exporter;
#      AIR2LEAN_TRANSLATOR (default .lake/build/bin/air2lean).
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
zig_air=${AIR2LEAN_ZIG_AIR:?set AIR2LEAN_ZIG_AIR to a patched compiler with this exporter}
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$zig_air" ] && [ -x "$translator" ] || { echo 'module identity: missing compiler or translator' >&2; exit 1; }
fixture=tests/roadmap/module-identity
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-module-identity.XXXXXX")
trap 'rm -rf "$work"' EXIT
fail() { echo "module identity: $*" >&2; exit 1; }

# dump <name> <filter> <zig args...>: AIR of one compilation into $work/<name>; status in $work/<name>.rc.
dump() {
  local name=$1 filter=$2; shift 2
  mkdir -p "$work/$name"
  local rc=0
  (cd "$fixture" && ZIG_AIR_JSON_DIR="$work/$name" ZIG_AIR_JSON_FILTER="$filter" "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
    --cache-dir "$work/cache-$name" --global-cache-dir "$work/global-cache" "$@") \
    2> "$work/$name.log" || rc=$?
  echo "$rc" > "$work/$name.rc"
}

# 1. Two modules, one `util.helper`: the exporter fails closed.
dump mods main.,util. --dep other -Mroot=mods/main.zig -Mother=mods/other/root.zig
[ "$(cat "$work/mods.rc")" != 0 ] || fail 'exporter accepted two util.helper declarations'
grep -Fq 'two different declarations export the output identity' "$work/mods.log" || {
  cat "$work/mods.log" >&2; fail 'missing explicit identity collision error'; }

# 2. Two input files that claim one identity: the translator fails closed.
python3 "$fixture/check_identity.py" duplicate "$work/mods" "$work/dup"
if "$translator" "$work/dup" -o "$work/Dup.lean" --namespace Dup --prefix main. 2> "$work/dup.log"; then
  fail 'translator accepted two files with one identity'
fi
grep -Fq "duplicate function name 'util.helper'" "$work/dup.log" || {
  cat "$work/dup.log" >&2; fail 'missing duplicate identity error'; }
[ ! -e "$work/Dup.lean" ] || fail 'translator wrote output for duplicate identities'

echo 'module identity regression passed'
