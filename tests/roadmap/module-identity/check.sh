#!/usr/bin/env bash
# B1 regression (tests/roadmap/module-identity/README.md): a fully qualified name in one module
# never becomes the identity of a declaration in another module.
#
# Env: AIR2LEAN_ZIG_AIR (required) a patched compiler with this exporter;
#      AIR2LEAN_TRANSLATOR (default .lake/build/bin/air2lean);
#      AIR2LEAN_ZIG_NATIVE (optional) a stock zig of the same version: the native reference.
# Checks generated Lean with `lake env lean` (ZigLean must be built).
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

# dump <name> <filter> <zig args...>: AIR of one compilation into $work/<name>.
dump() {
  local name=$1 filter=$2; shift 2
  mkdir -p "$work/$name"
  (cd "$fixture" && ZIG_AIR_JSON_DIR="$work/$name" ZIG_AIR_JSON_FILTER="$filter" "$zig_air" \
    build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
    --cache-dir "$work/cache-$name" --global-cache-dir "$work/global-cache" "$@") 2> "$work/$name.log"
}

# translate <name> <Ns>: $work/<name> to $work/<Ns>.lean.
translate() {
  "$translator" "$work/$1" -o "$work/$2.lean" --namespace "$2" --prefix main. 2> "$work/$2.log"
}

# evaluate <Ns> <x> <expected>...: the generated entry function's results, checked in Lean.
evaluate() {
  local ns=$1; shift
  cp "$work/$ns.lean" "$work/$ns.Check.lean"
  while [ "$#" -gt 0 ]; do
    printf '#guard match (%s.entry %s#32).run with | some (.ok v) => v == %s#32 | _ => false\n' \
      "$ns" "$1" "$2" >> "$work/$ns.Check.lean"
    shift 2
  done
  # A temporary package root permits checking a generated file outside the checkout.
  lake env lean -R "$work" "$work/$ns.Check.lean"
}

native() {
  [ -n "${AIR2LEAN_ZIG_NATIVE:-}" ] || return 0
  (cd "$fixture" && "$AIR2LEAN_ZIG_NATIVE" test -OReleaseSafe \
    --cache-dir "$work/native-cache" --global-cache-dir "$work/native-global-cache" "$@")
}

# 1. Two modules, one `util.helper`: two files, each call bound to its module's function, and
#    a translation that computes what Zig computes, (x+1) + 3x.
dump mods main.,util. --dep other -Mroot=mods/main.zig -Mother=mods/other/root.zig ||
  { cat "$work/mods.log" >&2; fail 'two-module export failed'; }
python3 "$fixture/check_identity.py" mods "$work/mods"
translate mods Mods || { cat "$work/Mods.log" >&2; fail 'two-module translation failed'; }
grep -q '^def other_util_helper ' "$work/Mods.lean" || fail 'no definition for other:util.helper'
grep -q 'Zig.call (other_util_helper p0)' "$work/Mods.lean" || fail 'entry does not call other:util.helper'
evaluate Mods 5 21 0xFFFFFFFF 0xFFFFFFFD
native --dep other -Mroot=mods/native_test.zig -Mother=mods/other/root.zig

# 2. A user `Thread.zig` (struct `Thread`, function `Thread.spawn`) is user code, never the
#    std `Thread` model: without its AIR the call has no target, with it the call is translated.
dump thread-alone main. thread/main.zig || { cat "$work/thread-alone.log" >&2; fail 'thread export failed'; }
if translate thread-alone ThreadAlone; then fail 'a user Thread.spawn without AIR was accepted'; fi
grep -Fq "the callee 'root:Thread.spawn' has no AIR file" "$work/ThreadAlone.log" || {
  cat "$work/ThreadAlone.log" >&2; fail 'missing no-AIR error for the user Thread.spawn'; }
dump thread main.,Thread. thread/main.zig || { cat "$work/thread.log" >&2; fail 'thread export failed'; }
python3 "$fixture/check_identity.py" thread "$work/thread"
translate thread UserThread || { cat "$work/UserThread.log" >&2; fail 'user Thread translation failed'; }
grep -q '^structure root_Thread ' "$work/UserThread.lean" || fail 'the user Thread struct is not a struct'
grep -q '^def root_Thread_spawn ' "$work/UserThread.lean" || fail 'the user Thread.spawn is not translated'
if grep -q 'Zig.spawn' "$work/UserThread.lean"; then fail 'the user Thread.spawn uses the std model'; fi
evaluate UserThread 5 12 0xFFFFFFFF 6
native thread/native_test.zig

# 3. The root and std modules both have `ascii.isDigit`, with one historical file name: the
#    exporter fails closed.
if dump collide main.,ascii. collide/main.zig; then fail 'exporter wrote two ascii.isDigit functions to one file'; fi
grep -Fq "two different declarations export the output identity 'ascii.isDigit.json'" "$work/collide.log" || {
  cat "$work/collide.log" >&2; fail 'missing explicit identity collision error'; }

# 4. Two input files that claim one identity: the translator fails closed.
python3 "$fixture/check_identity.py" duplicate "$work/mods" "$work/dup"
if translate dup Dup; then fail 'translator accepted two files with one identity'; fi
grep -Fq "duplicate function name 'util.helper'" "$work/Dup.log" || {
  cat "$work/Dup.log" >&2; fail 'missing duplicate identity error'; }
[ ! -e "$work/Dup.lean" ] || fail 'translator wrote output for duplicate identities'

echo 'module identity regression passed'
