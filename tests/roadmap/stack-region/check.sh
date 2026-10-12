#!/usr/bin/env bash
# MM-16 (docs/architecture-audit/memory-model.md): per-thread stack regions.
#
#   tests/roadmap/stack-region/check.sh                  # kernel regressions (Regressions.lean)
#   AIR2LEAN_STACK_ZIG=$HOME/.cache/air2lean/host-0.17.0/zig \
#     tests/roadmap/stack-region/check.sh [--docker-linux] # + the native fixture (evidence.zig)
#
# The native fixture runs on the host; --docker-linux also cross-compiles it for x86_64-linux and
# aarch64-linux and runs it in the local-CI images (--platform linux/amd64 under Rosetta, native
# linux/arm64). Every run must show E1' (an inlined callee's local and a later local of its caller
# share an address) and E2 (sibling calls share a slot), and on Linux E3 (a spawned thread's local
# lies in an anonymous mapping, MM-19). E1 (inlined callee above its caller) is printed: it holds
# on most rows and not on aarch64-linux 0.14.1/0.15.2, so the order is not fixed either way. The
# model reproduces these layouts under some placement (Regressions.lean `e1_native_layout`).
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$here/../../.." && pwd)
cd "$repo_root"
docker_linux=0
for arg in "$@"; do
  case "$arg" in
    --docker-linux) docker_linux=1 ;;
    *) echo "usage: $0 [--docker-linux]" >&2; exit 2 ;;
  esac
done
fail() { echo "stack-region: $1" >&2; exit 1; }

lake build ZigLean.Mem.Lemmas ZigLean.Mem.Alloc
out=$(lake env lean "$here/Regressions.lean" 2>&1) || { echo "$out"; fail 'Regressions.lean does not check'; }
echo "$out"
[ "$(grep -c 'depends on axioms' <<<"$out")" = 6 ] || fail 'expected 6 axiom reports'
used=$(grep -o 'axioms: \[[^]]*\]' <<<"$out" | sed 's/axioms: \[//; s/\]//' | tr ',' '\n' | tr -d ' ' | sort -u)
for a in $used; do
  case "$a" in propext|Quot.sound|Classical.choice) ;; *) fail "nonstandard axiom $a" ;; esac
done

zig=${AIR2LEAN_STACK_ZIG:-}
[ -n "$zig" ] || { echo 'stack-region: native fixture skipped (AIR2LEAN_STACK_ZIG unset)'; exit 0; }
work=$(mktemp -d "${TMPDIR:-/tmp}/air2lean-stack-region.XXXXXX")
trap 'rm -rf "$work"' EXIT

# expect <label> <output>: E1' and E2 always, E3 on Linux.
expect() {
  local label=$1 text=$2
  echo "--- $label"; echo "$text"
  field() { awk -v k="$1" '$1 == k { print $2; exit }' <<<"$text"; }
  [ "$(field "E1'")" = 1 ] || fail "$label: E1' (shared slot) not observed"
  [ "$(field E2)" = 1 ] || fail "$label: E2 (sibling slot reuse) not observed"
  case "$label" in
    *linux*) [ "$(field E3)" = 1 ] || fail "$label: E3 (child local in its thread mapping) not observed" ;;
  esac
  case "$(field E1)" in 0|1) ;; *) fail "$label: no E1 line" ;; esac
}

build() {  # build <out> [target]
  "$zig" build-exe -OReleaseSafe -fno-error-tracing ${2:+-target "$2"} "$here/evidence.zig" \
    -femit-bin="$1" --cache-dir "$work/cache" >/dev/null
}
version=$("$zig" version)
if build "$work/host" 2>"$work/host.log"; then
  expect "host $(uname -sm) $version" "$("$work/host" 2>&1)"
elif [ "$docker_linux" = 1 ] && [ "$(uname -s)" = Darwin ]; then
  # 0.14.1 and 0.15.2 do not link against the current macOS SDK; the Linux rows still run.
  echo "--- host $(uname -sm) $version: does not link, skipped"
else
  cat "$work/host.log" >&2; fail 'native build failed'
fi
if [ "$docker_linux" = 1 ]; then
  build "$work/ev-x86_64" x86_64-linux
  build "$work/ev-aarch64" aarch64-linux
  expect "x86_64-linux $version" "$(docker run --rm --platform linux/amd64 -v "$work:/w" \
    air2lean-local-ci:amd64 /w/ev-x86_64 2>&1)"
  expect "aarch64-linux $version" "$(docker run --rm --platform linux/arm64 -v "$work:/w" \
    air2lean-local-ci:arm64 /w/ev-aarch64 2>&1)"
fi
echo 'stack-region: ok'
