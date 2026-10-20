#!/usr/bin/env bash
# L04 pointer-try lifetimes and native runs (README.md). Lake builds the library TryLifetimes
# (tests/roadmap/lakefile.toml; scripts/fixtures.py, run it under scripts/build-guard.py).
#   check.sh [--check]          translate air/<version>/ (0.14.1, 0.15.2, 0.16.0, 0.17.0), compare
#                               with TryLifetimes/<version>/Gen.lean, check that each version's
#                               Lifetimes.lean is the 0.17.0 one with the version renamed, build
#                               the library, audit the axioms and run each version's Lifetimes
#                               `main` (kernel-checked sequential theorems, 32 scheduler oracles)
#   check.sh --native VERSION   with a stock Zig VERSION (AIR2LEAN_ZIG_NATIVE): the tests of
#                               try_pointers.zig, try_aliases.zig and try_lifetimes.zig for
#                               x86_64-linux-musl, ReleaseSafe and Debug, in Docker linux/amd64
#                               (AIR2LEAN_X86_64_RUN overrides the runner; empty: the host)
#   check.sh --export VERSION DIR   fresh AIR of try_lifetimes.zig (AIR2LEAN_ZIG_AIR)
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$repo_root"
dir=tests/roadmap/try-pointers/lifetimes
versions=(0.14.1 0.15.2 0.16.0 0.17.0)
case "${1:---check}" in
  --export)
    [ "$#" -eq 3 ] || { echo 'usage: check.sh --export VERSION DIR' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_AIR:?set a patched Zig with the repository exporter}"
    mkdir -p "$3"
    [ -z "$(find "$3" -mindepth 1 -maxdepth 1 -print -quit)" ] || { echo "$3 must be empty" >&2; exit 1; }
    ZIG_AIR_JSON_DIR="$(cd -- "$3" && pwd)" ZIG_AIR_JSON_FILTER=try_lifetimes. \
      "$AIR2LEAN_ZIG_AIR" build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing \
      -target x86_64-linux -mcpu=baseline "$dir/try_lifetimes.zig"
    exit ;;
  --native)
    [ "$#" -eq 2 ] || { echo 'usage: check.sh --native VERSION' >&2; exit 2; }
    : "${AIR2LEAN_ZIG_NATIVE:?set a stock Zig of that version}"
    work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-native.XXXXXX")
    trap 'rm -rf "$work"' EXIT
    for src in tests/roadmap/try-pointers/try_pointers.zig tests/roadmap/try-pointers/try_aliases.zig \
        "$dir/try_lifetimes.zig"; do
      for mode in ReleaseSafe Debug; do
        bin="$work/$(basename "$src" .zig)-$mode"
        "$AIR2LEAN_ZIG_NATIVE" test "$src" "-O$mode" -target x86_64-linux-musl --test-no-exec \
          -femit-bin="$bin"
        if [ -n "${AIR2LEAN_X86_64_RUN+set}" ]; then
          # shellcheck disable=SC2086
          ${AIR2LEAN_X86_64_RUN} "$bin"
        else
          docker run --rm --platform linux/amd64 -v "$work:/w:ro" alpine:3 "/w/$(basename "$bin")"
        fi
        echo "$2 x86_64-linux-musl $mode: $(basename "$src") tests pass"
      done
    done
    exit ;;
  --check) [ "$#" -le 1 ] || { echo 'usage: check.sh [--check]' >&2; exit 2; } ;;
  *) echo 'usage: check.sh [--check|--native VERSION|--export VERSION DIR]' >&2; exit 2 ;;
esac
translator=${AIR2LEAN_TRANSLATOR:-"$repo_root/.lake/build/bin/air2lean"}
[ -x "$translator" ] || { echo 'build the translator first (lake build air2lean)' >&2; exit 1; }
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/air2lean-try-lifetimes.XXXXXX")
trap 'rm -rf "$work"' EXIT
primary="$dir/TryLifetimes/V0_17_0/Lifetimes.lean"
modules=() mains=() theorems=()
for v in "${versions[@]}"; do
  t="V${v//./_}"
  # The retained translation is the fresh one, byte for byte (Lake builds the retained file).
  "$translator" "$dir/air/$v" -o "$work/$t.lean" --namespace "TryLifetimes.$t" \
    --prefix try_lifetimes.
  cmp "$work/$t.lean" "$dir/TryLifetimes/$t/Gen.lean"
  # Every version's module states the same theorems: the 0.17.0 one, the version renamed.
  [ "$t" = V0_17_0 ] || python3 -B scripts/fixtures.py instance "$primary" --subst "V0_17_0=$t"
  modules+=("TryLifetimes.$t.Lifetimes")
  mains+=("TryLifetimes.$t.Lifetimes:TryLifetimes.$t.Lifetimes.main")
  theorems+=(--declaration "TryLifetimes.$t.Lifetimes.readDangling_illegal")
done
python3 -B scripts/fixtures.py build TryLifetimes
# Compiled and audited (axioms, sorry, kernel replay), not only run: they are indexed (F2).
python3 -B scripts/fixtures.py audit "${modules[@]}" "${theorems[@]}"
python3 -B scripts/fixtures.py run "$work/out" "${mains[@]}"
for v in "${versions[@]}"; do
  echo "$v: $(cat "$work/out/TryLifetimes.V${v//./_}.Lifetimes.txt")"
done
